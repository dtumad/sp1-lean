import SP1Clean.Export.WriteAllocationWalks
import SP1Clean.Proofs.Operations.QueueAllocationEdges
import SP1Clean.Soundness.HostHintReadLocalQueue

/-! # Global queue order with allocating WRITEs and ordinary hint handlers

The published source and target boundary tokens, fixed target seal, HINT_READ, both
HINT_LEN variants and the allocation headers share the same physical state ledger.
-/

namespace SP1Clean.Export.WriteObservationAssembly
open Circuit Air.Flat Semantics Soundness WriteSourceRegistry HostHintQueue WriteAllocation
private abbrev F := ZMod SP1Prime
local instance queueDecidableEq : DecidableEq F := FiniteField.instDecidableEq
variable {image : ProgramImage} {source target : ExecutionSnapshot} {final : State F}

/-- HINT_READ and both HINT_LEN families, with the concrete registry identity and the
canonical environment of each original physical row. -/
def hintHandlerRows (w : EnsembleWitness (preprocessing image source target final)) : List (HostQueueOrder.Row (p := SP1Prime)) :=
  TransitionView.readIndexedRows HostQueueOrder.indices (HostHintReadLocal.queueTables (hostWitness (supervisor w)))

private abbrev original (w : EnsembleWitness (preprocessing image source target final)) :
    EnsembleWitness (HostObserved.ensemble image source target final) := supervisor w

attribute [local irreducible] withSources preprocessing

private theorem supervisor_queue (w : EnsembleWitness (preprocessing image source target final)) :
    ((supervisor w).interactionsWith stateChannel.toRaw).Perm
      ((hintHandlerRows w).flatMap (fun row => [stateChannel.pulledValue (HostQueueOrder.edge row).1,
         stateChannel.pushedValue (HostQueueOrder.edge row).2]) ++
       [stateChannel.pushedValue (SP1Clean.HostHintQueueBoundary.initial source.host.io.hints),
        stateChannel.pulledValue final]) := by
  let orig := original w
  let memory := HostObserved.baseWitness orig
  let boundary := HostFinalMemory.baseWitness memory
  let host := hostWitness orig
  let ch := (stateChannel (p := SP1Prime)).toRaw
  have regs : ch ∈ HostLocalCore.registry image source
      (HintReadWordChip.stateChannel.toRaw :: HostFinalMemory.sourceChannels (p := SP1Prime) target.sail.memorySnapshot) := by
    simp [ch,HostLocalCore.registry,HostFinalMemory.sourceChannels,LocalCore.baseEnsemble,sp1Ensemble_channels]
  have diff {other : RawChannel F} (h : (other.name == ch.name) = false) : ch ≠ other :=
    fun eq => by rw [← eq,beq_self_eq_true] at h; contradiction
  have fm := HostFinalMemory.baseWitness_silent_interactions memory ch (List.mem_append_left _ (List.mem_append_left _ regs))
    (diff rfl) (diff rfl) (diff rfl)
  have obs := HostObserved.baseWitness_interactions orig ch
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ regs))) (diff rfl) (diff rfl)
  have split := HostHintQueueBoundary.queue_ledger boundary
    (HostHintQueueBoundary.source_queue_silent (p := SP1Prime) (source := source)
      (extra := FinalMemoryChecks.checkTables target.sail.memorySnapshot))
  change (orig.interactionsWith ch).Perm _
  rw [← obs,← fm]
  apply split.trans
  change ((HostHintReadLocal.queueTables host).flatMap _ ++ _).Perm _
  rw [HostQueueOrder.interactions _ (HostHintReadLocal.queueTables_aligned host)]
  exact .refl _

/-- The complete signed queue ledger. The old boundary pair, three ordinary handler
families, singleton rebase and all guarded allocator state replacements occur exactly once. -/
theorem allocation_queue_ledger (w : EnsembleWitness (preprocessing image source target final)) :
    let ch := (stateChannel (p := SP1Prime)).toRaw
    (w.interactionsWith ch).Perm
      (((hintHandlerRows w).flatMap (fun row => [stateChannel.pulledValue (HostQueueOrder.edge row).1,
         stateChannel.pushedValue (HostQueueOrder.edge row).2]) ++
       [stateChannel.pushedValue (SP1Clean.HostHintQueueBoundary.initial source.host.io.hints),stateChannel.pulledValue final]) ++
       (((slot image source target final 11).table w).interactionsWith ch ++
        ((slot image source target final 15).table w).interactionsWith ch)) := by
  let ch := (stateChannel (p := SP1Prime)).toRaw
  have support : selectedSlots source target ch = [11,15] := rfl
  have eq := selected_ledger w ch (fun eq => Bool.noConfusion (congrArg (fun c => c.name == "sp1.native.write_readback") eq))
  simp only [support,List.flatMap_cons,List.flatMap_nil,List.append_nil] at eq
  change (w.interactionsWith ch).Perm _
  rw [eq]
  exact (supervisor_queue w).append_right _

/-- The fixed seal exposes the last genuine global queue state of the segment. -/
def finalQueue (w : EnsembleWitness (preprocessing image source target final)) : State F :=
  let s := slot image source target final 11
  HostHintSnapshot.Seal.physicalState target.host.io.hints (s.table w) (s.table_component w)

/-- Each actual queue operation is a tagged ordinary handler or an allocating WRITE.
The row tags survive ordering and allow the allocation walks to be joined at their physical calls. -/
abbrev QueueOperation := HostQueueOrder.Row (p := SP1Prime) ⊕ Open F

/-- Source and target states published on the global hint queue, including its clock and frontier. -/
def queueEdge : QueueOperation → State F × State F :=
  Sum.elim HostQueueOrder.edge (fun r => (r.previous,r.outgoing))

/-- Unordered physical inventory used to recover chronological queue operations. -/
def queueOperations (w : EnsembleWitness (preprocessing image source target final)) : List QueueOperation :=
  (hintHandlerRows w).map Sum.inl ++ (allocationInputs w).1.map Sum.inr

private theorem rebase_endpoints (initial publicEnd actualEnd : State F)
    (hs as_ : List (State F × State F))
    (paid : BalancedInteractions ((hs.flatMap (fun e => [stateChannel.pulledValue e.1,stateChannel.pushedValue e.2]) ++
      [stateChannel.pushedValue initial,stateChannel.pulledValue publicEnd]) ++
      ([stateChannel.pulledValue actualEnd,stateChannel.pushedValue publicEnd] ++
      as_.flatMap (fun e => [stateChannel.pulledValue e.1,stateChannel.pushedValue e.2])))) :
    (initial :: (hs ++ as_).map Prod.snd).Perm (actualEnd :: (hs ++ as_).map Prod.fst) := by
  let edges := (actualEnd,publicEnd) :: (hs ++ as_)
  have grouped : BalancedInteractions (stateChannel.transitionLedger initial publicEnd edges id) := by
    apply BalancedInteractions.of_perm paid
    apply Multiset.coe_eq_coe.mp
    simp only [Channel.transitionLedger,edges,List.flatMap_cons,List.flatMap_append,id_eq,← Multiset.coe_add]
    ac_rfl
  have matched :=  (stateChannel.transitionLedger_balanced_iff initial publicEnd edges id).mp grouped
  change (initial :: publicEnd :: (hs ++ as_).map Prod.snd).Perm (publicEnd :: actualEnd :: (hs ++ as_).map Prod.fst) at matched
  exact List.Perm.cons_inv ((List.Perm.swap _ _ _).trans matched)

/-- Raw native acceptance anchors the complete typed queue-operation inventory between the
incoming fixed state and the private terminal state exposed by the physical seal. -/
theorem native_queue_endpoints (w : EnsembleWitness (native image source target)) (checked : w.Constraints)
    (fit : w.InteractionsFit .logUp) (raw : w.Balanced .logUp) :
    let seen := observed w
    let opening :=  SP1Clean.HostHintQueueBoundary.initial (p := SP1Prime) source.host.io.hints
    (opening :: (queueOperations seen).map (fun r => (queueEdge r).2)).Perm
      (finalQueue seen :: (queueOperations seen).map (fun r => (queueEdge r).1)) := by
  let seen := observed w
  let closing : State F := SP1Clean.HostHintQueueBoundary.initial (p := SP1Prime) target.host.io.hints
  let terminal : TableSlot (preprocessing image source target closing).tables (HostHintSnapshot.Seal.component target.host.io.hints) := slot image source target closing 11
  let o := slot image source target closing 15
  let ch := (stateChannel (p := SP1Prime)).toRaw
  have checked' := (observed_constraints w).mp checked
  have used : ch ∈ (preprocessing image source target closing).channels := by
    apply (preprocessing image source target closing).tables_channels _ (terminal.component_eq ▸ List.getElem_mem terminal.index.isLt)
    exact List.mem_of_getElem? (i := 0) rfl
  have balanced := observed_balance w fit raw ch used (of_decide_eq_true rfl)
  have paid := BalancedInteractions.of_perm balanced (allocation_queue_ledger seen)
  have sealed := HostHintSnapshot.Seal.physical_queue_ledger target.host.io.hints (terminal.table seen)
    (terminal.table_component seen) (terminal.table_constraints seen checked')
  let os := guardedInputs Open (o.table seen)
  have ol : (o.table seen).interactionsWith ch = os.flatMap queueValues := by
    simp only [Table.interactionsWith,os,guardedInputs,List.flatMap_map,o.table_component seen]
    exact List.flatMap_congr fun row _ => openInput_queue _
  have flags : ∀ r ∈ os, IsBool r.2 := by
    intro r member
    obtain ⟨row,m,rfl⟩ := List.mem_map.mp member
    have valid := o.table_constraints seen checked' row m
    rw [o.table_component seen] at valid
    exact (openInput_valid _ valid).1
  change BalancedInteractions ((_ ++ _) ++ ((terminal.table seen).interactionsWith ch ++ (o.table seen).interactionsWith ch)) at paid
  rw [sealed,ol] at paid
  let hs := (hintHandlerRows seen).map HostQueueOrder.edge
  let active := (os.filter fun r => decide (r.2 = 1))
  have activeEq : enabledInputs os = active.map Prod.fst := by
    unfold enabledInputs
    apply congrArg (List.map Prod.fst)
    apply congrArg (fun f => os.filter f)
    funext x
    exact congrArg (@decide _) (Subsingleton.elim _ _)
  let as_ := (enabledInputs os).map (fun r => (r.previous,r.outgoing))
  have unitPairs (rows : List (State F × State F)) :
      ((rows.flatMap (fun e => [stateChannel.pulledValue e.1,stateChannel.pushedValue e.2])).filter
        (fun i => decide (i.mult ≠ 0))) = rows.flatMap (fun e => [stateChannel.pulledValue e.1,stateChannel.pushedValue e.2]) := by
    apply List.filter_eq_self.mpr
    intro i member
    obtain ⟨r,_,mem⟩ := List.mem_flatMap.mp member
    rcases List.mem_cons.mp mem with rfl | tail
    · exact decide_eq_true (by exact one_ne_zero)
    · obtain rfl := List.mem_singleton.mp tail
      exact decide_eq_true (by exact one_ne_zero)
  have handlers : (hintHandlerRows seen).flatMap (fun r => [stateChannel.pulledValue (HostQueueOrder.edge r).1,
      stateChannel.pushedValue (HostQueueOrder.edge r).2]) =
      hs.flatMap (fun e => [stateChannel.pulledValue e.1,stateChannel.pushedValue e.2]) := by
    simp only [hs,List.flatMap_map]
  rw [handlers] at paid
  have live := paid.filter_nonzero
  have calls := stateChannel.gatedPairs_filter_nonzero os Prod.snd (fun r => (r.1.previous,r.1.outgoing)) flags
  change ((os.flatMap queueValues).filter _) = _ at calls
  change BalancedInteractions (((hs.flatMap (fun e => [stateChannel.pulledValue e.1,stateChannel.pushedValue e.2]) ++
      [stateChannel.pushedValue _,stateChannel.pulledValue closing]) ++
      ([stateChannel.pulledValue (finalQueue seen),stateChannel.pushedValue closing] ++ os.flatMap queueValues)).filter _) at live
  simp only [List.filter_append,unitPairs,calls] at live
  have result := rebase_endpoints (SP1Clean.HostHintQueueBoundary.initial source.host.io.hints) closing (finalQueue seen) hs as_
    (by simpa [as_,activeEq,active,List.flatMap_map,Channel.pushedValue,Channel.pulledValue] using live)
  simpa only [queueOperations,queueEdge,List.map_append,List.map_map,Function.comp_def,Sum.elim_inl,Sum.elim_inr,
    hs,as_,allocationInputs,os,o,seen,closing] using result

end SP1Clean.Export.WriteObservationAssembly
