import SP1Clean.Export.WriteHintRecordOrigins
import SP1Clean.Proofs.Completeness.WriteAllocationCursorTables
import SP1Clean.Soundness.AllocationWalks
import ToClean.Air.UnitBalance

/-! # Allocation walks in an arbitrary accepted native ensemble

The private cursor's sole physical participants are the allocation headers and fresh nodes.
The complete signed ledger retains padded occurrences before selecting its Boolean unit rows.
-/

namespace SP1Clean.Export.WriteObservationAssembly

open Circuit Air.Flat Semantics WriteAllocation WriteSourceRegistry
private abbrev F := ZMod SP1Prime
attribute [local instance 2000] FiniteField.instDecidableEq
variable {image : ProgramImage} {source target : ExecutionSnapshot} {final : HostHintQueue.State F}
attribute [local irreducible] base withSources preprocessing

private theorem allocator_channel : (cursorChannel (p := SP1Prime)).toRaw ∈ channels := by
  apply List.mem_of_getElem? (i := 16)
  rfl

/-- Complete allocation cursor ledger of the two installed physical tables. -/
theorem allocation_cursor_ledger (w : EnsembleWitness (preprocessing image source target final)) :
    let ch := (cursorChannel (p := SP1Prime)).toRaw
    w.interactionsWith ch = ((slot image source target final 15).table w).interactionsWith ch ++
      ((slot image source target final 16).table w).interactionsWith ch := by
  let ch := (cursorChannel (p := SP1Prime)).toRaw
  have support : selectedSlots source target ch = [15,16] := rfl
  simpa only [support,List.flatMap_cons,List.flatMap_nil,List.append_nil] using fresh_slots_ledger w ch allocator_channel
    (fun eq => Bool.noConfusion (congrArg (fun c => c.name == "sp1.native.write_readback") eq))

/-- Decode all physical environments of a guarded component, including its inactive rows. -/
def guardedInputs (I : TypeMap) [ProvableType I] (t : Table F) : List (I F × F) :=
  t.table.map fun row => valueFromOffset (ProvablePair I field) 0 (t.environment row)

/-- Select unit activities without identifying repeated occurrences. -/
def enabledInputs {I : Type*} (rows : List (I × F)) : List I :=
  (rows.filter fun r => decide (r.2 = 1)).map Prod.fst

private theorem input_ledger (I : TypeMap) [ProvableType I] (t : Table F) (ch : RawChannel F)
    (values : I F × F → List (Interaction F))
    (rows : ∀ env, t.component.operations.interactionValuesWith ch env =
      values (valueFromOffset (ProvablePair I field) 0 env)) :
    t.interactionsWith ch = (guardedInputs I t).flatMap values := by
  simp only [Table.interactionsWith,guardedInputs,List.flatMap_map]
  exact List.flatMap_congr fun row _ => rows (t.environment row)

/-- The complete signed endpoint ledger of guarded source/terminal pairs and guarded
transitions, as used by both WRITE node allocation and byte placement. Each zero gate is
checked before its occurrences are removed from the resulting permutation. -/
theorem gated_walk_endpoints {O R : Type*} {M : TypeMap} [ProvableType M] (ch : Channel F M)
    (os : List O) (og : O → F) (start finish : O → M F) (rs : List R) (rg : R → F) (src dst : R → M F)
    (ob : ∀ o ∈ os, IsBool (og o)) (rb : ∀ r ∈ rs, IsBool (rg r))
    (paid : BalancedInteractions ((os.flatMap fun o => [ch.pushedIfValue (og o) (start o),ch.pulledIfValue (og o) (finish o)]) ++
      rs.flatMap fun r => [ch.pulledIfValue (rg r) (src r),ch.pushedIfValue (rg r) (dst r)])) :
    let openers := os.filter fun o => decide (og o = 1)
    let rows := rs.filter fun r => decide (rg r = 1)
    (openers.map start ++ rows.map dst).Perm (openers.map finish ++ rows.map src) := by
  let opening := fun o => (finish o,start o)
  let step := fun r => (src r,dst r)
  have switched := List.Perm.flatMap_left os (f := fun o => [ch.pushedIfValue (og o) (start o),ch.pulledIfValue (og o) (finish o)])
    (g := fun o => [ch.pulledIfValue (og o) (opening o).1,ch.pushedIfValue (og o) (opening o).2])
    (fun _ _ => List.Perm.swap _ _ [])
  have live := (BalancedInteractions.of_perm paid (switched.append_right _)).filter_nonzero
  rw [List.filter_append,ch.gatedPairs_filter_nonzero os og opening ob] at live
  change BalancedInteractions (_ ++ ((rs.flatMap fun r =>
    [ch.pulledIfValue (rg r) (step r).1,ch.pushedIfValue (rg r) (step r).2]).filter _)) at live
  rw [ch.gatedPairs_filter_nonzero rs rg step rb] at live
  let edges := (os.filter fun o => decide (og o = 1)).map opening ++ (rs.filter fun r => decide (rg r = 1)).map step
  have grouped := ch.pairedLedger_perm edges id
  simp only [edges,List.flatMap_append,List.flatMap_map,List.map_append,List.map_map,Function.comp_def,id_eq] at grouped
  apply (ch.balanced_unit_iff _ _).mp
  simpa only [List.map_append,List.map_map,Function.comp_def,opening,step,List.append_assoc] using
    BalancedInteractions.of_perm live grouped

private theorem cursor_perm (os : List (Open F × F)) (ss : List (Step F × F))
    (ob : ∀ r ∈ os, IsBool r.2) (sb : ∀ r ∈ ss, IsBool r.2)
    (paid : BalancedInteractions (os.flatMap openCursors ++ ss.flatMap stepCursors)) :
    ((enabledInputs os).map Open.first ++ (enabledInputs ss).map Step.after).Perm
      ((enabledInputs os).map Open.last ++ (enabledInputs ss).map Step.before) := by
  simpa only [enabledInputs,List.map_map,Function.comp_def] using gated_walk_endpoints cursorChannel
    os Prod.snd (fun o => o.1.first) (fun o => o.1.last) ss Prod.snd (fun r => r.1.before) (fun r => r.1.after) ob sb paid

/-- The lists of allocating calls and fresh nodes decoded from their actual installed slots. -/
def allocationInputs (w : EnsembleWitness (preprocessing image source target final)) : List (Open F) × List (Step F) :=
  (enabledInputs (guardedInputs Open ((slot image source target final 15).table w)),
   enabledInputs (guardedInputs Step ((slot image source target final 16).table w)))

/-- Every physical unit node is a checked fresh append. Every first or successor cursor
is matched to a final or predecessor cursor at its complete typed value. -/
theorem allocation_endpoints (w : EnsembleWitness (assembly image source target final)) (checked : w.Constraints)
    (fit : w.InteractionsFit .logUp) (raw : w.Balanced .logUp) :
    let ins := allocationInputs (observed w)
    (ins.1.map Open.first ++ ins.2.map Step.after).Perm (ins.1.map Open.last ++ ins.2.map Step.before) ∧
      ∀ r ∈ ins.2, r.Valid := by
  let seen := observed w
  let o : TableSlot (preprocessing image source target final).tables openComponent := slot image source target final 15
  let s : TableSlot (preprocessing image source target final).tables stepComponent := slot image source target final 16
  let ch := (cursorChannel (p := SP1Prime)).toRaw
  have checks := (observed_constraints w).mp checked
  have paid := observed_balance w fit raw ch (protocol_installed image source target final _ allocator_channel) (of_decide_eq_true rfl)
  change BalancedInteractions (seen.interactionsWith ch) at paid
  rw [allocation_cursor_ledger seen] at paid
  have ol := input_ledger Open (o.table seen) ch openCursors (fun env => by
    rw [o.table_component seen]; exact openInput_cursors env)
  have sl := input_ledger Step (s.table seen) ch stepCursors (fun env => by
    rw [s.table_component seen]; exact stepInput_cursors env)
  change BalancedInteractions ((o.table seen).interactionsWith ch ++ (s.table seen).interactionsWith ch) at paid
  rw [ol,sl] at paid
  have ob : ∀ r ∈ guardedInputs Open (o.table seen), IsBool r.2 := by
    intro r member
    obtain ⟨row,mem,rfl⟩ := List.mem_map.mp member
    have checks' := o.table_constraints seen checks row mem
    rw [o.table_component seen] at checks'
    have flag := Guarded.activity_of_constraints openCircuit openSupported
      (varFromOffset (ProvablePair Open field) 0) _ _ ((Component.constraintsHold_iff _).mp checks')
    rwa [Guarded.eval_activity,eval_varFromOffset_valueFromOffset] at flag
  have sf : ∀ r ∈ guardedInputs Step (s.table seen), IsBool r.2 ∧ (r.2 = 1 → r.1.Valid) := by
    intro r member
    obtain ⟨row,mem,rfl⟩ := List.mem_map.mp member
    have checks' := s.table_constraints seen checks row mem
    have bytes := (byte_guarantees seen checks (observed_byte_balance w fit raw)).2 _ (s.table_mem seen) row mem
    rw [s.table_component seen] at checks' bytes
    have flag := Guarded.activity_of_constraints stepCircuit stepSupported
      (varFromOffset (ProvablePair Step field) 0) _ _ ((Component.constraintsHold_iff _).mp checks')
    rw [Guarded.eval_activity,eval_varFromOffset_valueFromOffset] at flag
    exact ⟨flag,HintRecordPublications.valid_step _ checks' bytes⟩
  refine ⟨cursor_perm _ _ ob (fun r m => (sf r m).1) paid, ?_⟩
  intro r mem
  obtain ⟨i,member,rfl⟩ := List.mem_map.mp mem
  obtain ⟨physical,active⟩ := List.mem_filter.mp member
  exact (sf _ physical).2 (of_decide_eq_true active)

/-- The number of nodes along a checked cursor walk is the decrease in its outstanding
count and the increase in its permanent allocation frontier. The source and clock persist. -/
theorem allocation_walk_progress {rows : List (Step F)} {start finish : Cursor F}
    (walk : Soundness.Walk.IsWalk (fun r : Step F => (r.before, r.after)) start finish rows)
    (valid : ∀ r ∈ rows, r.Valid) :
    Address.toNat start.remaining = Address.toNat finish.remaining + rows.length ∧
    Address.toNat finish.state.allocated = Address.toNat start.state.allocated + rows.length ∧
    start.source = finish.source ∧ start.state.clk_high = finish.state.clk_high ∧
    start.state.clk_low = finish.state.clk_low := by
  induction rows generalizing start with
  | nil =>
    change start = finish at walk
    simp [walk]
  | cons r rs ih =>
    obtain ⟨same, next⟩ := walk
    change r.before = start at same
    subst start
    obtain ⟨remaining, allocated, src, high, low⟩ := ih next (fun x m => valid x (List.mem_cons_of_mem r m))
    change Address.toNat r.after.remaining = _ at remaining
    change Address.toNat finish.state.allocated = Address.toNat r.after.state.allocated + rs.length at allocated
    have v := valid r List.mem_cons_self
    have less : Address.toNat r.before.remaining = Address.toNat r.after.remaining + 1 := by
      have eq := v.2.2.2.2.2.2
      change Address.toNat r.remaining = Address.toNat r.index + Address.toNat (#v[1,0,0] : fields 3 F) at eq
      have one : Address.toNat (#v[1,0,0] : fields 3 F) = 1 := by decide
      rw [one] at eq
      exact eq
    have more : Address.toNat r.after.state.allocated = Address.toNat r.before.state.allocated + 1 :=
      v.2.1.2.2.2.2.2
    simp only [List.length_cons]
    exact ⟨by omega,by omega,src,high,low⟩

/-- The allocation slots of any accepted witness partition into exhaustive authenticated
walks in physical opening order. Each consumes exactly the authorised number of fresh nodes,
including zero on empty hooks. Final cursors retain their full source, clock and state. -/
theorem native_allocation_walks (w : EnsembleWitness (assembly image source target final)) (checked : w.Constraints)
    (fit : w.InteractionsFit .logUp) (raw : w.Balanced .logUp) :
    let ins := allocationInputs (observed w)
    ∃ paths : List (List (Step F) × Cursor F),
      List.Forall₂ (fun (call : Open F) path =>
        Soundness.Walk.IsWalk (fun r : Step F => (r.before, r.after)) call.first path.2 path.1 ∧
        path.1.length = Address.toNat call.count ∧
        Address.toNat path.2.state.allocated = Address.toNat call.previous.allocated + path.1.length ∧
        path.2.source = call.source ∧ path.2.state.clk_high = call.outgoing.clk_high ∧
        path.2.state.clk_low = call.outgoing.clk_low) ins.1 paths ∧
      (paths.map Prod.snd).Perm (ins.1.map Open.last) ∧ (paths.flatMap Prod.fst).Perm ins.2 := by
  let ins := allocationInputs (observed w)
  obtain ⟨matching, valid⟩ := allocation_endpoints w checked fit raw
  let edge := fun r : Step F => (r.before, r.after)
  have grows (r : Step F) (member : r ∈ ins.2) :
      Address.toNat r.before.state.allocated < Address.toNat r.after.state.allocated := by
    have succ : Address.toNat r.after.state.allocated = Address.toNat r.before.state.allocated + 1 :=
      (valid r member).2.1.2.2.2.2.2
    omega
  obtain ⟨paths, walking, ends, used⟩ := Soundness.Walk.partition_ranked edge
    (fun v => Address.toNat v.state.allocated) (ins.1.map Open.first) (ins.1.map Open.last) ins.2
    (by simpa only [Multiset.map_coe,Multiset.coe_add,Multiset.coe_eq_coe,edge] using matching) grows
  have terminals := Multiset.coe_eq_coe.mp ends
  have consumed := Multiset.coe_eq_coe.mp used
  refine ⟨paths, ?_, terminals, consumed⟩
  rw [List.forall₂_map_left_iff] at walking
  apply List.forall₂_iff_zip.mpr
  refine ⟨walking.length_eq, ?_⟩
  intro call path pair
  have walk := (List.forall₂_iff_zip.mp walking).2 pair
  have mem : path ∈ paths := List.of_mem_zip pair |>.2
  have checkedPath : ∀ r ∈ path.1, r.Valid := fun r used =>
    valid r (consumed.mem_iff.mp (List.mem_flatMap.mpr ⟨path,mem,used⟩))
  obtain ⟨count, frontier, src, high, low⟩ := allocation_walk_progress walk checkedPath
  have ended := terminals.mem_iff.mp (List.mem_map_of_mem (f := Prod.snd) mem)
  obtain ⟨other, _, terminal⟩ := List.mem_map.mp ended
  have zero : Address.toNat path.2.remaining = 0 := by
    rw [← terminal]
    change Address.toNat (#v[0,0,0] : fields 3 F) = 0
    decide
  exact ⟨walk, by change path.1.length = Address.toNat call.first.remaining; omega,
    frontier,src.symm,high.symm,low.symm⟩

end SP1Clean.Export.WriteObservationAssembly
