import SP1Clean.Export.WriteDirectLanes
import SP1Clean.Export.WriteObservationReads
import SP1Clean.Proofs.Operations.WriteOctetRows
import SP1Clean.Soundness.WriteBufferCoverage

/-! # Selected guest octets from the original physical Memory suppliers -/

namespace SP1Clean.Export.WriteObservationAssembly
open Circuit Air.Flat Semantics Soundness WriteEffects WriteSourceRegistry
private abbrev F := ZMod SP1Prime
attribute [local instance 2000] FiniteField.instDecidableEq
variable {image : ProgramImage} {source target : ExecutionSnapshot} {final : HostHintQueue.State F}
attribute [local irreducible] base withSources preprocessing

private theorem paired {M I J : TypeMap} [ProvableType M] [ProvableType I] [ProvableType J] (ch : Channel F M)
    (seen : EnsembleWitness (preprocessing image source target final)) (a b : Fin 19)
    (registered : ch.toRaw ∈ channels) (separate : ch.toRaw ≠ WriteProbe.readbackChannel.toRaw) (support : selectedSlots source target ch.toRaw = [a,b])
    (push : I F → M F) (pull : J F → M F)
    (produced : ∀ env, (tables source target)[a.val].operations.interactionValuesWith ch.toRaw env =
      let r := valueFromOffset (ProvablePair I field) 0 env; [ch.pushedIfValue r.2 (push r.1)])
    (consumed : ∀ env, (tables source target)[b.val].operations.interactionValuesWith ch.toRaw env =
      let r := valueFromOffset (ProvablePair J field) 0 env; [ch.pulledIfValue r.2 (pull r.1)])
    (left : ∀ r ∈ guardedInputs I ((slot image source target final a).table seen), IsBool r.2)
    (right : ∀ r ∈ guardedInputs J ((slot image source target final b).table seen), IsBool r.2)
    (paid : seen.BalancedChannel ch.toRaw) :
    ((enabledInputs (guardedInputs I ((slot image source target final a).table seen))).map push).Perm
      ((enabledInputs (guardedInputs J ((slot image source target final b).table seen))).map pull) := by
  let s := slot image source target final a
  let t := slot image source target final b
  let xs := guardedInputs I (s.table seen)
  let ys := guardedInputs J (t.table seen)
  have lhs : (s.table seen).interactionsWith ch.toRaw = xs.map (fun r => ch.pushedIfValue r.2 (push r.1)) := by
    rw [List.map_eq_flatMap]
    simp only [Table.interactionsWith,xs,guardedInputs,List.flatMap_map,s.table_component seen]
    exact List.flatMap_congr fun row _ => produced _
  have rhs : (t.table seen).interactionsWith ch.toRaw = ys.map (fun r => ch.pulledIfValue r.2 (pull r.1)) := by
    rw [List.map_eq_flatMap]
    simp only [Table.interactionsWith,ys,guardedInputs,List.flatMap_map,t.table_component seen]
    exact List.flatMap_congr fun row _ => consumed _
  change BalancedInteractions (seen.interactionsWith ch.toRaw) at paid
  rw [fresh_slots_ledger seen _ registered separate,support] at paid
  simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil] at paid
  change BalancedInteractions ((s.table seen).interactionsWith ch.toRaw ++ (t.table seen).interactionsWith ch.toRaw) at paid
  rw [lhs,rhs] at paid
  simpa only [enabledInputs,List.map_map,Function.comp_def] using
    ch.gated_perm_of_balanced xs Prod.snd (fun r => push r.1) ys Prod.snd (fun r => pull r.1) left right paid

private theorem active_facts {I : TypeMap} [ProvableType I] {t : Table F} {P : I F → Prop}
    (sound : ∀ row ∈ t.table, let x := valueFromOffset (ProvablePair I field) 0 (t.environment row)
      IsBool x.2 ∧ (x.2 = 1 → P x.1)) :
    (∀ x ∈ guardedInputs I t, IsBool x.2) ∧ ∀ x ∈ enabledInputs (guardedInputs I t), P x := by
  constructor
  · intro x m
    obtain ⟨row,present,rfl⟩ := List.mem_map.mp m
    exact (sound row present).1
  · intro x m
    obtain ⟨r,selected,rfl⟩ := List.mem_map.mp m
    obtain ⟨existsRow,on⟩ := List.mem_filter.mp selected
    obtain ⟨row,present,rfl⟩ := List.mem_map.mp existsRow
    exact (sound row present).2 (of_decide_eq_true on)

/-- Each enabled placement word has the exact key, clock and little-endian byte extraction
of an aligned RAM read covered by an original Memory supplier at that clock. -/
theorem native_guest_octets (w : EnsembleWitness (assembly image source target final)) (ok : w.Constraints)
    (fit : w.InteractionsFit .logUp) (raw : w.Balanced .logUp)
    (g : WriteEffects.Group F) (mem : g ∈ allocationGroups (observed w)) :
    ∃ s : WriteBuffer.Step F, s.Valid ∧
      WriteProbe.ReadMeaning (rawSource ((appended image source target final).project (observed w))) s.read ∧
      s.read.key = g.octets.key ∧ s.read.clock = g.octets.clock ∧
      ∀ i : Fin 8, g.octets.bytes[i].val < 256 ∧
        BitVec.ofNat 8 g.octets.bytes[i].val = s.read.value.toBitVec64.extractLsb' (8 * i.val) 8 := by
  let seen := observed w
  let b : TableSlot (preprocessing image source target final).tables WriteBuffer.wordComponent := slot image source target final 4
  let d := slot image source target final 6
  let p := slot image source target final 9
  have checked := (observed_constraints w).mp ok
  have byte := (byte_guarantees seen checked (observed_byte_balance w fit raw)).2
  have buf := active_facts (I := WriteBuffer.Step) (t := b.table seen) (P := WriteBuffer.Step.Valid) (by
    intro row m
    have c := b.table_constraints seen checked row m
    have v := byte _ (b.table_mem seen) row m
    rw [b.table_component seen] at c v
    exact WriteBuffer.wordInput_valid _ c v)
  have dec := active_facts (I := WordRow) (t := d.table seen) (P := WordRow.Valid) (by
    intro row m
    have c := d.table_constraints seen checked row m
    have v := byte _ (d.table_mem seen) row m
    rw [d.table_component seen] at c v
    exact decoder_valid_at _ c v)
  have grp := active_facts (I := WriteEffects.Group) (t := p.table seen) (P := WriteEffects.Group.Valid) (by
    intro row m
    have c := p.table_constraints seen checked row m
    rw [p.table_component seen] at c
    have facts := guarded_group_valid (varFromOffset (ProvablePair WriteEffects.Group field) 0) _ _ ((Component.constraintsHold_iff _).mp c)
    rwa [eval_varFromOffset_valueFromOffset] at facts)
  have regW : (WriteBuffer.wordChannel (p := SP1Prime)).toRaw ∈ channels := List.mem_of_getElem? (i := 5) rfl
  have regO : (octetsChannel (p := SP1Prime)).toRaw ∈ channels := List.mem_of_getElem? (i := 7) rfl
  have words := paired WriteBuffer.wordChannel seen 4 6 regW
    (fun eq => Bool.noConfusion (congrArg (fun c => c.name == "sp1.native.write_readback") eq))
    rfl WriteBuffer.Step.read WordRow.read WriteBuffer.word_forward_at decoder_word_at buf.1 dec.1
    (observed_balance w fit raw _ (protocol_installed image source target final _ regW) (of_decide_eq_true rfl))
  have octets := paired octetsChannel seen 6 9 regO
    (fun eq => Bool.noConfusion (congrArg (fun c => c.name == "sp1.native.write_readback") eq))
    rfl (fun r : WordRow F => r.octets (256 : F)⁻¹) WriteEffects.Group.octets decoder_octets_at group_octets_at dec.1 grp.1
    (observed_balance w fit raw _ (protocol_installed image source target final _ regO) (of_decide_eq_true rfl))
  obtain ⟨r,mr,equal⟩ := List.mem_map.mp (octets.mem_iff.mpr (List.mem_map_of_mem mem))
  obtain ⟨s,ms,same⟩ := List.mem_map.mp (words.mem_iff.mpr (List.mem_map_of_mem mr))
  have probe : WriteProbe.readChannel.pulledValue s.read ∈ seen.interactionsWith WriteProbe.readChannel.toRaw := by
    apply b.table_interactions_subset
    obtain ⟨x,kept,rfl⟩ := List.mem_map.mp ms
    obtain ⟨present,on⟩ := List.mem_filter.mp kept
    obtain ⟨row,m,rfl⟩ := List.mem_map.mp present
    apply List.mem_flatMap.mpr
    refine ⟨row,m,?_⟩
    change _ ∈ (b.table seen).component.operations.interactionValuesWith WriteProbe.readChannel.toRaw _
    rw [b.table_component seen,WriteBuffer.word_read_at]
    apply List.mem_singleton.mpr
    let input := valueFromOffset (ProvablePair WriteBuffer.Step field) 0 ((b.table seen).environment row)
    change WriteProbe.readChannel.pulledValue input.1.read = WriteProbe.readChannel.pulledIfValue input.2 input.1.read
    have active : input.2 = 1 := of_decide_eq_true on
    rw [active]; rfl
  have regR : (WriteProbe.readChannel (p := SP1Prime)).toRaw ∈ channels := List.mem_of_getElem? (i := 1) rfl
  have sourceRead := assembled_read_origin w ok fit raw s.read
    ((observed_ledger w _ (protocol_installed image source target final _ regR) (of_decide_eq_true rfl)) ▸ probe)
  refine ⟨s,buf.2 s ms,sourceRead,?_,?_,?_⟩
  · rw [same,← equal]; rfl
  · rw [same,← equal]; rfl
  · rw [same,← equal]
    exact dec.2 r mr

end SP1Clean.Export.WriteObservationAssembly
