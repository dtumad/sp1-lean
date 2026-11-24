import SP1Clean.Export.WriteAllocationWalks
import SP1Clean.Proofs.Operations.WriteMetadataRows

/-! # Authenticated endpoint metadata for actual allocating WRITE calls and nodes -/

namespace SP1Clean.Export.WriteObservationAssembly
open Circuit Air.Flat Semantics Soundness WriteAllocation WriteEffects WriteSourceRegistry
private abbrev F := ZMod SP1Prime
attribute [local instance 2000] FiniteField.instDecidableEq
variable {image : ProgramImage} {source target : ExecutionSnapshot} {final : HostHintQueue.State F}
attribute [local irreducible] base withSources preprocessing

private theorem not_supply {a : F} (r : Record F) (bit : IsBool a) : ¬(recordChannel.pulledIfValue a r).Push := by
  intro push
  rcases bit with rfl | rfl
  · exact push.1 rfl
  · exact push.2 rfl rfl

private theorem dispatch_no_push (t : Table F) (installed : t.component = dispatchComponent) (ok : t.Constraints)
    (funded : t.ChannelGuarantees Channels.byteChannel.toRaw) (P : Record F → Prop) : t.Authenticates recordChannel P := by
  intro row mem i occurrence positive
  have localOk := ok row mem
  have bytes := funded row mem
  rw [installed] at localOk bytes occurrence
  let env := t.environment row
  let input := valueFromOffset (ProvablePair Dispatch field) 0 env
  obtain ⟨flag,honest⟩ := dispatch_valid_at env localOk bytes
  change IsBool input.2 at flag
  change input.2 = 1 → input.1.Valid at honest
  have bit : IsBool (input.2 * input.1.flags.hook) := by
    rcases flag with inactive | active
    · simp [inactive,IsBool]
    · simpa only [active,one_mul] using (honest active).allocation_gates.1
  rw [dispatch_metadata_at] at occurrence
  obtain ⟨r,_,rfl⟩ := List.mem_map.mp occurrence
  exact (not_supply _ bit positive).elim

private theorem step_no_push (t : Table F) (installed : t.component = stepComponent) (ok : t.Constraints)
    (funded : t.ChannelGuarantees Channels.byteChannel.toRaw) (P : Record F → Prop) : t.Authenticates recordChannel P := by
  intro row mem i occurrence positive
  have localOk := ok row mem
  have bytes := funded row mem
  rw [installed] at localOk bytes occurrence
  let env := t.environment row
  let input := valueFromOffset (ProvablePair Step field) 0 env
  have flag := Guarded.activity_of_constraints stepCircuit stepSupported (varFromOffset (ProvablePair Step field) 0) _ _
    ((Component.constraintsHold_iff _).mp localOk)
  rw [Guarded.eval_activity,eval_varFromOffset_valueFromOffset] at flag
  change IsBool input.2 at flag
  have honest : input.2 = 1 → input.1.Valid := HintRecordPublications.valid_step _ localOk bytes
  have bit : IsBool (input.2*(1 - input.1.direct)) := by
    rcases flag with off | on
    · simp [off,IsBool]
    · rcases (honest on).1 with zero | one
      · simp only [on,zero,sub_zero,one_mul]; exact Or.inr rfl
      · simp only [on,one,sub_self,one_mul]; exact Or.inl rfl
  rw [step_metadata_at] at occurrence
  obtain rfl := List.mem_singleton.mp occurrence
  exact (not_supply _ bit positive).elim

/-- A real physical unit metadata read resolves to its public endpoint query and bounded
value. The only supplier is the verifier table. -/
theorem native_metadata_record (w : EnsembleWitness (assembly image source target final)) (checked : w.Constraints)
    (fit : w.InteractionsFit .logUp) (raw : w.Balanced .logUp) (r : Record F)
    (read : recordChannel.pulledValue r ∈ (observed w).interactionsWith recordChannel.toRaw) :
    r.Binds (.fromEndpoints source.host target.host) := by
  let seen := observed w
  let ch := (recordChannel (p := SP1Prime)).toRaw
  have ok := (observed_constraints w).mp checked
  have bytes := (byte_guarantees seen ok (observed_byte_balance w fit raw)).2
  have balance := observed_balance w fit raw ch (protocol_installed image source target final _ record_registered) (of_decide_eq_true rfl)
  change BalancedInteractions (seen.interactionsWith ch) at balance
  rw [allocation_metadata_ledger] at balance read
  apply authenticated_pull_of_tables _ recordChannel _ _ balance r read
  intro table member
  rcases List.mem_cons.mp member with rfl | rest
  · let s := slot image source target final 7
    exact stream_authenticates source.host target.host (s.table seen) (s.table_component seen) (s.table_constraints seen ok)
  rcases List.mem_cons.mp rest with rfl | last
  · let s := slot image source target final 8
    exact dispatch_no_push _ (s.table_component seen) (s.table_constraints seen ok) (bytes _ (s.table_mem seen)) _
  · obtain rfl := List.mem_singleton.mp last
    let s := slot image source target final 16
    exact step_no_push _ (s.table_component seen) (s.table_constraints seen ok) (bytes _ (s.table_mem seen)) _

/-- Every active hook allocation reads its authentic public hint length, even when the
buffer is empty and there are no occupied data blocks to request. -/
theorem native_returned_length (w : EnsembleWitness (assembly image source target final)) (checked : w.Constraints)
    (fit : w.InteractionsFit .logUp) (raw : w.Balanced .logUp) (r : Step F) (mem : r ∈ (allocationInputs (observed w)).2)
    (hook : r.direct = 0) :
    ∃ bytes, (StreamKey.returned (Address.toNat r.reply) (Address.toNat r.index)).contents
      (.fromEndpoints source.host target.host) = some bytes ∧ bytes.length = Address.toNat r.length := by
  let seen := observed w
  let h : TableSlot (preprocessing image source target final).tables stepComponent := slot image source target final 16
  obtain ⟨x,kept,same⟩ := List.mem_map.mp mem
  obtain ⟨physical,on⟩ := List.mem_filter.mp kept
  obtain ⟨row,m,found⟩ := List.mem_map.mp physical
  let data := valueFromOffset (ProvablePair Step field) 0 ((h.table seen).environment row)
  change data = x at found
  subst x
  change data.1 = r at same
  subst r
  have enabled : data.2 = 1 := of_decide_eq_true on
  have paid : recordChannel.pulledValue data.1.metadata ∈ seen.interactionsWith recordChannel.toRaw := by
    rw [allocation_metadata_ledger]
    apply List.mem_flatMap.mpr
    refine ⟨h.table seen,List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),List.mem_flatMap.mpr ⟨row,m,?_⟩⟩
    change _ ∈ (h.table seen).component.operations.interactionValuesWith recordChannel.toRaw ((h.table seen).environment row)
    rw [h.table_component seen,step_metadata_at]
    apply List.mem_singleton.mpr
    change recordChannel.pulledValue _ = recordChannel.pulledIfValue (data.2*(1-data.1.direct)) _
    rw [enabled,hook,sub_zero,one_mul]; rfl
  have owned := (native_metadata_record w checked fit raw data.1.metadata paid).lookup
  have coords : data.1.metadata.query? = some (.length (.returned (Address.toNat data.1.reply) (Address.toNat data.1.index))) := by
    simp only [Record.query?,Step.metadata,show (4 : F).val = 4 by decide,ZMod.val_zero]; rfl
  rw [coords,Option.bind_some] at owned
  exact Option.map_eq_some_iff.mp owned

end SP1Clean.Export.WriteObservationAssembly
