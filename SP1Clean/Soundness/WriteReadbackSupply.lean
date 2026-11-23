import SP1Clean.Native.Operations.WriteProbeReadback
import ToClean.Air.Authentication
import ToClean.Circuit.EmittedInteraction

/-! # Authentication of counted WRITE versions on a physical read-back ledger

A nonzero version row consumes one complete receipt. Count-bounded balance forces that
receipt to originate in the original physical provider, including its two timestamps.
-/

namespace SP1Clean.WriteProbe.ReadbackSupply

open Circuit Air.Flat

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

private theorem occurrences (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactions =
      [(readbackChannel.pulledIf input.active input.receipt).toRaw,
       (versionChannel.emitted input.count input.version).toRaw] := by
  simp [main, ClockParts.circuit, ClockParts.main, circuit_norm, Gadgets.ToBits.rangeCheck, Gadgets.ToBits.toBits,
    Gadgets.ToBits.main, Gadgets.Equality.main, Operations.interactions, FormalAssertion.toSubcircuit_interactions,
    GeneralFormalCircuit.toSubcircuit_interactions]

omit [Fact (2 ^ 24 < p)] in
private theorem eval_receipt (env : Environment (ZMod p)) (input : Var Inputs (ZMod p)) :
    eval env input.receipt = (ProvableStruct.eval env input).receipt := by
  cases input
  simp only [Inputs.receipt, ClockParts.high24, ClockParts.low24, circuit_norm]

omit [Fact (2 ^ 24 < p)] in
private theorem eval_version (env : Environment (ZMod p)) (input : Var Inputs (ZMod p)) :
    eval env input.version = (ProvableStruct.eval env input).version := by
  cases input
  simp only [Inputs.version, ClockParts.address, circuit_norm]

/-- The original receipt is consumed at the physical row's activity, including zero. -/
theorem receipt_values (env : Environment (ZMod p)) :
    component.operations.interactionValuesWith readbackChannel.toRaw env =
      [readbackChannel.pulledIfValue (component.rowInput env).active (component.rowInput env).receipt] := by
  let input : Var Inputs (ZMod p) := varFromOffset Inputs 0
  have raw : component.operations.interactionsWith readbackChannel.toRaw =
      [(readbackChannel.pulledIf input.active input.receipt).toRaw] := by
    rw [Component.interactionsWith_eq]
    change ((main input).operations (size Inputs)).interactionsWith _ = _
    rw [Operations.interactionsWith, occurrences]
    simp [readbackChannel, versionChannel, circuit_norm]
  rw [Operations.interactionValuesWith, raw]
  simp only [List.map_cons, List.map_nil, Channel.eval_pulledIf, eval_receipt]
  change [readbackChannel.pulledIfValue (eval env input.active) (ProvableStruct.eval env input).receipt] =
    [readbackChannel.pulledIfValue (valueFromOffset Inputs 0 env).active (valueFromOffset Inputs 0 env).receipt]
  rw [← eval_varFromOffset_valueFromOffset]
  simp only [input, circuit_norm]

/-- Query multiplicity is the sole free field of this positive version occurrence. -/
theorem version_values (env : Environment (ZMod p)) :
    component.operations.interactionValuesWith versionChannel.toRaw env =
      [versionChannel.emittedValue (component.rowInput env).count (component.rowInput env).version] := by
  let input : Var Inputs (ZMod p) := varFromOffset Inputs 0
  have raw : component.operations.interactionsWith versionChannel.toRaw =
      [(versionChannel.emitted input.count input.version).toRaw] := by
    rw [Component.interactionsWith_eq]
    change ((main input).operations (size Inputs)).interactionsWith _ = _
    rw [Operations.interactionsWith, occurrences]
    simp [readbackChannel, versionChannel, circuit_norm]
  rw [Operations.interactionValuesWith, raw]
  simp only [List.map_cons, List.map_nil, Channel.eval_emitted, eval_version]
  change [versionChannel.emittedValue (env input.count) (ProvableStruct.eval env input).version] =
    [versionChannel.emittedValue (valueFromOffset Inputs 0 env).count (valueFromOffset Inputs 0 env).version]
  rw [← eval_varFromOffset_valueFromOffset]
  simp only [input, circuit_norm]

/-- The structural incoming channel has no semantic assumption. Raw constraints alone give
the activity, clock ranges and the ban on positive funding from inactive rows. -/
theorem valid_of_constraints (env : Environment (ZMod p)) (checked : component.operations.ConstraintsHold env) :
    Valid (component.rowInput env) := by
  apply (component.weakSoundness (by trivial) checked ?_).1
  apply (Operations.guarantees_iff component.operations
    [readbackChannel.toRaw] env (component.inChannelsOrGuarantees env)).mpr
  intro channel member
  obtain rfl := List.mem_singleton.mp member
  exact Operations.channelGuarantees_of_trivial _ (by simp [readbackChannel, Channel.toRaw]) _ _

/-- This component cannot fund its own source receipt, including on inactive rows. -/
theorem no_readback_push (property : Readback (ZMod p) → Prop) :
    component.Authenticates readbackChannel property := by
  apply Component.Authenticates.of_pulls
  intro env checked interaction member
  rw [receipt_values] at member
  obtain rfl := List.mem_singleton.mp member
  rcases (valid_of_constraints env checked).1 with off | on
  · exact Or.inl off
  · exact Or.inr ⟨rfl, on⟩

/-- The property of an authentic read-back transfers to an arbitrary counted version row.
All witness premises concern physical component identities, raw row constraints or the complete
balanced private ledger. Any number of source tables can be installed. -/
theorem authenticates_versions (sources : List (Table (ZMod p))) (supply : Table (ZMod p))
    (family : supply.component = component) (checked : supply.Constraints)
    (property : Readback (ZMod p) → Prop)
    (authentic : ∀ table ∈ sources, table.Authenticates readbackChannel property)
    (balanced : BalancedInteractions ((supply :: sources).flatMap (·.interactionsWith readbackChannel.toRaw))) :
    supply.Authenticates versionChannel (fun version =>
      ∃ record, property record ∧ version.key = record.key ∧ version.value = record.value ∧
        Address.toNat version.lower = Semantics.clkNat record.previousHigh record.previousLow ∧
        Address.toNat version.upper = Semantics.clkNat record.currentHigh record.currentLow) := by
  intro row member interaction emitted push
  rw [family, version_values] at emitted
  obtain rfl := List.mem_singleton.mp emitted
  let r := component.rowInput (supply.environment row)
  have valid := valid_of_constraints _ (family ▸ checked row member)
  obtain ⟨active, key, word, low, high⟩ := valid.counted push.1
  refine ⟨r.version, rfl, r.receipt, ?_, key, word, low, high⟩
  apply authenticated_pull_of_tables (supply :: sources) readbackChannel property _ balanced
  · apply List.mem_flatMap.mpr
    refine ⟨supply, List.mem_cons_self, List.mem_flatMap.mpr ⟨row, member, ?_⟩⟩
    rw [family, receipt_values, active]
    exact List.mem_singleton.mpr rfl
  · intro table included
    rcases List.mem_cons.mp included with rfl | other
    · apply Table.Authenticates.of_component table _ _ _ checked
      rw [family]
      exact no_readback_push _
    · exact authentic table other

end SP1Clean.WriteProbe.ReadbackSupply
