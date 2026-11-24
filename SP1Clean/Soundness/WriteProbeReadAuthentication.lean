import SP1Clean.Proofs.Operations.WriteProbeLedger
import SP1Clean.Soundness.WriteAccessInventory

/-! # Physical origins and live clocks of WRITE probe receipts -/

namespace SP1Clean.WriteProbe

open Circuit Air.Flat AccessInventory

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- A constrained observer's actual activity gate controls both the signed version pull
and the typed read receipt. The live row checks the inclusive integer clock interval. -/
theorem row_valid (env : Environment (ZMod p)) (checked : component.operations.ConstraintsHold env) :
    IsBool (valueFromOffset RowInput 0 env).2 ∧ ((valueFromOffset RowInput 0 env).2 = 1 → Spec (valueFromOffset RowInput 0 env).1) := by
  have valid := guarded_spec_of_constraints (varFromOffset RowInput 0) (size RowInput) env
    ((Component.constraintsHold_iff env).mp checked)
  simpa only [eval_varFromOffset_valueFromOffset] using valid

attribute [local irreducible] component valueFromOffset

/-- A version pull from a constrained probe cannot also fund another probe's version. -/
theorem no_version_push (property : Version (ZMod p) → Prop) : component.Authenticates versionChannel property := by
  apply Component.Authenticates.of_pulls
  intro env checked interaction member
  rw [component_versions] at member
  obtain rfl := List.mem_singleton.mp member
  let r := valueFromOffset RowInput 0 env
  change r.2 = 0 ∨ ((versionChannel.pulledIfValue r.2 r.1.version).direction = .pull ∧ r.2 = 1)
  rcases (row_valid env checked).1 with off | on
  · exact Or.inl off
  · exact Or.inr ⟨rfl, on⟩

variable [Fact (2 ^ 25 < p)]

/-- The returned word comes from a genuine physical record whose location and inclusive
integer clock interval cover this very observation. -/
def ReadMeaning (raw : Source → Table (ZMod p)) (read : Read (ZMod p)) : Prop :=
  ∃ record, (∃ id, Origin raw id record) ∧ read.key = record.key ∧ read.value = record.value ∧
    ValidKey (Address.toNat read.key) ∧ Address.Bounded read.clock ∧
    Semantics.clkNat record.previousHigh record.previousLow ≤ Address.toNat read.clock ∧
    Address.toNat read.clock ≤ Semantics.clkNat record.currentHigh record.currentLow

/-- Transfer authenticated version pulls through the physical probe's checked inclusive
clock inequalities and its shared key and value columns. -/
theorem authenticates_reads (raw : Source → Table (ZMod p)) (probe : Table (ZMod p))
    (registered : probe.component = component) (checked : probe.Constraints)
    (versions : ∀ v, versionChannel.pulledValue v ∈ probe.interactionsWith versionChannel.toRaw → Meaning raw v) :
    probe.Authenticates readChannel (ReadMeaning raw) := by
  intro row member interaction traffic push
  rw [registered, component_reads] at traffic
  obtain rfl := List.mem_singleton.mp traffic
  let input := valueFromOffset RowInput 0 (probe.environment row)
  have gates := row_valid (probe.environment row) (registered ▸ checked row member)
  have active : input.2 = 1 := gates.1.resolve_left push.1
  obtain ⟨_, key, _, _, clock, _, lower, upper⟩ := gates.2 active
  have pull : versionChannel.pulledValue input.1.version ∈ probe.interactionsWith versionChannel.toRaw := by
    apply List.mem_flatMap.mpr
    refine ⟨row, member, ?_⟩
    rw [registered, component_versions]
    change _ ∈ [versionChannel.pulledIfValue input.2 input.1.version]
    rw [active]
    exact List.mem_singleton.mpr rfl
  obtain ⟨record, origin, addr, word, lo, hi⟩ := versions _ pull
  exact ⟨input.1.read, rfl, record, origin, addr, word, key, clock, lo ▸ lower, hi ▸ upper⟩

end SP1Clean.WriteProbe
