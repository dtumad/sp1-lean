import SP1Clean.FormalModel.Contracts.WriteReadback
import SP1Clean.Proofs.Chips.MemoryBumpChip.Formal
import ToClean.Circuit.Receipt
import ToClean.Air.ComponentReplacement

/-! # Publishing genuine register read-back intervals

The installed MemoryBump row already consumes a register record and republishes its word at
a later clock. Its receipt exposes precisely that pair of clocks, key and unchanged word.
Physical padding contributes a zero-weight occurrence with the original row intact.
-/

namespace SP1Clean.WriteProbe

open Circuit Air.Flat Channels

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Both timestamps and the register value are projected from the actual refreshed Memory cells. -/
def refreshReadback {F : Type} [Zero F] [Add F] [Mul F] [OfNat F 256] [OfNat F 65536]
    (r : MemoryBumpChip.Inputs F) : Readback F :=
  ⟨#v[r.addr, 0, 0], r.access.access_timestamp.prev_high, r.access.access_timestamp.prev_low,
    r.clk_24_32 + r.clk_32_48 * 256, r.clk_0_16 + r.clk_16_24 * 65536, r.access.prev_value⟩

private def projection : Receipt.Projection (ZMod p) MemoryBumpChip.Inputs Readback :=
  ⟨fun input _ => input.is_real, fun input _ => refreshReadback input⟩

/-- Attach the private receipt to the released register-refresh circuit. -/
def refreshComponent : Component (ZMod p) :=
  { circuit := Receipt.circuit MemoryBumpChip.circuit readbackChannel (fun _ _ => trivial) projection
    Assumptions := MemoryBumpChip.circuit.Assumptions
    generation := MemoryBumpChip.generation }

/-- The existing Memory and Byte ledgers keep their exact messages, signs and padding rows. -/
theorem refresh_original_interactions (selected : RawChannel (ZMod p)) (other : selected ≠ readbackChannel.toRaw) :
    refreshComponent.operations.interactionsWith selected =
      (MemoryBumpChip.circuit.instantiate.operations 0).interactionsWith selected :=
  Receipt.interactions _ _ (fun _ _ => trivial) projection selected other

omit [Fact (2 ^ 17 < p)] in
/-- The symbolic interval projects the same register, old and new timestamps, and unchanged word
as the two Memory interactions of the original circuit. -/
theorem refresh_messages (r : Var MemoryBumpChip.Inputs (ZMod p)) :
    let receipt := refreshReadback r
    MemoryBumpChip.pulledMsg r = ⟨receipt.previousHigh, receipt.previousLow, receipt.key[0],
      receipt.key[1], receipt.key[2], receipt.value⟩ ∧
    MemoryBumpChip.pushedMsg r = ⟨receipt.currentHigh, receipt.currentLow, receipt.key[0],
      receipt.key[1], receipt.key[2], receipt.value⟩ := ⟨rfl, rfl⟩

/-- The new physical channel retains precisely one occurrence per original physical row. -/
theorem refresh_row_receipt (env : Environment (ZMod p)) :
    refreshComponent.operations.interactionValuesWith readbackChannel.toRaw env =
      [readbackChannel.pushedIfValue (valueFromOffset MemoryBumpChip.Inputs 0 env).is_real
        (refreshReadback (valueFromOffset MemoryBumpChip.Inputs 0 env))] := by
  have silent : readbackChannel.toRaw ∉ (MemoryBumpChip.circuit (p := p)).channels := by
    simp [MemoryBumpChip.circuit, readbackChannel, Channels.byteChannel, Channels.memoryChannel, circuit_norm]
  have row := Receipt.row_receipt MemoryBumpChip.circuit readbackChannel (fun _ _ => trivial) projection silent env
  change ((Receipt.circuit MemoryBumpChip.circuit readbackChannel (fun _ _ => trivial) projection).instantiate.operations 0).interactionValuesWith _ _ = _
  rw [row, ← eval_varFromOffset_valueFromOffset]
  simp only [projection, refreshReadback, circuit_norm]

private abbrev original : Component (ZMod p) :=
  { circuit := MemoryBumpChip.circuit, Assumptions := MemoryBumpChip.circuit.Assumptions,
    generation := MemoryBumpChip.generation }

/-- Install the receipt on the actual register refresh table without changing its rows or hints. -/
def publishRefresh (table : Table (ZMod p)) (registered : table.component = original) : Table (ZMod p) :=
  table.withComponent refreshComponent (by rw [registered]; rfl) (by rw [registered]; rfl)
    (by rw [registered]; rfl) (by rw [registered]; rfl)

/-- Publishing the receipt retains all original row constraints. -/
theorem publishRefresh_constraints (table : Table (ZMod p)) (registered : table.component = original) :
    (publishRefresh table registered).Constraints ↔ table.Constraints := by
  apply Table.withComponent_constraints
  · rw [registered]
    exact Receipt.constraints _ _ (fun _ _ => trivial) projection
  · rw [registered]
    exact Receipt.lookups _ _ (fun _ _ => trivial) projection

/-- Count one authenticated occurrence for every physical row, including disabled padding. -/
theorem publishRefresh_receipts (table : Table (ZMod p)) (registered : table.component = original) :
    (publishRefresh table registered).interactionsWith readbackChannel.toRaw =
      table.table.map fun row =>
        let input := valueFromOffset MemoryBumpChip.Inputs 0 (table.environment row)
        readbackChannel.pushedIfValue input.is_real (refreshReadback input) := by
  simp only [publishRefresh, Table.interactionsWith, Table.withComponent, Table.environment, refresh_row_receipt]
  exact List.map_eq_flatMap.symm

end SP1Clean.WriteProbe
