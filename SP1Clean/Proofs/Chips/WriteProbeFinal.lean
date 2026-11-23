import SP1Clean.FormalModel.Contracts.WriteReadback
import ToClean.Circuit.Receipt
import ToClean.Air.ComponentReplacement
import SP1Clean.Native.Operations.FinalMemoryReceipt
import SP1Clean.Proofs.Chips.OrderedFinalProvider
import SP1Clean.Semantics.Transition.MicroTime
import ToClean.Air.Authentication

/-! # WRITE version suffixes from the two actual ordered Memory finalizers

The added private receipt uses the already-published full final record, including its
timestamp. Its upper bound is the last representable time. A finalized genesis record
therefore supplies every representable cut for that key.
-/

namespace SP1Clean.WriteProbe

open Circuit Air.Flat Channels Semantics

/-- Closed suffix from a final Memory record, using both released 24-bit clock limbs. -/
def finalReadback {F : Type} [OfNat F 16777215] (record : MemoryMsg F) : Readback F :=
  ⟨#v[record.addr0, record.addr1, record.addr2], record.clk_high, record.clk_low,
    16777215, 16777215, record.value⟩

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

private abbrev finalProvider (ram : Bool) := if ram then OrderedFinalProvider.ramCircuit (p := p)
  else OrderedFinalProvider.registerCircuit

/-- Current installed component: the ordered finalizer already publishes its target-check receipt. -/
def originalFinal (ram : Bool) : Component (ZMod p) where
  circuit := FinalMemoryReceipt.circuit ram (finalProvider ram)
  generation := OrderedMemoryProvider.generation OrderedFinalProvider.channelName
    (if ram then (FinalRamProvider.circuit (p := p)).name else (FinalRegisterProvider.circuit (p := p)).name)
  Assumptions := (finalProvider ram).Assumptions

private def finalProjection (ram : Bool) :
    Receipt.Projection (ZMod p) (OrderedMemoryProvider.RowInput MemoryMsg) Readback :=
  ⟨fun input _ => input.2, fun input offset => finalReadback ((finalProvider ram).output input offset)⟩

/-- Both finalizers keep their original row arrays, input mode, Memory pulls and target-value receipts. -/
def finalComponent (ram : Bool) : Component (ZMod p) where
  circuit := Receipt.circuit (FinalMemoryReceipt.circuit ram (finalProvider ram)) readbackChannel
    (fun _ _ => trivial) (finalProjection ram)
  generation := (originalFinal ram).generation
  Assumptions := (finalProvider ram).Assumptions

theorem final_original_interactions (ram : Bool) (selected : RawChannel (ZMod p)) (other : selected ≠ readbackChannel.toRaw) :
    (finalComponent ram).operations.interactionsWith selected = (originalFinal ram).operations.interactionsWith selected :=
  Receipt.interactions _ _ (fun _ _ => trivial) (finalProjection ram) selected other

private theorem fresh_final (ram : Bool) : readbackChannel.toRaw ∉ (originalFinal (p := p) ram).circuit.channels := by
  intro member
  have seen := List.contains_iff_mem.mpr (List.mem_map_of_mem (f := RawChannel.name) member)
  cases ram <;> change false = true at seen <;> contradiction

omit [Fact (2 ^ 17 < p)] in
private theorem eval_finalReadback (env : Environment (ZMod p)) (record : Var MemoryMsg (ZMod p)) :
    eval env (finalReadback record) = finalReadback (eval env record) := by
  cases record
  simp only [finalReadback, circuit_norm]

/-- Decode the complete checked Memory output from the existing row, at its actual starting offset. -/
def finalRecordAt (ram : Bool) (env : Environment (ZMod p)) : MemoryMsg (ZMod p) :=
  eval env ((finalProvider (p := p) ram).output (varFromOffset (OrderedMemoryProvider.RowInput MemoryMsg) 0)
    (size (OrderedMemoryProvider.RowInput MemoryMsg)))

/-- Every physical row, including padding, projects the same original full-record output. -/
theorem final_row_receipt (ram : Bool) (env : Environment (ZMod p)) :
    (finalComponent ram).operations.interactionValuesWith readbackChannel.toRaw env =
      [readbackChannel.pushedIfValue (valueFromOffset (OrderedMemoryProvider.RowInput MemoryMsg) 0 env).2
        (finalReadback (finalRecordAt ram env))] := by
  have row := Receipt.row_receipt _ readbackChannel (fun _ _ => trivial) (finalProjection ram) (fresh_final ram) env
  change ((Receipt.circuit (originalFinal ram).circuit readbackChannel (fun _ _ => trivial) (finalProjection ram)).instantiate.operations 0).interactionValuesWith _ env = _
  refine row.trans ?_
  rw [← eval_varFromOffset_valueFromOffset]
  simp only [finalProjection, finalRecordAt]
  rw [eval_finalReadback, eval_pair (α := OrderedMemoryProvider.Inputs MemoryMsg) (β := field)]
  rfl

private theorem final_fixedRows (ram : Bool)
    (mode : WitnessGeneration.Generation (ZMod p) (OrderedMemoryProvider.RowInput MemoryMsg)) :
    ({ circuit := (finalComponent (p := p) ram).circuit, generation := mode,
       Assumptions := (finalProvider ram).Assumptions } : Component (ZMod p)).FixedRowsMatch =
    ({ circuit := (originalFinal (p := p) ram).circuit, generation := mode,
       Assumptions := (finalProvider ram).Assumptions } : Component (ZMod p)).FixedRowsMatch := by
  funext rows
  cases mode <;> rfl

/-- Add the version source to an actual registered RAM or register finalizer. -/
def publishFinal (ram : Bool) (table : Table (ZMod p)) (family : table.component = originalFinal ram) : Table (ZMod p) :=
  table.withComponent (finalComponent ram) (by rw [family]; rfl) (by rw [family]; exact final_fixedRows ram _)
    (by rw [family]; rfl) (by rw [family]; rfl)

theorem publishFinal_constraints (ram : Bool) (table : Table (ZMod p)) (family : table.component = originalFinal ram) :
    (publishFinal ram table family).Constraints ↔ table.Constraints := by
  apply Table.withComponent_constraints
  · rw [family]
    exact Receipt.constraints _ _ (fun _ _ => trivial) (finalProjection ram)
  · rw [family]
    exact Receipt.lookups _ _ (fun _ _ => trivial) (finalProjection ram)

/-- The new private ledger retains every physically present finalizer and its zero padding. -/
theorem publishFinal_receipts (ram : Bool) (table : Table (ZMod p)) (family : table.component = originalFinal ram) :
    (publishFinal ram table family).interactionsWith readbackChannel.toRaw =
      table.table.map fun row =>
        let env := table.environment row
        readbackChannel.pushedIfValue (valueFromOffset (OrderedMemoryProvider.RowInput MemoryMsg) 0 env).2
          (finalReadback (finalRecordAt ram env)) := by
  simp only [publishFinal, Table.interactionsWith, Table.withComponent, Table.environment, final_row_receipt]
  exact List.map_eq_flatMap.symm

omit [Fact (2 ^ 17 < p)] in
/-- At a finalized key the emitted suffix ends at the last 48-bit clock. A zero clock starts it at genesis. -/
theorem finalReadback_clocks [Fact (2 ^ 24 < p)] (record : MemoryMsg (ZMod p)) :
    clkNat (finalReadback record).previousHigh (finalReadback record).previousLow = MemoryMsg.timeNat record ∧
    clkNat (finalReadback record).currentHigh (finalReadback record).currentLow = 2 ^ 48 - 1 := by
  refine ⟨rfl, ?_⟩
  have bound : 16777215 < p := by have := Fact.out (p := 2 ^ 24 < p); omega
  change (16777215 : ZMod p).val * 2 ^ 24 + (16777215 : ZMod p).val = _
  have exactLimb : (16777215 : ZMod p).val = 16777215 := ZMod.val_natCast_of_lt bound
  rw [exactLimb]
  decide

end SP1Clean.WriteProbe
