import SP1Clean.FormalModel.Contracts.HintQueueSnapshot
import SP1Clean.FormalModel.Contracts.HintQueue
import SP1Clean.FormalModel.Contracts.HintWords
import ToClean.Air.StaticProvider
import Clean.Gadgets.Boolean

/-! # A fixed word-by-word walk of the complete outgoing hint queue

The lengths, bytes, padding, ordinal and transition flags are verifier-fixed. Only the
actual node and tail are private. Each active row consumes a walk cursor, reads its word,
and emits the next cursor. The first word of each buffer also reads its node metadata.
-/

namespace SP1Clean.HostHintSnapshot

open Circuit Air.Flat Semantics Semantics.HintQueue HostHintQueue
open scoped Classical

variable {p : ℕ} [Fact p.Prime]

/-- Physical component name and key of its six private pointer limbs. -/
def tableName := "sp1.native.hint_target_words"

/-- Reject an oversized target even when the resulting padded inventory contains no live word.
The count is the generator-owned number of incoming cursor messages for this physical row. -/
def main (hints : List Bytes) (r : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  assertZero (.const (if fits hints then 0 else 1))
  assertZero (r.2.2 - r.1.active)
  assertBool r.1.first
  assertBool r.1.active
  channel.pullIf r.2.2 (r.1.before r.2.1)
  nodeChannel.pullIf r.1.first (r.1.node r.2.1)
  wordChannel.pullIf r.1.active (r.1.word r.2.1)
  channel.pushIf r.1.active (r.1.after r.2.1)

instance elaborated (hints : List Bytes) : ElaboratedCircuit (ZMod p) Inputs unit (main hints) := by elaborate_circuit

/-- A scheduled occurrence receives exactly one cursor and requests valid immutable metadata
and words. Padding has zero count. -/
def Valid (hints : List Bytes) (r : Inputs (ZMod p)) : Prop :=
  fits hints = true ∧ r.2.2 = r.1.active ∧ IsBool r.1.first ∧ IsBool r.1.active ∧
    (r.1.first = 1 → (r.1.node r.2.1).Valid) ∧ (r.1.active = 1 → (r.1.word r.2.1).Valid)

/-- Constrain the fixed schedule and its typed node and word reads. -/
def circuit (hints : List Bytes) : GeneralFormalCircuit (ZMod p) Inputs unit where
  name := tableName
  main := main hints
  elaborated := elaborated hints
  computableWitnesses := by computable_witnesses [Shape.before, Shape.after, Shape.node, Shape.word]
  Spec input _ _ := Valid hints input
  ProverAssumptions input _ _ := Valid hints input
  channelsWithRequirements := [channel.toRaw, nodeChannel.toRaw, wordChannel.toRaw]
  soundness := by
    circuit_proof_start [main, channel, nodeChannel, wordChannel, Shape.before, Shape.after, Shape.node, Shape.word]
    subst input
    simp only [Valid, Shape.node, Shape.word, sub_eq_zero] at *
    by_cases valid : fits hints = true
    · simp only [valid, ↓reduceIte, true_and] at *
      refine ⟨h_holds, ?_⟩
      rw [h_holds.1]
      simp only [IsBool] at h_holds
      tauto
    · simp [valid] at h_holds
  completeness := by
    circuit_proof_start [main, channel, nodeChannel, wordChannel, Shape.before, Shape.after, Shape.node, Shape.word]
    subst input
    obtain ⟨fit, count, first, active, node, word⟩ := h_assumptions
    simp only [fit, ↓reduceIte, sub_eq_zero, true_and]
    exact ⟨count, first, active, node, word⟩

/-- The backing fixed inventory contains a row for the padding word even when a buffer is empty. -/
def inventory (hints : List Bytes) : StaticTable (ZMod p) Shape :=
  StaticTable.ofRows tableName (schedule hints)

private theorem height_bound (hints : List Bytes) : (inventory (p := p) hints).height < UInt64.size := by
  have rows : (inventory (p := p) hints).length < 2 ^ 48 := by
    change (schedule (p := p) hints).length < _
    rw [schedule_length]
    split
    · simpa only [fits, decide_eq_true_eq] using ‹fits hints = true›
    · decide
  have padding := (inventory (p := p) hints).height_lt_double
  norm_num [UInt64.size] at *
  omega

/-- Fixed shapes are addressed by their physical row number. Padding reads the zero shape. -/
def fixedShapes (hints : List Bytes) : Vector (Shape (ZMod p)) (inventory (p := p) hints).height :=
  let rows := (schedule (p := p) hints).toArray
  Vector.ofFn fun i => (rows[i.val]?).getD 0

/-- Each prover hint has six cells, the actual node and tail at that public ordinal. -/
def generation (hints : List Bytes) : WitnessGeneration.PreallocatedMode (ZMod p) Inputs where
  channel := channel
  trigger := .push
  height := UInt64.ofNatLT _ (height_bound (p := p) hints)
  input i :=
    let pointers : Vector (WitnessGeneration.Cell (ZMod p)) 6 := Vector.ofFn (fun j : Fin 6 => WitnessGeneration.Cell.witness (.hintGet tableName 6 i j))
    WitnessGeneration.fixedPrefix (Witgen.literalRow (fixedShapes (p := p) hints) i)
      (fromElements pointers, .multiplicity)
  rowOf cursor := cursor.ordinal[0].val + cursor.ordinal[1].val * 65536 + cursor.ordinal[2].val * 4294967296

/-- A row of the physical table contains exactly its verifier-scheduled shape, irrespective of
the node pointers supplied by the prover. -/
theorem fixed_at (hints : List Bytes) (i : Fin (inventory (p := p) hints).height)
    (row : Inputs (ZMod p)) (fixed : (generation hints).FixedAt (UInt64.ofNat i.val) row) :
    row.1 = (fixedShapes hints)[i.val] := by
  exact (fixed.typed_prefix (row := Witgen.literalRow (fixedShapes hints) .idx) rfl).trans
    (Witgen.literalRow_evalRow _ (height_bound hints) i)

/-- Preallocated table that reads the complete outgoing queue. -/
def component (hints : List Bytes) : Component (ZMod p) where
  circuit := circuit hints
  generation := .preallocated (generation hints)

end SP1Clean.HostHintSnapshot
