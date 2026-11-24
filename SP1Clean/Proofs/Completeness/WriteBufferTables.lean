import SP1Clean.Proofs.Completeness.WriteBufferRows
import ToClean.Air.GuardedDemandTable

/-! # Certified physical span and word tables at their actual demand heights

Both constructors run Clean's normal row builder against consistent private input columns.
A successful semantic packet supplies the row data, arithmetic witnesses, and physical
index bounds. Word data retains the original read payloads and padding contributes zero.
-/

namespace SP1Clean.WriteBuffer
open Circuit Air.Flat Machine Semantics Soundness.Target TraceGen

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Compile active packet spans in the original order, including demand padding. -/
def spanTable (spans : List (Span (ZMod p))) (data : ProverData (ZMod p))
    (bound : WitnessGeneration.demandHeight spans.length ≤ UInt64.size) : Table (ZMod p) :=
  Table.ofInputs spanComponent (WitnessGeneration.guardedRows spans) data
    ((WitnessGeneration.guardedRows_length spans).trans_le bound) (fun _ => trivial)

/-- Compile active aligned-word consumers in the original order, including demand padding. -/
def wordTable (steps : List (Step (ZMod p))) (data : ProverData (ZMod p))
    (bound : WitnessGeneration.demandHeight steps.length ≤ UInt64.size) : Table (ZMod p) :=
  Table.ofInputs wordComponent (WitnessGeneration.guardedRows steps) data
    ((WitnessGeneration.guardedRows_length steps).trans_le bound) (fun _ => trivial)

theorem spanTable_length (spans : List (Span (ZMod p))) (data : ProverData (ZMod p)) (bound) :
    (spanTable spans data bound).table.length = WitnessGeneration.demandHeight spans.length :=
  (Table.ofInputs_length (spanComponent (p := p)) (WitnessGeneration.guardedRows (F := ZMod p) spans) data
    ((WitnessGeneration.guardedRows_length (F := ZMod p) spans).trans_le bound) (fun _ => trivial)).trans
    (WitnessGeneration.guardedRows_length (F := ZMod p) spans)

/-- Full signed cursor ledger of the generated span table, including padding. -/
theorem spanTable_cursors (spans : List (Span (ZMod p))) (data : ProverData (ZMod p)) (bound) :
    (spanTable spans data bound).interactionsWith channel.toRaw =
      (WitnessGeneration.guardedRows spans).flatMap spanCursors :=
  Table.ofInputs_ledger (spanComponent (p := p)) (WitnessGeneration.guardedRows spans) data
    ((WitnessGeneration.guardedRows_length (F := ZMod p) spans).trans_le bound) (fun _ => trivial)
    channel.toRaw spanCursors spanInput_cursor_ledger

theorem wordTable_length (steps : List (Step (ZMod p))) (data : ProverData (ZMod p)) (bound) :
    (wordTable steps data bound).table.length = WitnessGeneration.demandHeight steps.length :=
  (Table.ofInputs_length (wordComponent (p := p)) (WitnessGeneration.guardedRows (F := ZMod p) steps) data
    ((WitnessGeneration.guardedRows_length (F := ZMod p) steps).trans_le bound) (fun _ => trivial)).trans
    (WitnessGeneration.guardedRows_length (F := ZMod p) steps)

/-- Full signed cursor ledger of the generated word table, including padding. -/
theorem wordTable_cursors (steps : List (Step (ZMod p))) (data : ProverData (ZMod p)) (bound) :
    (wordTable steps data bound).interactionsWith channel.toRaw =
      (WitnessGeneration.guardedRows steps).flatMap wordCursors :=
  Table.ofInputs_ledger (wordComponent (p := p)) (WitnessGeneration.guardedRows steps) data
    ((WitnessGeneration.guardedRows_length (F := ZMod p) steps).trans_le bound) (fun _ => trivial)
    channel.toRaw wordCursors wordInput_cursor_ledger

theorem spanTable_complete {spans : List (Span (ZMod p))} (valid : ∀ s ∈ spans, s.Honest)
    (data : ProverData (ZMod p)) (bound) : (spanTable spans data bound).Constraints ∧ (spanTable spans data bound).Guarantees := by
  apply Table.ofInputs_valid
  exact WitnessGeneration.guardedRows_all Span.Honest valid

theorem wordTable_complete {steps : List (Step (ZMod p))} (valid : ∀ s ∈ steps, s.Honest)
    (data : ProverData (ZMod p)) (bound) : (wordTable steps data bound).Constraints ∧ (wordTable steps data bound).Guarantees := by
  apply Table.ofInputs_valid
  exact WitnessGeneration.guardedRows_all Step.Honest valid

/-- Every genuine read packet generates both physical tables. The actual bound on guest
memory supplies the word-table size without an additional shard-preset restriction. -/
theorem tables_of_read {before : SailState} {call : CoreSyscallEvent} {len : BitVec 64} {buffer : List (BitVec 64)}
    (read : WriteObservations.read? before call = some (len, buffer)) (clock : ℕ) (data : ProverData (ZMod p)) :
    let h := headerOfCall (p := p) clock call len
    let spans := [Span.populate h]
    let steps := wordSteps h.clock (call.arg2.toNat / 8) (buffer.map bitVecToWord)
    ∃ hs hw, (spanTable spans data hs).Constraints ∧ (spanTable spans data hs).Guarantees ∧
      (wordTable steps data hw).Constraints ∧ (wordTable steps data hw).Guarantees ∧
      (spanTable spans data hs).table.length = 1 ∧
      (wordTable steps data hw).table.length = WitnessGeneration.demandHeight buffer.length := by
  obtain ⟨span, words, _⟩ := rows_of_read (p := p) read clock
  obtain ⟨_, _, lo, hi, count, _⟩ := WriteObservations.read?_eq_some_iff.mp read
  let h := headerOfCall (p := p) clock call len
  let steps := wordSteps h.clock (call.arg2.toNat / 8) (buffer.map bitVecToWord)
  have size : steps.length = buffer.length := by simp [steps, wordSteps]
  have one : WitnessGeneration.demandHeight 1 ≤ UInt64.size := by decide
  have spanProof := spanTable_complete (spans := [Span.populate h]) (fun s member => List.mem_singleton.mp member ▸ span) data one
  have spanHeight : (spanTable [Span.populate h] data one).table.length = 1 := spanTable_length _ _ _
  have fits : steps.length ≤ 2 ^ 45 := by
    rw [size, count, WriteObservations.wordCount]
    omega
  have physical : WitnessGeneration.demandHeight steps.length ≤ UInt64.size :=
    (WitnessGeneration.demandHeight_le_pow fits).trans (by decide)
  refine ⟨one, physical, spanProof.1, spanProof.2, (wordTable_complete words data physical).1,
    (wordTable_complete words data physical).2, spanHeight, ?_⟩
  change (wordTable steps data physical).table.length = WitnessGeneration.demandHeight buffer.length
  exact (wordTable_length steps data physical).trans (congrArg WitnessGeneration.demandHeight size)

end SP1Clean.WriteBuffer
