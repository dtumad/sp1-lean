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

/-- The span table consumes a full original packet for each enabled header. Padding is retained. -/
theorem spanTable_headers (spans : List (Span (ZMod p))) (data : ProverData (ZMod p)) (bound) :
    (spanTable spans data bound).interactionsWith WritePacket.channel.toRaw =
      (WitnessGeneration.guardedRows spans).flatMap (fun r => [WritePacket.channel.pulledIfValue r.2 r.1.header]) := by
  apply Table.ofInputs_ledger (spanComponent (p := p)) (WitnessGeneration.guardedRows spans) data
    ((WitnessGeneration.guardedRows_length (F := ZMod p) spans).trans_le bound) (fun _ => trivial)
  intro env
  rw [Operations.interactionValuesWith, Component.interactionsWith_eq]
  change ((spanComponent.circuit.main (varFromOffset SpanRow 0)).operations (size SpanRow)).interactionValuesWith _ env =
    [WritePacket.channel.pulledIfValue (valueFromOffset SpanRow 0 env).2 (valueFromOffset SpanRow 0 env).1.header]
  have proj (i : Var SpanRow (ZMod p)) : eval env i.1.header = (eval env i).1.header := by simp only [circuit_norm]
  simpa only [Guarded.eval_activity, proj, eval_varFromOffset_valueFromOffset] using
    span_headers (varFromOffset SpanRow 0) (size SpanRow) env

/-- The host effect receiver receives each of those same headers at the same activity. Padding is retained. -/
theorem spanTable_effect_headers (spans : List (Span (ZMod p))) (data : ProverData (ZMod p)) (bound) :
    (spanTable spans data bound).interactionsWith effectHeaderChannel.toRaw =
      (WitnessGeneration.guardedRows spans).flatMap (fun r => [effectHeaderChannel.pushedIfValue r.2 r.1.header]) := by
  apply Table.ofInputs_ledger (spanComponent (p := p)) (WitnessGeneration.guardedRows spans) data
    ((WitnessGeneration.guardedRows_length (F := ZMod p) spans).trans_le bound) (fun _ => trivial)
  intro env
  rw [Operations.interactionValuesWith, Component.interactionsWith_eq]
  change ((spanComponent.circuit.main (varFromOffset SpanRow 0)).operations (size SpanRow)).interactionValuesWith _ env =
    [effectHeaderChannel.pushedIfValue (valueFromOffset SpanRow 0 env).2 (valueFromOffset SpanRow 0 env).1.header]
  have proj (i : Var SpanRow (ZMod p)) : eval env i.1.header = (eval env i).1.header := by simp only [circuit_norm]
  simpa only [Guarded.eval_activity, proj, eval_varFromOffset_valueFromOffset] using
    span_effect_headers (varFromOffset SpanRow 0) (size SpanRow) env

/-- The word table consumes each actual read payload in input order. Padding is retained. -/
theorem wordTable_reads (steps : List (Step (ZMod p))) (data : ProverData (ZMod p)) (bound) :
    (wordTable steps data bound).interactionsWith WriteProbe.readChannel.toRaw =
      (WitnessGeneration.guardedRows steps).flatMap (fun r => [WriteProbe.readChannel.pulledIfValue r.2 r.1.read]) := by
  apply Table.ofInputs_ledger (wordComponent (p := p)) (WitnessGeneration.guardedRows steps) data
    ((WitnessGeneration.guardedRows_length (F := ZMod p) steps).trans_le bound) (fun _ => trivial)
  exact word_read_at

/-- The effect receiver receives the complete raw words in the same order. Padding is retained. -/
theorem wordTable_values (steps : List (Step (ZMod p))) (data : ProverData (ZMod p)) (bound) :
    (wordTable steps data bound).interactionsWith wordChannel.toRaw =
      (WitnessGeneration.guardedRows steps).flatMap (fun r => [wordChannel.pushedIfValue r.2 r.1.read]) := by
  apply Table.ofInputs_ledger (wordComponent (p := p)) (WitnessGeneration.guardedRows steps) data
    ((WitnessGeneration.guardedRows_length (F := ZMod p) steps).trans_le bound) (fun _ => trivial)
  exact word_forward_at

/-- A constructed walk closes the original signed channel of its two physical tables,
including all disabled rows at their actual allocated heights. -/
theorem tables_cursor_closed (span : Span (ZMod p)) (steps : List (Step (ZMod p)))
    (walk : Soundness.Walk.IsWalk (fun r : Step (ZMod p) => (r.source, r.target)) span.source span.target steps)
    (data : ProverData (ZMod p)) (hs hw) :
    BalancedInteractions ((spanTable [span] data hs).interactionsWith channel.toRaw ++
      (wordTable steps data hw).interactionsWith channel.toRaw) := by
  rw [spanTable_cursors, wordTable_cursors]
  let rows := WitnessGeneration.guardedRows (F := ZMod p) steps
  let edge := fun r : WordRow (ZMod p) => (r.1.source, r.1.target)
  have binary r (m : r ∈ rows) : IsBool r.2 :=
    (WitnessGeneration.guardedRows_all (F := ZMod p) (fun _ => True) (fun _ _ => trivial) r m).1
  change BalancedInteractions (channel.gatedTransitionLedger span.source span.target rows Prod.snd edge)
  apply (channel.gatedTransitionLedger_balanced_iff _ _ _ _ _ binary).mpr
  have ends := Soundness.RankedGrounding.endpointBalanced_of_isWalk _ walk
  have hp : (span.source :: steps.map Step.target).Perm (span.target :: steps.map Step.source) := by
    simpa only [Soundness.RankedGrounding.EndpointBalanced, Multiset.map_coe, Multiset.cons_coe, Multiset.coe_eq_coe] using ends
  have active : rows.filter (fun r => @decide (r.2 = 1) (FiniteField.instDecidableEq r.2 1)) =
      steps.map (fun s => (s, 1)) := by
    simp [rows, WitnessGeneration.guardedRows, List.filter_map, Function.comp_def]
  simpa only [active, List.map_map, edge, Function.comp_def] using hp

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
      (wordTable steps data hw).table.length = WitnessGeneration.demandHeight buffer.length ∧
      BalancedInteractions ((spanTable spans data hs).interactionsWith channel.toRaw ++
        (wordTable steps data hw).interactionsWith channel.toRaw) := by
  obtain ⟨span, words, walk, _⟩ := rows_of_read (p := p) read clock
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
    (wordTable_complete words data physical).2, spanHeight, ?_, tables_cursor_closed _ _ walk _ _ _⟩
  change (wordTable steps data physical).table.length = WitnessGeneration.demandHeight buffer.length
  exact (wordTable_length steps data physical).trans (congrArg WitnessGeneration.demandHeight size)

end SP1Clean.WriteBuffer
