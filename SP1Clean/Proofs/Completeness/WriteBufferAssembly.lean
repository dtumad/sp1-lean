import SP1Clean.Proofs.Completeness.WriteBufferTables
import SP1Clean.Proofs.Completeness.WriteBufferBatch
import SP1Clean.Math.SP1Field
import ToClean.Air.MessageFilter

/-! # The batched physical WRITE span and aligned-word tables

All calls in the mixed tape share one span table and one word table. Each table is padded
once, so per-call table heights do not inflate the installed ledgers or the resource preset.
-/

namespace SP1Clean.WriteBuffer

open Circuit Air.Flat Semantics Machine FormalModel.Shard TraceGen Soundness Soundness.Target

variable {p : ℕ} [Fact p.Prime]

/-- Honest physical inputs and an exact consecutive traversal for each real WRITE. -/
def PacketRows.Valid (r : PacketRows (ZMod p)) : Prop :=
  r.span.Honest ∧ (∀ word ∈ r.steps, word.Honest) ∧
    Walk.IsWalk (fun w : Step (ZMod p) => (w.source, w.target)) r.span.source r.span.target r.steps

variable [Fact (2 ^ 17 < p)]

theorem packetRows_valid {limits : ResourceLimits} {image : ProgramImage} {source target : ExecutionSnapshot}
    {events : List ExecutionEvent} {packets : List WriteObservations.Packet} (run : AdmissibleExecution limits p image source target events)
    (collected : WriteObservations.packets? (policy p image) image.program source.realize events = some packets) :
    ∀ r ∈ packetRows (p := p) events packets, r.Valid := by
  intro r member
  obtain ⟨_, call, _, _, _, _, _, _, _, _, read, rfl⟩ := packetRows_member run collected member
  obtain ⟨span, words, consecutive, _⟩ := rows_of_read (p := p) read call.clock
  exact ⟨span, words, consecutive⟩

omit [Fact (2 ^ 17 < p)] in
private theorem active_sum {I : Type} [Zero I] (rows : List I) (values : I × ZMod p → List (Interaction (ZMod p)))
    (message : Array (ZMod p)) (inactive : balanceOf (values 0) message = 0) :
    balanceOf ((WitnessGeneration.guardedRows rows).flatMap values) message =
      balanceOf (rows.flatMap (fun r => values (r, 1))) message := by
  have disabled (n : ℕ) : balanceOf ((List.replicate n 0).flatMap values) message = 0 := by
    induction n with
    | zero => rfl
    | succ n ih => rw [List.replicate_succ, List.flatMap_cons, balanceOf_append, inactive, ih, add_zero]
  simp only [WitnessGeneration.guardedRows, List.flatMap_append, balanceOf_append, List.flatMap_map,
    disabled, add_zero]

omit [Fact (2 ^ 17 < p)] in
private theorem one_cursor (r : PacketRows (ZMod p)) (valid : r.Valid) (m : Array (ZMod p)) :
    balanceOf (spanCursors (r.span, 1)) m + balanceOf (r.steps.flatMap (fun w => wordCursors (w, 1))) m = 0 := by
  let edge := fun w : Step (ZMod p) => (w.source, w.target)
  have ends := RankedGrounding.endpointBalanced_of_isWalk edge valid.2.2
  have permutation : (r.span.source :: r.steps.map Step.target).Perm (r.span.target :: r.steps.map Step.source) := by
    simpa only [RankedGrounding.EndpointBalanced, Multiset.map_coe, Multiset.cons_coe, Multiset.coe_eq_coe, edge] using ends
  have raw := (channel.transitionLedger_balanced_iff r.span.source r.span.target r.steps edge).mpr permutation
  have isUnit : ∀ i ∈ channel.transitionLedger r.span.source r.span.target r.steps edge, IsBool i.mult := by
    intro i member
    have grouped := (channel.transitionLedger_perm r.span.source r.span.target r.steps edge).mem_iff.mp member
    rcases List.mem_append.mp grouped with put | get
    · obtain ⟨_, _, rfl⟩ := List.mem_map.mp put
      exact Or.inr rfl
    · obtain ⟨_, _, rfl⟩ := List.mem_map.mp get
      exact Or.inr rfl
  have zero := raw.logUp_of_isBool isUnit m
  rw [← balanceOf_append]
  exact zero

/-- The signed cursor ledger closes across both globally padded tables at every message. -/
theorem batch_cursor (batch : List (PacketRows (ZMod p))) (valid : ∀ r ∈ batch, r.Valid)
    (data : ProverData (ZMod p)) (hs hw) :
    LogUpBalanced ((spanTable (batch.map PacketRows.span) data hs).interactionsWith channel.toRaw ++
      (wordTable (batch.flatMap PacketRows.steps) data hw).interactionsWith channel.toRaw) := by
  intro msg
  rw [balanceOf_append, spanTable_cursors, wordTable_cursors, active_sum, active_sum]
  · clear hs hw
    induction batch with
    | nil => simp [balanceOf]
    | cons r rest ih =>
      have head := one_cursor r (valid r List.mem_cons_self) msg
      have tail := ih (fun t mem => valid t (List.mem_cons_of_mem _ mem))
      simp only [List.map_cons, List.flatMap_cons, List.flatMap_append, balanceOf_append]
      linear_combination head + tail
  · simp only [wordCursors, balanceOf_cons]
    simp [Channel.pulledIfValue, Channel.pushedIfValue, Interaction.signedMult, balanceOf]
    apply ite_self
  · simp only [spanCursors, balanceOf_cons]
    simp [Channel.pulledIfValue, Channel.pushedIfValue, Interaction.signedMult, balanceOf]
    apply ite_self

/-- The two actual installed component families, with their exact padded heights and all cursor
occurrences, are simultaneously populated for an arbitrary native mixed execution. -/
theorem native_buffer_tables {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events) (data : ProverData (ZMod SP1Prime)) :
    ∃ packets, WriteObservations.packets? (policy SP1Prime image) image.program source.realize events = some packets ∧
      let batch := packetRows (p := SP1Prime) events packets
      ∃ hs hw, let spans := spanTable (batch.map PacketRows.span) data hs
               let words := wordTable (batch.flatMap PacketRows.steps) data hw
               spans.Constraints ∧ spans.Guarantees ∧ words.Constraints ∧ words.Guarantees ∧
                 spans.table.length = WitnessGeneration.demandHeight packets.length ∧
                 words.table.length = WitnessGeneration.demandHeight (WriteObservations.wordProbes packets) ∧
                 LogUpBalanced (spans.interactionsWith channel.toRaw ++ words.interactionsWith channel.toRaw) := by
  obtain ⟨packets, collected⟩ := WriteObservations.admissible_packets run
  let batch := packetRows (p := SP1Prime) events packets
  have counted : batch.length = packets.length := (packetRows_length collected).trans (WriteObservations.packets_length collected).symm
  have many : (batch.flatMap PacketRows.steps).length = WriteObservations.wordProbes packets := packetRows_words collected
  have reads := run.2.2.1 .readBytes
  have ticks := run.2.2.1 .ticks
  rw [run.1.2.resources_ticks] at ticks
  obtain ⟨limited, bounded, _⟩ := WriteObservations.packets_native_bound run.1.2 collected ticks reads
  have hs : WitnessGeneration.demandHeight (batch.map PacketRows.span).length ≤ UInt64.size := by
    apply (WitnessGeneration.demandHeight_le_pow (exponent := 16) ?_).trans (by decide)
    rw [List.length_map, counted]; omega
  have hw : WitnessGeneration.demandHeight (batch.flatMap PacketRows.steps).length ≤ UInt64.size := by
    apply (WitnessGeneration.demandHeight_le_pow (exponent := 28) ?_).trans (by decide)
    rw [many]; omega
  have valid : ∀ r ∈ batch, r.Valid := packetRows_valid run collected
  have spans := spanTable_complete (spans := batch.map PacketRows.span) (by
    intro s m; obtain ⟨r, h, rfl⟩ := List.mem_map.mp m; exact (valid r h).1) data hs
  have words := wordTable_complete (steps := batch.flatMap PacketRows.steps) (by
    intro w m; obtain ⟨r, h, inside⟩ := List.mem_flatMap.mp m; exact (valid r h).2.1 w inside) data hw
  refine ⟨packets, collected, hs, hw, spans.1, spans.2, words.1, words.2, ?_, ?_, batch_cursor batch valid data hs hw⟩
  · simpa only [List.length_map, counted] using spanTable_length (batch.map PacketRows.span) data hs
  · simpa only [many] using wordTable_length (batch.flatMap PacketRows.steps) data hw

end SP1Clean.WriteBuffer
