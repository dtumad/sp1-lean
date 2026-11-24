import SP1Clean.Proofs.Completeness.WritePacketTables
import SP1Clean.Proofs.Completeness.WriteBufferAssembly
import SP1Clean.Proofs.Completeness.WriteProbeTables

/-! # Matching the mixed-tape WRITE packet, span, word, and read-probe tables

Every real packet consumes precisely the x12 receipt at its original clock, including a
zero-byte WRITE. Each aligned word consumes one more receipt. Sorting these demands by
physical table preserves their complete typed payloads and multiplicities.
-/

namespace SP1Clean.WritePacket

open Circuit Air.Flat Semantics Machine TraceGen FormalModel.Shard
open WriteBuffer (PacketRows)

variable {p : ℕ} [Fact p.Prime]

private def lengthRead (r : PacketRows (ZMod p)) : WriteProbe.Read (ZMod p) :=
  ⟨Address.ofNat 12, r.span.header.clock, r.span.header.length⟩

omit [Fact p.Prime] in
/-- Grouping requests by receiver leaves the same multiset of full reads, including repeats. -/
private theorem demand_receivers (batch : List (PacketRows (ZMod p))) :
    ((WriteBuffer.readDemand batch).map Prod.snd).Perm
      (batch.map lengthRead ++ (batch.flatMap PacketRows.steps).map WriteBuffer.Step.read) := by
  induction batch with
  | nil => exact .nil
  | cons r rest ih =>
    change ((r.reads.map (r.cut, ·) ++ WriteBuffer.readDemand rest).map Prod.snd).Perm _
    simp only [PacketRows.reads, List.map_append, List.map_cons, List.map_map, Function.comp_def,
      List.flatMap_cons, List.cons_append]
    exact .cons _ ((ih.append_left _).trans (List.perm_append_comm_assoc ..))

private theorem headers_eq {batch : List (PacketRows (ZMod p))} [Fact (2 ^ 24 < p)]
    (bounded : ∀ r ∈ batch, Address.Bounded r.span.header.clock) :
    (batch.map (fun r => fromHeader r.span.header)).map Inputs.header = (batch.map PacketRows.span).map WriteBuffer.Span.header := by
  simp only [List.map_map, Function.comp_def]
  exact List.map_congr_left (fun r mem => (fromHeader_spec _ (bounded r mem)).2)

private theorem lengths_eq {batch : List (PacketRows (ZMod p))} [Fact (2 ^ 24 < p)]
    (bounded : ∀ r ∈ batch, Address.Bounded r.span.header.clock) :
    (batch.map (fun r => fromHeader r.span.header)).map Inputs.read = batch.map lengthRead := by
  simp only [List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro r mem
  simp only [Inputs.read, (fromHeader_spec _ (bounded r mem)).2, lengthRead]
  norm_num [Address.ofNat, fromHeader]

variable [Fact (2 ^ 24 < p)] [Fact (2 ^ 17 < p)]

/-- Native packet pushes and native span pulls close on the raw field ledger, after each
table has been padded to its actual height. -/
theorem packet_span_balanced (batch : List (PacketRows (ZMod p)))
    (bounded : ∀ r ∈ batch, Address.Bounded r.span.header.clock) (data : ProverData (ZMod p)) (hp hs) :
    LogUpBalanced ((table (batch.map (fun r => fromHeader r.span.header)) data hp).interactionsWith channel.toRaw ++
      (WriteBuffer.spanTable (batch.map PacketRows.span) data hs).interactionsWith channel.toRaw) := by
  intro msg
  rw [balanceOf_append, table_headers, WriteBuffer.spanTable_headers, ← List.map_eq_flatMap,
    WitnessGeneration.guarded_push_sum channel _ Inputs.header, WitnessGeneration.guarded_pull_sum channel _ WriteBuffer.Span.header,
    headers_eq bounded, ← balanceOf_append]
  exact channel.logUp_unit_of_perm (List.Perm.refl _) msg

/-- Read probe outputs exactly pay for the x12 and RAM consumers in their separate physical
tables. The input order is the actual interleaved read demand at the guest's WRITE positions. -/
theorem probe_packet_words_balanced (batch : List (PacketRows (ZMod p)))
    (bounded : ∀ r ∈ batch, Address.Bounded r.span.header.clock) (inputs : List (WriteProbe.Inputs (ZMod p)))
    (emitted : inputs.map WriteProbe.Inputs.read = (WriteBuffer.readDemand batch).map Prod.snd)
    (data : ProverData (ZMod p)) (hq hp hw) :
    LogUpBalanced ((WriteProbe.table inputs data hq).interactionsWith WriteProbe.readChannel.toRaw ++
      (table (batch.map (fun r => fromHeader r.span.header)) data hp).interactionsWith WriteProbe.readChannel.toRaw ++
      (WriteBuffer.wordTable (batch.flatMap PacketRows.steps) data hw).interactionsWith WriteProbe.readChannel.toRaw) := by
  intro msg
  rw [balanceOf_append, balanceOf_append, WriteProbe.table_reads, table_reads, WriteBuffer.wordTable_reads]
  simp only [← List.map_eq_flatMap, WriteProbe.physicalInputs]
  rw [WitnessGeneration.guarded_push_sum _ _ WriteProbe.Inputs.read, WitnessGeneration.guarded_pull_sum _ _ Inputs.read,
    WitnessGeneration.guarded_pull_sum _ _ WriteBuffer.Step.read, lengths_eq bounded, emitted]
  have paid := WriteProbe.readChannel.logUp_unit_of_perm (demand_receivers batch) msg
  simpa only [List.map_append, balanceOf_append, add_assoc] using paid

/-- Every chronological packet clock comes from the honest native instruction input. -/
theorem batch_clocks {limits : ResourceLimits} {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution limits SP1Prime image source target events) {packets : List WriteObservations.Packet}
    (collected : WriteObservations.packets? (policy SP1Prime image) image.program source.realize events = some packets) :
    ∀ r ∈ WriteBuffer.packetRows (p := SP1Prime) events packets, Address.Bounded r.span.header.clock := by
  intro r mem
  obtain ⟨_, _, _, _, _, _, _, bound, header, _⟩ := packet_input_at run collected mem
  rw [← header]
  exact ClockParts.address_bounded _ bound

/-- An arbitrary native mixed execution builds all three packet and buffer tables. Both
private packet channels balance on these actual rows, with exact chronological read demand
and padded heights for the additional counted observer. -/
theorem native_packet_buffer_tables {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events) (data : ProverData (ZMod SP1Prime)) :
    ∃ packets, WriteObservations.packets? (policy SP1Prime image) image.program source.realize events = some packets ∧
      let batch := WriteBuffer.packetRows (p := SP1Prime) events packets
      ∃ hp hs hw, let packet := table (batch.map (fun r => fromHeader r.span.header)) data hp
                  let spans := WriteBuffer.spanTable (batch.map PacketRows.span) data hs
                  let words := WriteBuffer.wordTable (batch.flatMap PacketRows.steps) data hw
                  packet.Constraints ∧ packet.Guarantees ∧ spans.Constraints ∧ spans.Guarantees ∧ words.Constraints ∧ words.Guarantees ∧
                  packet.length = WitnessGeneration.demandHeight packets.length ∧ spans.length = packet.length ∧
                  words.length = WitnessGeneration.demandHeight (WriteObservations.wordProbes packets) ∧
                  LogUpBalanced (packet.interactionsWith channel.toRaw ++ spans.interactionsWith channel.toRaw) ∧
                  LogUpBalanced (spans.interactionsWith WriteBuffer.channel.toRaw ++ words.interactionsWith WriteBuffer.channel.toRaw) ∧
                  ∀ inputs : List (WriteProbe.Inputs (ZMod SP1Prime)), inputs.map WriteProbe.Inputs.read = (WriteBuffer.readDemand batch).map Prod.snd →
                    ∃ hq, let observer := WriteProbe.table inputs data hq
                          observer.length = WitnessGeneration.demandHeight (packets.length + WriteObservations.wordProbes packets) ∧
                          LogUpBalanced (observer.interactionsWith WriteProbe.readChannel.toRaw ++
                            packet.interactionsWith WriteProbe.readChannel.toRaw ++ words.interactionsWith WriteProbe.readChannel.toRaw) := by
  obtain ⟨packets, collected, hs, hw, spans, spanGood, words, wordGood, hsEq, hwEq, cursor⟩ := WriteBuffer.native_buffer_tables run data
  obtain ⟨hp, packet, packetGood, hpEq, _⟩ := native_packet_table run data collected
  let batch := WriteBuffer.packetRows (p := SP1Prime) events packets
  have bounded := batch_clocks run collected
  refine ⟨packets, collected, hp, hs, hw, packet, packetGood, spans, spanGood, words, wordGood, hpEq,
    hsEq.trans hpEq.symm, hwEq, packet_span_balanced batch bounded data hp hs, cursor, ?_⟩
  intro inputs emitted
  have size : inputs.length = (WriteBuffer.readDemand batch).length := by simpa only [List.length_map] using congrArg List.length emitted
  have ticks := run.2.2.1 .ticks
  rw [run.1.2.resources_ticks] at ticks
  have limit := WriteBuffer.readDemand_height (p := SP1Prime) run.1.2 collected ticks (run.2.2.1 .readBytes)
  have hq : WitnessGeneration.demandHeight inputs.length ≤ UInt64.size := by rw [size]; exact limit.trans (by decide)
  refine ⟨hq, ?_, probe_packet_words_balanced batch bounded inputs emitted data hq hp hw⟩
  have height : (WriteProbe.table inputs data hq).length = WitnessGeneration.demandHeight inputs.length :=
    (Table.ofInputs_length WriteProbe.component (WriteProbe.physicalInputs inputs) data
      ((WriteProbe.physicalInputs_length inputs).trans_le hq) (fun _ => trivial)).trans (WriteProbe.physicalInputs_length inputs)
  rw [height, size, WriteBuffer.readDemand_length collected, Nat.add_comm]

end SP1Clean.WritePacket
