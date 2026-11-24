import SP1Clean.Proofs.Completeness.WritePacketInputs
import SP1Clean.Proofs.Chips.WritePacket.Physical
import ToClean.Air.GuardedDemandTable
import ToClean.Air.Footprint

/-! # The mixed-tape native packet table and its original signed ledgers -/

namespace SP1Clean.WritePacket

open Circuit Air.Flat Semantics Machine TraceGen FormalModel.Shard
open scoped Classical

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-- One normal Clean table build for all packet inputs, padded globally. -/
def table (inputs : List (Inputs (ZMod p))) (data : ProverData (ZMod p))
    (fits : WitnessGeneration.demandHeight inputs.length ≤ UInt64.size) : Table (ZMod p) :=
  Table.ofInputs component (WitnessGeneration.guardedRows inputs) data ((WitnessGeneration.guardedRows_length inputs).trans_le fits)
    (fun _ => trivial)

theorem table_ledger (inputs : List (Inputs (ZMod p))) (data : ProverData (ZMod p)) (fits) (ch : RawChannel (ZMod p)) :
    (table inputs data fits).interactionsWith ch =
      (WitnessGeneration.guardedRows inputs).flatMap (fun r => (rowTraffic r).filter (·.channel = ch)) := by
  apply Table.ofInputs_ledger
  intro env
  rw [Operations.interactionValuesWith_eq_filter, component_traffic]
  rfl

/-- The exact signed packet-side header quantities used to cancel the span table. -/
theorem table_headers (inputs : List (Inputs (ZMod p))) (data : ProverData (ZMod p)) (fits) :
    (table inputs data fits).interactionsWith channel.toRaw =
      (WitnessGeneration.guardedRows inputs).map (fun r => channel.pushedIfValue r.2 r.1.header) := by
  rw [table_ledger, List.map_eq_flatMap]
  apply List.flatMap_congr
  intro r _
  simp [rowTraffic, Channel.pushedIfValue, Channel.pulledIfValue, HostCallChip.channel, WriteProbe.readChannel, channel, Channel.toRaw]

/-- The signed length record in each packet, including inactive rows and repeated x12 reads. -/
theorem table_reads (inputs : List (Inputs (ZMod p))) (data : ProverData (ZMod p)) (fits) :
    (table inputs data fits).interactionsWith WriteProbe.readChannel.toRaw =
      (WitnessGeneration.guardedRows inputs).map (fun r => WriteProbe.readChannel.pulledIfValue r.2 r.1.read) := by
  rw [table_ledger, List.map_eq_flatMap]
  apply List.flatMap_congr
  intro r _
  simp [rowTraffic, Channel.pushedIfValue, Channel.pulledIfValue, HostCallChip.channel, WriteProbe.readChannel, channel, Channel.toRaw]

/-- The signed original ECALL receipts consumed from the common HostCall channel. -/
theorem table_calls (inputs : List (Inputs (ZMod p))) (data : ProverData (ZMod p)) (fits) :
    (table inputs data fits).interactionsWith HostCallChip.channel.toRaw =
      (WitnessGeneration.guardedRows inputs).map (fun r => HostCallChip.channel.pulledIfValue r.2 r.1.call) := by
  rw [table_ledger, List.map_eq_flatMap]
  apply List.flatMap_congr
  intro r _
  simp [rowTraffic, Channel.pushedIfValue, Channel.pulledIfValue, HostCallChip.channel, WriteProbe.readChannel, channel, Channel.toRaw]

/-- Every active packet row in a real mixed tape is populated from the execution's matching
span. The original public input is unrestricted; every raw packet ledger has its exact native height. -/
theorem native_packet_table {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events) (data : ProverData (ZMod SP1Prime))
    {packets : List WriteObservations.Packet} (collected : WriteObservations.packets? (policy SP1Prime image) image.program source.realize events = some packets) :
    let inputs := (WriteBuffer.packetRows (p := SP1Prime) events packets).map (fun r => fromHeader r.span.header)
    ∃ fits, let packet := table inputs data fits
            packet.Constraints ∧ packet.Guarantees ∧ packet.length = WitnessGeneration.demandHeight packets.length ∧
            ∀ ch ∈ [HostCallChip.channel.toRaw, WriteProbe.readChannel.toRaw, channel.toRaw], (packet.interactionsWith ch).length = packet.length := by
  let batch := WriteBuffer.packetRows (p := SP1Prime) events packets
  let inputs := batch.map (fun r => fromHeader r.span.header)
  have size : inputs.length = packets.length := (List.length_map ..).trans
    ((WriteBuffer.packetRows_length collected).trans (WriteObservations.packets_length collected).symm)
  have ticks := run.2.2.1 .ticks
  rw [run.1.2.resources_ticks] at ticks
  have bound := (WriteObservations.packets_native_bound run.1.2 collected ticks (run.2.2.1 .readBytes)).1
  have fits : WitnessGeneration.demandHeight inputs.length ≤ UInt64.size := by
    apply (WitnessGeneration.demandHeight_le_pow (exponent := 16) ?_).trans (by decide)
    rw [size]; omega
  have honest (i) (used : i ∈ inputs) : i.timestamp.Bounded := by
    obtain ⟨r, member, rfl⟩ := List.mem_map.mp used
    obtain ⟨_, _, _, _, _, _, _, ok, _⟩ := packet_input_at run collected member
    exact ok
  have valid := Table.ofInputs_valid component (WitnessGeneration.guardedRows inputs) data
    ((WitnessGeneration.guardedRows_length inputs).trans_le fits) (fun _ => trivial)
    (WitnessGeneration.guardedRows_all _ honest)
  have height : (table inputs data fits).length = WitnessGeneration.demandHeight inputs.length :=
    (Table.ofInputs_length ..).trans (WitnessGeneration.guardedRows_length inputs)
  refine ⟨fits, valid.1, valid.2, height.trans (congrArg _ size), ?_⟩
  intro ch member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · rw [table_calls, List.length_map, WitnessGeneration.guardedRows_length, height]
  · rw [table_reads, List.length_map, WitnessGeneration.guardedRows_length, height]
  · rw [table_headers, List.length_map, WitnessGeneration.guardedRows_length, height]

end SP1Clean.WritePacket
