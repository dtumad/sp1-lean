import SP1Clean.Export.InstalledFixedPreset
import SP1Clean.Proofs.Completeness.WriteProbeDemand

/-! # Observation demand of released WRITE calls under the installed shard preset

The existing tick and read-byte limits pay for one x12 probe per call and its actual aligned
RAM packet. The row count applies to a demand table storing one probe per row.
-/

namespace SP1Clean.Export.InstalledAssembly
open Semantics Machine FormalModel.Shard TraceGen.WriteObservations

/-- At the installed resource preset every WRITE supplies its complete aligned packet. The
joint probe count fits one power-of-two table of height at most 2²⁸. -/
theorem fixedProviderPreset_write_probe_bound (ctx : Context) {events : List ExecutionEvent}
    (execution : AdmissibleExecution ctx.limits SP1Prime ctx.image ctx.source ctx.target events)
    (preset : ctx.limits.LE fixedProviderPreset) :
    ∃ packets, packets? (policy SP1Prime ctx.image) ctx.image.program ctx.source.realize events = some packets ∧
      packets.length = events.countP isWriteCall ∧
      requestedBytes packets = executionResources (policy SP1Prime ctx.image) ctx.image.program ctx.source.realize events .readBytes ∧
      8 * wordProbes packets ≤ requestedBytes packets + 14 * packets.length ∧
      packets.length ≤ 63550 ∧ wordProbes packets ≤ 266449516 ∧
      wordProbes packets + packets.length ≤ 266513066 ∧
      Air.Flat.WitnessGeneration.demandHeight (wordProbes packets + packets.length) ≤ 2 ^ 28 := by
  obtain ⟨packets, built⟩ := admissible_packets execution
  obtain ⟨bytes, _, alignment⟩ := packets_cost execution.1.2 built
  have reads := execution.2.2.1 .readBytes
  have ticks := execution.2.2.1 .ticks
  rw [execution.1.2.resources_ticks] at ticks
  exact ⟨packets, built, packets_length built, bytes, alignment,
    packets_native_bound execution.1.2 built (ticks.trans preset.2.1) (reads.trans preset.2.2.1)⟩

end SP1Clean.Export.InstalledAssembly
