import SP1Clean.Export.InstalledFixedPreset
import SP1Clean.Native.Operations.WriteStreamSource
import SP1Clean.Proofs.Completeness.WriteFixedDataCapacity

/-! # Physical height of the fixed WRITE transcript

The output bytes live at the destination. Consumed hook replies and their ordered return
buffers come from the source. A consumed reply also leaves a request at the destination.
Together these two endpoint budgets pay for all fixed rows and power-of-two padding.
-/

namespace SP1Clean.Export.InstalledAssembly

open Circuit Air.Flat Semantics Machine FormalModel.Shard WriteEffects

/-- The installed transcript source reserves one fixed-stream occurrence for every padded row. -/
theorem fixedProviderPreset_stream_height (ctx : Context) {events : List ExecutionEvent}
    (run : AdmissibleExecution ctx.limits SP1Prime ctx.image ctx.source ctx.target events)
    (preset : ctx.limits.LE fixedProviderPreset) :
    (streamTable (p := SP1Prime) ctx.source.host ctx.target.host).height ≤ 2 ^ 30 :=
  (admissible_fixed_heights (run.mono (preset.trans fixedProviderPreset_le_native))).2.1

end SP1Clean.Export.InstalledAssembly
