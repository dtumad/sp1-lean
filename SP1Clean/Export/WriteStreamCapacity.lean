import SP1Clean.Export.InstalledFixedPreset
import SP1Clean.Native.Operations.WriteStreamSource
import SP1Clean.Proofs.Completeness.WriteStreamExecution

/-! # Physical height of the fixed WRITE transcript

The output bytes live at the destination. Consumed hook replies and their ordered return
buffers come from the source. A consumed reply also leaves a request at the destination.
Together these two endpoint budgets pay for all fixed rows and power-of-two padding.
-/

namespace SP1Clean.Export.InstalledAssembly

open Circuit Air.Flat Semantics Machine FormalModel.Shard WriteEffects

private theorem replies_fit (state : ExecutionState) :
    (state.host.replies.map HookReply.payloadCost).sum + 125 ≤ state.boundaryPayload := by
  simp only [ExecutionState.boundaryPayload, HostState.payloadCost, hintPayloadCost, bytePayloadCost]
  omega

private theorem outputs_fit (state : ExecutionState) :
    state.host.stdout.length + state.host.stderr.length + state.host.io.publicOutput.length +
      (state.host.requests.map HookRequest.payloadCost).sum + 125 ≤ state.boundaryPayload := by
  simp only [ExecutionState.boundaryPayload, HostState.payloadCost, hintPayloadCost, bytePayloadCost]
  omega

/-- The installed transcript source reserves one fixed-stream occurrence for every padded row. -/
theorem fixedProviderPreset_stream_height (ctx : Context) {events : List ExecutionEvent}
    (run : AdmissibleExecution ctx.limits SP1Prime ctx.image ctx.source ctx.target events)
    (preset : ctx.limits.LE fixedProviderPreset) :
    (streamTable (p := SP1Prime) ctx.source.host ctx.target.host).height ≤ 2 ^ 30 := by
  let streams := WriteStreams.fromEndpoints ctx.source.host ctx.target.host
  have bound : streams.Binds ctx.source.host ctx.target.host := execution_streams run.1.2
  have inventory := admissible_inventoryOK (run.mono (preset.trans fixedProviderPreset_le_native))
  have active : (streamTable (p := SP1Prime) ctx.source.host ctx.target.host).length = (queries streams).length :=
    fixedRows_length_eq inventory
  apply Nat.pow_le_pow_right (by decide : 0 < 2)
  apply (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mpr
  rw [active]
  apply (queries_length_le streams).trans
  have smaller := run.mono preset
  have src := (replies_fit ctx.source.realize).trans (smaller.2.2.2.1 .boundaryBytes)
  have dst := (outputs_fit ctx.target.realize).trans (smaller.2.2.2.2.1 .boundaryBytes)
  change (ctx.source.host.replies.map HookReply.payloadCost).sum + 125 ≤ 2 ^ 29 + 124 at src
  change ctx.target.host.stdout.length + ctx.target.host.stderr.length + ctx.target.host.io.publicOutput.length +
    (ctx.target.host.requests.map HookRequest.payloadCost).sum + 125 ≤ 2 ^ 29 + 124 at dst
  rw [bound.stdout, bound.stderr, bound.publicOutput, bound.requests] at dst
  rw [bound.replies] at src
  simp only [List.length_append, List.map_append, List.sum_append] at src dst
  unfold streamCost
  cases replies : streams.hooks with
  | nil => simp only [List.map_nil, List.sum_nil, Nat.add_zero]; omega
  | cons r rs =>
    simp only [replies, List.map_cons, List.sum_cons, HookRequest.payloadCost, bytePayloadCost] at src dst ⊢
    omega

end SP1Clean.Export.InstalledAssembly
