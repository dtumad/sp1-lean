import SP1Clean.Export.InstalledFixedPreset
import SP1Clean.Proofs.Completeness.WriteBlockCapacity

/-! # Full physical WRITE block matching at the fixed-provider preset

Guest reads pay for grouped placements. Live and popped queue words pay for the complete
allocation table. The two endpoints pay for the fixed block source, including the submitted
request left at the target by every consumed hook reply. These charges bound all occurrences
before applying Clean's signed-to-matching theorem.
-/

namespace SP1Clean.Export.InstalledAssembly
open Circuit Air.Flat Semantics Machine FormalModel.Shard TraceGen WriteAllocation WriteEffects WriteEffects.Witness

private theorem incoming_bytes (state : ExecutionState) :
    (state.host.replies.map HookReply.payloadCost).sum + 125 ≤ state.boundaryPayload := by
  simp only [ExecutionState.boundaryPayload,HostState.payloadCost,hintPayloadCost,bytePayloadCost]
  omega

private theorem outgoing_bytes (state : ExecutionState) :
    state.host.stdout.length + state.host.stderr.length + state.host.io.publicOutput.length +
      (state.host.requests.map HookRequest.payloadCost).sum + 125 ≤ state.boundaryPayload := by
  simp only [ExecutionState.boundaryPayload,HostState.payloadCost,hintPayloadCost,bytePayloadCost]
  omega

private theorem fixed_paid {source target : ExecutionSnapshot} {s : WriteStreams}
    (streams : s.Binds source.host target.host)
    (low : source.realize.boundaryPayload ≤ 2^29+124) (high : target.realize.boundaryPayload ≤ 2^29+124) :
    (dataBlocks (p := SP1Prime) s).length ≤ 2^27 := by
  have initial := (incoming_bytes source.realize).trans low
  have final := (outgoing_bytes target.realize).trans high
  change (source.host.replies.map HookReply.payloadCost).sum + 125 ≤ 2^29+124 at initial
  change target.host.stdout.length + target.host.stderr.length + target.host.io.publicOutput.length +
    (target.host.requests.map HookRequest.payloadCost).sum + 125 ≤ 2^29+124 at final
  rw [streams.stdout,streams.stderr,streams.publicOutput,streams.requests] at final
  rw [streams.replies] at initial
  simp only [List.length_append,List.map_append,List.sum_append,List.map_map] at initial final
  have blocks := dataBlocks_paid (p := SP1Prime) s
  unfold streamCost at blocks
  cases returned : s.hooks with
  | nil => simp only [returned,List.map_nil,List.sum_nil] at blocks; omega
  | cons reply rest =>
    have request : 12 ≤ ((HookRequest.payloadCost ∘ HookReply.request) reply) := by
      simp only [Function.comp_apply,HookRequest.payloadCost,bytePayloadCost]; omega
    rw [returned] at final
    simp only [List.map_cons,List.sum_cons] at final
    omega

/-- The two paid boundary inventories suffice for at most 2^27 physical fixed rows.
The case of a consumed, but empty, hook reply retains its actual request charge. -/
theorem fixedProviderPreset_block_height {ctx : Context} {events : List ExecutionEvent}
    (run : AdmissibleExecution ctx.limits SP1Prime ctx.image ctx.source ctx.target events)
    (preset : ctx.limits.LE fixedProviderPreset) :
    (blockTable (p := SP1Prime) (.fromEndpoints ctx.source.host ctx.target.host)).height ≤ 2^27 := by
  let s := WriteStreams.fromEndpoints ctx.source.host ctx.target.host
  have bounded := run.mono preset
  have raw := fixed_paid (execution_streams run.1.2) (bounded.2.2.2.1 .boundaryBytes) (bounded.2.2.2.2.1 .boundaryBytes)
  have shape := admissible_inventoryOK (run.mono (preset.trans fixedProviderPreset_le_native))
  have length : (blockTable (p := SP1Prime) s).length ≤ 2^27 := by
    change (if inventoryOK s then dataBlocks (p := SP1Prime) s else []).length ≤ _
    rw [ite_eq_left shape]
    exact raw
  exact Nat.pow_le_pow_right (by decide : 0 < 2) ((Nat.clog_le_iff_le_pow (by decide)).mpr length)

/-- Simultaneous count-fit of all occurrences on the generated block ledger at the existing
fixed-provider preset. The three local ceilings are 2^28, 2^27 and 2^27 respectively. -/
theorem fixedProviderPreset_write_blocks_fit {ctx : Context} {events : List ExecutionEvent}
    (run : AdmissibleExecution ctx.limits SP1Prime ctx.image ctx.source ctx.target events)
    (preset : ctx.limits.LE fixedProviderPreset) (readers : Readers)
    {entries : List Witness.Entry} (collected : Witness.native? ctx.image ctx.source events readers = some entries)
    {placements words fixed : Table Fp}
    (checked : Witness.CombinedBlocksChecked ctx.source.host ctx.target.host
      (entries.flatMap (Witness.Entry.placementGroups (.fromEndpoints ctx.source.host ctx.target.host))).length
      (Witness.inputs entries).words.length placements words fixed) :
    let ledger := placements.interactionsWith blockChannel.toRaw ++ words.interactionsWith blockChannel.toRaw ++ fixed.interactionsWith blockChannel.toRaw
    ledger.length ≤ 7*2^27 ∧ (Balance.logUp (F := Fp)).fits ledger.length = true ∧ BalancedInteractions ledger := by
  let native := run.mono (preset.trans fixedProviderPreset_le_native)
  obtain ⟨actual,built,_,observed,_⟩ := native_inputs native readers
  cases Option.some.inj (collected.symm.trans built)
  have ticks := native.2.2.1 .ticks
  rw [native.1.2.resources_ticks] at ticks
  have small := (WriteObservations.packets_native_bound native.1.2 observed ticks (native.2.2.1 .readBytes)).2.1
  have hg : WitnessGeneration.demandHeight (entries.flatMap (Witness.Entry.placementGroups (.fromEndpoints ctx.source.host ctx.target.host))).length ≤ 2^28 :=
    WitnessGeneration.demandHeight_le_pow ((placementGroups_length _ entries).trans_le (small.trans (by decide)))
  have charge := Witness.word_charge (run.mono preset) fixedProviderPreset_le_native readers collected
  change 8*(Witness.inputs entries).words.length + 125 ≤ (2^29+124)+2^24 at charge
  have hw : WitnessGeneration.demandHeight (Witness.inputs entries).words.length ≤ 2^27 := WitnessGeneration.demandHeight_le_pow (by omega)
  have hf := fixedProviderPreset_block_height run preset
  intro ledger
  have total : ledger.length ≤ 7*2^27 := by rw [show ledger.length = _ from checked.occurrences]; omega
  have below := total.trans_lt (show 7*2^27 < SP1Prime by decide)
  have fit : (Balance.logUp (F := Fp)).fits ledger.length = true := by
    simpa only [Balance.logUp,decide_eq_true_eq,ComputableRingChar.char_eq,ZMod.ringChar_zmod_n] using below
  exact ⟨total,fit,Balance.logUp.balancedInteractions_of_balanced ledger fit checked.signed⟩

end SP1Clean.Export.InstalledAssembly
