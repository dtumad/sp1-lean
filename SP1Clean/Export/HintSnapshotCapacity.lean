import SP1Clean.Export.InstalledFixedPreset
import SP1Clean.Proofs.Completeness.HintSnapshotLedger

/-! # Physical capacity of the complete outgoing hint walk

Each hint already pays eight bytes for its length in the public boundary measure. This
covers its final padded word, including for empty and eight-byte-aligned hints.
-/

namespace SP1Clean.Export.InstalledAssembly
open Circuit Air.Flat Semantics Semantics.HintQueue Machine FormalModel.Shard HostHintSnapshot

private theorem words_cost (hints : List Bytes) :
    8 * wordRows hints ≤ (hints.map bytePayloadCost).sum := by
  induction hints with
  | nil => simp [wordRows]
  | cons bytes rest ih =>
    simp only [wordRows, List.map_cons, List.sum_cons, Nat.mul_add, wordCount, bytePayloadCost] at *
    omega

private theorem boundary_words (state : ExecutionState) :
    8 * wordRows state.host.io.hints + 125 ≤ state.boundaryPayload := by
  have cost := words_cost state.host.io.hints
  simp only [ExecutionState.boundaryPayload, HostState.payloadCost, hintPayloadCost, bytePayloadCost]
  omega

/-- Every native resource-admissible endpoint admits all fixed word ordinals, including the
exclusive endpoint consumed at the seal. -/
theorem admissible_hint_snapshot_fits {image : ProgramImage} {source target : ExecutionSnapshot}
    {events : List ExecutionEvent}
    (run : AdmissibleExecution (ResourceLimits.native SP1Prime) SP1Prime image source target events) :
    HostHintSnapshot.fits target.host.io.hints = true := by
  have capacity := (boundary_words target.realize).trans (run.2.2.2.2.1 .boundaryBytes)
  change 8 * wordRows target.host.io.hints + 125 ≤ SP1Prime - 1 at capacity
  simp only [fits, decide_eq_true_eq]
  unfold SP1Prime at capacity
  omega

/-- An arbitrary mixed execution supplies the complete physical outgoing reader and singleton
seal. The seal accepts the private queue access clock from the state ledger; its head and
historical allocation frontier come from replay, including after intervening pops. -/
theorem admissible_hint_snapshot_tables {image : ProgramImage} {source target : ExecutionSnapshot}
    {events : List ExecutionEvent}
    (run : AdmissibleExecution (ResourceLimits.native SP1Prime) SP1Prime image source target events)
    (data : ProverData (ZMod SP1Prime)) :
    ∃ cursor, storeAfter? (policy SP1Prime image) image.program source.realize events (ofList source.host.io.hints) = some cursor ∧
      let reader := HostHintSnapshot.tableFor cursor.1 cursor.2 target.host.io.hints (admissible_hint_snapshot_fits run) data
      reader.Constraints ∧ reader.Guarantees ∧
      ∀ clock : BitVec 48,
        let terminal := Seal.tableFor target.host.io.hints (HostHintQueue.State.encode clock.toNat cursor.2 cursor.1.size) data
        terminal.Constraints ∧ terminal.Guarantees ∧
          LogUpBalanced (reader.interactionsWith HostHintSnapshot.channel.toRaw ++ terminal.interactionsWith HostHintSnapshot.channel.toRaw) := by
  obtain ⟨cursor, tails, replay, _, read⟩ := TraceGen.admissibleExecution_hintSnapshot run
  have valid := HostHintSnapshot.tableFor_valid read (admissible_hint_snapshot_fits run) data
  refine ⟨cursor, replay, valid.1, valid.2, fun clock => ?_⟩
  have sealValid := Seal.tableFor_valid target.host.io.hints (HostHintQueue.State.encode (p := SP1Prime) clock.toNat cursor.2 cursor.1.size) data
  exact ⟨sealValid.1, sealValid.2, tableFor_closed read _ data clock⟩

/-- The installed shard preset pays for every physical row of the new outgoing queue reader. -/
theorem fixedProviderPreset_hint_snapshot_height (ctx : Context) {events : List ExecutionEvent}
    (run : AdmissibleExecution ctx.limits SP1Prime ctx.image ctx.source ctx.target events)
    (preset : ctx.limits.LE fixedProviderPreset) :
    (HostHintSnapshot.inventory (p := SP1Prime) ctx.target.host.io.hints).height ≤ 2 ^ 26 := by
  have uses := (boundary_words ctx.target.realize).trans ((run.mono preset).2.2.2.2.1 .boundaryBytes)
  change 8 * wordRows ctx.target.host.io.hints + 125 ≤ 2 ^ 29 + 124 at uses
  have fits := admissible_hint_snapshot_fits (run.mono (preset.trans fixedProviderPreset_le_native))
  apply Nat.pow_le_pow_right (by decide : 0 < 2)
  apply (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mpr
  change (schedule (p := SP1Prime) ctx.target.host.io.hints).length ≤ _
  simp only [schedule_length, fits, ↓reduceIte]
  omega

end SP1Clean.Export.InstalledAssembly
