import SP1Clean.Proofs.Completeness.HintHandlerLedger

/-! # Physical HINT_READ handler and transfer handoff on the same mixed tape

Both endpoints on a generated header are the endpoints of its actual populated word walk.
The five original readers keep every occurrence on the immutable channels, including guarded
padding. Native ticks and paid padded bytes bound the heights without additional premises.
-/

namespace SP1Clean.TraceGen.HintHandlers

open Channels Circuit Air.Flat Semantics HintQueue Machine FormalModel.Shard Soundness HostHintQueue WitnessGeneration
private abbrev F := ZMod SP1Prime

variable {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
  (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events) (data : ProverData F)

include run in
/-- The active read headers and the terminal word transfers occur once per real HINT_READ. -/
theorem readRows_length :
    (readRows (history image source events)).length = (events.filterMap HintReadDemand.length?).length := by
  rw [readRows, history, List.filterMap_filterMap, List.length_filterMap_eq_countP, List.length_filterMap_eq_countP]
  conv_rhs => rw [← List.map_getElem_finRange events, List.countP_map]
  apply List.countP_congr
  intro i _
  exact Bool.eq_iff_iff.mp (at_complete run (List.getElem?_eq_getElem i.isLt)).2.2.2

include run in
private theorem active_cursors :
    (readRows (history image source events)).flatMap headerCursors = HintReadTransfers.endpointLedger image source events := by
  rw [readRows, history, List.filterMap_filterMap]
  simp only [List.filterMap_eq_flatMap_toList,
    List.flatMap_assoc, HintReadTransfers.endpointLedger]
  apply List.flatMap_congr
  intro pos _
  exact (at_complete run (List.getElem?_eq_getElem pos.isLt)).2.2.1.symm

/-- Two actual header cursor sites at every physical row, with the same gate on both. -/
theorem readTable_cursors :
    (readTable run data).interactionsWith HintReadWordChip.stateChannel.toRaw =
      (guardedRows (F := F) (readRows (history image source events))).flatMap (fun r =>
        [HintReadWordChip.stateChannel.pushedIfValue r.2 r.1.first, HintReadWordChip.stateChannel.pulledIfValue r.2 r.1.final]) := by
  apply Table.ofInputs_ledger
  case bound =>
    have height := tables_heights run data
    exact (guardedRows_length _).trans_le ((height.1.symm.le.trans height.2.1).trans (by decide))
  case demand => intro _; trivial
  intro env
  have sites := HostHintReadCoverage.handler_cursor env
  rw [HostHintReadCoverage.decoded_activity] at sites
  exact sites

/-- All physical cursor requests and publications balance between the populated HINT_READ
header and its continuing and final word tables, including calls with empty payloads. -/
theorem transfer_closed :
    let channel := (HintReadWordChip.stateChannel (p := SP1Prime)).toRaw
    LogUpBalanced (((readTable run data).interactionsWith channel ++ (transferTable run false data).interactionsWith channel) ++
      (transferTable run true data).interactionsWith channel) := by
  dsimp only
  obtain ⟨_, _, _, _, _, _, closed⟩ := HintReadTransfers.tables_cursor_closed run data
  intro msg
  have sum := closed msg
  rw [balanceOf_append, balanceOf_append] at sum ⊢
  rw [readTable_cursors]
  let values (r : HostHintReadChip.Inputs F × F) :=
    [HintReadWordChip.stateChannel.pushedIfValue r.2 r.1.first, HintReadWordChip.stateChannel.pulledIfValue r.2 r.1.final]
  have zero : balanceOf (values 0) msg = 0 := by
    simp only [values, balanceOf_cons]
    simp [Channel.pushedIfValue, Channel.pulledIfValue, Interaction.signedMult, balanceOf]
    exact ite_self 0
  rw [guardedRows_balanceOf _ values msg zero]
  change balanceOf ((readRows _).flatMap headerCursors) msg + _ + _ = 0
  rwa [active_cursors run]

/-- Each physical row contributes two cursor sites. The native paid heights keep their sum
below the field characteristic, so Clean's signed test implies active message matching. -/
theorem transfer_matches :
    let channel := (HintReadWordChip.stateChannel (p := SP1Prime)).toRaw
    let ledger := (readTable run data).interactionsWith channel ++ (transferTable run false data).interactionsWith channel ++
      (transferTable run true data).interactionsWith channel
    ledger.length = 2 * ((readTable run data).length + (transferTable run false data).length + (transferTable run true data).length) ∧
      (Balance.logUp (F := F)).fits ledger.length = true ∧ BalancedInteractions ledger := by
  dsimp only
  obtain ⟨headHeight, headBound, _, transferHeight⟩ := tables_heights run data
  have count (last : Bool) :
      ((transferTable run last data).interactionsWith HintReadWordChip.stateChannel.toRaw).length =
        2 * (transferTable run last data).length := by
    rw [(transferHeight last).1]
    unfold transferTable
    rw [HintReadTransfers.wordTable_cursors]
    simp [List.length_flatMap, List.map_const', HintReadTransfers.physicalInputs_length, Nat.mul_comm]
  have heads : ((readTable run data).interactionsWith HintReadWordChip.stateChannel.toRaw).length = 2*(readTable run data).length := by
    rw [readTable_cursors, headHeight]
    simp [List.length_flatMap, List.map_const', guardedRows_length, Nat.mul_comm]
  let ch := (HintReadWordChip.stateChannel (p := SP1Prime)).toRaw
  let ledger := (readTable run data).interactionsWith ch ++ (transferTable run false data).interactionsWith ch ++
    (transferTable run true data).interactionsWith ch
  have total : ledger.length = 2 * ((readTable run data).length + (transferTable run false data).length + (transferTable run true data).length) := by
    dsimp only [ledger, ch]
    rw [List.length_append, List.length_append, heads, count false, count true]
    omega
  refine ⟨total, ?_⟩
  have fit : (Balance.logUp (F := F)).fits ledger.length = true := by
    rw [total]
    simp only [Balance.logUp, decide_eq_true_eq, ComputableRingChar.char_eq, ZMod.ringChar_zmod_n]
    have safety : 2*(2^16 + 2*2^28) < SP1Prime := by decide
    have next := (transferHeight false).2
    have last := (transferHeight true).2
    omega
  exact ⟨fit, Balance.logUp.balancedInteractions_of_balanced _ fit (transfer_closed run data)⟩

/-- Exact immutable node and word occurrence counts, including every independent zero-weight
read at padding. The count on each channel sits below the characteristic on the native preset. -/
theorem reader_counts :
    let ts := readerTables run data
    let nodes := (ts.flatMap (·.interactionsWith nodeChannel.toRaw)).length
    let words := (ts.flatMap (·.interactionsWith wordChannel.toRaw)).length
    nodes = (readTable run data).length + (lengthTable run false data).length ∧
    words = (readTable run data).length + (transferTable run false data).length + (transferTable run true data).length ∧
    nodes < SP1Prime ∧ words < SP1Prime := by
  dsimp only
  obtain ⟨readNode, readWord⟩ := readTable_records run data
  obtain ⟨empty, lengths, transfers⟩ := silent_records run data
  obtain ⟨readHeight, readBound, lengthHeight, transferHeight⟩ := tables_heights run data
  simp only [readerTables, List.flatMap_cons, List.flatMap_nil, List.append_nil, empty, lengths, transfers,
    readNode, readWord, lengthTable_nodes, transferTable_words, List.nil_append, List.length_append,
    List.length_map, guardedRows_length, HintReadTransfers.physicalInputs_length]
  obtain ⟨lenHeight, lenBound⟩ := lengthHeight false
  obtain ⟨nextHeight, nextBound⟩ := transferHeight false
  obtain ⟨lastHeight, lastBound⟩ := transferHeight true
  rw [← readHeight, ← lenHeight, ← nextHeight, ← lastHeight]
  have characteristic : 2^16 + 2*2^28 < SP1Prime := by decide
  omega

/-- Physical permission, host RAM, Memory and Byte sites obey the semantic padded-byte bounds
on the actual three HINT_READ tables. The shared Byte bus also charges the handler separately. -/
theorem paid_fanout :
    let limits := ResourceLimits.native SP1Prime
    let ts := [readTable run data, transferTable run false data, transferTable run true data]
    let sites := fun channel => (ts.flatMap (·.interactionsWith channel)).length
    sites WritePermissionProvider.channel.toRaw ≤ 2 * limits.writeBytes ∧
    2 * sites HostRamAccessChip.channel.toRaw ≤ limits.writeBytes ∧
    2 * sites memoryChannel.toRaw ≤ limits.writeBytes ∧
    sites byteChannel.toRaw ≤ 3 * limits.writeBytes + 24 * (events.filterMap HintReadDemand.length?).length ∧
    sites byteChannel.toRaw ≤ 6 * limits.writeBytes := by
  obtain ⟨readHeight, _, _, transferHeight⟩ := tables_heights run data
  rw [readRows_length run] at readHeight
  apply HintReadCapacity.padded_counts_le run _ _ _ rfl rfl rfl readHeight
  · simpa only [HintReadTransfers.selected_length run, Bool.false_eq_true, ↓reduceIte] using (transferHeight false).1
  · simpa only [readHeight, HintReadTransfers.selected_length run, ↓reduceIte] using (transferHeight true).1

end SP1Clean.TraceGen.HintHandlers
