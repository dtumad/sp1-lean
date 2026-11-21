import SP1Clean.Math.SP1Field
import SP1Clean.FormalModel.ShardResources
import SP1Clean.Native.Operations.HintQueueSource
import SP1Clean.Native.Operations.HintQueueWordSource
import ToClean.Air.Footprint

/-! # Capacity of the fixed source hint providers

The eight-byte length prefix of each hint pays for its mandatory final word, including for
empty and aligned buffers. The complete incoming payload bounds the original inventories,
their power-of-two preprocessing and their separate node and word channel occurrences.
-/

namespace SP1Clean.Export
open Air.Flat Semantics Semantics.HintQueue HostHintQueue

/-- The fixed node and word components each emit exactly once per physical row on their own
channel, including zero-count duplicates and power-of-two padding. -/
theorem fixed_hint_occurrences (hints : List Bytes) (nodes words : Table (ZMod SP1Prime))
    (nodeSlot : nodes.component = HostHintQueue.source hints)
    (wordSlot : words.component = sourceWord hints) :
    (nodes.interactionsWith nodeChannel.toRaw).length = (sourceTable (p := SP1Prime) hints).height ∧
    (words.interactionsWith wordChannel.toRaw).length = (sourceWordInventory (p := SP1Prime) hints).height := by
  have nodeRows := nodes.fixed_rows_match
  have wordRows := words.fixed_rows_match
  rw [nodeSlot] at nodeRows
  rw [wordSlot] at wordRows
  have nodeHeight : nodes.length = (sourceTable (p := SP1Prime) hints).height := nodeRows.1
  have wordHeight : words.length = (sourceWordInventory (p := SP1Prime) hints).height := wordRows.1
  rw [Table.interactionsWith_length, Table.interactionsWith_length, nodeHeight, wordHeight, nodeSlot, wordSlot]
  simp [Component.channelWidth, Component.interactionsWith_eq, Component.rowOperations,
    HostHintQueue.source, sourceWord, StaticTable.payloadComponent, StaticTable.payloadProvider, circuit_norm]

end SP1Clean.Export

namespace SP1Clean.FormalModel.Shard
open Semantics Machine HintQueue HostHintQueue

private theorem hintCosts (hints : List Bytes) :
    (hints.map bytePayloadCost).sum = 8 * hints.length + (hints.map List.length).sum ∧
    hints.length ≤ (hints.map wordCount).sum ∧
    8 * (hints.map wordCount).sum ≤ (hints.map bytePayloadCost).sum := by
  induction hints with
  | nil => simp
  | cons bytes rest ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, bytePayloadCost, wordCount] at *
    omega

/-- A source admitted beneath the native boundary budget preserves every initial node and
padded hint word. The actual fixed heights fit the same payload-derived power of two, at
most 2^28. Each channel can spend its own remaining field capacity on other occurrences. -/
theorem AdmissibleExecution.fixed_hint_capacity {limits : ResourceLimits} {image : ProgramImage}
    {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (execution : AdmissibleExecution limits SP1Prime image source target events)
    (ceiling : limits.boundaryBytes ≤ SP1Prime - 1) :
    let hints := source.host.io.hints
    let nodes := sourceTable (p := SP1Prime) hints
    let words := sourceWordInventory (p := SP1Prime) hints
    let bound := 2 ^ Nat.clog 2 ((limits.boundaryBytes - 125) / 8)
    nodes.length = hints.length ∧ words = sourceWordTable hints ∧
      words.length = (hints.map wordCount).sum ∧
      nodes.height ≤ bound ∧ words.height ≤ bound ∧ bound ≤ 2 ^ 28 ∧
      ∀ otherNodes otherWords : ℕ,
        (nodes.height + otherNodes < SP1Prime ↔ otherNodes ≤ SP1Prime - 1 - nodes.height) ∧
        (words.height + otherWords < SP1Prime ↔ otherWords ≤ SP1Prime - 1 - words.height) := by
  let hints := source.host.io.hints
  have sourceFit := execution.2.2.2.1
  rw [source.resources_realize] at sourceFit
  have payload := sourceFit .boundaryBytes
  change source.resources .boundaryBytes ≤ limits.boundaryBytes at payload
  have overhead : (hints.map bytePayloadCost).sum + 125 ≤ source.resources .boundaryBytes := by
    simp only [hints, ExecutionSnapshot.resources, HostState.payloadCost, hintPayloadCost, bytePayloadCost]
    omega
  obtain ⟨cost, nodes_le_words, wordCost⟩ := hintCosts hints
  have fieldSize : SP1Prime < 2 ^ 31 := by decide
  have nodeBound : hints.length < 2 ^ 48 := by omega
  have bytesBound : (hints.map List.length).sum ≤ SP1Prime - 1 := by omega
  have retained := sourceWordInventory_of_limits (p := SP1Prime) hints (SP1Prime - 1)
    (by omega) bytesBound (by decide)
  have nodeLength : (sourceTable (p := SP1Prime) hints).length = hints.length := by
    simp only [sourceTable, StaticTable.ofRows, sourceRows, ite_eq_left nodeBound, List.length_ofFn, ofList_size]
  have wordLength : (sourceWordInventory (p := SP1Prime) hints).length = (hints.map wordCount).sum := by
    rw [retained]
    simp only [sourceWordTable, StaticTable.ofRows, sourceWordRows_length, ite_eq_left nodeBound]
    apply congrArg List.sum
    apply List.map_congr_left
    intro bytes member
    have size := List.le_sum_of_mem (List.mem_map_of_mem (f := List.length) member)
    apply Nat.min_eq_left
    unfold wordCount
    omega
  have rows : (hints.map wordCount).sum ≤ (limits.boundaryBytes - 125) / 8 := by omega
  have nodeHeight := Nat.pow_le_pow_right (by decide : 0 < 2)
    (Nat.clog_mono_right 2 (nodeLength.le.trans (nodes_le_words.trans rows)))
  have wordHeight := Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.clog_mono_right 2 (wordLength.le.trans rows))
  have maxRows : (limits.boundaryBytes - 125) / 8 ≤ 2 ^ 28 := by omega
  have maxHeight := Nat.pow_le_pow_right (by decide : 0 < 2) ((Nat.clog_le_iff_le_pow (by decide)).mpr maxRows)
  refine ⟨nodeLength, retained, wordLength, nodeHeight, wordHeight, maxHeight, ?_⟩
  have remaining (height other : ℕ) (small : height ≤ 2 ^ 28) :
      height + other < SP1Prime ↔ other ≤ SP1Prime - 1 - height := by
    have room : 2 ^ 28 < SP1Prime := by decide
    omega
  exact fun n w => ⟨remaining _ n (nodeHeight.trans maxHeight), remaining _ w (wordHeight.trans maxHeight)⟩

end SP1Clean.FormalModel.Shard
