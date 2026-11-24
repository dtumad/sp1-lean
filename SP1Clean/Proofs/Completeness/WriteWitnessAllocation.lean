import SP1Clean.Proofs.Completeness.WriteAllocationStore

/-! # Physical rows emitted by one allocating WRITE

An open row includes empty hook replies. Each new immutable node has exactly one contents
seed and its complete padded word walk. Query multiplicities are indexed by the actual
published records so identical lookups share the same committed supply.
-/

namespace SP1Clean.WriteAllocation

open Semantics HintQueue Machine
private abbrev F := ZMod SP1Prime

/-- Multiplicities on the three original node, placement-block and immutable-word channels. -/
structure Readers where
  /-- Number of queries to this immutable node. -/
  nodes : NodeRecord F → F
  /-- Number of guest placement queries to this direct block. -/
  blocks : WriteEffects.StreamBlock F → F
  /-- Number of queries to this immutable word. -/
  words : WordRecord F → F

/-- A node step, its seed authorization and the associated physical word rows in pointer order.
The mandatory seed is the step's own contents projection. -/
structure NodeRows where
  /-- Source of the sole contents authorization for the word walk. -/
  step : Step F
  /-- Includes the final padded position, even for an empty or aligned buffer. -/
  words : List (Words.Row F)

/-- Actual rows for a single queue ticket, including the open row when a hook allocates no nodes. -/
structure BatchRows where
  /-- The allocation consumes exactly this dispatch ticket. -/
  opening : Open F
  /-- Fresh nodes appear in increasing physical pointer order. -/
  nodes : List NodeRows

/-- Produce the checked word walk with multiplicities indexed by its actual carried payloads. -/
def nodeRows (readers : Readers) (step : Step F) (bytes : Bytes) : NodeRows :=
  let word := fun i => Words.populate step.contents bytes i 0 0
  ⟨step, Words.walk step.contents bytes (fun i => readers.blocks (word i).direct) (fun i => readers.words (word i).word)⟩

/-- Compile all rows of an allocating WRITE. Reverse logical buffer order is the order of
fresh physical pointers used by persistent prepend. -/
def Batch.rows (batch : Batch) (previous clock : Nat) (before : Store × Nat) (readers : Readers) : BatchRows :=
  let steps := batch.steps clock before.1 before.2 readers.nodes
  ⟨batch.openRow previous clock before.1 before.2, List.zipWith (nodeRows readers) steps batch.buffers.reverse⟩

private theorem Batch.steps_length (batch : Batch) (clock : Nat) (before : Store × Nat) (readers : Readers) :
    (batch.steps clock before.1 before.2 readers.nodes).length = batch.buffers.length := by
  simp only [Batch.steps, List.length_map, List.length_zipIdx, HintNodeAllocate.compilePrepend_length]

/-- The node and contents tables have exactly one row per allocated buffer, with no truncation
when the semantic and physical node lists are joined. -/
theorem Batch.rows_length (batch : Batch) (previous clock : Nat) (before : Store × Nat) (readers : Readers) :
    (batch.rows previous clock before readers).nodes.length = batch.buffers.length := by
  simp [Batch.rows, List.length_zipWith, batch.steps_length clock before readers]

/-- At every fresh pointer, these exact emitted node and word rows bind the real persistent
store and every later extension. The carried cursor, word count and byte length are preserved. -/
theorem Batch.rows_at (batch : Batch) (previous clock : Nat) (before : Store × Nat) (after : Store)
    (publishes : batch.Publishes clock before after) (readers : Readers) (i : Fin batch.buffers.length) :
    let bytes := batch.buffers.reverse[i.val]'(by simp)
    ∃ rows, (batch.rows previous clock before readers).nodes[i.val]? = some rows ∧
      rows.step.Valid ∧ rows.step.before = batch.cursorAt clock before.2 before.1.size i ∧
      rows.step.after = batch.cursorAt clock before.2 before.1.size (i.val+1) ∧
      rows.step.contents.pointer = Address.ofNat (before.1.size + i + 1) ∧ rows.step.contents.length = Address.ofNat bytes.length ∧
      rows.words.length = wordCount bytes ∧ ∀ later, Extends after later →
        rows.step.node.node.Binds later ∧ ∀ r ∈ rows.words, r.word.Binds later := by
  intro bytes
  obtain ⟨step, found, valid, first, last, pointer, size, _, binds⟩ := publishes readers.nodes i
  let node := nodeRows readers step bytes
  have rowAt : (batch.rows previous clock before readers).nodes[i.val]? = some node := by
    have atBytes : batch.buffers.reverse[i.val]? = some bytes := List.getElem?_eq_getElem (by simp)
    simp only [Batch.rows, List.getElem?_zipWith, found, atBytes]
    rfl
  have height : node.words.length = wordCount bytes := by
    simp only [node, nodeRows, Words.walk_length]
  refine ⟨node, rowAt, valid, first, last, pointer, size, height, ?_⟩
  intro later ext
  refine ⟨(binds later ext).1, ?_⟩
  intro r member
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp member
  exact (binds later ext).2 j j.isLt _ _

end SP1Clean.WriteAllocation
