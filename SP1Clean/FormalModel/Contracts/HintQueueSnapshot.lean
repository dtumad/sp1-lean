module

public import SP1Clean.Semantics.Host.HintQueueSnapshot

/-! # Fixed outgoing hint words and their private cursor

Each target word has one sequential ordinal across the entire outgoing queue. The cursor
carries the current node and its tail between adjacent words. It follows the tail at the
last word of each buffer, including the mandatory padding of an empty or aligned buffer.
-/

@[expose] public section

namespace SP1Clean.HostHintSnapshot

open Semantics Semantics.HintQueue Soundness.Target

/-- The next fixed ordinal and private node identities at a queue-word boundary. -/
structure Cursor (F : Type) where
  /-- Global word ordinal, including all padding words required by hint semantics. -/
  ordinal : fields 3 F
  /-- Node holding the current target buffer. -/
  head : fields 3 F
  /-- Tail already bound by the node lookup, or zero at a buffer boundary. -/
  tail : fields 3 F
deriving ProvableStruct, DecidableEq
provable_struct_eval_lemmas Cursor

/-- Connect adjacent fixed target-word positions and their private node pointers. -/
def channel {p : ℕ} : Channel (ZMod p) Cursor where
  name := "sp1.native.hint_target_walk"
  Guarantees _ _ := True

/-- The two representations of a queue endpoint share no private node identities across shards. -/
def endpoint {p : ℕ} (ordinal : ℕ) (head : fields 3 (ZMod p)) : Cursor (ZMod p) :=
  ⟨Address.ofNat ordinal, head, 0⟩

/-- Verifier-owned metadata and payload of one outgoing queue word. -/
structure Shape (F : Type) where
  /-- One for a public word, zero on physical table padding. -/
  active : F
  /-- One on the first word of a target hint. -/
  first : F
  /-- One on the final padded word of the target hint. -/
  last : F
  /-- Cursor ordinal before reading this word. -/
  ordinal : fields 3 F
  /-- Cursor ordinal after reading this word. -/
  nextOrdinal : fields 3 F
  /-- Word index within the target hint. -/
  index : fields 3 F
  /-- Target buffer length in bytes, before padding. -/
  length : Word F
  /-- Target bytes at this position, zero-padded to a full word. -/
  value : Word F
deriving ProvableStruct, DecidableEq
provable_struct_eval_lemmas Shape

/-- Private node identities checked against immutable metadata and words. -/
structure Links (F : Type) where
  /-- Node pointer for the buffer that contains this word. -/
  head : fields 3 F
  /-- Next node in the ordered outgoing queue. -/
  tail : fields 3 F
deriving ProvableStruct
provable_struct_eval_lemmas Links

/-- A fixed word shape, private pointers, and the incoming cursor multiplicity. -/
abbrev Inputs := ProvablePair Shape (ProvablePair Links field)

/-- Receive the current head and retain the previously authenticated tail inside a buffer. -/
def Shape.before {F : Type} [Sub F] [Mul F] [One F] (shape : Shape F) (links : Links F) : Cursor F :=
  ⟨shape.ordinal, links.head, links.tail.map (fun x => (1 - shape.first) * x)⟩

/-- Carry both node pointers inside the buffer and follow its tail on its final word. -/
def Shape.after {F : Type} [Sub F] [Add F] [Mul F] [One F] (shape : Shape F) (links : Links F) : Cursor F :=
  ⟨shape.nextOrdinal, Vector.ofFn (fun i : Fin 3 => links.head[i.val] + shape.last * (links.tail[i.val] - links.head[i.val])),
    links.tail.map (fun x => (1 - shape.last) * x)⟩

/-- Node metadata demanded by the first word in a target hint. -/
def Shape.node {F : Type} (shape : Shape F) (links : Links F) : NodeRecord F :=
  ⟨links.head, links.tail, shape.length⟩

/-- Immutable word demanded at this fixed target position. -/
def Shape.word {F : Type} (shape : Shape F) (links : Links F) : WordRecord F :=
  ⟨links.head, shape.index, shape.value, shape.last⟩

/-- Number of fixed word rows, retaining the terminal padded word of each target hint. -/
def wordRows (hints : List Bytes) : ℕ := (hints.map wordCount).sum

/-- The table and the terminal cursor must represent the exclusive ordinal exactly. -/
def fits (hints : List Bytes) : Bool := decide (wordRows hints < 2 ^ 48)

/-- Construct word values in constant-time indexed reads after converting each buffer once. -/
def arrayWord (bytes : Array (BitVec 8)) (i : ℕ) : BitVec 64 :=
  Word.bytesValue (Vector.ofFn (fun slot : Fin 8 => bytes[8 * i + slot.val]?.getD 0))

theorem arrayWord_toArray (bytes : Bytes) (i : ℕ) : arrayWord bytes.toArray i = wordValue bytes i := by
  simp [arrayWord, wordValue, wordBytes, Nat.mul_comm]

/-- Encode an active public target word with its exact position and boundary flags. -/
def shape {p : ℕ} [Fact p.Prime] (serial i length : ℕ) (word : BitVec 64) : Shape (ZMod p) :=
  ⟨1, if i = 0 then 1 else 0, if i = length / 8 then 1 else 0,
    Address.ofNat serial, Address.ofNat (serial+1), Address.ofNat i, bitVecToWord (BitVec.ofNat 64 length),
    bitVecToWord word⟩

/-- Enumerate the public target once in queue order. For an unrepresentable target, the
physical component rejects through its mandatory verifier-fixed row. -/
def schedule {p : ℕ} [Fact p.Prime] (hints : List Bytes) : List (Shape (ZMod p)) :=
  if fits hints then
    (hints.flatMap fun bytes =>
      let data := bytes.toArray
      (List.range (data.size / 8 + 1)).map fun i => (i, data.size, arrayWord data i)).mapIdx
        fun serial (i, len, value) => shape serial i len value
  else []

theorem schedule_length {p : ℕ} [Fact p.Prime] (hints : List Bytes) :
    (schedule (p := p) hints).length = if fits hints then wordRows hints else 0 := by
  simp only [schedule]
  split
  · simp only [List.length_mapIdx, List.length_flatMap, List.length_map, List.length_range, List.size_toArray, wordRows]
    rfl
  · rfl

end SP1Clean.HostHintSnapshot
