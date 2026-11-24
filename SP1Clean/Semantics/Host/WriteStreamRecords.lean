module

public import SP1Clean.Semantics.Host.WriteEffects
public import SP1Clean.Math.Address
public import ToClean.Circuit.StaticTable
public import Clean.Utils.Tactics.ProvableStructDeriving

/-! # Verifier-fixed WRITE output and hook transcript records

Every local stream has a length record, even for an empty byte sequence. Each consumed
hook has an ordered reply index, a full u32 descriptor, its complete request bytes, and the
length and bytes of every returned hint. Equal byte values at different positions are separate
records. All data comes from the two host snapshots.
-/

@[expose] public section

namespace SP1Clean.WriteEffects
open Semantics

/-- A typed verifier-owned byte string. The last two cases use the ordinal of the consumed reply;
the returned hint also has its own position within that reply. -/
inductive StreamKey where
  | stdout | stderr | publicOutput | request (reply : Nat) | returned (reply hint : Nat)
deriving DecidableEq, Repr

/-- Resolve a stream identifier against the verifier-owned endpoint data. -/
def StreamKey.contents (streams : WriteStreams) : StreamKey → Option Bytes
  | .stdout => some streams.stdout
  | .stderr => some streams.stderr
  | .publicOutput => some streams.publicOutput
  | .request r => (streams.hooks[r]?).map (·.request.input)
  | .returned r h => (streams.hooks[r]?).bind (·.hints[h]?)

/-- A byte, length, descriptor or reply count in the verifier-owned transcript. -/
inductive Query where
  | length (key : StreamKey)
  | byte (key : StreamKey) (index : Nat)
  | descriptor (reply : Nat)
  | returnCount (reply : Nat)
deriving DecidableEq, Repr

/-- The authoritative lookup value. Absent replies, hints and bytes return none. -/
def Query.lookup (streams : WriteStreams) : Query → Option Nat
  | .length key => (key.contents streams).map List.length
  | .byte key i => (key.contents streams).bind fun bytes => bytes[i]?.map BitVec.toNat
  | .descriptor r => streams.hooks[r]? |>.map (·.request.descriptor.toNat)
  | .returnCount r => streams.hooks[r]? |>.map (·.hints.length)

/-- Enumerate the length and every ordered byte position of one stream. -/
def byteQueries (key : StreamKey) (bytes : Bytes) : List Query :=
  .length key :: (List.range bytes.length).map (.byte key)

/-- Enumerate only actual owned positions, retaining metadata and empty strings. -/
def queries (streams : WriteStreams) : List Query :=
  byteQueries .stdout streams.stdout ++ byteQueries .stderr streams.stderr ++
    byteQueries .publicOutput streams.publicOutput ++
    (streams.hooks.zipIdx.flatMap fun (reply, r) =>
      [.descriptor r, .returnCount r] ++ byteQueries (.request r) reply.request.input ++
        (reply.hints.zipIdx.flatMap fun (bytes, h) => byteQueries (.returned r h) bytes))

private theorem query_of_hook {streams : WriteStreams} {r : Nat} {reply : HookReply} {q : Query}
    (found : streams.hooks[r]? = some reply)
    (member : q ∈ [.descriptor r, .returnCount r] ++ byteQueries (.request r) reply.request.input ++
        (reply.hints.zipIdx.flatMap fun (bytes, h) => byteQueries (.returned r h) bytes)) : q ∈ queries streams := by
  apply List.mem_append_right
  exact List.mem_flatMap.mpr ⟨(reply, r), List.mk_mem_zipIdx_iff_getElem?.mpr found, member⟩

private theorem bytes_enumerated {streams : WriteStreams} {key : StreamKey} {bytes : Bytes}
    (found : key.contents streams = some bytes) {q : Query} (member : q ∈ byteQueries key bytes) :
    q ∈ queries streams := by
  cases key with
  | stdout =>
    cases found
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ member))
  | stderr =>
    cases found
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ member))
  | publicOutput =>
    cases found
    exact List.mem_append_left _ (List.mem_append_right _ member)
  | request r =>
    obtain ⟨reply, atReply, rfl⟩ := Option.map_eq_some_iff.mp found
    exact query_of_hook atReply (List.mem_append_left _ (List.mem_append_right _ member))
  | returned r h =>
    obtain ⟨reply, atReply, atHint⟩ := Option.bind_eq_some_iff.mp found
    exact query_of_hook atReply (List.mem_append_right _ (List.mem_flatMap.mpr
      ⟨(bytes, h), List.mk_mem_zipIdx_iff_getElem?.mpr atHint, member⟩))

/-- Every defined byte or metadata value has an actual position in the fixed inventory. -/
theorem Query.enumerated {streams : WriteStreams} {q : Query} {v : Nat} (found : q.lookup streams = some v) :
    q ∈ queries streams := by
  cases q with
  | length key =>
    obtain ⟨bytes, read, _⟩ := Option.map_eq_some_iff.mp found
    exact bytes_enumerated read List.mem_cons_self
  | byte key i =>
    obtain ⟨bytes, read, someByte⟩ := Option.bind_eq_some_iff.mp found
    obtain ⟨byte, atByte, _⟩ := Option.map_eq_some_iff.mp someByte
    exact bytes_enumerated read (List.mem_cons_of_mem _ (List.mem_map.mpr
      ⟨i, List.mem_range.mpr (List.getElem?_eq_some_iff.mp atByte).1, rfl⟩))
  | descriptor r =>
    obtain ⟨reply, atReply, _⟩ := Option.map_eq_some_iff.mp found
    exact query_of_hook atReply (List.mem_append_left _ (List.mem_append_left _ List.mem_cons_self))
  | returnCount r =>
    obtain ⟨reply, atReply, _⟩ := Option.map_eq_some_iff.mp found
    exact query_of_hook atReply (List.mem_append_left _ (List.mem_append_left _ (by simp)))

/-- Field key plus a canonical 48-bit payload. The stream tags are 1/2/13 for the three output
streams, 3 for hook input and 4 for a returned hint. Attributes are length, byte, descriptor
or returned-hint count (0 through 3). -/
structure Record (F : Type) where
  /-- Tag identifying the output, request or returned-hint stream. -/
  stream : F
  /-- Record tag for a length, byte, hook descriptor or return count. -/
  kind : F
  /-- Ordinal of the consumed hook reply, zero for ordinary output streams. -/
  reply : fields 3 F
  /-- Ordinal within a hook’s returned hints when the stream identifies one. -/
  hint : fields 3 F
  /-- Byte position within the stream, zero on metadata records. -/
  offset : fields 3 F
  /-- Exact byte or metadata value carried in three limbs. -/
  value : fields 3 F
deriving ProvableStruct, DecidableEq
provable_struct_eval_lemmas Record

/-- Numeric form has a distinct constructor tag and all three positional coordinates. -/
def StreamKey.coordinates : StreamKey → Nat × Nat × Nat
  | .stdout => (1, 0, 0)
  | .stderr => (2, 0, 0)
  | .publicOutput => (13, 0, 0)
  | .request r => (3, r, 0)
  | .returned r h => (4, r, h)

/-- Assign each query its stream, record tag and position. -/
def Query.coordinates : Query → StreamKey × Nat × Nat
  | .length key => (key, 0, 0)
  | .byte key i => (key, 1, i)
  | .descriptor r => (.request r, 2, 0)
  | .returnCount r => (.request r, 3, 0)

/-- No position or value can alias a different record by wrapping modulo 2^48. -/
def Query.Fits (q : Query) (v : Nat) : Prop :=
  q.coordinates.1.coordinates.2.1 < 2 ^ 48 ∧ q.coordinates.1.coordinates.2.2 < 2 ^ 48 ∧
    q.coordinates.2.2 < 2 ^ 48 ∧ v < 2 ^ 48

instance (q : Query) (v : Nat) : Decidable (q.Fits v) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- Encode a query and its resolved value in the fixed table columns. -/
def Query.encode {p : Nat} (q : Query) (v : Nat) : Record (ZMod p) :=
  let (key, attr, pos) := q.coordinates
  let (tag, r, h) := key.coordinates
  ⟨tag, attr, Address.ofNat r, Address.ofNat h, Address.ofNat pos, Address.ofNat v⟩

/-- Recover the typed position from the fixed columns. -/
def Record.query? {p : Nat} (row : Record (ZMod p)) : Option Query := do
  let r := Address.toNat row.reply
  let h := Address.toNat row.hint
  let key ← match row.stream.val with
    | 1 => some StreamKey.stdout
    | 2 => some StreamKey.stderr
    | 13 => some StreamKey.publicOutput
    | 3 => some (StreamKey.request r)
    | 4 => some (StreamKey.returned r h)
    | _ => none
  match row.kind.val with
  | 0 => return .length key
  | 1 => return .byte key (Address.toNat row.offset)
  | 2 => return .descriptor r
  | 3 => return .returnCount r
  | _ => none

/-- Full recovery prevents a field or positional alias between distinct endpoint requests. -/
theorem Query.decode_encode {p : Nat} [Fact p.Prime] [Fact (2 ^ 17 < p)] (q : Query) (v : Nat) (fits : q.Fits v) :
    (q.encode (p := p) v).query? = some q ∧ Address.toNat (q.encode (p := p) v).value = v := by
  have hp : 2 ^ 17 < p := Fact.out
  have scalar (n : Nat) (small : n ≤ 13) : (n : ZMod p).val = n := ZMod.val_natCast_of_lt (by omega)
  obtain ⟨r, h, pos, val⟩ := fits
  cases q <;> try cases ‹StreamKey›
  all_goals
    simp only [Query.coordinates, StreamKey.coordinates] at r h pos
    simp only [encode, coordinates, StreamKey.coordinates, Record.query?, scalar 0 (by decide), scalar 1 (by decide), scalar 2 (by decide),
      scalar 3 (by decide), scalar 4 (by decide), scalar 13 (by decide), Address.toNat_ofNat _ r, Address.toNat_ofNat _ h, Address.toNat_ofNat _ pos,
      Address.toNat_ofNat _ val]
    simp

/-- A physically represented value has an actual, nonwrapping endpoint lookup. -/
def Record.Binds {p : Nat} (row : Record (ZMod p)) (streams : WriteStreams) : Prop :=
  ∃ q v, q ∈ queries streams ∧ q.lookup streams = some v ∧ q.Fits v ∧ row = q.encode v

/-- Look up one verifier-owned query and encode its value when all coordinates fit. -/
def fixedRow? {p : Nat} (streams : WriteStreams) (q : Query) : Option (Record (ZMod p)) := do
  let v ← q.lookup streams
  if q.Fits v then some (q.encode v) else none

private theorem fixedRow_iff {p : Nat} (streams : WriteStreams) (q : Query) (row : Record (ZMod p)) :
    fixedRow? streams q = some row ↔ ∃ v, q.lookup streams = some v ∧ q.Fits v ∧ row = q.encode v := by
  unfold fixedRow?
  cases found : q.lookup streams with
  | none => simp
  | some v => by_cases fits : q.Fits v <;> simp [fits, eq_comm]

/-- Verifier-side representability of the entire fixed inventory. A single missing lookup,
oversized scalar, or overflowing position invalidates the endpoint pair. -/
def inventoryOK (streams : WriteStreams) : Bool :=
  decide ((queries streams).length < 2 ^ 48) &&
    (queries streams).all fun q => (q.lookup streams).any fun v => decide (q.Fits v)

theorem inventoryOK_iff (streams : WriteStreams) :
    inventoryOK streams = true ↔
      (queries streams).length < 2 ^ 48 ∧ ∀ q ∈ queries streams, ∃ v, q.lookup streams = some v ∧ q.Fits v := by
  have entry (q : Query) : ((q.lookup streams).any fun v => decide (q.Fits v)) = true ↔
      ∃ v, q.lookup streams = some v ∧ q.Fits v := by
    cases found : q.lookup streams <;> simp
  simp only [inventoryOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, entry]

/-- Overlarge physical endpoint inventory fails closed as a whole. -/
def fixedRows {p : Nat} (streams : WriteStreams) : List (Record (ZMod p)) :=
  if inventoryOK streams then (queries streams).filterMap (fixedRow? streams) else []

theorem fixedRows_iff {p : Nat} (streams : WriteStreams) (row : Record (ZMod p)) :
    row ∈ fixedRows streams ↔ inventoryOK streams = true ∧ row.Binds streams := by
  unfold fixedRows Record.Binds
  by_cases bound : inventoryOK streams = true
  · simp only [bound, ite_true, true_and, List.mem_filterMap, fixedRow_iff]
    constructor
    · rintro ⟨q, member, v, found, fits, same⟩
      exact ⟨q, v, member, found, fits, same⟩
    · rintro ⟨q, v, member, found, fits, same⟩
      exact ⟨q, member, v, found, fits, same⟩
  · simp [Bool.eq_false_iff.mpr bound]

theorem fixedRows_length {p : Nat} (streams : WriteStreams) : (fixedRows (p := p) streams).length < 2 ^ 48 := by
  unfold fixedRows
  split
  · exact (List.length_filterMap_le ..).trans_lt ((inventoryOK_iff _).mp (by assumption)).1
  · norm_num

/-- All enumerated occurrences survive physical encoding on a checked endpoint pair. -/
theorem fixedRows_length_eq {p : Nat} {streams : WriteStreams} (checked : inventoryOK streams = true) :
    (fixedRows (p := p) streams).length = (queries streams).length := by
  simp only [fixedRows, checked, ite_true]
  apply Nat.le_antisymm (List.length_filterMap_le ..)
  by_contra! smaller
  obtain ⟨q, member, absent⟩ := List.length_filterMap_lt_length_iff_exists.mp smaller
  obtain ⟨v, found, fits⟩ := ((inventoryOK_iff _).mp checked).2 q member
  simp [fixedRow?, found, fits] at absent

/-- Every representable actual lookup is physically available when the fixed inventory fits. -/
theorem Query.present {p : Nat} {streams : WriteStreams} {q : Query} {v : Nat}
    (found : q.lookup streams = some v) (checked : inventoryOK streams = true) :
    q.encode (p := p) v ∈ fixedRows streams := by
  obtain ⟨actual, eq, fits⟩ := ((inventoryOK_iff _).mp checked).2 q (q.enumerated found)
  obtain rfl := Option.some.inj (found.symm.trans eq)
  exact (fixedRows_iff ..).mpr ⟨checked, q, v, q.enumerated found, found, fits, rfl⟩

/-- Every returned word-sized scalar has its exact natural meaning. -/
theorem Record.Binds.readout {p : Nat} [Fact p.Prime] [Fact (2 ^ 17 < p)] {row : Record (ZMod p)}
    {streams : WriteStreams} (binding : row.Binds streams) :
    ∃ q, q ∈ queries streams ∧ q.lookup streams = some (Address.toNat row.value) ∧
      Address.toNat row.reply = q.coordinates.1.coordinates.2.1 ∧
      Address.toNat row.hint = q.coordinates.1.coordinates.2.2 ∧
      Address.toNat row.offset = q.coordinates.2.2 ∧
      row.stream = (q.coordinates.1.coordinates.1 : ZMod p) ∧ row.kind = (q.coordinates.2.1 : ZMod p) := by
  obtain ⟨q, v, member, found, fits, rfl⟩ := binding
  obtain ⟨r, h, i, val⟩ := fits
  refine ⟨q, member, ?_, ?_, ?_, ?_, rfl, rfl⟩ <;>
    simp only [Query.encode, Address.toNat_ofNat _ r, Address.toNat_ofNat _ h,
      Address.toNat_ofNat _ i, Address.toNat_ofNat _ val, found]

/-- A consumer naming one concrete key receives its actual fixed byte or metadata value. -/
theorem Record.Binds.lookup {p : Nat} [Fact p.Prime] [Fact (2 ^ 17 < p)] {row : Record (ZMod p)}
    {streams : WriteStreams} (binding : row.Binds streams) :
    (row.query?.bind (Query.lookup streams)) = some (Address.toNat row.value) := by
  obtain ⟨q, v, _, found, fits, rfl⟩ := binding
  obtain ⟨key, value⟩ := q.decode_encode (p := p) v fits
  simpa only [key, value, Option.bind_some] using found

end SP1Clean.WriteEffects
