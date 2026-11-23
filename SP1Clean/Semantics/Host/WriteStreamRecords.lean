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

def StreamKey.contents (streams : WriteStreams) : StreamKey → Option Bytes
  | .stdout => some streams.stdout
  | .stderr => some streams.stderr
  | .publicOutput => some streams.publicOutput
  | .request r => (streams.hooks[r]?).map (·.request.input)
  | .returned r h => (streams.hooks[r]?).bind (·.hints[h]?)

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

def byteQueries (key : StreamKey) (bytes : Bytes) : List Query :=
  .length key :: (List.range bytes.length).map (.byte key)

/-- Enumerate only actual owned positions, retaining metadata and empty strings. -/
def queries (streams : WriteStreams) : List Query :=
  byteQueries .stdout streams.stdout ++ byteQueries .stderr streams.stderr ++
    byteQueries .publicOutput streams.publicOutput ++
    (streams.hooks.zipIdx.flatMap fun (reply, r) =>
      [.descriptor r, .returnCount r] ++ byteQueries (.request r) reply.request.input ++
        (reply.hints.zipIdx.flatMap fun (bytes, h) => byteQueries (.returned r h) bytes))

/-- Field key plus a canonical 48-bit payload. The stream tags are 1/2/13 for the three output
streams, 3 for hook input and 4 for a returned hint. Attributes are length, byte, descriptor
or returned-hint count (0 through 3). -/
structure Record (F : Type) where
  stream : F
  kind : F
  reply : fields 3 F
  hint : fields 3 F
  offset : fields 3 F
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

def fixedRow? {p : Nat} (streams : WriteStreams) (q : Query) : Option (Record (ZMod p)) := do
  let v ← q.lookup streams
  if q.Fits v then some (q.encode v) else none

private theorem fixedRow_iff {p : Nat} (streams : WriteStreams) (q : Query) (row : Record (ZMod p)) :
    fixedRow? streams q = some row ↔ ∃ v, q.lookup streams = some v ∧ q.Fits v ∧ row = q.encode v := by
  unfold fixedRow?
  cases found : q.lookup streams with
  | none => simp
  | some v => by_cases fits : q.Fits v <;> simp [fits, eq_comm]

/-- Overlarge physical endpoint inventory fails closed as a whole. -/
def fixedRows {p : Nat} (streams : WriteStreams) : List (Record (ZMod p)) :=
  if (queries streams).length < 2 ^ 48 then (queries streams).filterMap (fixedRow? streams) else []

theorem fixedRows_iff {p : Nat} (streams : WriteStreams) (row : Record (ZMod p)) :
    row ∈ fixedRows streams ↔ (queries streams).length < 2 ^ 48 ∧ row.Binds streams := by
  unfold fixedRows Record.Binds
  by_cases bound : (queries streams).length < 2 ^ 48
  · simp only [bound, ite_true, true_and, List.mem_filterMap, fixedRow_iff]
    constructor
    · rintro ⟨q, member, v, found, fits, same⟩
      exact ⟨q, v, member, found, fits, same⟩
    · rintro ⟨q, v, member, found, fits, same⟩
      exact ⟨q, member, v, found, fits, same⟩
  · simp only [bound, ite_false, List.not_mem_nil, false_and]

theorem fixedRows_length {p : Nat} (streams : WriteStreams) : (fixedRows (p := p) streams).length < 2 ^ 48 := by
  unfold fixedRows
  split
  · exact (List.length_filterMap_le ..).trans_lt (by assumption)
  · norm_num

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
