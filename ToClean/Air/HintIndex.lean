module

public import Clean.Air.WitnessGeneration.Generation
public import Clean.Circuit.WitnessIRSugar

/-! # Sparse private-input indexing through the existing witness IR

Clean exposes indexed hint reads but no keyed hint lookup. This authoring helper encodes a
private inventory keyed by fixed-length UInt64 tuples as a radix-256 index,
using eight levels per key component. Its reads are ordinary
`hintGet` expressions; Clean still owns evaluation, lowering and scheduling. Row zero and page
zero are absent sentinels. A caller must check the complete returned payload before accepting
it: hints are untrusted, and the index is not an authenticated map.

The encoder rejects duplicate keys and pointers that do not fit the field. This is a runtime
input-format check, not an additional premise of any circuit soundness theorem. Replace this
helper when upstream offers a keyed private-input view.
-/

@[expose] public section

namespace Witgen.HintIndex

variable {F : Type} [FiniteField F]

/-- Eight byte-wise page reads per key component. Missing paths stay in page zero. -/
def rowKeys (name : String) (keys : List (U64Expr F)) : U64Expr F :=
  keys.foldl (fun page key =>
    (List.range 8).foldl (fun page digit =>
      (.hintGet (name ++ ".index") 1
        (page * 256 + (key / .const (UInt64.ofNat (256 ^ (7 - digit)))) % 256) 0
        : FExpr F).val) page) 1

/-- A single-key inventory uses the same encoding as a one-element tuple. -/
def row (name : String) (key : U64Expr F) : U64Expr F := rowKeys name [key]

/-- The typed private input selected by the complete key tuple. -/
def inputKeys {Input : TypeMap} [ProvableType Input] (name : String) (keys : List (U64Expr F)) :
    Input (FExpr F) :=
  fromElements (Vector.ofFn fun column : Fin (size Input) =>
    .hintGet name (size Input) (rowKeys name keys) column)

/-- The typed private input selected by a UInt64 key. -/
def input {Input : TypeMap} [ProvableType Input] (name : String) (key : U64Expr F) :
    Input (FExpr F) := inputKeys name [key]

/-- Compare all cells, rather than trusting the private index or a partial key. -/
def messageEq {Message : TypeMap} [ProvableType Message]
    (candidate : Message (FExpr F)) (message : Var Message F) : BExpr F :=
  ((toElements candidate).toList.zip (toElements (M := Message) message).toList).foldr
    (fun (left, right) rest => .and (.feq left (.expr right)) rest) .true

/-- A typed, unit-demand route backed by private indexed inputs. Exact payload equality
prevents an absent, malformed or misrouted private entry from answering another request. -/
def unitDemandKeys {Input Message : TypeMap} [ProvableType Input] [ProvableType Message]
    (name : String) (channel : Channel F Message) (trigger : Channel.Direction)
    (keys : Var Message F → List (U64Expr F))
    (payload : Input (FExpr F) → Message (FExpr F))
    (activity : Input (FExpr F) → FExpr F) (padding : Input F := 0) :
    Air.Flat.WitnessGeneration.Generation F Input :=
  .demand {
    channel
    trigger
    guard message :=
      let candidate := inputKeys (Input := Input) name (keys message)
      .and (.feq (activity candidate) 1) (messageEq (payload candidate) message)
    input message := pure (fromElements ((toElements (inputKeys (Input := Input) name (keys message))).map
      Air.Flat.WitnessGeneration.Cell.witness))
    padding
  }

/-- Single-key demand is the one-component specialization of tuple-indexed demand. -/
def unitDemand {Input Message : TypeMap} [ProvableType Input] [ProvableType Message]
    (name : String) (channel : Channel F Message) (trigger : Channel.Direction)
    (key : Var Message F → U64Expr F)
    (payload : Input (FExpr F) → Message (FExpr F))
    (activity : Input (FExpr F) → FExpr F) (padding : Input F := 0) :
    Air.Flat.WitnessGeneration.Generation F Input :=
  unitDemandKeys name channel trigger (fun message => [key message]) payload activity padding

/-- Encoded index and values, including their absent sentinels. -/
structure Prepared (Input : TypeMap) [ProvableType Input] (F : Type) where
  /-- Sparse byte-page index; page zero represents a missing key. -/
  index : Array (Vector F 1)
  /-- Typed input rows; row zero is the absent-input sentinel. -/
  inputs : Array (Vector F (size Input))

/-- Build a sparse index for nonempty, equally sized key tuples. The row order follows the
supplied inventory; mixed widths are rejected so one key cannot alias another's prefix. -/
def prepareKeys {Input : TypeMap} [ProvableType Input]
    (entries : List (List UInt64 × Input F)) : Except String (Prepared Input F) := do
  let keyWidth := (entries.head?.map fun entry => entry.1.length).getD 1
  unless keyWidth > 0 do throw "empty private-input key"
  let mut pointers : Array Nat := Array.replicate 512 0
  let mut inputs : Array (Vector F (size Input)) := #[Vector.replicate (size Input) 0]
  for (keys, value) in entries do
    unless keys.length == keyWidth do throw "inconsistent private-input key width"
    let digits := (keys.flatMap fun key =>
      (List.range 8).map fun digit => key.toNat / 256 ^ (7 - digit) % 256).toArray
    let mut page := 1
    for digit in [:digits.size] do
      let slot := page * 256 + digits[digit]!
      let found := pointers[slot]?.getD 0
      if digit + 1 == digits.size then
        unless found == 0 do throw "duplicate private-input key"
        pointers := pointers.set! slot inputs.size
        inputs := inputs.push (toElements value)
      else if found == 0 then
        let next := pointers.size / 256
        pointers := (pointers.set! slot next) ++ Array.replicate 256 0
        page := next
      else
        page := found
  unless pointers.all (· < FiniteField.size F) do
    throw "private-input index exceeds field pointer capacity"
  unless pointers.size ≤ UInt64.size do
    throw "private-input index exceeds UInt64 addressing capacity"
  pure {
    index := pointers.map fun pointer => #v[FiniteField.fromNat pointer]
    inputs
  }

/-- Encode the single-key inventory used by `row` and `input`. -/
def prepare {Input : TypeMap} [ProvableType Input]
    (entries : List (UInt64 × Input F)) : Except String (Prepared Input F) :=
  prepareKeys (entries.map fun (key, value) => ([key], value))

end Witgen.HintIndex
