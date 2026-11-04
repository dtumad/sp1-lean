import ToClean.Air.HintIndex
import SP1Clean.Proofs.Chips.HintReadWordChip.Populate
import SP1Clean.Model.SP1Field
import SP1Clean.Proofs.Chips.HaltChip.Formal
import Clean.Air.WitnessGeneration

/-! Private-index regressions: high keys, zero keys, missing keys, and duplicate rejection. -/

namespace SP1CleanTest.Core.HintIndex

open Air.Flat.WitnessGeneration
abbrev Fp := ZMod SP1Clean.SP1Prime

def entries : List (UInt64 × Vector Fp 2) :=
  [(0, #v[7, 11]), (1, #v[13, 17]), (256, #v[19, 23]),
   (281474976710655, #v[29, 31]), (18446744073709551615, #v[37, 41])]

def check : Except String Bool := do
  let prepared ← Witgen.HintIndex.prepare (Input := fields 2) entries
  let hint : ProverHint Fp := readNamedRows [
    ("values.index", .ofRows (prepared.index.map (·.toArray)) 1),
    ("values", .ofRows (prepared.inputs.map (·.toArray)) 2)]
  let read (key : UInt64) :=
    let input := Witgen.HintIndex.input (Input := fields 2) "values" (.const key)
    input.map fun expression => expression.eval { env := { get _ := 0, data := .empty Fp, hint } }
  pure ((entries.all fun (key, value) => read key == value) &&
    [2, 255, 257, 281474976710654].all (fun key => read key == #v[0, 0]))

example : check = .ok true := by native_decide
example : (Witgen.HintIndex.prepare (F := Fp) (Input := fields 2)
    [(0, #v[1, 2]), (0, #v[3, 4])]).isOk = false := by native_decide

/-- Equal clocks with different word indices and equal indices at different clocks stay distinct. -/
def checkTuples : Except String Bool := do
  let entries : List (List UInt64 × Vector Fp 2) :=
    [([16777217, 0], #v[7, 11]), ([16777217, 281474976710655], #v[13, 17]),
     ([281474976710655, 0], #v[19, 23]), ([18446744073709551615, 18446744073709551615], #v[29, 31])]
  let prepared ← Witgen.HintIndex.prepareKeys (Input := fields 2) entries
  let hint : ProverHint Fp := readNamedRows [
    ("pairs.index", .ofRows (prepared.index.map (·.toArray)) 1),
    ("pairs", .ofRows (prepared.inputs.map (·.toArray)) 2)]
  let read (keys : List UInt64) :=
    let input := Witgen.HintIndex.inputKeys (Input := fields 2) "pairs" (keys.map .const)
    input.map fun expression => expression.eval { env := { get _ := 0, data := .empty Fp, hint } }
  pure ((entries.all fun (keys, value) => read keys == value) &&
    [[0, 0], [16777217, 1], [281474976710655, 281474976710655]].all
      (fun keys => read keys == #v[0, 0]))

example : checkTuples = .ok true := by native_decide
example : (Witgen.HintIndex.prepareKeys (F := Fp) (Input := fields 2)
    [([], #v[1, 2])]).isOk = false := by native_decide
example : (Witgen.HintIndex.prepareKeys (F := Fp) (Input := fields 2)
    [([1], #v[1, 2]), ([1, 2], #v[3, 4])]).isOk = false := by native_decide
example : (Witgen.HintIndex.prepareKeys (F := Fp) (Input := fields 2)
    [([1, 2], #v[1, 2]), ([1, 2], #v[3, 4])]).isOk = false := by native_decide

open SP1Clean in
private def wordInput (high : Fp) (index : ℕ) : HintReadWordChip.RowInput Fp :=
  let ram := HostRamAccessChip.populate ⟨0, 0, 0, 1, 0, #v[0, 0, 0, 0]⟩
    high 17 0 #v[7, 11, 13, 17]
  HintReadWordChip.populate false ram #v[8, 1, 0] (Address.ofNat index)

open SP1Clean in
private def acceptsWord (state : HintReadWordChip.State Fp) : Except String Bool := do
  let prepared ← Witgen.HintIndex.prepareKeys (Input := HintReadWordChip.RowInput)
    [([16777233, 0], wordInput 1 0), ([16777233, 4294967296], wordInput 1 (2 ^ 32)),
      ([33554449, 0], wordInput 2 0)]
  let name := (HintReadWordChip.circuit (p := SP1Prime) false).name
  let hint : ProverHint Fp := readNamedRows [
    (name ++ ".index", .ofRows (prepared.index.map (·.toArray)) 1),
    (name, .ofRows (prepared.inputs.map (·.toArray)) (size HintReadWordChip.RowInput))]
  match HintReadWordChip.generation (p := SP1Prime) false with
  | .demand mode => pure (mode.accepts
      ⟨(HintReadWordChip.stateChannel (p := SP1Prime)).name, (toElements state).toArray, 1⟩ (.empty Fp) hint)
  | .preallocated _ => throw "word transfers must preserve unit occurrences"

example : acceptsWord (wordInput 1 0).1.previous = .ok true := by native_decide
example : acceptsWord (wordInput 1 (2 ^ 32)).1.previous = .ok true := by native_decide
example : acceptsWord (wordInput 2 0).1.previous = .ok true := by native_decide
example : acceptsWord (wordInput 1 1).1.previous = .ok false := by native_decide
example : acceptsWord { (wordInput 1 0).1.previous with pointer := #v[9, 1, 0] } = .ok false := by native_decide
example : acceptsWord { (wordInput 1 0).1.previous with address := #v[8, 1, 0] } = .ok false := by native_decide

open SP1Clean in
private def acceptsHaltPadding (present : Bool) (code : Fp) : Except String Bool := do
  let prepared ← Witgen.HintIndex.prepare (Input := HaltChip.Inputs)
    (if present then [(0, (0 : HaltChip.Inputs Fp))] else [])
  let name := (HaltChip.circuit (p := SP1Prime)).name
  let hint : ProverHint Fp := readNamedRows [
    (name ++ ".index", .ofRows (prepared.index.map (·.toArray)) 1),
    (name, .ofRows (prepared.inputs.map (·.toArray)) (size HaltChip.Inputs))]
  match HaltChip.generation (p := SP1Prime) with
  | .demand mode => pure (mode.accepts ⟨(Channels.exitChannel (p := SP1Prime)).name, #[code], -1⟩ (.empty Fp) hint)
  | .preallocated _ => throw "legacy HALT must be optional"

/-- Absent hints must not create an extra Exit; an explicitly supplied zero row still can. -/
example : acceptsHaltPadding false 0 = .ok false ∧
    acceptsHaltPadding true 0 = .ok true ∧ acceptsHaltPadding true 1 = .ok false := by
  native_decide

end SP1CleanTest.Core.HintIndex
