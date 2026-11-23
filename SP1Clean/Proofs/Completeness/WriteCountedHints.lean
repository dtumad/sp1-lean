import SP1Clean.Proofs.Completeness.WriteCountedRouting
import SP1Clean.Math.SP1Field
import Clean.Air.WitnessGeneration.PreparedRows
import Std.Data.HashMap.Basic

/-! # Private inputs for the registered WRITE demand generators

Emit the exact named index/input tables read by Clean's two demand generators. Equal
queries share a hint entry and remain distinct charged physical requests. Conflicting
rows at the same key fail before preparing the lookup trie.
-/

namespace SP1Clean.WriteProbe.Counted
open Circuit Air.Flat Air.Flat.WitnessGeneration

private abbrev F := ZMod SP1Prime

private def prepareDistinct {n : ℕ} (entries : List (List UInt64 × Vector F n)) :
    Except String (Witgen.HintIndex.Prepared (fields n) F) := do
  let mut seen : Std.HashMap (List UInt64) (Vector F n) := {}
  let mut unique := #[]
  for (key, value) in entries do
    match seen.get? key with
    | some previous => unless previous = value do throw "conflicting WRITE inputs at the same private index key"
    | none =>
      seen := seen.insert key value
      unique := unique.push (key, value)
  Witgen.HintIndex.prepareKeys (Input := fields n) unique.toList

/-- Build both named hint pairs from the exact rows proved to balance. The source tuple
includes all eleven original Memory fields. The probe index uses absolute clock and byte
address in the same order as the installed read demand. -/
def prepareHints (records : List (Readback F)) (requests : List (Request records.length F)) :
    Except String (List (String × PreparedRows F)) := do
  let supply := allocated records requests
  let counts ← prepareDistinct (supply.map fun r =>
    ((toElements r.receipt).toList.map (fun x => UInt64.ofNat x.val), #v[r.count]))
  let readEntries ← (probes records requests).mapM fun input => do
    let read := input.read
    let clock := Address.toNat read.clock
    let key := Address.toNat read.key
    unless clock < UInt64.size ∧ key < UInt64.size do throw "WRITE probe private index exceeds UInt64"
    return ([UInt64.ofNat clock, UInt64.ofNat key], toElements (M := RowInput) (input, 1))
  let reads ← prepareDistinct readEntries
  let countName := "sp1.native.write_readback_counts"
  let probeName := (guarded (p := SP1Prime)).name
  return [(countName ++ ".index", .ofRows (counts.index.map (·.toArray)) 1),
    (countName, .ofRows (counts.inputs.map (·.toArray)) 1),
    (probeName ++ ".index", .ofRows (reads.index.map (·.toArray)) 1),
    (probeName, .ofRows (reads.inputs.map (·.toArray)) (size RowInput))]

end SP1Clean.WriteProbe.Counted
