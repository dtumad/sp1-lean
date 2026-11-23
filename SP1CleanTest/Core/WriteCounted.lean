import SP1Clean.Proofs.Completeness.WriteCountedHints
import Clean.Air.WitnessGeneration

/-! # Counted WRITE demand regressions

Exercise the registered read and supply generators against their real prepared hint tables.
The same read is requested twice and two disjoint intervals share an address.
-/

namespace SP1CleanTest.Core.WriteCounted

open Circuit Air.Flat Air.Flat.WitnessGeneration SP1Clean SP1Clean.WriteProbe

private abbrev F := ZMod SP1Prime

private def record (key lo hi value : ℕ) : Readback F :=
  ⟨Address.ofNat key, 0, lo, 0, hi, #v[(value : F), 0, 0, 0]⟩

private def read (key clock value : ℕ) : Read F :=
  ⟨Address.ofNat key, Address.ofNat clock, #v[(value : F), 0, 0, 0]⟩

private def records : List (Readback F) := [record 12 0 20 7, record 12 21 40 9, record 65536 1 50 3]

private def reads : List (Read F) := [read 12 1 7, read 12 21 9, read 12 1 7, read 65536 40 3, read 12 18 7]

private def generates {Input : TypeMap} [ProvableType Input] (generation : Generation F Input) (demand : Demand F)
    (hint : ProverHint F) (expected : Input F) : Bool :=
  match generation with
  | .demand mode =>
    let env := ProverEnvironment.fromArray demand.message (.empty F) hint
    mode.accepts demand (.empty F) hint &&
      evalInput (mode.input (varFromOffset mode.Message 0)) env 0 demand.count == (toElements expected).toArray
  | .preallocated _ => false

private def check : Except String Bool := do
  let some requests := Counted.route? records reads | throw "missing positive fixture read"
  let supply := Counted.allocated records requests
  let inputs := Counted.probes records requests
  let hint := readNamedRows (← Counted.prepareHints records requests)
  let allSupply := supply.all fun r => generates ReadbackSupply.generation
    ⟨(readbackChannel (p := SP1Prime)).name, (toElements r.receipt).toArray, 1⟩ hint r
  let allReads := inputs.all fun r => generates WriteProbe.generation
    ⟨(readChannel (p := SP1Prime)).name, (toElements r.read).toArray, -1⟩ hint (r, 1)
  return (supply.map (·.count.val) == [3, 1, 1]) && inputs.map Inputs.read == reads &&
    (Counted.physical supply).length == 4 && (physicalInputs inputs).length == 8 && allSupply && allReads

example : check = .ok true := by native_decide

example : (Counted.route? records [read 12 21 7]).isNone = true := by decide +kernel
example : (Counted.route? records [read 65536 51 3]).isNone = true := by decide +kernel

end SP1CleanTest.Core.WriteCounted
