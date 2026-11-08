import SP1Clean.Proofs.Chips.MemoryFinalizeChip
import SP1Clean.Model.SP1Field
import Clean.Air.WitnessGeneration

/-! Final-memory routing uses addresses, so simultaneous host RAM writes remain distinct. -/
namespace SP1CleanTest.Core.MemoryDemand

open SP1Clean Air.Flat.WitnessGeneration
abbrev Fp := ZMod SP1Prime

def first : MemoryFinalizeChip.Inputs Fp :=
  ⟨3, 17, 12288, 0, 4096, #v[1, 2, 3, 4], 1⟩
def second : MemoryFinalizeChip.Inputs Fp :=
  ⟨3, 17, 12288, 0, 8192, #v[5, 6, 7, 8], 1⟩

def accepts (record : Channels.MemoryMsg Fp) : Except String Bool := do
  let prepared ← Witgen.HintIndex.prepare (Input := MemoryFinalizeChip.Inputs)
    [(17592186056704, first), (35184372101120, second)]
  let name := (MemoryFinalizeChip.circuit (p := SP1Prime)).name
  let hint : ProverHint Fp := readNamedRows [
    (name ++ ".index", .ofRows (prepared.index.map (·.toArray)) 1),
    (name, .ofRows (prepared.inputs.map (·.toArray)) (size MemoryFinalizeChip.Inputs))]
  match MemoryFinalizeChip.generation (p := SP1Prime) with
  | .demand mode => pure (mode.accepts
      ⟨(Channels.memoryChannel (p := SP1Prime)).name, (toElements record).toArray, 1⟩ (.empty Fp) hint)
  | .preallocated _ => throw "finalization must preserve unit occurrences"

example : accepts first.toMessage = .ok true := by native_decide
example : accepts second.toMessage = .ok true := by native_decide
example : accepts { first.toMessage with clk_low := 18 } = .ok false := by native_decide
example : accepts { first.toMessage with value := #v[1, 2, 3, 5] } = .ok false := by native_decide
example : accepts { first.toMessage with addr2 := 12288 } = .ok false := by native_decide

end SP1CleanTest.Core.MemoryDemand
