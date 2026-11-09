import SP1Clean.Proofs.Chips.LoadByteStaticChip.Formal
import SP1Clean.Proofs.Chips.LoadByteChip.Formal
import SP1Clean.Native.Operations.AddressOperation
import Clean.Circuit.Theorems
import Clean.Circuit.Subcircuit
import ToClean.Air.TableBuild

/-! # The unchanged executable witness of the fixed-byte LoadByte alternative -/

namespace SP1Clean.LoadByteStaticChip

open Circuit
open LoadByteChip (Inputs Columns)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The replacement allocates no cells and preserves every input and generated witness cell. -/
theorem witgen_eq_original (input : Var Inputs (ZMod p)) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) (init : Array (ZMod p)) :
    (main input).witgenWithData data hint init =
      (LoadByteChip.main input).witgenWithData data hint init := by
  simp only [Circuit.witgenWithData, main, LoadByteChip.main, circuit_norm,
    FlatOperation.witgen, List.foldl_append, List.foldl_cons,
    FlatOperation.witgenStep]

/-- The alternative component is separate from the unchanged production registry. -/
def component : Air.Flat.Component (ZMod p) := { circuit := circuit, Assumptions := (circuit).Assumptions, generation := LoadByteChip.generation }

/-- Every built cell is unchanged, for arbitrary inputs (including inactive rows). -/
theorem buildRow_eq_original (input : Inputs (ZMod p)) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) :
    component.buildRow input data hint =
      Air.Flat.Component.buildRow { circuit := LoadByteChip.circuit, Assumptions := (LoadByteChip.circuit).Assumptions, generation := LoadByteChip.generation } input data hint :=
  witgen_eq_original _ _ _ _

end SP1Clean.LoadByteStaticChip
