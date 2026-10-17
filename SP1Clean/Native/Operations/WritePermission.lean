import SP1Clean.FormalModel.Contracts.WritePermission
import SP1Clean.Native.Operations.AddressOrder
import SP1Clean.Native.Operations.InitialMemoryLookup.Witness
import ToClean.Air.StaticProvider

/-! # A native permission provider for ordinary and host memory writes

The provider authenticates an inclusive writable interval, checks the query's limbs, compares both
endpoints, and supplies one byte permission. Fixed interval membership comes from a separate
verifier-fixed provider through Clean's existing channel interface.
The deterministic constructor succeeds exactly for writable native addresses; all remaining local
cells come from Clean's exportable zero-test and bit-decomposition witness programs.
-/

namespace SP1Clean.WritePermissionProvider

open Circuit SP1Clean.Model.Core

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
/-- The complete permission inventory and its padding fit Clean's physical row index. The bound
comes from the finite address space, independently of how the ROM stores repeated entries. -/
theorem membership_height_lt_uint64 (image : ProgramImage) :
    (image.writePermissionTable (p := p)).height < UInt64.size := by
  have intervals := image.protectionMask.intervals_length_le (2 ^ 48)
  have support := image.protectionMask.supportBelow_card_le_limit (2 ^ 48)
  have filtered := List.length_filter_le
    (fun interval : MemoryInterval => decide (interval.value = 0 ∧ interval.lower < interval.upper))
    (image.protectionMask.intervals (2 ^ 48))
  have padded := (image.writePermissionTable (p := p)).height_lt_double
  have length : (image.writePermissionTable (p := p)).length = image.writableIntervals.length := by
    simp only [ProgramImage.writePermissionTable, StaticTable.ofRows, List.length_map]
  rw [length] at padded
  change image.writableIntervals.length ≤ _ at filtered
  norm_num [UInt64.size] at *
  omega

/-- Fixed writable intervals authenticate endpoint membership; only their counts are prover-owned. -/
def membershipComponent (image : ProgramImage) : Air.Flat.Component (ZMod p) :=
  image.writePermissionTable.component (membership_height_lt_uint64 image)

/-- Permission requests carry only the semantic byte address. -/
def ProverAssumptions (image : ProgramImage) (input : Inputs (ZMod p)) : Prop :=
  Spec image input

/-- Encode a writable address; interval and comparison cells are generated internally. -/
def populate? (image : ProgramImage) (address : ℕ) : Option (Inputs (ZMod p)) :=
  (image.writableIntervalAt? address).map fun _ => ⟨Address.ofNat address⟩

theorem populate?_sound (image : ProgramImage) (address : ℕ) (input : Inputs (ZMod p))
    (found : populate? image address = some input) :
    ProverAssumptions image input ∧ Address.toNat input.address = address := by
  obtain ⟨interval, selected, rfl⟩ := Option.map_eq_some_iff.mp found
  obtain ⟨member, contains⟩ := image.writableIntervalAt?_sound address interval selected
  have permitted := (image.writableIntervals_sound interval member).2.2 address contains
  have encoded := Address.toNat_ofNat (p := p) address permitted.1
  exact ⟨⟨Address.bounded_ofNat _, by rw [encoded]; exact permitted⟩, encoded⟩

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
theorem populate?_isSome_iff (image : ProgramImage) (address : ℕ) :
    (populate? (p := p) image address).isSome = true ↔
      address < 2 ^ 48 ∧ image.readOnly address = false := by
  simpa only [populate?, Option.isSome_map] using image.writableIntervalAt?_isSome_iff address

/-- Reuse the memory selector's field expressions for both inclusive permission endpoints. -/
def intervalFE (image : ProgramImage) (address : fields 3 (Witgen.FExpr (ZMod p))) :
    WritePermissionInterval (Witgen.FExpr (ZMod p)) :=
  ⟨Vector.ofFn fun i => InitialMemoryLookup.selectFE (Address.asWord address)
      (fun interval => (WritePermissionInterval.encode (p := p) interval).lower[i]) image.writableIntervals,
    Vector.ofFn fun i => InitialMemoryLookup.selectFE (Address.asWord address)
      (fun interval => (WritePermissionInterval.encode (p := p) interval).upper[i]) image.writableIntervals⟩

/-- The exported selector chooses the same interval as the semantic permission search. -/
theorem intervalFE_eval (ctx : Witgen.Ctx (ZMod p)) (image : ProgramImage)
    (address : fields 3 (Witgen.FExpr (ZMod p))) (value : fields 3 (ZMod p))
    (evaluates : ∀ (i : ℕ) (_ : i < 3), address[i].eval ctx = value[i])
    (bounded : Address.Bounded value) (interval : MemoryInterval)
    (found : image.writableIntervalAt? (Address.toNat value) = some interval) :
    Witgen.eval ctx (intervalFE image address) = WritePermissionInterval.encode interval := by
  have bounds (row : MemoryInterval) (member : row ∈ image.writableIntervals) :
      row.lower < 2 ^ 64 ∧ row.upper < 2 ^ 64 := by
    have endpoints := image.writableIntervals_sound row member
    constructor <;> omega
  have inputEval (i : ℕ) (hi : i < 4) :
      (Address.asWord address)[i].eval ctx = (Address.asWord value)[i] := by
    interval_cases i <;> simp only [Address.asWord, circuit_norm, evaluates]
  have fieldEval (field : MemoryInterval → ZMod p) :
      (InitialMemoryLookup.selectFE (Address.asWord address) field image.writableIntervals).eval ctx =
        field interval := by
    rw [InitialMemoryLookup.selectFE_eval ctx _ _ inputEval (Address.isU64_asWord bounded)
      field _ bounds, Address.toNat_asWord]
    change ((image.writableIntervalAt? (Address.toNat value)).map field).getD 0 = _
    rw [found]
    rfl
  rw [Witgen.StructEval.eval_eq_eval]
  simp only [intervalFE, circuit_norm, ProvableStruct.toComponents,
    ProvableStruct.fromComponents, Witgen.eval_fields', Vector.map_ofFn]
  congr 1 <;> ext i hi <;>
    simpa only [Vector.getElem_ofFn, Function.comp_apply, WritePermissionInterval.encode] using fieldEval _

def main (image : ProgramImage) (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  let interval ← witness (var := Var WritePermissionInterval)
    (intervalFE image (input.address.map Witgen.FExpr.expr))
  image.writePermissionTable.channel.pull ⟨interval, 1⟩
  assertion (Gadgets.ToBits.rangeCheck 16 (by have := Fact.out (p := 2 ^ 17 < p); omega)) input.address[0]
  assertion (Gadgets.ToBits.rangeCheck 16 (by have := Fact.out (p := 2 ^ 17 < p); omega)) input.address[1]
  assertion (Gadgets.ToBits.rangeCheck 16 (by have := Fact.out (p := 2 ^ 17 < p); omega)) input.address[2]
  assertion AddressOrder.circuit ⟨interval.lower, input.address⟩
  assertion AddressOrder.circuit ⟨input.address, interval.upper⟩
  channel.push input.address

instance elaborated (image : ProgramImage) :
    ElaboratedCircuit (ZMod p) Inputs unit (main image) := by elaborate_circuit

def circuit (image : ProgramImage) : GeneralFormalCircuit (ZMod p) Inputs unit where
  name := "sp1.native.write_permission"
  main := main image
  elaborated := elaborated image
  channelsWithRequirements := [channel.toRaw]
  Spec input _ _ := Spec image input
  ProverAssumptions input _ _ := ProverAssumptions image input
  soundness := by
    circuit_proof_start [Gadgets.ToBits.rangeCheck, AddressOrder.circuit, StaticTable.channel]
    subst input_address
    obtain ⟨member, low, middle, high, lower, upper⟩ := h_holds
    have bounded : Address.Bounded (input_var_address.map (Expression.eval env)) := by
      intro index
      fin_cases index
      · simpa using low
      · simpa using middle
      · simpa using high
    have ranges := image.writePermissionTable_sound _ member
    have permitted : Permitted image (input_var_address.map (Expression.eval env)) :=
      ⟨bounded, ranges.2.2 _ (lower ⟨ranges.1, bounded⟩) (upper ⟨bounded, ranges.2.1⟩)⟩
    exact ⟨permitted, fun _ _ => True.intro⟩
  completeness := by
    circuit_proof_start [Gadgets.ToBits.rangeCheck, AddressOrder.circuit, ProverAssumptions,
      StaticTable.channel]
    have inputEval (i : ℕ) (hi : i < 3) :
        (input_var_address.map Witgen.FExpr.expr)[i].eval { env := env } = input_address[i] := by
      simpa only [Vector.getElem_map, Witgen.FExpr.eval] using
        congrArg (fun address : fields 3 (ZMod p) => address[i]) h_input
    obtain ⟨interval, found⟩ := Option.isSome_iff_exists.mp
      ((image.writableIntervalAt?_isSome_iff (Address.toNat input_address)).mpr h_assumptions.2)
    have selected := h_env.trans
      (intervalFE_eval { env := env } image _ input_address inputEval h_assumptions.1 interval found)
    have lowerEq := congrArg WritePermissionInterval.lower selected
    have upperEq := congrArg WritePermissionInterval.upper selected
    dsimp only at lowerEq upperEq
    rw [selected, lowerEq, upperEq]
    have addressEval (i : ℕ) (hi : i < 3) :
        Expression.eval env.toEnvironment input_var_address[i] = input_address[i] := by
      simpa only [Vector.getElem_map] using
        congrArg (fun address : fields 3 (ZMod p) => address[i]) h_input
    simp only [addressEval]
    have selection := image.writableIntervalAt?_sound _ interval found
    have endpoints := image.writableIntervals_sound interval selection.1
    have member := (image.writePermissionTable_spec (WritePermissionInterval.encode (p := p) interval)).mpr
      ⟨interval, selection.1, rfl⟩
    have ranges := image.writePermissionTable_sound _ member
    have lower : Address.toNat (WritePermissionInterval.encode (p := p) interval).lower ≤
        Address.toNat input_address := by
      rw [WritePermissionInterval.encode, Address.toNat_ofNat _ (by omega)]
      exact selection.2.1
    have upper : Address.toNat input_address ≤
        Address.toNat (WritePermissionInterval.encode (p := p) interval).upper := by
      rw [WritePermissionInterval.encode, Address.toNat_ofNat _ (by omega)]
      have := selection.2.2
      omega
    exact ⟨member, by simpa using h_assumptions.1 0, by simpa using h_assumptions.1 1,
      by simpa using h_assumptions.1 2, ⟨⟨ranges.1, h_assumptions.1⟩, lower⟩,
      ⟨h_assumptions.1, ranges.2.1⟩, upper⟩

end SP1Clean.WritePermissionProvider
