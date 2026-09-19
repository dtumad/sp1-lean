import SP1Clean.FormalModel.Contracts.InitialMemory
import SP1Clean.Native.Operations.WordRangeCheck
import SP1Clean.Proofs.Operations.LtOperationUnsigned.Formal

/-! # A Clean-native lookup of canonical initial-memory bytes

The circuit looks up the complete fixed interval row, range-checks the query address, and composes
two unsigned comparisons to establish containment. Its result is the byte-read contract, not an
assumption about a memory provider. Comparison columns are explicit input columns, constructed by
the native `populate` function below; the fixed rows come only from the supplied sparse image.
-/

namespace SP1Clean.InitialMemoryLookup

open Circuit SP1Clean.Model.Core SP1Clean.Soundness.Target

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Row-generation conditions. The constructor derives them from an in-range semantic address. -/
def ProverAssumptions (memory : ByteMemory) (limit : ℕ) (input : Inputs (ZMod p)) : Prop :=
  Word.isU64 input.address ∧ (memory.fixedTable limit).Spec input.interval ∧
    Word.toNat input.interval.lower ≤ Word.toNat input.address ∧
    Word.toNat input.address < Word.toNat input.interval.upper ∧
    input.lowerCompare = LtOperationUnsigned.populate input.address input.interval.lower ∧
    input.upperCompare = LtOperationUnsigned.populate input.address input.interval.upper

/-- Honest row-generation conditions imply the same semantic byte-read contract. -/
theorem ProverAssumptions.spec (memory : ByteMemory) (limit : ℕ) (limitBound : limit < 2 ^ 64)
    (input : Inputs (ZMod p)) (valid : ProverAssumptions memory limit input) :
    Spec memory limit input :=
  ⟨valid.1, memory.fixedTable_read limit limitBound input.interval valid.2.1 _
    ⟨valid.2.2.1, valid.2.2.2.1⟩⟩

/-- Construct every comparison column from a semantic address and its selected fixed interval. -/
def populate (address : ℕ) (interval : MemoryInterval) : Inputs (ZMod p) :=
  let addressWord := bitVecToWord (BitVec.ofNat 64 address)
  let row := interval.encode
  ⟨addressWord, row, LtOperationUnsigned.populate addressWord row.lower,
    LtOperationUnsigned.populate addressWord row.upper⟩

/-- Select and construct a lookup row, with no proof arguments or supplied comparison hints. -/
def populate? (memory : ByteMemory) (limit address : ℕ) : Option (Inputs (ZMod p)) :=
  (memory.intervalAt? limit address).map (populate address)

theorem populate_assumptions (memory : ByteMemory) (limit address : ℕ)
    (limitBound : limit < 2 ^ 64) (interval : MemoryInterval)
    (member : interval ∈ memory.intervals limit) (inside : interval.Contains address) :
    ProverAssumptions memory limit (populate (p := p) address interval) := by
  have bounds := memory.intervals_bounds limit interval member
  have endpoints := interval.encode_endpoints (p := p) (by omega) (by omega)
  have addressEq := endpoint_toNat (p := p) address (by have := inside.2; omega)
  refine ⟨isU64_bitVecToWord _, (memory.fixedTable_spec limit _).mpr ⟨interval, member, rfl⟩,
    ?_, ?_, rfl, rfl⟩
  · change Word.toNat (interval.encode (p := p)).lower ≤
      Word.toNat (bitVecToWord (p := p) (BitVec.ofNat 64 address))
    rw [endpoints.1, addressEq]
    exact inside.1
  · change Word.toNat (bitVecToWord (p := p) (BitVec.ofNat 64 address)) <
      Word.toNat (interval.encode (p := p)).upper
    rw [addressEq, endpoints.2]
    exact inside.2

/-- Successful construction supplies every circuit-generation condition and preserves the query. -/
theorem populate?_sound (memory : ByteMemory) (limit address : ℕ) (limitBound : limit < 2 ^ 64)
    (input : Inputs (ZMod p)) (found : populate? memory limit address = some input) :
    ProverAssumptions memory limit input ∧ Word.toNat input.address = address := by
  obtain ⟨interval, selected, rfl⟩ := Option.map_eq_some_iff.mp found
  have selection := memory.intervalAt?_sound limit address interval selected
  exact ⟨populate_assumptions memory limit address limitBound interval selection.1 selection.2.1,
    endpoint_toNat _ (lt_trans selection.2.2.1 limitBound)⟩

omit [Fact (2 ^ 17 < p)] in
/-- Construction succeeds on exactly the semantic address window. -/
theorem populate?_isSome_iff (memory : ByteMemory) (limit address : ℕ) :
    (populate? (p := p) memory limit address).isSome = true ↔ address < limit := by
  simpa only [populate?, Option.isSome_map] using memory.intervalAt?_isSome_iff limit address

private theorem compare_lower {address lower : Word (ZMod p)}
    {cols : Extracted.LtOperationUnsigned (ZMod p)}
    (addressBound : Word.isU64 address) (lowerBound : Word.isU64 lower)
    (spec : LtOperationUnsigned.Spec ⟨address, lower, cols, 1⟩)
    (zero : cols.u16_compare_operation.bit = 0) : Word.toNat lower ≤ Word.toNat address := by
  have equal := (LtOperationUnsigned.result_semantic addressBound lowerBound rfl spec).1
  change cols.u16_compare_operation.bit = if Word.toNat address < Word.toNat lower then 1 else 0 at equal
  rw [zero] at equal
  split at equal
  · exact False.elim (zero_ne_one equal)
  · omega

private theorem compare_upper {address upper : Word (ZMod p)}
    {cols : Extracted.LtOperationUnsigned (ZMod p)}
    (addressBound : Word.isU64 address) (upperBound : Word.isU64 upper)
    (spec : LtOperationUnsigned.Spec ⟨address, upper, cols, 1⟩)
    (one : cols.u16_compare_operation.bit - 1 = 0) : Word.toNat address < Word.toNat upper := by
  have equal := (LtOperationUnsigned.result_semantic addressBound upperBound rfl spec).1
  change cols.u16_compare_operation.bit = if Word.toNat address < Word.toNat upper then 1 else 0 at equal
  rw [sub_eq_zero.mp one] at equal
  split at equal
  · assumption
  · exact False.elim (one_ne_zero equal)

/-- Compose the fixed lookup, address range check, and two word comparisons. -/
def main (memory : ByteMemory) (limit : ℕ) (input : Var Inputs (ZMod p))
    (tableName : String := "sp1.native.initial_memory") : Circuit (ZMod p) Unit := do
  lookup { (memory.fixedTable limit).toTable with name := tableName } input.interval
  assertion WordRangeCheck.circuit input.address
  assertion LtOperationUnsigned.circuit ⟨input.address, input.interval.lower, input.lowerCompare, 1⟩
  assertZero input.lowerCompare.u16_compare_operation.bit
  assertion LtOperationUnsigned.circuit ⟨input.address, input.interval.upper, input.upperCompare, 1⟩
  assertZero (input.upperCompare.u16_compare_operation.bit - 1)

@[local circuit_norm] private theorem range_guarantees :
    (WordRangeCheck.circuit (p := p)).channelsWithGuarantees = [] := rfl

@[local circuit_norm] private theorem range_requirements :
    (WordRangeCheck.circuit (p := p)).channelsWithRequirements = [] := rfl

@[local circuit_norm] private theorem compare_guarantees :
    (LtOperationUnsigned.circuit (p := p)).channelsWithGuarantees =
      [SP1Clean.Channels.byteChannel.toRaw] := rfl

instance elaborated (memory : ByteMemory) (limit : ℕ) (tableName : String) :
    ElaboratedCircuit (ZMod p) Inputs unit (main memory limit (tableName := tableName)) where
  localLength _ := 64
  output _ _ := ()
  channelsWithGuarantees := [SP1Clean.Channels.byteChannel.toRaw]

/-- Sound and complete byte lookup, with an explicit fixed-table identity for export. -/
def circuitNamed (memory : ByteMemory) (limit : ℕ) (limitBound : limit < 2 ^ 64)
    (tableName : String) :
    GeneralFormalCircuit (ZMod p) Inputs unit where
  main := main memory limit (tableName := tableName)
  elaborated := elaborated memory limit tableName
  channelsWithRequirements := []
  requirementsChannelsLawful := by
    intro input offset
    refine ⟨?_, ?_, ?_⟩
    · simp only [main, circuit_norm]
    · simp only [main, circuit_norm]
    · intro env _
      simp only [main, circuit_norm]
  Spec input _ _ := Spec memory limit input
  ProverAssumptions input _ _ := ProverAssumptions memory limit input
  soundness := by
    circuit_proof_start [WordRangeCheck.circuit, WordRangeCheck.Assumptions, WordRangeCheck.Spec]
    obtain ⟨member, addressBound, lowerSpec, lowerZero, upperSpec, upperOne⟩ := h_holds
    have ranges := memory.fixedTable_sound limit limitBound _ member
    have lower := lowerSpec ⟨fun _ => ⟨addressBound, ranges.1⟩, Or.inr rfl⟩
    have upper := upperSpec ⟨fun _ => ⟨addressBound, ranges.2.1⟩, Or.inr rfl⟩
    have inside := And.intro (compare_lower addressBound ranges.1 lower lowerZero)
      (compare_upper addressBound ranges.2.1 upper upperOne)
    exact ⟨addressBound, memory.fixedTable_read limit limitBound _ member _ inside⟩
  completeness := by
    circuit_proof_start [WordRangeCheck.circuit, WordRangeCheck.Assumptions, WordRangeCheck.Spec,
      ProverAssumptions]
    obtain ⟨addressBound, member, lowerLe, upperLt, lowerEq, upperEq⟩ := h_assumptions
    have ranges := memory.fixedTable_sound limit limitBound _ member
    have lowerSpec := LtOperationUnsigned.spec_populate (b := input_address) (cc := input_interval_lower)
    have upperSpec := LtOperationUnsigned.spec_populate (b := input_address) (cc := input_interval_upper)
    have lowerResult := (LtOperationUnsigned.result_semantic addressBound ranges.1 rfl lowerSpec).1
    have upperResult := (LtOperationUnsigned.result_semantic addressBound ranges.2.1 rfl upperSpec).1
    rw [← lowerEq] at lowerSpec lowerResult
    rw [← upperEq] at upperSpec upperResult
    dsimp only at lowerResult upperResult
    refine ⟨member, addressBound,
      ⟨⟨fun _ => ⟨addressBound, ranges.1⟩, Or.inr rfl⟩, lowerSpec⟩, ?_,
      ⟨⟨fun _ => ⟨addressBound, ranges.2.1⟩, Or.inr rfl⟩, upperSpec⟩, ?_⟩
    · simpa only [if_neg (Nat.not_lt.mpr lowerLe)] using lowerResult
    · rw [upperResult, if_pos upperLt, sub_self]

@[circuit_norm ↓, explicit_circuit_norm] theorem circuitNamed_elaborated (memory : ByteMemory)
    (limit : ℕ) (limitBound : limit < 2 ^ 64) (tableName : String) :
    (circuitNamed (p := p) memory limit limitBound tableName).elaborated = elaborated memory limit tableName := rfl

@[circuit_norm, explicit_circuit_norm] theorem circuit_localLength (memory : ByteMemory) (limit : ℕ)
    (bound : limit < 2 ^ 64) (input : Var Inputs (ZMod p))
    (tableName : String := "sp1.native.initial_memory") :
    (circuitNamed memory limit bound (tableName := tableName)).localLength input = 64 := rfl

@[circuit_norm, explicit_circuit_norm] theorem circuit_guarantees (memory : ByteMemory) (limit : ℕ)
    (bound : limit < 2 ^ 64) (tableName : String := "sp1.native.initial_memory") :
    (circuitNamed (p := p) memory limit bound (tableName := tableName)).channelsWithGuarantees =
      [SP1Clean.Channels.byteChannel.toRaw] := rfl

@[circuit_norm, explicit_circuit_norm] theorem circuit_requirements (memory : ByteMemory) (limit : ℕ)
    (bound : limit < 2 ^ 64) (tableName : String := "sp1.native.initial_memory") :
    (circuitNamed (p := p) memory limit bound (tableName := tableName)).channelsWithRequirements = [] := rfl

/-- Source-memory specialization of the named fixed byte lookup. -/
abbrev circuit (memory : ByteMemory) (limit : ℕ) (limitBound : limit < 2 ^ 64) :=
  circuitNamed (p := p) memory limit limitBound "sp1.native.initial_memory"

end SP1Clean.InitialMemoryLookup
