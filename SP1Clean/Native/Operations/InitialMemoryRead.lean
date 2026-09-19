import SP1Clean.FormalModel.Contracts.InitialMemoryRead
import SP1Clean.Native.Operations.InitialMemoryLookup
import SP1Clean.Proofs.Operations.AddOperation.Formal

/-! # An initial-memory word read composed from native byte lookups

Each byte is authenticated against the image-derived fixed table. The addition subcircuit ties
its address to the first byte, and the result packs the eight authenticated bytes into four limbs.
All address splitting and byte assembly stay behind the word-read semantic contract.
-/

namespace SP1Clean.InitialMemoryRead

open Circuit SP1Clean.Model.Core SP1Clean.Soundness.Target

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

private def offset (index : Fin 8) : Word (ZMod p) := bitVecToWord (BitVec.ofNat 64 index.val)

/-- Row construction supplies the byte rows and their semantic address offsets. -/
def ProverAssumptions (memory : ByteMemory) (input : Inputs (ZMod p)) : Prop :=
  ∀ index : Fin 8,
    InitialMemoryLookup.ProverAssumptions memory (2 ^ 48) input.bytes[index.val] ∧
      Word.toBitVec64 input.bytes[index.val].address =
        Word.toBitVec64 input.bytes[0].address + BitVec.ofNat 64 index.val

/-- Construct all eight byte rows and comparison columns directly from a semantic address. -/
def populate (memory : ByteMemory) (address : ℕ) : Inputs (ZMod p) where
  bytes := Vector.ofFn fun index =>
    (InitialMemoryLookup.populate? memory (2 ^ 48) (address + index.val)).getD
      (InitialMemoryLookup.populate 0 ⟨0, 0, 0⟩)

/-- Reject exactly those requests whose eight-byte footprint leaves native memory. -/
def populate? (memory : ByteMemory) (address : ℕ) : Option (Inputs (ZMod p)) :=
  if address + 8 ≤ 2 ^ 48 then some (populate memory address) else none

private theorem populate_byte (memory : ByteMemory) (address : ℕ)
    (footprint : address + 8 ≤ 2 ^ 48) (index : Fin 8) :
    InitialMemoryLookup.ProverAssumptions memory (2 ^ 48) (populate (p := p) memory address).bytes[index.val] ∧
      Word.toNat (populate (p := p) memory address).bytes[index.val].address = address + index.val := by
  obtain ⟨input, found⟩ := Option.isSome_iff_exists.mp
    ((InitialMemoryLookup.populate?_isSome_iff (p := p) memory (2 ^ 48) (address + index.val)).mpr
      (by have := index.isLt; omega))
  have valid := InitialMemoryLookup.populate?_sound memory (2 ^ 48) (address + index.val)
    (by norm_num) input found
  simpa only [populate, Vector.getElem_ofFn, found, Option.getD_some] using valid

/-- The constructor discharges every internal byte-row and address-link obligation. -/
theorem populate_assumptions (memory : ByteMemory) (address : ℕ)
    (footprint : address + 8 ≤ 2 ^ 48) : ProverAssumptions memory (populate (p := p) memory address) := by
  intro index
  refine ⟨(populate_byte memory address footprint index).1, ?_⟩
  change BitVec.ofNat 64 (Word.toNat (populate memory address).bytes[index.val].address) =
    BitVec.ofNat 64 (Word.toNat (populate memory address).bytes[0].address) + BitVec.ofNat 64 index.val
  have base : Word.toNat (populate (p := p) memory address).bytes[0].address = address :=
    (populate_byte memory address footprint ⟨0, by decide⟩).2
  exact (congrArg (BitVec.ofNat 64) (populate_byte memory address footprint index).2).trans
    ((BitVec.ofNat_add address index.val).trans
      (congrArg (fun value => BitVec.ofNat 64 value + BitVec.ofNat 64 index.val) base).symm)

/-- Successful word-row construction preserves the query and supplies all completeness conditions. -/
theorem populate?_sound (memory : ByteMemory) (address : ℕ) (input : Inputs (ZMod p))
    (found : populate? memory address = some input) :
    ProverAssumptions memory input ∧ Word.toNat input.bytes[0].address = address := by
  unfold populate? at found
  split at found
  · cases Option.some.inj found
    exact ⟨populate_assumptions memory address ‹_›, by
      simpa only [Fin.val_zero, Nat.add_zero] using (populate_byte memory address ‹_› 0).2⟩
  · contradiction

omit [Fact (2 ^ 17 < p)] in
/-- The compiler's domain is exactly the semantic eight-byte footprint bound. -/
theorem populate?_isSome_iff (memory : ByteMemory) (address : ℕ) :
    (populate? (p := p) memory address).isSome = true ↔ address + 8 ≤ 2 ^ 48 := by
  simp only [populate?]
  split <;> simp_all

omit [Fact (2 ^ 17 < p)] in
private theorem address_offset {base query : Word (ZMod p)} (index : Fin 8)
    (baseBound : Word.isU64 base) (baseWindow : Word.toNat base < 2 ^ 48)
    (queryBound : Word.isU64 query)
    (equal : Word.toBitVec64 query = Word.toBitVec64 base + BitVec.ofNat 64 index.val) :
    Word.toNat query = Word.toNat base + index.val := by
  have indexBound : index.val < 2 ^ 64 := by have := index.isLt; omega
  rw [← Word.toBitVec64_toNat queryBound, equal, BitVec.toNat_add,
    Word.toBitVec64_toNat baseBound, BitVec.toNat_ofNat, Nat.mod_eq_of_lt indexBound,
    Nat.mod_eq_of_lt (by have := index.isLt; omega)]

private theorem read_of_bytes (memory : ByteMemory) (input : Inputs (ZMod p))
    (reads : ∀ index : Fin 8, InitialMemoryLookup.Spec memory (2 ^ 48) input.bytes[index.val])
    (addresses : ∀ index : Fin 8, Word.toBitVec64 input.bytes[index.val].address =
      Word.toBitVec64 input.bytes[0].address + BitVec.ofNat 64 index.val) :
    Spec memory input (Word.ofBytes (input.bytes.map fun byte => byte.interval.value)) := by
  have positions (index : Fin 8) := address_offset index (reads 0).1 (reads 0).2.1
    (reads index).1 (addresses index)
  have values : input.bytes.map (fun byte => byte.interval.value) =
      (memory.wordBytes (Word.toNat input.bytes[0].address)).map (fun byte => (byte.toNat : ZMod p)) := by
    ext index bound
    simp only [Vector.getElem_map, ByteMemory.wordBytes, Vector.getElem_ofFn]
    have position := positions ⟨index, bound⟩
    dsimp only at position
    exact ((reads ⟨index, bound⟩).2.2).trans
      (congrArg (fun address => ((memory.read address).toNat : ZMod p)) position)
  refine ⟨(reads 0).1, ?_, ?_, ?_⟩
  · have last : Word.toNat input.bytes[0].address + 7 < 2 ^ 48 :=
      (positions ⟨7, by decide⟩) ▸ (reads ⟨7, by decide⟩).2.1
    omega
  · rw [values]
    exact Word.ofBytes_isU64 _
  · rw [values, Word.toBitVec64_ofBytes]
    rfl

/-- The data-only constructor conditions already determine the authenticated output word. -/
theorem ProverAssumptions.spec (memory : ByteMemory) (input : Inputs (ZMod p))
    (valid : ProverAssumptions memory input) :
    Spec memory input (Word.ofBytes (input.bytes.map fun byte => byte.interval.value)) :=
  read_of_bytes memory input
    (fun index => InitialMemoryLookup.ProverAssumptions.spec memory (2 ^ 48) (by norm_num)
      _ (valid index).1) (fun index => (valid index).2)

omit [Fact (2 ^ 17 < p)] in
private theorem eval_address (env : Environment (ZMod p))
    (vars : Var InitialMemoryLookup.Inputs (ZMod p)) (value : InitialMemoryLookup.Inputs (ZMod p))
    (equal : eval env vars = value) :
    Vector.map (Expression.eval env) vars.address = value.address :=
  by
    rcases vars with ⟨address, interval, lower, upper⟩
    simpa only [circuit_norm] using congrArg InitialMemoryLookup.Inputs.address equal

omit [Fact (2 ^ 17 < p)] in
private theorem eval_byte (env : Environment (ZMod p))
    (vars : Var InitialMemoryLookup.Inputs (ZMod p)) (value : InitialMemoryLookup.Inputs (ZMod p))
    (equal : eval env vars = value) : env vars.interval.value = value.interval.value := by
  rcases vars with ⟨address, ⟨lower, upper, byte⟩, lowerCompare, upperCompare⟩
  simpa only [circuit_norm] using
    congrArg (fun input : InitialMemoryLookup.Inputs (ZMod p) => input.interval.value) equal

omit [Fact (2 ^ 17 < p)] in
theorem eval_base (env : Environment (ZMod p))
    (vars : Vector (Var InitialMemoryLookup.Inputs (ZMod p)) 8)
    (values : Vector (InitialMemoryLookup.Inputs (ZMod p)) 8)
    (equal : eval env vars = values) :
    Vector.map (Expression.eval env) vars[0].address = values[0].address :=
  eval_address env _ _ (eval_vector_eq_get (M := InitialMemoryLookup.Inputs) env vars values equal 0 (by decide))

omit [Fact (2 ^ 17 < p)] in
theorem eval_result (env : Environment (ZMod p))
    (vars : Vector (Var InitialMemoryLookup.Inputs (ZMod p)) 8)
    (values : Vector (InitialMemoryLookup.Inputs (ZMod p)) 8)
    (equal : eval env vars = values) :
    Vector.map (Expression.eval env) (Word.ofBytes (vars.map fun byte => byte.interval.value)) =
      Word.ofBytes (values.map fun byte => byte.interval.value) := by
  have byte (index : Fin 8) : env (vars[index].interval.value) = values[index].interval.value :=
    eval_byte env _ _ (eval_vector_eq_get (M := InitialMemoryLookup.Inputs)
      env vars values equal index index.isLt)
  have byteNat (index : ℕ) (bound : index < 8) :
      env (vars[index].interval.value) = values[index].interval.value := byte ⟨index, bound⟩
  ext index bound
  interval_cases index <;> simp only [Word.ofBytes, circuit_norm, byteNat]

def main (memory : ByteMemory) (input : Var Inputs (ZMod p))
    (tableName : String := "sp1.native.initial_memory") : Circuit (ZMod p) (Var Word (ZMod p)) := do
  Circuit.forEach (Vector.finRange 8) fun index => do
    let _ ← InitialMemoryLookup.circuitNamed memory (2 ^ 48) (by norm_num) (tableName := tableName) input.bytes[index.val]
    assertion AddOperation.circuit
      ⟨input.bytes[0].address, const (offset index), ⟨input.bytes[index.val].address⟩, 1⟩
  return Word.ofBytes (input.bytes.map fun byte => byte.interval.value)

@[local circuit_norm] private theorem add_length (input : Var AddOperation.Inputs (ZMod p)) :
    AddOperation.circuit.localLength input = 0 := rfl

@[local circuit_norm] private theorem add_requirements :
    (AddOperation.circuit (p := p)).channelsWithRequirements = [] := rfl

@[local circuit_norm] private theorem add_guarantees :
    (AddOperation.circuit (p := p)).channelsWithGuarantees =
      List.replicate 4 SP1Clean.Channels.byteChannel.toRaw := rfl

instance elaborated (memory : ByteMemory) (tableName : String) :
    ElaboratedCircuit (ZMod p) Inputs Word (main memory (tableName := tableName)) := by
  elaborate_circuit

/-- Sound and complete word read with an explicit fixed-table identity for export. -/
def circuitNamed (memory : ByteMemory) (tableName : String) : GeneralFormalCircuit (ZMod p) Inputs Word where
  main := main memory (tableName := tableName)
  elaborated := elaborated memory tableName
  Spec input output _ := Spec memory input output
  ProverAssumptions input _ _ := ProverAssumptions memory input
  soundness := by
    circuit_proof_start [InitialMemoryLookup.circuitNamed]
    have atByte (index : Fin 8) :=
      eval_vector_eq_get env input_var_bytes input_bytes h_input index index.isLt
    have atAddress (index : ℕ) (bound : index < 8) :
        Vector.map (Expression.eval env) input_var_bytes[index].address = input_bytes[index].address :=
      eval_address env _ _ (atByte ⟨index, bound⟩)
    simp only [circuit_norm] at atByte
    have atOffset (index : Fin 8) :
        Vector.map (Expression.eval env) (Vector.map Expression.const (offset (p := p) index)) =
          offset index := by
      simp only [Vector.map_map, Function.comp_def, Expression.eval]
      exact Vector.map_id _
    simp only [atByte, atAddress, atOffset] at h_holds
    apply (congrArg (Spec memory ⟨input_bytes⟩) (eval_result env _ _ h_input)).mpr
    apply read_of_bytes memory ⟨input_bytes⟩ (fun index => (h_holds index).1)
    intro index
    have addition := (h_holds index).2
      ⟨fun _ => ⟨(h_holds 0).1.1, isU64_bitVecToWord _⟩, Or.inr rfl⟩
    change Word.toBitVec64 input_bytes[index.val].address =
      Word.toBitVec64 input_bytes[0].address + BitVec.ofNat 64 index.val
    simpa only [offset, toBitVec64_bitVecToWord] using (addition rfl).2
  completeness := by
    circuit_proof_start [InitialMemoryLookup.circuitNamed]
    have atByte (index : Fin 8) :=
      eval_vector_eq_get env.toEnvironment input_var_bytes input_bytes h_input index index.isLt
    have atAddress (index : ℕ) (bound : index < 8) :
        Vector.map (Expression.eval env.toEnvironment) input_var_bytes[index].address = input_bytes[index].address :=
      eval_address env.toEnvironment _ _ (atByte ⟨index, bound⟩)
    simp only [circuit_norm] at atByte
    have atOffset (index : Fin 8) :
        Vector.map (Expression.eval env.toEnvironment)
            (Vector.map Expression.const (offset (p := p) index)) = offset index := by
      simp only [Vector.map_map, Function.comp_def, Expression.eval]
      exact Vector.map_id _
    simp only [atByte, atAddress, atOffset]
    intro index
    refine ⟨(h_assumptions index).1,
      ⟨fun _ => ⟨(h_assumptions 0).1.1, isU64_bitVecToWord _⟩, Or.inr rfl⟩,
      fun _ => ⟨(h_assumptions index).1.1, ?_⟩⟩
    simpa only [offset, toBitVec64_bitVecToWord] using (h_assumptions index).2

@[circuit_norm ↓, explicit_circuit_norm] theorem circuitNamed_elaborated (memory : ByteMemory) (tableName : String) :
    (circuitNamed (p := p) memory tableName).elaborated = elaborated memory tableName := rfl

@[circuit_norm, explicit_circuit_norm] theorem circuitNamed_localLength (memory : ByteMemory) (tableName : String)
    (input : Var Inputs (ZMod p)) :
    (circuitNamed memory tableName).localLength input = 512 := rfl

@[circuit_norm, explicit_circuit_norm] theorem circuitNamed_output (memory : ByteMemory) (tableName : String)
    (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (circuitNamed memory tableName).output input offset =
      Word.ofBytes (input.bytes.map fun byte => byte.interval.value) := rfl

@[circuit_norm, explicit_circuit_norm] theorem circuitNamed_requirements (memory : ByteMemory) (tableName : String) :
    (circuitNamed (p := p) memory tableName).channelsWithRequirements = [] := rfl

@[circuit_norm, explicit_circuit_norm] theorem circuitNamed_guarantees (memory : ByteMemory) (tableName : String) :
    (circuitNamed (p := p) memory tableName).channelsWithGuarantees =
      List.replicate 40 SP1Clean.Channels.byteChannel.toRaw := rfl

/-- Source-memory specialization of the named fixed word read. -/
abbrev circuit (memory : ByteMemory) := circuitNamed (p := p) memory "sp1.native.initial_memory"

end SP1Clean.InitialMemoryRead
