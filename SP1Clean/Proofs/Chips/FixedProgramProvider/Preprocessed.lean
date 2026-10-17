import SP1Clean.Model.Core.ProgramTable
import SP1Clean.Model.Channels
import ToClean.Air.FixedPrefix
import ToClean.Air.FixedRows
import Mathlib.Data.Nat.Log

/-! # Verifier-fixed Program instructions with prover-owned counts

The fixed prefix contains SP1's sixteen instruction fields; the only committed input is the
lookup count. Every decoded ROM entry is retained in order, including unused entries. Padding
repeats the first instruction, as in SP1. Clean's backend requires a power-of-two height, with
32 rows as the minimum nonempty SP1 block. Empty inventories instead have one inert zero row.

The physical constructor checks its capacity explicitly. An oversized invalid image supplies
no instructions; the existing loader validity predicate proves that this case is unreachable
for every admitted image. This component replaces the migration-era static lookup provider;
its installation and whole-machine consumers are migrated separately.
-/

namespace SP1Clean.FixedProgramProvider.Preprocessed

open Circuit Air.Flat SP1Clean.Model.Core SP1Clean.Channels

variable {p : ℕ} [Fact p.Prime]

/-- SP1's verifier-fixed Program message followed by its prover-owned multiplicity. -/
abbrev Input := ProvablePair ProgramMsg field

/-- Fail closed on physically oversized inputs, without retaining a truncated ROM prefix. -/
def rows (image : ProgramImage) : List (ProgramMsg (ZMod p)) :=
  let decoded := image.programRows (p := p)
  if decoded.length ≤ 2 ^ 48 then decoded else []

/-- Every admitted image retains its entire decoded inventory. -/
theorem rows_of_valid (image : ProgramImage) (valid : image.Valid) :
    rows (p := p) image = image.programRows := by
  simp only [rows, if_pos (image.programRows_length_le valid)]

private theorem rows_length_le (image : ProgramImage) :
    (rows (p := p) image).length ≤ 2 ^ 48 := by
  dsimp only [rows]
  split <;> simp_all

private theorem rows_subset (image : ProgramImage) {msg : ProgramMsg (ZMod p)}
    (member : msg ∈ rows image) : msg ∈ image.programRows := by
  dsimp only [rows] at member
  split at member
  · exact member
  · contradiction

/-- Backend height preserves every entry and extends a nonempty inventory by first-row copies. -/
def height (image : ProgramImage) : ℕ :=
  if (rows (p := p) image).isEmpty then 1
  else 2 ^ Nat.clog 2 (max (rows (p := p) image).length 32)

/-- Padding never removes an original occurrence. -/
theorem length_le_height (image : ProgramImage) :
    (rows (p := p) image).length ≤ height (p := p) image := by
  unfold height
  split
  · rename_i empty
    simp only [List.isEmpty_iff] at empty
    simp [empty]
  · exact (Nat.le_max_left _ _).trans (Nat.le_pow_clog (by decide) _)

/-- The checked inventory and its padding fit Clean's physical row index. -/
theorem height_lt_uint64 (image : ProgramImage) : height (p := p) image < UInt64.size := by
  have bounded := rows_length_le (p := p) image
  have logarithm : Nat.clog 2 (max (rows (p := p) image).length 32) ≤ 48 := by
    apply (Nat.clog_le_iff_le_pow (by decide)).mpr
    exact max_le bounded (by norm_num)
  have power := Nat.pow_le_pow_right (by decide : 1 ≤ 2) logarithm
  unfold height
  split
  · decide
  · change 2 ^ Nat.clog 2 (max (rows (p := p) image).length 32) < 18446744073709551616
    norm_num at power
    omega

/-- Fixed payload at a physical row. Empty-table padding carries no instruction authority. -/
def message (image : ProgramImage) (index : ℕ) : ProgramMsg (ZMod p) :=
  let rom := rows (p := p) image
  rom[index]?.getD (rom.headD (fromElements (Vector.replicate (size ProgramMsg) 0)))

/-- The original prefix preserves row order and repeated payloads exactly. -/
theorem message_original (image : ProgramImage) (index : Fin (rows (p := p) image).length) :
    message image index.val = (rows (p := p) image)[index] := by
  simp [message, index.isLt]

/-- Every decoded instruction in an admitted image has a physical fixed row, whether or not
execution requests it. -/
theorem message_covers (image : ProgramImage) (valid : image.Valid)
    (msg : ProgramMsg (ZMod p)) (member : msg ∈ image.programRows) :
    ∃ index : Fin (height (p := p) image), message image index.val = msg := by
  rw [← rows_of_valid image valid] at member
  obtain ⟨index, equal⟩ := List.mem_iff_get.mp member
  exact ⟨⟨index.val, index.isLt.trans_le (length_le_height image)⟩,
    (message_original image index).trans equal⟩

/-- Every fixed row in a nonempty inventory is an actual decoded ROM instruction, even when
its count is zero or its physical index lies in padding. -/
theorem message_mem (image : ProgramImage) (index : ℕ) (nonempty : rows (p := p) image ≠ []) :
    message (p := p) image index ∈ image.programRows := by
  apply rows_subset image
  unfold message
  cases romEq : rows (p := p) image with
  | nil => exact (nonempty romEq).elim
  | cons first rest =>
    cases found : (first :: rest)[index]? with
    | none => simp [found]
    | some value =>
      simp only [found, Option.getD_some]
      exact List.mem_of_getElem? found

/-- Public columns use Clean's row program and lowering without a separate extraction path. -/
def fixedColumns (image : ProgramImage) : FixedColumns (ZMod p) :=
  FixedColumns.ofRows (Vector.ofFn fun index : Fin (height (p := p) image) =>
    toElements (message image index.val)) (height_lt_uint64 image)

/-- Lean and exported fixed-column evaluation recover the same typed instruction. -/
theorem fixedColumns_row (image : ProgramImage) (index : Fin (height (p := p) image)) :
    (fixedColumns (p := p) image).row (UInt64.ofNat index.val) =
      (toElements (message image index.val)).toArray := by
  simp [fixedColumns, FixedColumns.ofRows_row]

/-- Emit the fixed instruction at its chosen count. Only an empty inventory needs an arithmetic
constraint: its inert row cannot satisfy a Program demand. -/
def circuit (image : ProgramImage) : GeneralFormalCircuit (ZMod p) Input unit :=
  if rows (p := p) image = [] then {
    name := "sp1.native.program.fixed"
    main input := do
      assertZero input.2
      programChannel.emit input.2 input.1
    Spec input _ _ := input.2 ≠ 0 → input.1 ∈ image.programRows
    ProverAssumptions input _ _ := input.2 = 0
    channelsWithRequirements := [programChannel.toRaw]
    soundness := by
      circuit_proof_start [programChannel]
      subst input
      simp_all
    completeness := by
      circuit_proof_start [programChannel]
      subst input
      exact h_assumptions
  } else {
    name := "sp1.native.program.fixed"
    main input := programChannel.emit input.2 input.1
    Assumptions input _ := ProgramMsg.RowSpec input.1 ∧ input.1 ∈ image.programRows
    Spec input _ _ := input.2 ≠ 0 → input.1 ∈ image.programRows
    channelsWithRequirements := [programChannel.toRaw]
    soundness := by
      circuit_proof_start [programChannel]
      subst input
      exact ⟨fun _ => h_assumptions.2, fun _ _ => h_assumptions.1⟩
    completeness := by circuit_proof_start [programChannel]
  }

/-- Fixed preprocessing establishes the circuit's assumptions, with no residual validity
condition on the enclosing ensemble or on the prover's count. -/
def component [Fact (2 ^ 17 < p)] (image : ProgramImage) : Component (ZMod p) where
  circuit := circuit image
  fixedColumns := some (fixedColumns image)
  Assumptions _ _ := True
  circuit_assumptions_of_assumptions := by
    intro index input data fixed _ _
    have bound : index.toNat < height (p := p) image := (fixed _ rfl).1
    have fixedCells := fixed.input_prefix (by rfl)
    have rowEq := fixedColumns_row image ⟨index.toNat, bound⟩
    simp only [UInt64.ofNat_toNat] at rowEq
    rw [rowEq] at fixedCells
    have decoded := congrArg (fromElements (M := ProgramMsg)) (Vector.toArray_inj.mp fixedCells)
    simp only [ProvableType.fromElements_toElements] at decoded
    dsimp only [circuit]
    split
    · trivial
    rename_i nonempty
    change ProgramMsg.RowSpec input.1 ∧ input.1 ∈ image.programRows
    rw [decoded]
    have member := message_mem image index.toNat nonempty
    exact ⟨image.programRows_rowSpec _ member, member⟩
  fixed_width_le_input := by change 16 ≤ 17; decide

end SP1Clean.FixedProgramProvider.Preprocessed
