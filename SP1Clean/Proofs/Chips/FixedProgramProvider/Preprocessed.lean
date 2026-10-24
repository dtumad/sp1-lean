module

public import SP1Clean.Model.Core.ProgramTable
public import SP1Clean.Model.Channels
public import ToClean.Air.FixedPrefix
public import ToClean.Air.FixedRows
public import ToClean.Air.ChannelClosure
public import Mathlib.Data.Nat.Log

/-! # Verifier-fixed Program instructions with prover-owned counts

The fixed prefix contains SP1's sixteen instruction fields; the only committed input is the
lookup count. Every decoded ROM entry is retained in order, including unused entries. Padding
repeats the first instruction, as in SP1. Clean's backend requires a power-of-two height, with
32 rows as the minimum nonempty SP1 block. Empty inventories instead have one inert zero row.

The physical constructor checks its capacity explicitly. An oversized invalid image supplies
no instructions; the existing loader validity predicate proves that this case is unreachable
for every admitted image. The native and local assemblies install this component directly; counted fetches are
authenticated through its fixed prefix and the complete Program channel balance.
-/

@[expose] public section

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
  let rom := (rows (p := p) image).toArray
  let padding := rom[0]?.getD (fromElements (Vector.replicate (size ProgramMsg) 0))
  FixedColumns.ofRows (Vector.ofFn fun index : Fin (height (p := p) image) =>
    toElements (rom[index.val]?.getD padding)) (height_lt_uint64 image)

/-- Lean and exported fixed-column evaluation recover the same typed instruction. -/
theorem fixedColumns_row (image : ProgramImage) (index : Fin (height (p := p) image)) :
    (fixedColumns (p := p) image).row (UInt64.ofNat index.val) =
      (toElements (message image index.val)).toArray := by
  simp [fixedColumns, FixedColumns.ofRows_row, message, List.head?_eq_getElem?]

/-- Emit the fixed instruction at its chosen count. Only an empty inventory needs an arithmetic
constraint: its inert row cannot satisfy a Program demand. -/
private def implementation (image : ProgramImage) : GeneralFormalCircuit (ZMod p) Input unit :=
  if rows (p := p) image = [] then {
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

/-- One named ROM interface, with its row program selected by the fixed inventory. -/
def circuit (image : ProgramImage) : GeneralFormalCircuit (ZMod p) Input unit :=
  { implementation image with name := "sp1.native.program.fixed" }

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
    dsimp only [circuit, implementation]
    split
    · trivial
    rename_i nonempty
    change ProgramMsg.RowSpec input.1 ∧ input.1 ∈ image.programRows
    rw [decoded]
    have member := message_mem image index.toNat nonempty
    exact ⟨image.programRows_rowSpec _ member, member⟩
  fixed_width_le_input := by change 16 ≤ 17; decide

/-- Empty and nonempty images keep one stable component identity. -/
@[simp, circuit_norm] theorem circuit_name (image : ProgramImage) :
    (circuit (p := p) image).name = "sp1.native.program.fixed" := rfl

/-- Program preprocessing requires no incoming channel guarantees. -/
@[simp, circuit_norm] theorem circuit_guarantees (image : ProgramImage) :
    (circuit (p := p) image).channelsWithGuarantees = [] := by
  change (implementation (p := p) image).channelsWithGuarantees = []
  unfold implementation
  split <;> rfl

/-- Program is the provider's only outgoing requirement channel. -/
@[simp, circuit_norm] theorem circuit_requirements (image : ProgramImage) :
    (circuit (p := p) image).channelsWithRequirements = [programChannel.toRaw] := by
  change (implementation (p := p) image).channelsWithRequirements = [programChannel.toRaw]
  unfold implementation
  split <;> rfl

/-- The declared channel inventory is independent of empty-table padding. -/
@[simp, circuit_norm] theorem circuit_channels (image : ProgramImage) :
    (circuit (p := p) image).channels = [programChannel.toRaw] := by
  change (implementation (p := p) image).channels = [programChannel.toRaw]
  unfold implementation
  split <;> rfl

/-- The ROM predicate is enforced by the fixed prefix, without legacy static lookups. -/
@[simp] theorem component_lookups [Fact (2 ^ 17 < p)] (image : ProgramImage) :
    (component (p := p) image).operations.lookups = [] := by
  by_cases empty : rows (p := p) image = []
  all_goals simp [component, circuit, implementation, empty, Component.lookups_eq,
    Component.rowOperations, circuit_norm]

/-- Both layouts retain the complete payload and count as one literal Program occurrence. -/
theorem main_interactions (image : ProgramImage)
    (input : Var Input (ZMod p)) (offset : ℕ) :
    (((circuit image).main input).operations offset).interactions =
      [(programChannel.pushedIf input.2 input.1).toRaw] := by
  by_cases empty : rows (p := p) image = []
  all_goals simp [circuit, implementation, empty, circuit_norm]

/-- Filtering for Program retains the provider's sole occurrence. -/
theorem main_program_interactions (image : ProgramImage)
    (input : Var Input (ZMod p)) (offset : ℕ) :
    (((circuit image).main input).operations offset).interactionsWith programChannel.toRaw =
      [(programChannel.pushedIf input.2 input.1).toRaw] := by
  by_cases empty : rows (p := p) image = []
  all_goals simp [circuit, implementation, empty, circuit_norm]

/-- Only counted messages claim instruction membership; inert empty padding has no authority. -/
@[simp] theorem circuit_spec (image : ProgramImage) (input : Input (ZMod p))
    (output : Unit) (data : ProverData (ZMod p)) :
    (circuit image).Spec input output data ↔ (input.2 ≠ 0 → input.1 ∈ image.programRows) := by
  change (implementation image).Spec input output data ↔ _
  unfold implementation
  split <;> rfl

/-- Physical table invariants discharge the circuit assumptions; callers supply no ROM validity
condition on prover-owned rows. Canonical data consistency comes from the ensemble witness. -/
theorem table_spec_and_requirements [Fact (2 ^ 17 < p)] (image : ProgramImage)
    (table : Table (ZMod p)) (same : table.component = component image)
    (consistent : table.DataConsistency) (constraints : table.Constraints) :
    table.Spec ∧ table.Requirements := by
  have assumptions : table.Assumptions := by
    intro row _
    change table.component.Assumptions _ _
    rw [same]
    trivial
  have noGuarantees : table.component.circuit.channelsWithGuarantees = [] := by
    rw [same]
    exact circuit_guarantees image
  have sound (row : Array (ZMod p)) (member : row ∈ table.table) :=
    table.component.weakSoundness_of_no_guarantees noGuarantees
      (table.circuitAssumptions_of_dataConsistency consistent assumptions row member)
      (constraints row member)
  exact ⟨fun row member => (sound row member).1, fun row member => (sound row member).2⟩

/-- A physical occurrence identifies both its complete instruction and its chosen count. -/
theorem program_interaction [Fact (2 ^ 17 < p)] (image : ProgramImage)
    (env : Environment (ZMod p)) (interaction : Interaction (ZMod p))
    (member : interaction ∈ (component image).operations.interactionValuesWith
      programChannel.toRaw env) :
    interaction.msg = (toElements (valueFromOffset Input 0 env).1).toArray ∧
      interaction.mult = (valueFromOffset Input 0 env).2 := by
  rw [Operations.interactionValuesWith, Component.interactionsWith_eq] at member
  change interaction ∈ ((((circuit image).main (varFromOffset Input 0)).operations
    (size Input)).interactionsWith programChannel.toRaw).map _ at member
  rw [main_program_interactions] at member
  obtain rfl := List.mem_singleton.mp member
  have evaluated := Channel.eval_pushedIf (channel := programChannel (p := p))
    (enabled := (varFromOffset Input 0).2) (msg := (varFromOffset Input 0).1) (env := env)
  have inputEq := eval_varFromOffset_valueFromOffset (F := ZMod p) Input 0 env
  simp only [CircuitType.eval_provablePair_dispatch] at inputEq
  constructor
  · exact (congrArg Interaction.msg evaluated).trans
      (congrArg (fun input : Input (ZMod p) => (toElements input.1).toArray) inputEq)
  · exact (congrArg Interaction.mult evaluated).trans (congrArg Prod.snd inputEq)

/-- Other channels have no provider obligations, even before fixed-prefix authentication. -/
theorem requirements_of_other_channel [Fact (2 ^ 17 < p)] (image : ProgramImage)
    (channel : RawChannel (ZMod p)) (different : channel ≠ programChannel.toRaw)
    (env : Environment (ZMod p))
    (constraints : (component image).operations.ConstraintsHold env) :
    (component image).operations.ChannelRequirements channel env := by
  apply Operations.requirements_of_not_mem _ _ _
    ((component image).inChannelsOrRequirements_of_constraints env constraints)
  simpa only [component, circuit_requirements, List.mem_singleton] using different

end SP1Clean.FixedProgramProvider.Preprocessed
