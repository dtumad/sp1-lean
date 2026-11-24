import SP1Clean.Proofs.Chips.FixedProgramProvider.Preprocessed
import ToClean.Air.ReaderCounts
import ToClean.Air.TableBuild

/-! # Populating the fixed Program circuit from counted decoded fetches

Each active fetch belongs to an original decoded ROM row. Assign it to the first complete
matching prefix at its original index, retaining all other rows and their physical padding.
-/

namespace SP1Clean.FixedProgramProvider.Preprocessed

open Circuit Air.Flat Air.Flat.WitnessGeneration Semantics Channels

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

private def indexOfFetch (image : ProgramImage) (valid : image.Valid) (fetch : ProgramMsg (ZMod p))
    (fetched : fetch ∈ image.programRows) : Fin (height (p := p) image) :=
  ⟨(rows image).idxOf fetch, (List.idxOf_lt_length_iff.mpr ((rows_of_valid (p := p) image valid).symm ▸ fetched)).trans_le (length_le_height (p := p) image)⟩

omit [Fact (2 ^ 17 < p)] in
private theorem message_indexOfFetch (image : ProgramImage) (valid : image.Valid) (fetch : ProgramMsg (ZMod p))
    (fetched : fetch ∈ image.programRows) : message image (indexOfFetch image valid fetch fetched).val = fetch := by
  have used : fetch ∈ rows image := (rows_of_valid (p := p) image valid).symm ▸ fetched
  exact (message_original image ⟨_,List.idxOf_lt_length_iff.mpr used⟩).trans (List.getElem_idxOf (List.idxOf_lt_length_iff.mpr used))

/-- Preallocate every fixed ROM row with its actual counted fetch multiplicity. -/
def countedTable (image : ProgramImage) (ids : List (Fin (height (p := p) image))) (data : ProverData (ZMod p)) : Table (ZMod p) :=
  let c := component (p := p) image
  let inputs : List (Input (ZMod p)) := List.ofFn (fun i : Fin (height (p := p) image) => (message image i.val,((ReaderCounts.counts ids)[i] : ZMod p)))
  let localData := c.inputData inputs data
  Table.build c inputs localData (.empty _) (List.length_ofFn.trans_le (height_lt_uint64 image).le) (by
    apply (c.fixedRowsMatch_buildRows _ _ _ (mode := generation image) rfl).mpr
    refine ⟨List.length_ofFn.trans (UInt64.toNat_ofNatLT ..).symm,?_⟩
    intro i inside
    have bound : i < height (p := p) image := inside.trans_eq List.length_ofFn
    have cell : inputs[i] = (message image i,((ReaderCounts.counts ids)[i]'bound : ZMod p)) := List.getElem_ofFn ..
    change (generation (p := p) image).FixedAt (UInt64.ofNat i) (inputs[i].1, inputs[i].2)
    rw [cell]
    rw [← fixedRow_evalRow image ⟨i,bound⟩]
    apply PreallocatedMode.fixedAt_of_typed_prefix (row := fixedRow image .idx) (suffix := (.multiplicity : Cell (ZMod p))) _ rfl
    intro cell mem
    exact List.mem_singleton.mp mem ▸ rfl)
    (c.inputData_consistent inputs data)

/-- Original physical indices, in fetch order, including every repeated occurrence. -/
def fetchIndices (image : ProgramImage) (valid : image.Valid) (fetches : List (ProgramMsg (ZMod p)))
    (covered : ∀ m ∈ fetches, m ∈ image.programRows) : List (Fin (height (p := p) image)) :=
  fetches.attach.map fun ⟨m,used⟩ => indexOfFetch image valid m (covered m used)

omit [Fact (2 ^ 17 < p)] in
private theorem indices_messages (image : ProgramImage) (valid : image.Valid) (fetches : List (ProgramMsg (ZMod p)))
    (covered : ∀ m ∈ fetches, m ∈ image.programRows) :
    (fetchIndices image valid fetches covered).map (fun i => message image i.val) = fetches := by
  simp only [fetchIndices, List.map_map, Function.comp_def, message_indexOfFetch, List.attach_map_subtype_val]

private theorem emitted (image : ProgramImage) (env : Environment (ZMod p)) :
    let c := component (p := p) image
    c.operations.interactionValuesWith programChannel.toRaw env =
      [programChannel.emittedValue (c.rowInput env).2 (c.rowInput env).1] := by
  let c := component (p := p) image
  let input := varFromOffset Input (F := ZMod p) 0
  change c.operations.interactionValuesWith programChannel.toRaw env = _
  rw [Operations.interactionValuesWith, Component.interactionsWith_eq]
  change ((((circuit image).main input).operations (size Input)).interactionsWith programChannel.toRaw).map _ = _
  rw [main_program_interactions, List.map_singleton, Channel.eval_pushedIf]
  have coords := eval_varFromOffset_valueFromOffset (F := ZMod p) Input 0 env
  simp only [CircuitType.eval_provablePair_dispatch] at coords
  exact congrArg (fun r : Input (ZMod p) => [programChannel.emittedValue r.2 r.1]) coords

/-- Original row order, all padding multiplicities and the complete weighted Program ledger. -/
theorem counted_interactions (image : ProgramImage) (ids : List (Fin (height (p := p) image))) (data : ProverData (ZMod p)) :
    (countedTable image ids data).interactionsWith programChannel.toRaw =
      List.ofFn (fun i : Fin (height (p := p) image) => programChannel.emittedValue ((ReaderCounts.counts ids)[i] : ZMod p) (message image i.val)) := by
  unfold countedTable
  refine (Table.build_interactions _ _ _ _ _ _ _ programChannel.toRaw).trans ?_
  simp only [emitted, Component.rowInput_buildRow]
  let emit (r : Input (ZMod p)) := programChannel.emittedValue r.2 r.1
  change (List.ofFn _).flatMap (fun r => [emit r]) = _
  rw [← List.map_eq_flatMap, List.map_ofFn]
  rfl

/-- Build an honest fixed ROM provider for the exact ordered sequence of decoded fetches.
An empty ROM has one inert row, and every fetch on a nonempty ROM uses an original entry. -/
theorem counted_fetches (image : ProgramImage) (valid : image.Valid) (fetches : List (ProgramMsg (ZMod p)))
    (covered : ∀ m ∈ fetches, m ∈ image.programRows) (data : ProverData (ZMod p)) :
    let ids := fetchIndices image valid fetches covered
    let table := countedTable image ids data
    table.Constraints ∧ table.Guarantees ∧ table.length = height (p := p) image ∧
      LogUpBalanced (table.interactionsWith programChannel.toRaw ++ fetches.map programChannel.pulledValue) := by
  intro ids table
  have inert (empty : rows (p := p) image = []) : ids = [] := by
    have missing (m : ProgramMsg (ZMod p)) (used : m ∈ fetches) := covered m used
    rw [← rows_of_valid (p := p) image valid, empty] at missing
    have none : fetches = [] := List.eq_nil_iff_forall_not_mem.mpr (fun m mem => List.not_mem_nil (missing m mem))
    simp [ids, fetchIndices, none]
  let inputs : List (Input (ZMod p)) := List.ofFn (fun i : Fin (height (p := p) image) => (message image i.val,((ReaderCounts.counts ids)[i] : ZMod p)))
  have ready (d : ProverData (ZMod p)) (h : ProverHint (ZMod p)) (r : Input (ZMod p)) (used : r ∈ inputs) :
      (circuit image).ProverAssumptions r d h := by
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp used
    apply prover_assumptions_of_empty_count
    intro empty
    simp only [ReaderCounts.counts_at, inert empty, List.count_nil, Nat.cast_zero]
  refine ⟨?_,?_,(List.length_map ..).trans List.length_ofFn,?_⟩
  · dsimp only [table, countedTable]
    apply Table.build_constraints
    exact ready _ _
  · dsimp only [table, countedTable]
    apply Table.build_guarantees
    exact ready _ _
  · have payloads := congrArg (List.map programChannel.pulledValue) (indices_messages image valid fetches covered)
    rw [List.map_map] at payloads
    rw [show table.interactionsWith programChannel.toRaw = _ from counted_interactions image ids data, ← payloads]
    exact ReaderCounts.balanced programChannel (fun i : Fin (height (p := p) image) => message image i.val) ids

end SP1Clean.FixedProgramProvider.Preprocessed
