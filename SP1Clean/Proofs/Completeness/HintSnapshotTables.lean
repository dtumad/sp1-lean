import SP1Clean.Native.Operations.HintQueueSeal
import SP1Clean.Proofs.Completeness.HintQueueSnapshot
import ToClean.Air.TableBuild

/-! # Constructing the physical outgoing hint walk from its actual persistent store

The public target fixes the word shape. The witness follows the final private head once per
buffer and retains its two node identities on every word, including its terminal padding.
-/

namespace SP1Clean.HostHintSnapshot

open Circuit Air.Flat Semantics Semantics.HintQueue Soundness.Target

variable {p : ℕ} [Fact p.Prime]

/-- Read the actual tail once per target buffer, keeping node identities on all of its words. -/
def liveInputs (store : Store) (start head : ℕ) : List Bytes → List (Inputs (ZMod p))
  | [] => []
  | bytes :: rest =>
    let tail := ((node? store head).map Node.tail).getD 0
    let links : Links (ZMod p) := ⟨Address.ofNat head, Address.ofNat tail⟩
    ((bufferShapes start bytes).map fun s => (s, links, 1)) ++
      liveInputs store (start + wordCount bytes) tail rest

private theorem live_shapes (store : Store) (start head : ℕ) (hints : List Bytes) :
    (liveInputs (p := p) store start head hints).map Prod.fst = shapesFrom start hints := by
  induction hints generalizing start head with
  | nil => rfl
  | cons bytes rest ih => simp [liveInputs, shapesFrom, ih, List.map_map, Function.comp_def]

private theorem shape_valid [Fact (2 ^ 17 < p)] {hints : List Bytes} (fit : fits hints = true)
    {bytes : Bytes} {head tail : ℕ} (bounded : head < 2 ^ 48) (down : tail < head)
    (start i : ℕ) :
    let s := shape (p := p) (start + i) i bytes.length (wordValue bytes i)
    let links : Links (ZMod p) := ⟨Address.ofNat head, Address.ofNat tail⟩
    Valid hints (s, links, 1) := by
  refine ⟨fit, rfl, ?_, Or.inr rfl, fun _ => NodeRecord.encode_valid head ⟨bytes, tail⟩ bounded down, ?_⟩
  · change IsBool (if i = 0 then (1 : ZMod p) else 0)
    split <;> simp [IsBool]
  · intro _
    simpa only [Shape.word, shape, WordRecord.encode, wordCount, Nat.add_left_inj] using
      WordRecord.encode_valid (p := p) head bytes i (by omega) bounded

private theorem live_valid [Fact (2 ^ 17 < p)] {target : List Bytes} (fit : fits target = true)
    {store : Store} {head : ℕ} {hints : List Bytes} {tails : List ℕ}
    (read : ReadsSnapshot p store head hints tails) (start : ℕ) :
    ∀ row ∈ liveInputs (p := p) store start head hints, Valid target row := by
  induction hints generalizing start head tails with
  | nil => simp [liveInputs]
  | cons bytes rest ih =>
    cases tails with
    | nil => contradiction
    | cons tail tails =>
      obtain ⟨bounded, down, indices, node, suffix⟩ := read
      have found := (readsNode_iff bounded down indices).mp node
      intro row member
      simp only [liveInputs, found, Option.map_some, Option.getD_some, List.mem_append] at member
      rcases member with here | later
      · obtain ⟨s, inside, rfl⟩ := List.mem_map.mp here
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp inside
        simpa only [List.size_toArray, arrayWord_toArray] using shape_valid (bytes := bytes) fit bounded down start i
      · exact ih suffix _ _ later

/-- Populate exactly the preallocated height with the live walk and zero rows on padding. -/
def inputsFor (store : Store) (head : ℕ) (hints : List Bytes) : List (Inputs (ZMod p)) :=
  let live := (liveInputs (p := p) store 0 head hints).toArray
  List.ofFn fun i : Fin (inventory (p := p) hints).height => live[i.val]?.getD (Shape.padding, 0, 0)

private theorem inputs_length (store : Store) (head : ℕ) (hints : List Bytes) :
    (inputsFor (p := p) store head hints).length = (inventory (p := p) hints).height := List.length_ofFn

/-- The constructed inputs retain the chronological word order, followed by exactly enough
inactive rows to reach the declared physical height. -/
theorem inputs_eq_padded (store : Store) (head : ℕ) (hints : List Bytes) (fit : fits hints = true) :
    let live := liveInputs (p := p) store 0 head hints
    inputsFor store head hints = live ++ List.replicate ((inventory (p := p) hints).height - live.length)
      (Shape.padding, 0, 0) := by
  dsimp only
  have height := (inventory (p := p) hints).length_le_height
  have same := congrArg List.length (live_shapes (p := p) store 0 head hints)
  simp only [List.length_map, shapesFrom_length] at same
  change (schedule (p := p) hints).length ≤ _ at height
  simp only [schedule_length, fit, ↓reduceIte, ← same] at height
  apply List.ext_getElem
  · rw [inputs_length, List.length_append, List.length_replicate]
    omega
  · intro idx left right
    simp only [inputsFor, List.getElem_ofFn, List.getElem?_toArray]
    by_cases inside : idx < (liveInputs (p := p) store 0 head hints).length
    · simp [inside, List.getElem_append_left]
    · simp [List.getElem_append_right, Nat.le_of_not_gt inside]

private theorem input_shape (store : Store) (head : ℕ) (hints : List Bytes) (fit : fits hints = true)
    (i : Fin (inventory (p := p) hints).height) :
    ((inputsFor (p := p) store head hints)[i.val]'(by simp [inputsFor])).1 = (fixedShapes hints)[i.val] := by
  have same : (liveInputs (p := p) store 0 head hints).map Prod.fst = schedule hints := by
    simp [live_shapes, schedule, fit]
  simp only [inputsFor, List.getElem_ofFn, fixedShapes, Vector.getElem_ofFn, List.getElem?_toArray]
  rw [← same, List.getElem?_map]
  cases (liveInputs (p := p) store 0 head hints)[i.val]? <;> rfl

private theorem fixed_inputs (store : Store) (head : ℕ) (hints : List Bytes) (fit : fits hints = true)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    (component hints).FixedRowsMatch ((inputsFor store head hints).map ((component hints).buildRow · data hint)) := by
  apply ((component hints).fixedRowsMatch_buildRows _ _ _ (mode := generation hints) rfl).mpr
  refine ⟨(inputs_length store head hints).trans (UInt64.toNat_ofNatLT ..).symm, ?_⟩
  intro idx bound
  have inside := bound.trans_eq (inputs_length (p := p) store head hints)
  let row := (inputsFor (p := p) store head hints)[idx]
  have same : row.1 = (fixedShapes hints)[idx] := input_shape (p := p) store head hints fit ⟨idx, inside⟩
  change (generation hints).FixedAt (UInt64.ofNat idx) (row.1, row.2.1, row.2.2)
  rw [same]
  exact fixed_of_shape hints ⟨idx, inside⟩ row.2.1 row.2.2

/-- Construct the outgoing physical reader using the actual store and head. -/
def tableFor (store : Store) (head : ℕ) (hints : List Bytes) (fit : fits hints = true)
    (data : ProverData (ZMod p)) : Table (ZMod p) :=
  let c := component (p := p) hints
  let rows := inputsFor store head hints
  let own := c.inputData rows data
  Table.build c rows own (.empty _) ((inputs_length store head hints).trans_le (height_bound (p := p) hints).le)
    (fixed_inputs store head hints fit _ _) (c.inputData_consistent rows data)

/-- A represented queue makes every live and padded row satisfy the component contract. -/
theorem tableFor_valid [Fact (2 ^ 17 < p)] {store : Store} {head : ℕ} {hints : List Bytes} {tails : List ℕ}
    (read : ReadsSnapshot p store head hints tails) (fit : fits hints = true) (data : ProverData (ZMod p)) :
    (tableFor store head hints fit data).Constraints ∧ (tableFor store head hints fit data).Guarantees := by
  have rows : ∀ row ∈ inputsFor (p := p) store head hints, Valid hints row := by
    intro row member
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp member
    simp only [List.getElem?_toArray]
    cases entry : (liveInputs (p := p) store 0 head hints)[i.val]? with
    | some input => exact live_valid fit read 0 input (List.mem_of_getElem? entry)
    | none =>
      change Valid hints (Shape.padding, (0 : Links (ZMod p)), (0 : ZMod p))
      simp [Valid, Shape.padding, IsBool, fit]
  unfold tableFor
  exact ⟨Table.build_constraints _ _ _ _ _ _ _ rows, Table.build_guarantees _ _ _ _ _ _ _ rows⟩

namespace Seal
open HostHintQueue WitnessGeneration

private theorem fixed_input (hints : List Bytes) (state : State (ZMod p))
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    (component hints).FixedRowsMatch ([(1, state, 1)].map ((component hints).buildRow · data hint)) := by
  apply ((component hints).fixedRowsMatch_buildRows _ _ _ (mode := generation) rfl).mpr
  refine ⟨rfl, ?_⟩
  intro i bound
  change i < 1 at bound
  obtain rfl : i = 0 := by omega
  let ticket : Witgen.M (ZMod p) (Witgen.FExpr (ZMod p)) := pure 1
  have publicTicket : ticket.evalRow (Row := field) 0 = 1 := by
    simp [ticket, Witgen.M.evalRow, Witgen.eval, Witgen.M.pure_def, Witgen.FExpr.eval, circuit_norm]
  change generation.FixedAt 0 (1, state, 1)
  have fixed := PreallocatedMode.fixedAt_of_typed_prefix (mode := generation) (row := ticket) (i := 0)
    (state, 1) rfl (privateWithMultiplicity_unfixed _)
  simpa only [publicTicket] using fixed

/-- Construct the compulsory physical seal with all eight fields of the private final state. -/
def tableFor (hints : List Bytes) (state : State (ZMod p)) (data : ProverData (ZMod p)) : Table (ZMod p) :=
  let c := component (p := p) hints
  let rows : List (c.Input (ZMod p)) := [(1, state, 1)]
  let own := c.inputData rows data
  Table.build c rows own (.empty _) (by change 1 ≤ UInt64.size; decide)
    (fixed_input hints state own _) (c.inputData_consistent rows data)

/-- The generated singleton satisfies its full physical obligations for every private endpoint. -/
theorem tableFor_valid (hints : List Bytes) (state : State (ZMod p)) (data : ProverData (ZMod p)) :
    (tableFor hints state data).Constraints ∧ (tableFor hints state data).Guarantees := by
  have valid (own : ProverData (ZMod p)) : ∀ row ∈ [(1, state, 1)], (component (p := p) hints).circuit.ProverAssumptions row own (.empty _) := by
    intro row member
    obtain rfl := List.mem_singleton.mp member
    exact ⟨rfl, rfl⟩
  unfold tableFor
  exact ⟨Table.build_constraints _ _ _ _ _ _ _ (valid _), Table.build_guarantees _ _ _ _ _ _ _ (valid _)⟩

end Seal

end SP1Clean.HostHintSnapshot
