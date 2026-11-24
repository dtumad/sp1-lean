import SP1Clean.Proofs.Operations.HintQueueSnapshot
import SP1Clean.Soundness.RankedCoverage
import ToClean.Air.UnitBalance

/-! # Public ordinals force the physical order of the outgoing queue walk

Every active word has a distinct verifier-fixed ordinal. The reader's physical order is
the unique order compatible with the signed cursor ledger, including on empty targets.
-/

namespace SP1Clean.HostHintSnapshot
open Circuit Air.Flat Semantics Semantics.HintQueue Soundness Soundness.RankedGrounding
open scoped Classical
variable {p : ℕ} [Fact p.Prime]

private theorem indices_from (hints : List Bytes) (start i : ℕ) (inside : i < (shapesFrom (p := p) start hints).length) :
    let s := (shapesFrom (p := p) start hints)[i]
    s.active = 1 ∧ s.ordinal = Address.ofNat (start + i) ∧ s.nextOrdinal = Address.ofNat (start + i + 1) := by
  induction hints generalizing i start with
  | nil => simp [shapesFrom] at inside
  | cons bytes rest ih =>
    have length : (bufferShapes (p := p) start bytes).length = wordCount bytes := by simp [bufferShapes, wordCount]
    by_cases front : i < (bufferShapes (p := p) start bytes).length
    · have entry : (shapesFrom (p := p) start (bytes :: rest))[i] = (bufferShapes start bytes)[i] :=
        List.getElem_append_left front
      rw [entry]
      simp [bufferShapes, shape]
    · have split : (shapesFrom (p := p) start (bytes :: rest))[i] =
          (shapesFrom (p := p) (start + wordCount bytes) rest)[i - wordCount bytes]'(by
            simp only [shapesFrom, List.length_append, length] at inside; omega) := by
        simp only [shapesFrom, List.getElem_append_right (Nat.le_of_not_gt front), length]
      rw [split]
      have offset : start + wordCount bytes + (i - wordCount bytes) = start + i := by omega
      simpa only [offset] using ih (start + wordCount bytes) (i - wordCount bytes) (by
        simp only [shapesFrom, List.length_append, length] at inside; omega)

/-- Every live physical row carries its exact two public ordinals. Every padded row is inactive. -/
theorem fixed_ordinals (hints : List Bytes) (fit : fits hints = true) (i : Fin (inventory (p := p) hints).height) :
    let s := (fixedShapes (p := p) hints)[i.val]
    if i.val < wordRows hints then s.active = 1 ∧ s.ordinal = Address.ofNat i.val ∧ s.nextOrdinal = Address.ofNat (i.val + 1)
    else s.active = 0 := by
  have length := shapesFrom_length (p := p) 0 hints
  simp only [fixedShapes, Vector.getElem_ofFn, List.getElem?_toArray, schedule, fit, ↓reduceIte]
  split
  · have live : i.val < (shapesFrom (p := p) 0 hints).length := by omega
    rw [List.getElem?_eq_getElem live, Option.getD_some]
    simpa only [Nat.zero_add] using indices_from (p := p) hints 0 i.val live
  · rw [List.getElem?_eq_none (by omega), Option.getD_none]
    rfl

/-- The verifier's fixed schedule and the private link cells in the committed word row. -/
def physicalInput (t : Table (ZMod p)) (i : Fin t.table.length) : Inputs (ZMod p) :=
  valueFromOffset Inputs 0 (t.environment t.table[i.val])

/-- Both full cursors of a physical word, retaining its head and tail fields. -/
def physicalEdge (t : Table (ZMod p)) (i : Fin t.table.length) : Cursor (ZMod p) × Cursor (ZMod p) :=
  let r := physicalInput t i
  (r.1.before r.2.1, r.1.after r.2.1)

private theorem table_walk_values (hints : List Bytes) (t : Table (ZMod p)) (same : t.component = component hints) :
    t.interactionsWith channel.toRaw = (List.finRange t.table.length).flatMap (fun i => walkValues (physicalInput t i)) := by
  have row (r : Array (ZMod p)) : t.component.operations.interactionValuesWith channel.toRaw (t.environment r) =
      walkValues (valueFromOffset Inputs 0 (t.environment r)) := by
    rw [same, Operations.interactionValuesWith, Component.interactionsWith_eq]
    change ((main hints (varFromOffset Inputs 0)).operations (size Inputs)).interactionValuesWith channel.toRaw _ = _
    rw [walk_values, eval_varFromOffset_valueFromOffset]
  simp only [Table.interactionsWith, row]
  conv_lhs => arg 2; rw [← List.map_get_finRange t.table]
  rw [List.flatMap_map]
  rfl

/-- A balanced endpoint pair and the actual constrained word table force a walk in the physical
order of the entire public prefix. The endpoints carry the seal's head and the null pointer. -/
theorem physical_walk [Fact (2 ^ 17 < p)] (hints : List Bytes) (t : Table (ZMod p))
    (same : t.component = component hints) (checked : t.Constraints) (head : fields 3 (ZMod p))
    (balanced : BalancedInteractions ([channel.pushedValue (endpoint 0 head),
      channel.pulledValue (endpoint (wordRows hints) 0)] ++ t.interactionsWith channel.toRaw)) :
    Walk.IsWalk (physicalEdge t) (endpoint 0 head) (endpoint (wordRows hints) 0)
      ((List.finRange t.table.length).take (wordRows hints)) := by
  let rows := List.finRange t.table.length
  let gate := fun i => (physicalInput t i).1.active
  let index := fun c : Cursor (ZMod p) => Address.toNat c.ordinal
  let start := endpoint (p := p) 0 head
  let stop := endpoint (p := p) (wordRows hints) 0
  have height := physical_height hints t same
  have counted (i : Fin t.table.length) : fits hints = true ∧ (physicalInput t i).2.2 = gate i :=
    count_of_constraints hints _ (same ▸ checked _ (List.getElem_mem i.isLt))
  have nonempty : 0 < t.table.length := height ▸ (inventory (p := p) hints).height_pos
  have fit := (counted ⟨0, nonempty⟩).1
  have bounded : wordRows hints < 2 ^ 48 := of_decide_eq_true fit
  have shape (i : Fin t.table.length) := physical_shape hints t same i
  have fixed (i : Fin t.table.length) := fixed_ordinals (p := p) hints fit ⟨i.val, height ▸ i.isLt⟩
  have live (i : Fin t.table.length) (inside : i.val < wordRows hints) :
      gate i = 1 ∧ index (physicalEdge t i).1 = i.val ∧ index (physicalEdge t i).2 = i.val + 1 := by
    obtain ⟨active, before, after⟩ := (ite_eq_left inside).mp (fixed i)
    dsimp only [gate, index, physicalEdge, physicalInput, Shape.before, Shape.after]
    rw [shape i, active, before, after, Address.toNat_ofNat i.val (by omega), Address.toNat_ofNat (i.val + 1) (by omega)]
    exact ⟨rfl, rfl, rfl⟩
  have padding (i : Fin t.table.length) (outside : ¬ i.val < wordRows hints) : gate i = 0 :=
    (congrArg Shape.active (shape i)).trans ((ite_eq_right outside).mp (fixed i))
  have binary (i : Fin t.table.length) (_ : i ∈ rows) : gate i = 0 ∨ gate i = 1 := by
    by_cases inside : i.val < wordRows hints
    · exact .inr (live i inside).1
    · exact .inl (padding i inside)
  have ledger := table_walk_values hints t same
  have edges : BalancedInteractions (channel.gatedTransitionLedger start stop rows gate (physicalEdge t)) := by
    rw [ledger] at balanced
    unfold Channel.gatedTransitionLedger
    convert balanced using 2
    apply congrArg List.flatten
    apply List.map_congr_left
    intro i _
    simp only [walkValues, (counted i).2, physicalEdge, gate]
  let active := rows.filter (fun i => @decide (gate i = 1) (FiniteField.instDecidableEq _ _))
  have inside (i : Fin t.table.length) (m : i ∈ active) : i.val < wordRows hints := by
    simp only [active, List.mem_filter, decide_eq_true_eq] at m
    by_contra outside
    exact zero_ne_one ((padding i outside).symm.trans m.2)
  have ends : EndpointBalanced (↑active) (physicalEdge t) start stop := by
    simpa only [EndpointBalanced, Multiset.map_coe, Multiset.cons_coe, Multiset.coe_eq_coe, active] using
      (channel.gatedTransitionLedger_balanced_iff start stop rows gate (physicalEdge t) binary).mp edges
  obtain ⟨path, perm, walk, length, ordinals, _, _⟩ :=
    consecutive_coverage (physicalEdge t) index (fun _ => ()) active start stop ends (by
      intro i member
      have spec := (live i (inside i member)).2
      rw [spec.1, spec.2]) (fun _ _ => rfl)
  have zero : index start = 0 := Address.toNat_ofNat 0 (by decide)
  have last : index stop = wordRows hints := Address.toNat_ofNat _ bounded
  rw [zero, last, Nat.zero_add] at length
  rw [zero, ← length, ← List.range_eq_range'] at ordinals
  have ordered : path.map Fin.val = List.range (wordRows hints) := by
    rw [← ordinals]
    exact List.map_congr_left fun i m => (live i (inside i (perm.mem_iff.mp m))).2.1.symm
  have capacity : wordRows hints ≤ t.table.length := by
    rw [height]
    have available := (inventory (p := p) hints).length_le_height
    simpa only [inventory, StaticTable.ofRows, schedule_length, fit, ↓reduceIte] using available
  have eqPath : path = rows.take (wordRows hints) := by
    apply List.map_injective_iff.mpr Fin.val_injective
    rw [ordered, List.map_take]
    simp [rows, Nat.min_eq_left capacity]
  rwa [eqPath] at walk

end SP1Clean.HostHintSnapshot
