import SP1Clean.Proofs.Chips.HintReadWordChip.Ledger
import SP1Clean.Soundness.RankedGrounding
import ToClean.Air.TransitionView

/-! # Complete successive hint word coverage from physical table balance

Both consumer variants contribute their actual cursor edges. Unit balance and exact natural
index successors yield an exhaustive path with precisely the consecutive index inventory.
The cursor retains the clock and node throughout. Endpoint authentication, immutable word
binding, and installation in the mixed ensemble are separate integration obligations.
-/

namespace SP1Clean.Soundness.HintReadCoverage

open Circuit Air.Flat HintReadWordChip RankedGrounding
open scoped Classical

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

omit [Fact (2 ^ 25 < p)] in
private theorem eval_previous (env : Environment (ZMod p)) (input : Var Inputs (ZMod p)) :
    Eval.eval env input.previous = (Eval.eval env input).previous := by
  rcases input with ⟨ram, pointer, index, nextIndex, nextAddress⟩
  rcases ram with ⟨access, high, low0, low1, addr0, addr1, addr2, value⟩
  simp only [Inputs.previous, Inputs.address, HostRamAccessChip.Inputs.clockLow, circuit_norm]

omit [Fact (2 ^ 25 < p)] in
private theorem eval_next (env : Environment (ZMod p)) (input : Var Inputs (ZMod p)) :
    Eval.eval env input.next = (Eval.eval env input).next := by
  rcases input with ⟨ram, pointer, index, nextIndex, nextAddress⟩
  rcases ram with ⟨access, high, low0, low1, addr0, addr1, addr2, value⟩
  simp only [Inputs.next, HostRamAccessChip.Inputs.clockLow, circuit_norm]

def view (last : Bool) : TransitionView (stateChannel (p := p)) where
  component := ⟨HintReadWordChip.circuit last⟩
  edge env :=
    let input := valueFromOffset Inputs 0 env
    (input.previous, input.next)
  interactions := by
    intro env
    simp only [Operations.interactionValuesWith, Component.interactionsWith_eq,
      Component.rowOperations, HintReadWordChip.circuit]
    rw [main_state_interactions]
    simp only [List.map_cons, List.map_nil, Channel.eval_pulled, Channel.eval_pushed,
      eval_previous, eval_next, eval_varFromOffset_valueFromOffset]

def variants : List Bool := [false, true]

abbrev Row := Bool × Environment (ZMod p)

def rowInput (row : Row (p := p)) : Inputs (ZMod p) := valueFromOffset Inputs 0 row.2

def edge (row : Row (p := p)) : State (ZMod p) × State (ZMod p) :=
  ((rowInput row).previous, (rowInput row).next)

def context (state : State (ZMod p)) := (state.clk_high, state.clk_low, state.pointer)

theorem rows_spec (tables : List (Table (ZMod p)))
    (aligned : List.Forall₂ (fun last table => (view last).component = table.component) variants tables)
    (valid : ∀ table ∈ tables, table.Spec) :
    ∀ row ∈ TransitionView.readIndexedRows variants tables, Spec row.1 (rowInput row) := by
  have alignment : List.Forall₂ (fun view table => view.component = table.component)
      (variants.map view) tables := by
    simpa only [List.forall₂_map_left_iff] using aligned
  exact TransitionView.readIndexedRows_spec variants view tables alignment valid

theorem rows_balanced (tables : List (Table (ZMod p)))
    (initial final : State (ZMod p))
    (aligned : List.Forall₂ (fun last table => (view last).component = table.component)
      variants tables)
    (balanced : BalancedInteractions
      ([stateChannel.pushedValue initial, stateChannel.pulledValue final] ++
        tables.flatMap (·.interactionsWith stateChannel.toRaw))) :
    EndpointBalanced (↑(TransitionView.readIndexedRows variants tables)) edge initial final := by
  let rows := TransitionView.readIndexedRows variants tables
  have alignment : List.Forall₂ (fun view table => view.component = table.component)
      (variants.map view) tables := by
    simpa only [List.forall₂_map_left_iff] using aligned
  have projected := TransitionView.readRows_interactions
    (variants.map view) tables alignment
  rw [TransitionView.readRows_eq_indexed] at projected
  simp only [List.flatMap_map] at projected
  rw [projected] at balanced
  change BalancedInteractions (stateChannel.transitionLedger initial final rows edge) at balanced
  have endpoints := (stateChannel.transitionLedger_balanced_iff initial final rows edge).mp balanced
  simpa only [EndpointBalanced, Multiset.map_coe, Multiset.cons_coe, Multiset.coe_eq_coe]
    using endpoints.2

omit [Fact (2 ^ 25 < p)] in
private theorem indices_of_walk {R V : Type*} (edge : R → V × V) (index : V → ℕ)
    (initial final : V) (path : List R) (walk : Walk.IsWalk edge initial final path)
    (step : ∀ row ∈ path, index (edge row).2 = index (edge row).1 + 1) :
    index final = index initial + path.length ∧
      path.map (fun row => index (edge row).1) = List.range' (index initial) path.length := by
  induction path generalizing initial with
  | nil =>
    change initial = final at walk
    subst final
    simp
  | cons row rest ih =>
    obtain ⟨source, tail⟩ := walk
    have successor := step row (List.mem_cons_self ..)
    rw [source] at successor
    have result := ih _ tail (fun other member => step other (List.mem_cons_of_mem _ member))
    refine ⟨by simp only [List.length_cons]; omega, ?_⟩
    rw [List.map_cons, source, result.2, successor, List.length_cons, List.range'_succ]

omit [Fact (2 ^ 25 < p)] in
private theorem context_of_walk {R V C : Type*} (edge : R → V × V) (context : V → C)
    (initial final : V) (path : List R) (walk : Walk.IsWalk edge initial final path)
    (preserve : ∀ row ∈ path, context (edge row).2 = context (edge row).1) :
    context final = context initial ∧ ∀ row ∈ path, context (edge row).1 = context initial := by
  induction path generalizing initial with
  | nil =>
    change initial = final at walk
    subst final
    simp
  | cons row rest ih =>
    obtain ⟨source, tail⟩ := walk
    have same := preserve row (List.mem_cons_self ..)
    rw [source] at same
    have result := ih _ tail (fun other member => preserve other (List.mem_cons_of_mem _ member))
    refine ⟨result.1.trans same, ?_⟩
    intro other member
    rcases List.mem_cons.mp member with rfl | member
    · rw [source]
    · exact (result.2 other member).trans same

omit [Fact (2 ^ 25 < p)] in
private theorem successor_of_spec (last : Bool) (input : Inputs (ZMod p)) (valid : Spec last input) :
    Address.toNat input.next.index = Address.toNat input.previous.index + 1 := valid.2.2.2.2.2.1

omit [Fact (2 ^ 25 < p)] in
private theorem ranked_cover {R V C : Type*} (edge : R → V × V) (index : V → ℕ) (context : V → C)
    (rows : List R) (initial final : V) (balance : EndpointBalanced (↑rows) edge initial final)
    (successors : ∀ row ∈ rows, index (edge row).2 = index (edge row).1 + 1)
    (preserve : ∀ row ∈ rows, context (edge row).2 = context (edge row).1) :
    ∃ path : List R, path.Perm rows ∧ Walk.IsWalk edge initial final path ∧
      index final = index initial + path.length ∧
      path.map (fun row => index (edge row).1) = List.range' (index initial) path.length ∧
      context final = context initial ∧ ∀ row ∈ path, context (edge row).1 = context initial := by
  obtain ⟨path, walk, exhaustive⟩ := exists_exhaustiveTrail_of_endpointBalanced
    (↑rows) edge index initial final balance (by
      intro row member
      rw [successors row (Multiset.mem_coe.mp member)]
      omega)
  have perm : path.Perm rows := Multiset.coe_eq_coe.mp exhaustive
  have indices := indices_of_walk edge index initial final path walk
    (fun row member => successors row (perm.mem_iff.mp member))
  have same := context_of_walk edge context initial final path walk
    (fun row member => preserve row (perm.mem_iff.mp member))
  exact ⟨path, perm, walk, indices.1, indices.2, same.1, same.2⟩

omit [Fact (2 ^ 25 < p)] in
private theorem context_preserve (input : Inputs (ZMod p)) : context input.next = context input.previous := rfl

/-- Every physical word row occurs exactly once, with successive indices and a fixed call/node.
The hypotheses concern actual table specifications and ledger balance, not a supplied row order. -/
theorem ordered_cover (tables : List (Table (ZMod p))) (initial final : State (ZMod p))
    (aligned : List.Forall₂ (fun last table => (view last).component = table.component) variants tables)
    (valid : ∀ table ∈ tables, table.Spec)
    (balanced : BalancedInteractions
      ([stateChannel.pushedValue initial, stateChannel.pulledValue final] ++
        tables.flatMap (·.interactionsWith stateChannel.toRaw))) :
    ∃ path : List (Row (p := p)),
      path.Perm (TransitionView.readIndexedRows variants tables) ∧
      Walk.IsWalk edge initial final path ∧
      Address.toNat final.index = Address.toNat initial.index + path.length ∧
      path.map (fun row => Address.toNat (rowInput row).index) =
        List.range' (Address.toNat initial.index) path.length ∧
      context final = context initial ∧
      ∀ row ∈ path, context (rowInput row).previous = context initial := by
  apply ranked_cover edge (fun state : State (ZMod p) => Address.toNat state.index) context
    (TransitionView.readIndexedRows variants tables) initial final
    (rows_balanced tables initial final aligned balanced)
  · intro row member
    exact successor_of_spec row.1 (rowInput row) (rows_spec tables aligned valid row member)
  · intro row _
    exact context_preserve (rowInput row)

/-- Zero-based endpoints force exactly the full count, independently of physical row order. -/
theorem complete_indices (tables : List (Table (ZMod p))) (initial final : State (ZMod p))
    (aligned : List.Forall₂ (fun last table => (view last).component = table.component) variants tables)
    (valid : ∀ table ∈ tables, table.Spec)
    (balanced : BalancedInteractions
      ([stateChannel.pushedValue initial, stateChannel.pulledValue final] ++
        tables.flatMap (·.interactionsWith stateChannel.toRaw)))
    (zero : Address.toNat initial.index = 0) :
    ((TransitionView.readIndexedRows variants tables).map fun row => Address.toNat (rowInput row).index).Perm
      (List.range (Address.toNat final.index)) := by
  obtain ⟨path, perm, _, count, indices, _⟩ := ordered_cover tables initial final aligned valid balanced
  rw [zero, Nat.zero_add] at count
  rw [zero, ← List.range_eq_range'] at indices
  rw [count, ← indices]
  exact (perm.map _).symm

/-- A constructed complete cursor walk balances the physical tables under Clean's count guard. -/
theorem balanced_of_walk (tables : List (Table (ZMod p))) (initial final : State (ZMod p))
    (aligned : List.Forall₂ (fun last table => (view last).component = table.component) variants tables)
    (path : List (Row (p := p))) (perm : path.Perm (TransitionView.readIndexedRows variants tables))
    (walk : Walk.IsWalk edge initial final path) (bound : 2 * (path.length + 1) < p) :
    BalancedInteractions
      ([stateChannel.pushedValue initial, stateChannel.pulledValue final] ++
        tables.flatMap (·.interactionsWith stateChannel.toRaw)) := by
  have alignment : List.Forall₂ (fun view table => view.component = table.component)
      (variants.map view) tables := by
    simpa only [List.forall₂_map_left_iff] using aligned
  have projected := TransitionView.readRows_interactions (variants.map view) tables alignment
  rw [TransitionView.readRows_eq_indexed] at projected
  simp only [List.flatMap_map] at projected
  rw [projected]
  change BalancedInteractions (stateChannel.transitionLedger initial final
    (TransitionView.readIndexedRows variants tables) edge)
  apply (stateChannel.transitionLedger_balanced_iff _ _ _ _).mpr
  refine ⟨Or.inl ?_, ?_⟩
  · simpa only [← perm.length_eq, ZMod.ringChar_zmod_n] using bound
  · have endpoints := endpointBalanced_of_isWalk edge walk
    have endpointPerm : (initial :: path.map (fun row => (edge row).2)).Perm
        (final :: path.map (fun row => (edge row).1)) := by
      simpa only [EndpointBalanced, Multiset.map_coe, Multiset.cons_coe, Multiset.coe_eq_coe] using endpoints
    exact ((perm.map (fun row => (edge row).2)).cons initial).symm.trans
      (endpointPerm.trans ((perm.map (fun row => (edge row).1)).cons final))

end SP1Clean.Soundness.HintReadCoverage
