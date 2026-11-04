import SP1Clean.Proofs.Chips.HintReadWordChip.Ledger
import SP1Clean.Soundness.RankedGrounding
import ToClean.Air.TransitionView
import ToClean.Air.MessageFilter

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

/-- The installed word-transfer component, including Boolean physical padding activity. -/
def component (last : Bool) : Component (ZMod p) where
  circuit := HintReadWordChip.circuit last
  generation := HintReadWordChip.generation last
  Assumptions := (HintReadWordChip.circuit last).Assumptions

def view (last : Bool) : TransitionView (stateChannel (p := p)) where
  component := component last
  activity := (varFromOffset RowInput 0).2
  edge env :=
    let input := valueFromOffset RowInput 0 env
    (input.1.previous, input.1.next)
  activity_binary := by
    intro env valid
    rw [Guarded.eval_activity, eval_varFromOffset_valueFromOffset]
    exact valid.1
  activity_of_constraints := by
    intro env valid
    rw [Component.constraintsHold_iff] at valid
    exact Guarded.activity_of_constraints (activeCircuit last) inferInstance
      (varFromOffset RowInput 0) (size RowInput) env valid
  interactions := by
    intro env
    simp only [Operations.interactionValuesWith, Component.interactionsWith_eq,
      Component.rowOperations]
    change (((circuit last).main (varFromOffset RowInput 0)).operations
      (size RowInput)).interactionValuesWith stateChannel.toRaw env = _
    rw [guarded_state_values, eval_previous, eval_next]
    have decoded := eval_varFromOffset_valueFromOffset RowInput 0 env
    rw [CircuitType.eval_var_provablePair] at decoded
    have payload := congrArg Prod.fst decoded
    change Eval.eval env (varFromOffset RowInput 0).1 =
      (valueFromOffset RowInput 0 env).1 at payload
    rw [payload]

theorem view_activity (last : Bool) :
    (view (p := p) last).activity = (varFromOffset RowInput 0).2 := by
  simp only [view]

def variants : List Bool := [false, true]

abbrev Row := Bool × Environment (ZMod p)

def rowInput (row : Row (p := p)) : Inputs (ZMod p) := (valueFromOffset RowInput 0 row.2).1

omit [Fact (2 ^ 25 < p)] in
theorem eval_rowInput (row : Row (p := p)) :
    Eval.eval row.2 (varFromOffset (F := ZMod p) RowInput 0).1 = rowInput row := by
  have decoded := eval_varFromOffset_valueFromOffset RowInput 0 row.2
  rw [CircuitType.eval_var_provablePair] at decoded
  exact congrArg Prod.fst decoded

/-- The physical activity cell is independent of the semantic word payload. -/
def rowActivity (row : Row (p := p)) : ZMod p := row.2 (varFromOffset field (size Inputs))

theorem active_rows (tables : List (Table (ZMod p))) :
    TransitionView.readIndexedActiveRows variants view tables =
      (TransitionView.readIndexedRows variants tables).filter
        (fun row => @decide (rowActivity row = 1) (FiniteField.instDecidableEq _ _)) := by
  simp only [TransitionView.readIndexedActiveRows, view_activity, rowActivity,
    varFromOffset_pair, Nat.zero_add]
  congr 1
  funext row
  exact congrArg (@decide _) (Subsingleton.elim _ _)

def edge (row : Row (p := p)) : State (ZMod p) × State (ZMod p) :=
  ((rowInput row).previous, (rowInput row).next)

private theorem view_edge (row : Row (p := p)) : (view row.1).edge row.2 = edge row := by
  simp only [view, edge, rowInput]

private theorem view_rowActivity (row : Row (p := p)) : row.2 (view row.1).activity = rowActivity row := by
  simp only [view_activity, rowActivity, varFromOffset_pair, Nat.zero_add]

/-- Read a channel at each original row environment, preserving repeated and inactive occurrences. -/
noncomputable def interactions (rows : List (Row (p := p))) (channel : RawChannel (ZMod p)) :
    List (Interaction (ZMod p)) :=
  rows.flatMap fun row => (view row.1).component.operations.interactionValuesWith channel row.2

theorem cursor_interactions (rows : List (Row (p := p))) :
    interactions rows stateChannel.toRaw = rows.flatMap (fun row =>
      [stateChannel.pulledIfValue (rowActivity row) (edge row).1,
        stateChannel.pushedIfValue (rowActivity row) (edge row).2]) := by
  apply List.flatMap_congr
  intro row _
  simpa only [view_rowActivity, view_edge] using (view row.1).interactions row.2

theorem interactions_readIndexedRows (tables : List (Table (ZMod p)))
    (aligned : List.Forall₂ (fun last table => (view last).component = table.component) variants tables)
    (channel : RawChannel (ZMod p)) :
    interactions (TransitionView.readIndexedRows variants tables) channel =
      tables.flatMap (·.interactionsWith channel) :=
  (TransitionView.readIndexedRows_interactions variants (fun last => (view last).component)
    tables channel aligned).symm

theorem mem_active_rows {tables : List (Table (ZMod p))} {row : Row (p := p)} :
    row ∈ TransitionView.readIndexedActiveRows variants view tables ↔
      row ∈ TransitionView.readIndexedRows variants tables ∧ rowActivity row = 1 := by
  rw [TransitionView.mem_readIndexedActiveRows, view_rowActivity]

/-- Active semantic occurrences at the data environment of their source rows. -/
def activeRows (rows : List (Row (p := p))) : List (Row (p := p)) :=
  rows.filter fun row => @decide (rowActivity row = 1) (FiniteField.instDecidableEq _ _)

theorem activeRows_readIndexedRows (tables : List (Table (ZMod p))) :
    activeRows (TransitionView.readIndexedRows variants tables) =
      TransitionView.readIndexedActiveRows variants view tables := by
  rw [active_rows]
  simp only [activeRows]

/-- The exact physical cursor ledger decoded at the original committed data. -/
theorem physical_ledger (tables : List (Table (ZMod p)))
    (aligned : List.Forall₂ (fun last table => (view last).component = table.component) variants tables) :
    tables.flatMap (·.interactionsWith stateChannel.toRaw) =
      (TransitionView.readIndexedRows variants tables).flatMap (fun row =>
        [stateChannel.pulledIfValue (rowActivity row) (edge row).1,
          stateChannel.pushedIfValue (rowActivity row) (edge row).2]) := by
  have alignment : List.Forall₂ (fun view table => view.component = table.component)
      (variants.map view) tables := by
    simpa only [List.forall₂_map_left_iff] using aligned
  have projected := TransitionView.readRows_interactions (variants.map view) tables alignment
  rw [TransitionView.readRows_eq_indexed] at projected
  simpa only [List.flatMap_map, view_rowActivity, view_edge] using projected

/-- The physical guard is Boolean before any semantic or channel authentication. -/
theorem row_activity_binary (row : Row (p := p))
    (valid : (view row.1).component.operations.ConstraintsHold row.2) :
    rowActivity row = 0 ∨ rowActivity row = 1 := by
  simpa only [view_rowActivity] using (view row.1).activity_of_constraints row.2 valid

/-- Active rows retain the child constraints at the guarded row's actual witness offset. -/
theorem active_constraints (row : Row (p := p)) (active : rowActivity row = 1)
    (valid : (view row.1).component.operations.ConstraintsHold row.2) :
    ((HintReadWordChip.main row.1 (varFromOffset RowInput 0).1).operations
      (size RowInput)).ConstraintsHold row.2 := by
  rw [Component.constraintsHold_iff] at valid
  apply Guarded.constraints_of_active (activeCircuit row.1) inferInstance
    (varFromOffset RowInput 0) (size RowInput) row.2 _ valid
  simpa only [varFromOffset_pair, Nat.zero_add, rowActivity] using active

/-- Active rows retain each child channel guarantee without assuming other channels. -/
theorem active_channelGuarantees (row : Row (p := p)) (channel : RawChannel (ZMod p))
    (active : rowActivity row = 1)
    (valid : (view row.1).component.operations.ChannelGuarantees channel row.2) :
    ((HintReadWordChip.main row.1 (varFromOffset RowInput 0).1).operations
      (size RowInput)).ChannelGuarantees channel row.2 := by
  rw [Component.channelGuarantees_iff] at valid
  apply Guarded.channelGuarantees_of_active (activeCircuit row.1) inferInstance
    (varFromOffset RowInput 0) (size RowInput) row.2 channel _ valid
  simpa only [varFromOffset_pair, Nat.zero_add, rowActivity] using active

def context (state : State (ZMod p)) := (state.clk_high, state.clk_low, state.pointer)

theorem rows_spec (tables : List (Table (ZMod p)))
    (aligned : List.Forall₂ (fun last table => (view last).component = table.component) variants tables)
    (valid : ∀ table ∈ tables, table.Spec) :
    ∀ row ∈ TransitionView.readIndexedActiveRows variants view tables, Spec row.1 (rowInput row) := by
  have alignment : List.Forall₂ (fun view table => view.component = table.component)
      (variants.map view) tables := by
    simpa only [List.forall₂_map_left_iff] using aligned
  intro row member
  have checked := TransitionView.readIndexedActiveRows_spec variants view tables alignment valid row member
  have active := (TransitionView.mem_readIndexedActiveRows.mp member).2
  rw [view_activity] at active
  rw [Guarded.eval_activity, eval_varFromOffset_valueFromOffset] at active
  exact checked.2 active

/-- Actual row constraints establish Boolean activity before any channel authentication. -/
theorem rows_activity_binary (tables : List (Table (ZMod p)))
    (aligned : List.Forall₂ (fun last table => (view last).component = table.component) variants tables)
    (valid : ∀ table ∈ tables, table.Constraints) :
    ∀ row ∈ TransitionView.readIndexedRows variants tables,
      rowActivity row = 0 ∨ rowActivity row = 1 := by
  intro row member
  exact row_activity_binary row
    (TransitionView.readIndexedRows_constraints variants (fun last => (view last).component)
      tables aligned valid row member)

/-- Coverage uses authenticated words and exact index/address successors. The prior RAM values
and timestamps are separate facts to be established by Memory grounding. -/
structure Steps (rows : List (Row (p := p))) : Prop where
  /-- Every retained physical occurrence has Boolean activity. -/
  binary : ∀ row ∈ rows, rowActivity row = 0 ∨ rowActivity row = 1
  /-- Only active rows are semantic word transfers. -/
  step : ∀ row ∈ activeRows rows, HintReadStep.Spec row.1 ((rowInput row).step row.1)

theorem steps_of_specs (tables : List (Table (ZMod p)))
    (aligned : List.Forall₂ (fun last table => (view last).component = table.component) variants tables)
    (valid : ∀ table ∈ tables, table.Spec) :
    Steps (TransitionView.readIndexedRows variants tables) where
  binary row member := by
    simpa only [view_rowActivity] using (view row.1).activity_binary row.2
      (TransitionView.readIndexedRows_spec variants view tables
        (by simpa only [List.forall₂_map_left_iff] using aligned) valid row member)
  step row member := (rows_spec tables aligned valid row
    (by rwa [← activeRows_readIndexedRows])).2

omit [Fact (2 ^ 25 < p)] in
/-- Selecting one call retains its word-step facts at the original data. -/
theorem Steps.select {rows : List (Row (p := p))}
    (valid : Steps rows) (keep : Row (p := p) → Bool) : Steps (rows.filter keep) := by
  constructor
  · intro row member
    exact valid.binary row (List.mem_filter.mp member).1
  · intro row member
    obtain ⟨selected, active⟩ := List.mem_filter.mp member
    exact valid.step row (List.mem_filter.mpr ⟨(List.mem_filter.mp selected).1, active⟩)

omit [Fact (2 ^ 25 < p)] in
theorem rows_balanced (rows : List (Row (p := p))) (initial final : State (ZMod p))
    (valid : Steps rows)
    (balanced : BalancedInteractions (stateChannel.gatedTransitionLedger initial final rows rowActivity edge)) :
    EndpointBalanced (↑(activeRows rows)) edge initial final := by
  have endpoints := (stateChannel.gatedTransitionLedger_balanced_iff initial final rows rowActivity edge
    valid.binary).mp balanced
  exact Quot.sound endpoints

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
private theorem successor_of_spec (last : Bool) (input : Inputs (ZMod p))
    (valid : HintReadStep.Spec last (input.step last)) :
    Address.toNat input.next.index = Address.toNat input.previous.index + 1 := valid.2.2.2.2.1

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

omit [Fact p.Prime] [Fact (2 ^ 25 < p)] in
private theorem nil_of_closed {R V : Type*} (edge : R → V × V) (index : V → ℕ) (rows : List R)
    (closed : (rows.map (fun row => (edge row).2)).Perm (rows.map (fun row => (edge row).1)))
    (successors : ∀ row ∈ rows, index (edge row).2 = index (edge row).1 + 1) : rows = [] := by
  classical
  cases rows with
  | nil => rfl
  | cons row rest =>
    have balanced : EndpointBalanced (↑(row :: rest)) edge (edge row).1 (edge row).1 := by
      simpa only [EndpointBalanced, Multiset.map_coe, Multiset.cons_coe, Multiset.coe_eq_coe] using
        closed.cons (edge row).1
    have empty := eq_zero_of_endpointBalanced_self (↑(row :: rest)) edge index
      (fun current member => by rw [successors current (Multiset.mem_coe.mp member)]; omega) balanced
    simp at empty

omit [Fact (2 ^ 25 < p)] in
/-- A balanced set of consumers without any handler endpoints must be empty. -/
theorem rows_nil_of_balanced (rows : List (Row (p := p))) (valid : Steps rows)
    (balanced : BalancedInteractions (rows.flatMap (fun row =>
      [stateChannel.pulledIfValue (rowActivity row) (edge row).1,
        stateChannel.pushedIfValue (rowActivity row) (edge row).2]))) : activeRows rows = [] := by
  have active := balanced.filter_nonzero
  rw [stateChannel.gatedPairs_filter_nonzero _ rowActivity edge valid.binary] at active
  have closed := (stateChannel.pairedLedger_balanced_iff _ edge).mp active
  exact nil_of_closed edge (fun state : State (ZMod p) => Address.toNat state.index)
    _ (by simpa only [activeRows] using closed) (fun row member => successor_of_spec row.1 (rowInput row) (valid.step row member))

omit [Fact (2 ^ 25 < p)] in
/-- Every active word row occurs exactly once, with successive indices and a fixed call/node.
Authenticated word-step contracts and ledger balance determine the order internally. -/
theorem ordered_cover (rows : List (Row (p := p))) (initial final : State (ZMod p))
    (valid : Steps rows)
    (balanced : BalancedInteractions
      (stateChannel.gatedTransitionLedger initial final rows rowActivity edge)) :
    ∃ path : List (Row (p := p)),
      path.Perm (activeRows rows) ∧
      Walk.IsWalk edge initial final path ∧
      Address.toNat final.index = Address.toNat initial.index + path.length ∧
      path.map (fun row => Address.toNat (rowInput row).index) =
        List.range' (Address.toNat initial.index) path.length ∧
      context final = context initial ∧
      ∀ row ∈ path, context (rowInput row).previous = context initial := by
  apply ranked_cover edge (fun state : State (ZMod p) => Address.toNat state.index) context
    (activeRows rows) initial final
    (rows_balanced rows initial final valid balanced)
  · intro row member
    exact successor_of_spec row.1 (rowInput row) (valid.step row member)
  · intro row _
    exact context_preserve (rowInput row)

omit [Fact p.Prime] [Fact (2 ^ 25 < p)] in
private theorem lower_of_walk {R V : Type*} (edge : R → V × V) (address : V → ℕ)
    (initial final : V) (path : List R) (walk : Walk.IsWalk edge initial final path)
    (steps : ∀ row ∈ path, address (edge row).1 ≤ address (edge row).2) :
    ∀ row ∈ path, address initial ≤ address (edge row).1 := by
  induction path generalizing initial with
  | nil => simp
  | cons row rest ih =>
    obtain ⟨source, tail⟩ := walk
    intro other member
    rcases List.mem_cons.mp member with rfl | member
    · rw [source]
    · exact le_trans (by rw [← source]; exact steps row (List.mem_cons_self ..))
        (ih _ tail (fun r h => steps r (List.mem_cons_of_mem _ h)) other member)

omit [Fact (2 ^ 25 < p)] in
/-- Every consumer address is at least the handler's start address. This needs only the
authenticated successor constraints, independently of the prior RAM word or timestamp. -/
theorem address_lower (rows : List (Row (p := p))) (initial final : State (ZMod p))
    (valid : Steps rows)
    (balanced : BalancedInteractions
      (stateChannel.gatedTransitionLedger initial final rows rowActivity edge)) :
    ∀ row ∈ activeRows rows,
      Address.toNat initial.address ≤ Address.toNat (rowInput row).address := by
  obtain ⟨path, perm, walk, _⟩ := ordered_cover rows initial final valid balanced
  have lower := lower_of_walk edge (fun state : State (ZMod p) => Address.toNat state.address)
    initial final path walk (by
      intro row member
      have advance := (valid.step row (perm.mem_iff.mp member)).2.2.2.2.2.2
      change Address.toNat (rowInput row).address ≤ Address.toNat (rowInput row).nextAddress
      change Address.toNat (rowInput row).nextAddress = Address.toNat (rowInput row).address + _ at advance
      omega)
  exact fun row member => lower row (perm.mem_iff.mpr member)

omit [Fact (2 ^ 25 < p)] in
/-- Zero-based endpoints force exactly the full count, independently of physical row order. -/
theorem complete_indices (rows : List (Row (p := p))) (initial final : State (ZMod p))
    (valid : Steps rows)
    (balanced : BalancedInteractions
      (stateChannel.gatedTransitionLedger initial final rows rowActivity edge))
    (zero : Address.toNat initial.index = 0) :
    ((activeRows rows).map fun row => Address.toNat (rowInput row).index).Perm
      (List.range (Address.toNat final.index)) := by
  obtain ⟨path, perm, _, count, indices, _⟩ := ordered_cover rows initial final valid balanced
  rw [zero, Nat.zero_add] at count
  rw [zero, ← List.range_eq_range'] at indices
  rw [count, ← indices]
  exact (perm.map _).symm

omit [Fact (2 ^ 25 < p)] in
/-- A constructed active cursor walk balances the physical tables under their original count guard. -/
theorem balanced_of_walk (rows : List (Row (p := p))) (initial final : State (ZMod p))
    (binary : ∀ row ∈ rows, rowActivity row = 0 ∨ rowActivity row = 1)
    (path : List (Row (p := p))) (perm : path.Perm (activeRows rows))
    (walk : Walk.IsWalk edge initial final path) :
    BalancedInteractions (stateChannel.gatedTransitionLedger initial final rows rowActivity edge) := by
  apply (stateChannel.gatedTransitionLedger_balanced_iff _ _ _ _ _ binary).mpr
  have endpoints := endpointBalanced_of_isWalk edge walk
  have endpointPerm : (initial :: path.map (fun row => (edge row).2)).Perm
      (final :: path.map (fun row => (edge row).1)) := by
    simpa only [EndpointBalanced, Multiset.map_coe, Multiset.cons_coe, Multiset.coe_eq_coe] using endpoints
  simpa only [activeRows] using ((perm.map (fun row => (edge row).2)).cons initial).symm.trans
    (endpointPerm.trans ((perm.map (fun row => (edge row).1)).cons final))

end SP1Clean.Soundness.HintReadCoverage
