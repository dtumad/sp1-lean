import SP1Clean.Soundness.HostHintReadCoverage
import SP1Clean.Proofs.Chips.HostHintLengthChip.Guarded

/-! # Queue chronology from the physical HINT_LEN and HINT_READ tables

The implemented queue handlers each replace one complete queue token, including its allocation
frontier. Strict event clocks turn their actual balanced ledger into an exhaustive ordered path.
Boundary messages are explicit here: a ledger containing only these transitions can balance
only when all three tables are empty. Source-record providers do not supply queue endpoints.
The path retains head/frontier continuity; semantic queue truth and future allocating handlers
must be connected by the enclosing execution argument.
-/

namespace SP1Clean.Soundness.HostQueueOrder

open Circuit Air.Flat HostHintQueue RankedGrounding

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

omit [Fact (2 ^ 25 < p)] in
private theorem eval_read_queue (env : Environment (ZMod p)) (row : Var HostHintReadChip.Inputs (ZMod p)) :
    eval env row.previous = (eval env row).previous ∧ eval env row.next = (eval env row).next := by
  rcases row with ⟨call, previous, node, span, lastIndex, lastValue⟩
  cases call
  cases previous
  cases node
  simp only [HostHintReadChip.Inputs.next, circuit_norm, and_self]

omit [Fact (2 ^ 25 < p)] in
private theorem eval_length_queue (env : Environment (ZMod p)) (row : Var HostHintLengthChip.Inputs (ZMod p)) :
    eval env row.previous = (eval env row).previous ∧ eval env row.next = (eval env row).next := by
  rcases row with ⟨call, previous, node⟩
  cases call
  cases previous
  simp only [HostHintLengthChip.Inputs.next, circuit_norm, and_self]

omit [Fact (2 ^ 25 < p)] in
theorem length_input (env : Environment (ZMod p)) :
    (valueFromOffset HostHintLengthChip.RowInput 0 env).1 = valueFromOffset HostHintLengthChip.Inputs 0 env := by
  have decoded := eval_varFromOffset_valueFromOffset HostHintLengthChip.RowInput 0 env
  rw [CircuitType.eval_var_provablePair] at decoded
  have payload := congrArg Prod.fst decoded
  change Eval.eval env (varFromOffset HostHintLengthChip.RowInput 0).1 = _ at payload
  simpa only [HostHintLengthChip.RowInput,varFromOffset_pair,eval_varFromOffset_valueFromOffset] using payload.symm

def readView : TransitionView (stateChannel (p := p)) where
  component := HostHintReadCoverage.handler
  edge env := let row := HostHintReadCoverage.input env; (row.previous, row.next)
  activity := HostHintReadCoverage.activity
  activity_binary env valid := (HostHintReadCoverage.decoded_activity env).symm ▸ valid.1
  activity_of_constraints env valid := Guarded.activity_of_constraints HostHintReadChip.circuit inferInstance
    (varFromOffset HostHintReadChip.RowInput 0) (size HostHintReadChip.RowInput) env ((Component.constraintsHold_iff env).mp valid)
  interactions env := by
    simp only [Operations.interactionValuesWith, Component.interactionsWith_eq]
    change ((Guarded.main HostHintReadChip.circuit inferInstance (varFromOffset HostHintReadChip.RowInput 0)).operations
      (size HostHintReadChip.RowInput)).interactionValuesWith stateChannel.toRaw env = _
    rw [Guarded.main_interactionValuesWith]
    change (((HostHintReadChip.main (varFromOffset HostHintReadChip.RowInput 0).1).operations (size HostHintReadChip.RowInput)).interactionValuesWith stateChannel.toRaw env).map _ = _
    rw [HostHintReadChip.queue_values, (eval_read_queue _ _).1, (eval_read_queue _ _).2,HostHintReadCoverage.decoded_input]
    simp [HostHintReadCoverage.activity,Channel.pulledValue,Channel.pushedValue,Channel.pulledIfValue,Channel.pushedIfValue]

def lengthView (empty : Bool) : TransitionView (stateChannel (p := p)) where
  component := HostHintLengthChip.component empty
  edge env := let row := valueFromOffset HostHintLengthChip.Inputs 0 env; (row.previous, row.next)
  activity := (varFromOffset HostHintLengthChip.RowInput 0).2
  activity_binary := by
    intro env valid
    rw [Guarded.eval_activity, eval_varFromOffset_valueFromOffset]
    exact valid.1
  activity_of_constraints env valid := Guarded.activity_of_constraints (HostHintLengthChip.circuit empty) inferInstance
    (varFromOffset HostHintLengthChip.RowInput 0) (size HostHintLengthChip.RowInput) env ((Component.constraintsHold_iff env).mp valid)
  interactions env := by
    simp only [Operations.interactionValuesWith, Component.interactionsWith_eq]
    change ((Guarded.main (HostHintLengthChip.circuit empty) inferInstance (varFromOffset HostHintLengthChip.RowInput 0)).operations
      (size HostHintLengthChip.RowInput)).interactionValuesWith stateChannel.toRaw env = _
    rw [Guarded.main_interactionValuesWith]
    change (((HostHintLengthChip.main empty (varFromOffset HostHintLengthChip.RowInput 0).1).operations (size HostHintLengthChip.RowInput)).interactionValuesWith stateChannel.toRaw env).map _ = _
    rw [HostHintLengthChip.state_values, (eval_length_queue _ _).1, (eval_length_queue _ _).2]
    simp only [HostHintLengthChip.RowInput,varFromOffset_pair, eval_varFromOffset_valueFromOffset, List.map_cons,List.map_nil,Channel.pulledValue,Channel.pushedValue,Channel.pulledIfValue,Channel.pushedIfValue,mul_one]

/-- The current queue-changing/observing registry; allocating WRITE/hook handlers remain open. -/
abbrev Index := Option Bool

def indices : List Index := [none, some false, some true]

def view : Index → TransitionView (stateChannel (p := p))
  | none => readView
  | some empty => lengthView empty

abbrev Row := Index × Environment (ZMod p)

def edge (row : Row (p := p)) : State (ZMod p) × State (ZMod p) := (view row.1).edge row.2

def time (state : State (ZMod p)) : ℕ := Semantics.clkNat state.clk_high state.clk_low

omit [Fact (2 ^ 25 < p)] in
private theorem read_strict (input : HostHintReadChip.Inputs (ZMod p)) (valid : HostHintReadChip.Spec input) :
    time input.previous < time input.next := valid.2.2.2.2.2.2.1.2.2.2.2

omit [Fact (2 ^ 25 < p)] in
private theorem length_strict (empty : Bool) (input : HostHintLengthChip.Inputs (ZMod p))
    (valid : HostHintLengthChip.Spec empty input) : time input.previous < time input.next := valid.2.1.2.2.2.2

theorem view_strict (index : Index) (env : Environment (ZMod p)) (valid : (view index).component.Spec env)
    (active : env (view index).activity = 1) :
    time ((view index).edge env).1 < time ((view index).edge env).2 := by
  cases index with
  | none =>
    simp only [view,readView] at valid active ⊢
    exact read_strict (HostHintReadCoverage.input env) (HostHintReadCoverage.active_spec env valid active)
  | some empty =>
    simp only [view,lengthView] at valid active ⊢
    change env (varFromOffset HostHintLengthChip.RowInput 0).2 = 1 at active
    rw [Guarded.eval_activity,eval_varFromOffset_valueFromOffset] at active
    have sem : HostHintLengthChip.Spec empty (valueFromOffset HostHintLengthChip.RowInput 0 env).1 := valid.2 active
    rw [length_input] at sem
    exact length_strict empty _ sem

/-- Physical queue rows with a checked activity of one, in original table order. -/
def activeRows (tables : List (Table (ZMod p))) := TransitionView.readIndexedActiveRows indices view tables

theorem rows_spec (tables : List (Table (ZMod p)))
    (aligned : List.Forall₂ (fun index table => (view index).component = table.component) indices tables)
    (valid : ∀ table ∈ tables, table.Spec) :
    ∀ row ∈ activeRows tables, (view row.1).component.Spec row.2 := by
  apply TransitionView.readIndexedActiveRows_spec indices view tables _ valid
  simpa only [List.forall₂_map_left_iff] using aligned

/-- Every occurrence of a physical queue row contributes exactly one complete token pair. -/
theorem interactions (tables : List (Table (ZMod p)))
    (aligned : List.Forall₂ (fun index table => (view index).component = table.component) indices tables) :
    tables.flatMap (·.interactionsWith stateChannel.toRaw) =
      (TransitionView.readIndexedRows indices tables).flatMap (fun (row : Row (p := p)) =>
        [stateChannel.pulledIfValue (row.2 (view row.1).activity) (edge row).1, stateChannel.pushedIfValue (row.2 (view row.1).activity) (edge row).2]) := by
  rw [TransitionView.readIndexedRows_interactions indices (fun index => (view index).component) tables _ aligned]
  apply List.flatMap_congr
  intro row _
  have effect := (view row.1).interactions row.2
  exact effect

/-- Actual token balance orders all queue rows, retaining head and allocation-frontier continuity.
The enclosing verifier must supply and bind both endpoint messages. -/
theorem ordered (tables : List (Table (ZMod p)))
    (aligned : List.Forall₂ (fun index table => (view index).component = table.component) indices tables)
    (valid : ∀ table ∈ tables, table.Spec) (initial final : State (ZMod p))
    (balanced : BalancedInteractions ([stateChannel.pushedValue initial, stateChannel.pulledValue final] ++
      tables.flatMap (·.interactionsWith stateChannel.toRaw))) :
    ∃ path : List (Row (p := p)), path.Perm (activeRows tables) ∧ Walk.IsWalk edge initial final path := by
  classical
  have endpoints := TransitionView.active_endpoints_perm indices view tables initial final
    (by simpa only [List.forall₂_map_left_iff] using aligned) valid balanced
  have balance : EndpointBalanced (↑(activeRows tables)) edge initial final := by
    simpa only [activeRows,edge,EndpointBalanced, Multiset.map_coe, Multiset.cons_coe, Multiset.coe_eq_coe] using endpoints
  obtain ⟨path, walk, exhaustive⟩ := exists_exhaustiveTrail_of_endpointBalanced
    (↑(activeRows tables)) edge time initial final
    balance (fun row member =>
      view_strict row.1 row.2 (rows_spec tables aligned valid row (Multiset.mem_coe.mp member))
        (TransitionView.mem_readIndexedActiveRows.mp (Multiset.mem_coe.mp member)).2)
  exact ⟨path, Multiset.coe_eq_coe.mp exhaustive, walk⟩

omit [Fact p.Prime] [Fact (2 ^ 25 < p)] in
private theorem nil_of_strict_balance {R V : Type*} (edge : R → V × V) (rank : V → ℕ) (rows : List R)
    (closed : (rows.map (fun row => (edge row).2)).Perm (rows.map (fun row => (edge row).1)))
    (strict : ∀ row ∈ rows, rank (edge row).1 < rank (edge row).2) : rows = [] := by
  classical
  cases rows with
  | nil => rfl
  | cons row rest =>
    have endpoints : EndpointBalanced (↑(row :: rest)) edge (edge row).1 (edge row).1 := by
      exact Quot.sound (closed.cons (edge row).1)
    have empty := eq_zero_of_endpointBalanced_self _ edge rank
      (fun row member => strict row (Multiset.mem_coe.mp member)) endpoints
    simp at empty

/-- Omitting queue endpoints forbids every active HINT_LEN/HINT_READ row; record sources alone
cannot establish non-vacuity of the complete ensemble relation. -/
theorem rows_nil_of_balanced (tables : List (Table (ZMod p)))
    (aligned : List.Forall₂ (fun index table => (view index).component = table.component) indices tables)
    (valid : ∀ table ∈ tables, table.Spec)
    (balanced : BalancedInteractions (tables.flatMap (·.interactionsWith stateChannel.toRaw))) :
    activeRows tables = [] := by
  classical
  have raw := balanced.filter_nonzero
  rw [interactions tables aligned] at raw
  let phys := TransitionView.readIndexedRows indices tables
  have binary (row : Row (p := p)) (m : row ∈ phys) : IsBool (row.2 (view (p := p) row.1).activity) := (view row.1).activity_binary row.2
    (TransitionView.readIndexedRows_spec indices view tables (by simpa only [List.forall₂_map_left_iff] using aligned) valid row m)
  rw [stateChannel.gatedPairs_filter_nonzero phys (fun r => r.2 (view r.1).activity) edge binary] at raw
  have closed := (stateChannel.pairedLedger_balanced_iff (activeRows tables) edge).mp raw
  exact nil_of_strict_balance edge time _ closed (fun row member => view_strict row.1 row.2
    (rows_spec tables aligned valid row member) (TransitionView.mem_readIndexedActiveRows.mp member).2)

/-- The present queue clock encoding cannot represent a queue handler at event time zero.
This agrees with SP1's active 1-mod-8 profile; range-only source checks also admit identities at zero. -/
theorem positive_event_time (index : Index) (env : Environment (ZMod p))
    (valid : (view index).component.Spec env) (active : env (view index).activity = 1) : 0 < time ((view index).edge env).2 :=
  Nat.lt_of_le_of_lt (Nat.zero_le _) (view_strict index env valid active)

end SP1Clean.Soundness.HostQueueOrder
