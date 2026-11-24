import SP1Clean.Soundness.HostHintReadWrites
import ToClean.Air.MessageFilter

/-! # Per-call HINT_READ rows from one shared cursor ledger

Both ends of every handler and word row retain the same event clock. Selecting that clock in
the shared physical ledger therefore selects complete rows and preserves balance. A unique
handler clock leaves exactly one pair of endpoints. The instruction handoff must still derive
that uniqueness when the subsystem is installed; global balance alone cannot distinguish two
handlers at the same event. No row order or independently balanced per-call witness is assumed.
Selected rows retain their original environments and shared data. They are semantic views of
the committed tables; no new physical table or recomputed witness data is introduced.
-/

namespace SP1Clean.Soundness.HostHintReadPartition

open Circuit Air.Flat HostHintReadCoverage
open Semantics Semantics.HintQueue

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

def clock (state : HintReadWordChip.State (ZMod p)) : ZMod p × ZMod p :=
  (state.clk_high, state.clk_low)

def callClock (env : Environment (ZMod p)) : ZMod p × ZMod p := clock (input env).first

def keepState (key : ZMod p × ZMod p) (state : HintReadWordChip.State (ZMod p)) : Bool :=
  decide (clock state = key)

def keepWord (key : ZMod p × ZMod p) (last : Bool) (env : Environment (ZMod p)) : Bool :=
  keepState key (HintReadCoverage.rowInput (last, env)).previous

/-- Per-call occurrences at the environments of their original committed tables. -/
def rowsFor (key : ZMod p × ZMod p) (tables : List (Table (ZMod p))) :
    List (HintReadCoverage.Row (p := p)) :=
  TransitionView.selectRows HintReadCoverage.variants tables (keepWord key)

omit [Fact (2 ^ 25 < p)] in
private theorem handler_selection (key : ZMod p × ZMod p) (input : HostHintReadChip.Inputs (ZMod p))
    (interaction : Interaction (ZMod p))
    (member : interaction ∈ [HintReadWordChip.stateChannel.pushedValue input.first,
      HintReadWordChip.stateChannel.pulledValue input.final]) :
    ProvableType.selectMessage (keepState key) interaction.msg = keepState key input.first := by
  rcases List.mem_cons.mp member with equal | member
  · rw [equal]
    exact ProvableType.selectMessage_toElements _ _
  · rw [List.mem_singleton.mp member]
    exact ProvableType.selectMessage_toElements _ _

omit [Fact (2 ^ 25 < p)] in
private theorem word_clock (input : HintReadWordChip.Inputs (ZMod p)) :
    clock input.next = clock input.previous := rfl

private theorem view_edge (last : Bool) (env : Environment (ZMod p)) :
    (HintReadCoverage.view last).edge env =
      ((HintReadCoverage.rowInput (last, env)).previous, (HintReadCoverage.rowInput (last, env)).next) := rfl

/-- Active transfers commute with selecting a call's original physical occurrences. -/
theorem active_rows_for (key : ZMod p × ZMod p) (tables : List (Table (ZMod p))) :
    HintReadCoverage.activeRows (rowsFor key tables) =
      (TransitionView.readIndexedActiveRows HintReadCoverage.variants HintReadCoverage.view tables).filter
        (fun row => keepWord key row.1 row.2) := by
  rw [← HintReadCoverage.activeRows_readIndexedRows]
  exact List.filter_comm _ _ _

/-- Row selection is exactly payload selection in the shared cursor ledger. -/
theorem cursor_for (key : ZMod p × ZMod p) (tables : List (Table (ZMod p)))
    (aligned : List.Forall₂ (fun last table => (HintReadCoverage.view last).component = table.component)
      HintReadCoverage.variants tables) :
    HintReadCoverage.interactions (rowsFor key tables) HintReadWordChip.stateChannel.toRaw =
      (tables.flatMap (·.interactionsWith HintReadWordChip.stateChannel.toRaw)).filter
        (fun interaction => ProvableType.selectMessage (keepState key) interaction.msg) := by
  rw [← HintReadCoverage.interactions_readIndexedRows tables aligned]
  apply selectedRows_interactions
  intro row _ interaction member
  rw [(HintReadCoverage.view row.1).interactions] at member
  rcases List.mem_cons.mp member with rfl | member
  · exact ProvableType.selectMessage_toElements _ _
  · rw [List.mem_singleton.mp member]
    change ProvableType.selectMessage (keepState key)
      (toElements ((HintReadCoverage.view row.1).edge row.2).2).toArray = keepWord key row.1 row.2
    rw [ProvableType.selectMessage_toElements, view_edge]
    exact congrArg (fun value => decide (value = key))
      (word_clock (HintReadCoverage.rowInput row))

omit [Fact p.Prime] [Fact (2 ^ 25 < p)] in
private theorem filter_unique {Row Key : Type*} [DecidableEq Key] (key : Row → Key)
    (rows : List Row) (unique : (rows.map key).Nodup) (row : Row) (member : row ∈ rows) :
    rows.filter (fun other => decide (key other = key row)) = [row] := by
  induction rows with
  | nil => simp at member
  | cons head rest ih =>
    obtain ⟨fresh, unique⟩ := List.nodup_cons.mp unique
    rcases List.mem_cons.mp member with rfl | member
    · have empty : rest.filter (fun other => decide (key other = key row)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro other present equal
        exact fresh (List.mem_map.mpr ⟨other, present, of_decide_eq_true equal⟩)
      simp [empty]
    · have different : key head ≠ key row := by
        intro equal
        exact fresh (List.mem_map.mpr ⟨row, member, equal.symm⟩)
      simp [different, ih unique member]

private def endpoints (env : Environment (ZMod p)) :=
  [HintReadWordChip.stateChannel.pushedValue (input env).first,HintReadWordChip.stateChannel.pulledValue (input env).final]

/-- Keep the original count-sensitive balance as the premise. Its projection onto the active
handler pairs preserves every unit read and every consumer-side occurrence. -/
private theorem active_balance (table : Table (ZMod p)) (component : table.component = handler)
    (constraints : table.Constraints) (rest : List (Interaction (ZMod p)))
    (balanced : BalancedInteractions (table.interactionsWith HintReadWordChip.stateChannel.toRaw ++ rest)) :
    BalancedInteractions ((activeEnvs table table.data).flatMap endpoints ++ rest) := by
  let sites := (handler (p := p)).operations.interactionValuesWith HintReadWordChip.stateChannel.toRaw
  let envs := table.table.map table.environment
  have physical : table.interactionsWith HintReadWordChip.stateChannel.toRaw = envs.flatMap sites := by
    simp only [envs,sites,Table.interactionsWith,List.flatMap_map,component]
  have binary env (member : env ∈ envs) : IsBool (env activity) := by
    obtain ⟨raw,present,rfl⟩ := List.mem_map.mp member
    have checked := constraints raw present
    rw [component,Component.constraintsHold_iff] at checked
    exact Guarded.activity_of_constraints HostHintReadChip.circuit inferInstance (varFromOffset HostHintReadChip.RowInput 0)
      (size HostHintReadChip.RowInput) _ checked
  have strip (rs : List (Environment (ZMod p))) (bits : ∀ e ∈ rs, IsBool (e activity)) :
      ((rs.flatMap sites).filter (fun i => decide (i.mult ≠ 0))) =
      (((rs.filter (fun e => decide (e activity = 1))).flatMap endpoints).filter (fun i => decide (i.mult ≠ 0))) := by
    induction rs with
    | nil => rfl
    | cons e rs ih =>
      have next := ih (fun x m => bits x (List.mem_cons_of_mem _ m))
      rcases bits e (List.mem_cons_self ..) with disabled | enabled
      · simp [sites,handler_cursor,disabled,Channel.pulledIfValue,Channel.pushedIfValue] at next ⊢
        exact next
      · simp [sites,handler_cursor,enabled,endpoints,Channel.pulledIfValue,Channel.pushedIfValue,Channel.pulledValue,Channel.pushedValue] at next ⊢
        exact next
  apply BalancedInteractions.filter_nonzero_iff.mp
  have projected := balanced.filter_nonzero
  rw [physical,List.filter_append] at projected
  rw [List.filter_append]
  let explicit := fun i : Interaction (ZMod p) => decide (i.mult ≠ 0)
  have same : (fun i : Interaction (ZMod p) => @decide (i.mult ≠ 0)
      (@instDecidableNot _ (FiniteField.instDecidableEq _ _))) = explicit := by
    funext i
    exact congrArg (@decide _) (Subsingleton.elim _ _)
  rw [same] at projected ⊢
  exact (congrArg (fun xs => BalancedInteractions (xs ++ rest.filter explicit)) (strip envs binary)).mp projected

omit [Fact (2 ^ 25 < p)] in

private theorem handler_row_filter (key : ZMod p × ZMod p) (envs : List (Environment (ZMod p))) :
    (envs.filter (fun env => decide (callClock env = key))).flatMap endpoints =
    (envs.flatMap endpoints).filter (fun interaction => ProvableType.selectMessage (keepState key) interaction.msg) := by
  apply selectedRows_interactions
  intro env _ interaction present
  exact handler_selection key (input env) interaction present

/-- A shared physical ledger supplies each unique handler's per-call balance and its count bound. -/
theorem balanced_for (handlers : Table (ZMod p)) (component : handlers.component = handler)
    (constraints : handlers.Constraints) (tables : List (Table (ZMod p)))
    (aligned : List.Forall₂ (fun last table => (HintReadCoverage.view last).component = table.component)
      HintReadCoverage.variants tables)
    (env : Environment (ZMod p)) (member : env ∈ activeEnvs handlers handlers.data)
    (unique : ((activeEnvs handlers handlers.data).map callClock).Nodup)
    (balanced : BalancedInteractions
      (handlers.interactionsWith HintReadWordChip.stateChannel.toRaw ++
        tables.flatMap (·.interactionsWith HintReadWordChip.stateChannel.toRaw))) :
    BalancedInteractions
      (handler.operations.interactionValuesWith HintReadWordChip.stateChannel.toRaw env ++
        HintReadCoverage.interactions (rowsFor (callClock env) tables) HintReadWordChip.stateChannel.toRaw) := by
  have selected := (active_balance handlers component constraints _ balanced).filter_messages (ProvableType.selectMessage (keepState (callClock env)))
  rw [List.filter_append, ← handler_row_filter, filter_unique callClock _ unique env member,List.flatMap_singleton,
    ← cursor_for _ tables aligned] at selected
  have active := of_decide_eq_true (List.mem_filter.mp member).2
  rw [handler_cursor,show env activity = 1 from active]
  exact selected

/-- Global balance cannot hide consumer rows whose event clock has no handler. -/
theorem consumer_has_handler (handlers : Table (ZMod p)) (component : handlers.component = handler)
    (constraints : handlers.Constraints) (tables : List (Table (ZMod p)))
    (aligned : List.Forall₂ (fun last table => (HintReadCoverage.view last).component = table.component)
      HintReadCoverage.variants tables) (valid : HintReadCoverage.Steps (TransitionView.readIndexedRows HintReadCoverage.variants tables))
    (balanced : BalancedInteractions
      (handlers.interactionsWith HintReadWordChip.stateChannel.toRaw ++
        tables.flatMap (·.interactionsWith HintReadWordChip.stateChannel.toRaw)))
    (row : HintReadCoverage.Row (p := p))
    (member : row ∈ TransitionView.readIndexedActiveRows HintReadCoverage.variants HintReadCoverage.view tables) :
    ∃ env ∈ activeEnvs handlers handlers.data,
      callClock env = clock (HintReadCoverage.rowInput row).previous := by
  classical
  by_contra! absent
  let key := clock (HintReadCoverage.rowInput row).previous
  have noHandlers : (activeEnvs handlers handlers.data).filter
      (fun env => decide (callClock env = key)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro env present equal
    exact absent env present (of_decide_eq_true equal)
  have noEndpoints : ((activeEnvs handlers handlers.data).flatMap endpoints).filter
      (fun interaction => ProvableType.selectMessage (keepState key) interaction.msg) = [] := by
    rw [← handler_row_filter key, noHandlers, List.flatMap_nil]
  have selected := (active_balance handlers component constraints _ balanced).filter_messages (ProvableType.selectMessage (keepState key))
  rw [List.filter_append, noEndpoints, List.nil_append, ← cursor_for key tables aligned] at selected
  rw [HintReadCoverage.cursor_interactions] at selected
  have specs := valid.select (fun row => keepWord key row.1 row.2)
  have empty := HintReadCoverage.rows_nil_of_balanced (rowsFor key tables) specs selected
  have included : row ∈ HintReadCoverage.activeRows (rowsFor key tables) := by
    rw [active_rows_for]
    exact List.mem_filter.mpr ⟨member, by simp [keepWord, keepState, key]⟩
  rw [empty] at included
  exact List.not_mem_nil included

/-- Successful concrete dispatch and complete writes follow from the shared physical cursor ledger.
Unique handler clocks and authenticated records/permissions remain enclosing-ensemble obligations. -/
theorem run_of_shared_tables (handlers : Table (ZMod p)) (component : handlers.component = handler)
    (constraints : handlers.Constraints) (handlerSpecs : handlers.Spec) (tables : List (Table (ZMod p)))
    (aligned : List.Forall₂ (fun last table => (HintReadCoverage.view last).component = table.component)
      HintReadCoverage.variants tables) (wordSpecs : HintReadCoverage.Steps (TransitionView.readIndexedRows HintReadCoverage.variants tables))
    (env : Environment (ZMod p)) (member : env ∈ activeEnvs handlers handlers.data)
    (unique : ((activeEnvs handlers handlers.data).map callClock).Nodup)
    (balanced : BalancedInteractions
      (handlers.interactionsWith HintReadWordChip.stateChannel.toRaw ++
        tables.flatMap (·.interactionsWith HintReadWordChip.stateChannel.toRaw)))
    (host : HostState) (store : Store) (current : (input env).previous.Binds store host.io.hints)
    (header : (input env).node.Binds store) (ending : (input env).endStep.word.Binds store)
    (words : ∀ row ∈ TransitionView.readIndexedActiveRows HintReadCoverage.variants HintReadCoverage.view tables,
      clock (HintReadCoverage.rowInput row).previous = callClock env →
        ((HintReadCoverage.rowInput row).step row.1).word.Binds store)
    (running : host.exitCode = none) (policy : HostPolicy) (context : HostReadContext)
    (permissions : ∀ request, WritePermissionProvider.channel.pulledValue request ∈
      tables.flatMap (·.interactionsWith WritePermissionProvider.channel.toRaw) →
      policy.memory.permits (Address.toNat request) 1 = true)
    (code : context.register 5 = some (Word.toBitVec64 (input env).call.code))
    (arg1 : context.register 10 = some (Word.toBitVec64 (input env).call.arg1))
    (arg2 : context.register 11 = some (Word.toBitVec64 (input env).call.arg2)) :
    ∃ bytes rest, host.io.hints = bytes :: rest ∧ (input env).next.Binds store rest ∧
      host.run policy context = some (HostHintReadChip.execution (input env) host bytes rest) ∧
      ((HintReadCoverage.activeRows (rowsFor (callClock env) tables)).map
        HintReadWrites.produced).Perm (wordWrites (Address.toNat (input env).span.start) bytes) := by
  have valid : handler.Spec env := by
    obtain ⟨physical, present, equal⟩ := List.mem_map.mp (List.mem_filter.mp member).1
    rw [← equal, ← component]
    exact handlerSpecs physical present
  have specs := wordSpecs.select (fun row => keepWord (callClock env) row.1 row.2)
  have selectedPermissions := TransitionView.selectRows_interactions_sublist HintReadCoverage.variants tables
    (fun last => (HintReadCoverage.view last).component) (keepWord (callClock env))
    WritePermissionProvider.channel.toRaw aligned
  exact HostHintReadWrites.run_of_rows env (rowsFor (callClock env) tables) valid (of_decide_eq_true (List.mem_filter.mp member).2) specs
    (balanced_for handlers component constraints tables aligned env member unique balanced) host store current header ending
    (fun row present => by
      have selected := List.mem_filter.mp ((active_rows_for _ tables) ▸ present)
      exact words row selected.1 (of_decide_eq_true selected.2))
    running policy context (fun request present => permissions request (selectedPermissions.subset present))
    code arg1 arg2

end SP1Clean.Soundness.HostHintReadPartition
