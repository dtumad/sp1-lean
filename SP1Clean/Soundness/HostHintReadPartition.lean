import SP1Clean.Soundness.HostHintReadWrites
import ToClean.Air.MessageFilter

/-! # Per-call HINT_READ tables from one shared cursor ledger

Both ends of every handler and word row retain the same event clock. Selecting that clock in
the shared physical ledger therefore selects complete rows and preserves balance. A unique
handler clock leaves exactly one pair of endpoints. The instruction handoff must still derive
that uniqueness when the subsystem is installed; global balance alone cannot distinguish two
handlers at the same event. No row order or independently balanced per-call witness is assumed.
-/

namespace SP1Clean.Soundness.HostHintReadPartition

open Circuit Air.Flat HostHintReadCoverage
open Model.Core Model.Core.HintQueue

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

def clock (state : HintReadWordChip.State (ZMod p)) : ZMod p × ZMod p :=
  (state.clk_high, state.clk_low)

def callClock (env : Environment (ZMod p)) : ZMod p × ZMod p := clock (input env).first

def keepState (key : ZMod p × ZMod p) (state : HintReadWordChip.State (ZMod p)) : Bool :=
  decide (clock state = key)

def keepWord (key : ZMod p × ZMod p) (last : Bool) (env : Environment (ZMod p)) : Bool :=
  keepState key (HintReadCoverage.rowInput (last, env)).previous

def tablesFor (key : ZMod p × ZMod p) (tables : List (Table (ZMod p))) : List (Table (ZMod p)) :=
  TransitionView.selectTables HintReadCoverage.variants tables (keepWord key)

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

private theorem word_filter (key : ZMod p × ZMod p) (last : Bool) (table : Table (ZMod p))
    (component : (HintReadCoverage.view last).component = table.component) :
    (table.filterRows (keepWord key last)).interactionsWith HintReadWordChip.stateChannel.toRaw =
      (table.interactionsWith HintReadWordChip.stateChannel.toRaw).filter
        (fun interaction => ProvableType.selectMessage (keepState key) interaction.msg) := by
  have preserved : ∀ env, keepState key ((HintReadCoverage.view last).edge env).2 =
      keepState key ((HintReadCoverage.view last).edge env).1 := by
    intro env
    rw [view_edge]
    change decide (clock (HintReadCoverage.rowInput (last, env)).next = key) =
      decide (clock (HintReadCoverage.rowInput (last, env)).previous = key)
    exact congrArg (fun value => decide (value = key))
      (word_clock (HintReadCoverage.rowInput (last, env)))
  have projected := (HintReadCoverage.view last).filterRows_interactions table component (keepState key) preserved
  simp only [view_edge] at projected
  exact projected

omit [Fact (2 ^ 25 < p)] in
/-- Both physical variants retain exactly the rows at this call clock, on every channel. -/
theorem rows_for (key : ZMod p × ZMod p) (tables : List (Table (ZMod p))) :
    TransitionView.readIndexedRows HintReadCoverage.variants (tablesFor key tables) =
      (TransitionView.readIndexedRows HintReadCoverage.variants tables).filter
        (fun row => keepWord key row.1 row.2) :=
  TransitionView.readIndexedRows_selectTables _ _ _

/-- Selecting the actual consumer tables is exactly payload selection in their shared cursor ledger. -/
theorem cursor_for (key : ZMod p × ZMod p) (tables : List (Table (ZMod p)))
    (aligned : List.Forall₂ (fun last table => (HintReadCoverage.view last).component = table.component)
      HintReadCoverage.variants tables) :
    (tablesFor key tables).flatMap (·.interactionsWith HintReadWordChip.stateChannel.toRaw) =
      (tables.flatMap (·.interactionsWith HintReadWordChip.stateChannel.toRaw)).filter
        (fun interaction => ProvableType.selectMessage (keepState key) interaction.msg) := by
  unfold tablesFor
  generalize HintReadCoverage.variants = variants at aligned ⊢
  induction aligned with
  | nil => rfl
  | @cons last table variants tables same _ ih =>
    simp only [TransitionView.selectTables, List.zip_cons_cons, List.map_cons, List.flatMap_cons,
      List.filter_append] at ih ⊢
    rw [word_filter key last table same, ih]

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

private theorem handler_table_filter (key : ZMod p × ZMod p)
    (table : Table (ZMod p)) (component : table.component = handler) :
    (table.filterRows (fun env => decide (callClock env = key))).interactionsWith
      HintReadWordChip.stateChannel.toRaw =
    (table.interactionsWith HintReadWordChip.stateChannel.toRaw).filter
        (fun interaction => ProvableType.selectMessage (keepState key) interaction.msg) := by
  apply table.filterRows_interactions
  intro physical _ interaction present
  rw [component, handler_cursor] at present
  exact handler_selection key (input (table.environment physical)) interaction present

private theorem handler_filter (table : Table (ZMod p)) (component : table.component = handler)
    (env : Environment (ZMod p)) (member : env ∈ table.table.map table.environment)
    (unique : ((table.table.map table.environment).map callClock).Nodup) :
    (table.interactionsWith HintReadWordChip.stateChannel.toRaw).filter
        (fun interaction => ProvableType.selectMessage (keepState (callClock env)) interaction.msg) =
      handler.operations.interactionValuesWith HintReadWordChip.stateChannel.toRaw env := by
  rw [← handler_table_filter (callClock env) table component]
  have selected := filter_unique callClock (table.table.map table.environment) unique env member
  change (table.table.filter (fun row => decide (callClock (table.environment row) = callClock env))).flatMap
    (fun physical => table.component.operations.interactionValuesWith HintReadWordChip.stateChannel.toRaw
      (table.environment physical)) = _
  rw [component]
  rw [List.filter_map] at selected
  have projected := congrArg (List.flatMap
    (fun row => handler.operations.interactionValuesWith HintReadWordChip.stateChannel.toRaw row)) selected
  simpa only [List.flatMap_map, Function.comp_def, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    using projected

/-- A shared physical ledger supplies each unique handler's per-call balance and its count bound. -/
theorem balanced_for (handlers : Table (ZMod p)) (component : handlers.component = handler)
    (tables : List (Table (ZMod p)))
    (aligned : List.Forall₂ (fun last table => (HintReadCoverage.view last).component = table.component)
      HintReadCoverage.variants tables)
    (env : Environment (ZMod p)) (member : env ∈ handlers.table.map handlers.environment)
    (unique : ((handlers.table.map handlers.environment).map callClock).Nodup)
    (balanced : BalancedInteractions
      (handlers.interactionsWith HintReadWordChip.stateChannel.toRaw ++
        tables.flatMap (·.interactionsWith HintReadWordChip.stateChannel.toRaw))) :
    BalancedInteractions
      (handler.operations.interactionValuesWith HintReadWordChip.stateChannel.toRaw env ++
        (tablesFor (callClock env) tables).flatMap (·.interactionsWith HintReadWordChip.stateChannel.toRaw)) := by
  have selected := balanced.filter_messages (ProvableType.selectMessage (keepState (callClock env)))
  rw [List.filter_append, handler_filter handlers component env member unique,
    ← cursor_for _ tables aligned] at selected
  exact selected

/-- Global balance cannot hide consumer rows whose event clock has no handler. -/
theorem consumer_has_handler (handlers : Table (ZMod p)) (component : handlers.component = handler)
    (tables : List (Table (ZMod p)))
    (aligned : List.Forall₂ (fun last table => (HintReadCoverage.view last).component = table.component)
      HintReadCoverage.variants tables) (valid : HintReadCoverage.Steps tables)
    (balanced : BalancedInteractions
      (handlers.interactionsWith HintReadWordChip.stateChannel.toRaw ++
        tables.flatMap (·.interactionsWith HintReadWordChip.stateChannel.toRaw)))
    (row : HintReadCoverage.Row (p := p))
    (member : row ∈ TransitionView.readIndexedRows HintReadCoverage.variants tables) :
    ∃ env ∈ handlers.table.map handlers.environment,
      callClock env = clock (HintReadCoverage.rowInput row).previous := by
  classical
  by_contra! absent
  let key := clock (HintReadCoverage.rowInput row).previous
  have noHandlers : handlers.table.filter
      (fun physical => decide (callClock (handlers.environment physical) = key)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro physical present equal
    exact absent (handlers.environment physical) (List.mem_map.mpr ⟨physical, present, rfl⟩)
      (of_decide_eq_true equal)
  have noEndpoints : (handlers.interactionsWith HintReadWordChip.stateChannel.toRaw).filter
      (fun interaction => ProvableType.selectMessage (keepState key) interaction.msg) = [] := by
    rw [← handler_table_filter key handlers component]
    change (handlers.table.filter _).flatMap _ = []
    rw [noHandlers, List.flatMap_nil]
  have selected := balanced.filter_messages (ProvableType.selectMessage (keepState key))
  rw [List.filter_append, noEndpoints, List.nil_append, ← cursor_for key tables aligned] at selected
  have alignment := TransitionView.selectTables_aligned _ _
    (fun last => (HintReadCoverage.view last).component) (keepWord key) aligned
  have specs := valid.select (keepWord key)
  have empty := HintReadCoverage.rows_nil_of_balanced (tablesFor key tables) alignment specs selected
  have included : row ∈ TransitionView.readIndexedRows HintReadCoverage.variants (tablesFor key tables) := by
    rw [rows_for]
    exact List.mem_filter.mpr ⟨member, by simp [keepWord, keepState, key]⟩
  rw [empty] at included
  exact List.not_mem_nil included

/-- Successful concrete dispatch and complete writes follow from the shared physical cursor ledger.
Unique handler clocks and authenticated records/permissions remain enclosing-ensemble obligations. -/
theorem run_of_shared_tables (handlers : Table (ZMod p)) (component : handlers.component = handler)
    (handlerSpecs : handlers.Spec) (tables : List (Table (ZMod p)))
    (aligned : List.Forall₂ (fun last table => (HintReadCoverage.view last).component = table.component)
      HintReadCoverage.variants tables) (wordSpecs : HintReadCoverage.Steps tables)
    (env : Environment (ZMod p)) (member : env ∈ handlers.table.map handlers.environment)
    (unique : ((handlers.table.map handlers.environment).map callClock).Nodup)
    (balanced : BalancedInteractions
      (handlers.interactionsWith HintReadWordChip.stateChannel.toRaw ++
        tables.flatMap (·.interactionsWith HintReadWordChip.stateChannel.toRaw)))
    (host : HostState) (store : Store) (current : (input env).previous.Binds store host.io.hints)
    (header : (input env).node.Binds store) (ending : (input env).endStep.word.Binds store)
    (words : ∀ row ∈ TransitionView.readIndexedRows HintReadCoverage.variants tables,
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
      ((TransitionView.readIndexedRows HintReadCoverage.variants (tablesFor (callClock env) tables)).map
        HintReadWrites.produced).Perm (wordWrites (Address.toNat (input env).span.start) bytes) := by
  have valid : handler.Spec env := by
    obtain ⟨physical, present, equal⟩ := List.mem_map.mp member
    rw [← equal, ← component]
    exact handlerSpecs physical present
  have alignment := TransitionView.selectTables_aligned _ _
    (fun last => (HintReadCoverage.view last).component) (keepWord (callClock env)) aligned
  have specs := wordSpecs.select (keepWord (callClock env))
  have selectedPermissions := TransitionView.selectTables_interactions_sublist HintReadCoverage.variants tables
    (fun last => (HintReadCoverage.view last).component) (keepWord (callClock env))
    WritePermissionProvider.channel.toRaw aligned
  exact HostHintReadWrites.run_of_tables env (tablesFor (callClock env) tables) valid alignment specs
    (balanced_for handlers component tables aligned env member unique balanced) host store current header ending
    (fun row present => by
      have selected := List.mem_filter.mp ((rows_for _ tables) ▸ present)
      exact words row selected.1 (of_decide_eq_true selected.2))
    running policy context (fun request present => permissions request (selectedPermissions.subset present))
    code arg1 arg2

end SP1Clean.Soundness.HostHintReadPartition
