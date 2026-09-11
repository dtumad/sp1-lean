import SP1Clean.Native.Operations.HostCommitBoundary
import SP1Clean.Soundness.HostCommitHistory
import ToClean.Air.ChannelClosure

/-! # Publicly bounded native commitment histories

Each bank registers eight slot components and one terminal component. The terminal is a
semantically inert transition to a fixed clock outside ordinary timestamps. Consequently the
same ranked-balance argument binds a zero initial bank to public final words, including when
there are no calls. The execution fold retains physical row identities and ignores only the
proved terminal no-op. Local contracts follow from constraints and Byte guarantees.
-/

namespace SP1Clean.Soundness.HostCommitBank

open Circuit Air.Flat HostCommitChip Model.Core RankedGrounding
open scoped Classical

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

abbrev Index := Option (Fin 8)
def indices : List Index := (List.finRange 8).map some ++ [none]

omit [Fact (2 ^ 25 < p)] in
private theorem eval_values (input : Var State (ZMod p)) (env : Environment (ZMod p)) :
    Eval.eval env input.values = (Eval.eval env input).values := by
  rcases input with ⟨high, low, values⟩
  simp only [circuit_norm]

def terminalView (deferred : Bool) : TransitionView (stateChannel (p := p) deferred) where
  component := ⟨HostCommitBoundary.terminal deferred⟩
  edge env :=
    let input := valueFromOffset State 0 env
    (input, HostCommitBoundary.final input.values)
  interactions := by
    intro env
    simp only [Operations.interactionValuesWith, Component.interactionsWith_eq,
      Component.rowOperations, HostCommitBoundary.terminal]
    change ((HostCommitBoundary.terminalMain deferred (varFromOffset State 0)).operations (size State)).interactionValuesWith
      (stateChannel deferred).toRaw env = _
    rw [HostCommitBoundary.terminal_values]
    simp only [eval_values, eval_varFromOffset_valueFromOffset]

def view (deferred : Bool) : Index → TransitionView (stateChannel (p := p) deferred)
  | some slot => HostCommitHistory.view deferred slot
  | none => terminalView deferred

def views (deferred : Bool) := indices.map (view (p := p) deferred)
def components (deferred : Bool) := (views (p := p) deferred).map (·.component)

theorem components_length (deferred : Bool) : (components (p := p) deferred).length = 9 := by
  simp [components, views, indices]

abbrev Row := Index × Environment (ZMod p)
def edge (deferred : Bool) (row : Row (p := p)) := (view deferred row.1).edge row.2

def execute (deferred : Bool) (policy : HostPolicy) (context : HostReadContext)
    (host : HostState) (row : Row (p := p)) : Option HostState :=
  match row.1 with
  | some slot => HostCommitHistory.execute deferred policy context host (slot, row.2)
  | none => some host

/-- Only Byte is a nontrivial incoming guarantee of either kind of bank row. -/
theorem view_spec_of_byte (deferred : Bool) (index : Index) (env : Environment (ZMod p))
    (constraints : (view deferred index).component.operations.ConstraintsHold env)
    (byte : (view deferred index).component.operations.ChannelGuarantees Channels.byteChannel.toRaw env) :
    (view deferred index).component.Spec env := by
  have assumptions : (view deferred index).component.Assumptions env := by cases index <;> trivial
  apply (Component.weakSoundness assumptions constraints ?_).1
  rw [Operations.guarantees_iff _ _ _ ((view deferred index).component.inChannelsOrGuarantees env)]
  intro channel member
  cases index with
  | none =>
    change channel ∈ [(stateChannel deferred).toRaw] at member
    obtain rfl := List.mem_singleton.mp member
    exact Operations.channelGuarantees_of_trivial _ (by simp [stateChannel, Channel.toRaw]) _ _
  | some slot =>
    have metadata : (view (p := p) deferred (some slot)).component.circuit.channelsWithGuarantees =
        [Channels.byteChannel.toRaw, Channels.byteChannel.toRaw,
          HostCallChip.channel.toRaw, (stateChannel deferred).toRaw] := by cases deferred <;> rfl
    rw [metadata] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact byte
    · exact byte
    · exact Operations.channelGuarantees_of_trivial _ (by simp [HostCallChip.channel, Channel.toRaw]) _ _
    · exact Operations.channelGuarantees_of_trivial _ (by simp [stateChannel, Channel.toRaw]) _ _

private theorem commit_strict (deferred : Bool) (slot : Fin 8) (input : Inputs (ZMod p))
    (valid : Spec deferred slot input) :
    Semantics.clkNat input.previous.clk_high input.previous.clk_low <
      Semantics.clkNat (input.next slot).clk_high (input.next slot).clk_low :=
  valid.2.1.2.2.2.2

private theorem view_strict (deferred : Bool) (index : Index) (env : Environment (ZMod p))
    (valid : (view deferred index).component.Spec env) :
    Semantics.clkNat ((view deferred index).edge env).1.clk_high ((view deferred index).edge env).1.clk_low <
      Semantics.clkNat ((view deferred index).edge env).2.clk_high ((view deferred index).edge env).2.clk_low := by
  cases index with
  | none => exact HostCommitBoundary.terminal_strict _ valid
  | some slot => exact commit_strict deferred slot _ valid

omit [Fact (2 ^ 25 < p)] in
private theorem terminal_apply (input : State (ZMod p)) (deferred : Bool) (host : HostState) :
    input.apply deferred host = (HostCommitBoundary.final input.values).apply deferred host := rfl

private theorem commit_effect (deferred : Bool) (slot : Fin 8) (input : Inputs (ZMod p))
    (valid : Spec deferred slot input) (host : HostState)
    (policy : HostPolicy) (characteristic : policy.characteristic = p) (context : HostReadContext) :
    ((input.previous.apply deferred host).executeKind policy context
      (if deferred then .commitDeferred else .commit)
      (Word.toBitVec64 input.call.arg1) (Word.toBitVec64 input.call.arg2)).map (·.state) =
        some ((input.next slot).apply deferred host) := by
  rw [executeKind_of_spec deferred slot input valid host policy characteristic context]
  rfl

private theorem view_executes (deferred : Bool) (index : Index) (env : Environment (ZMod p))
    (valid : (view deferred index).component.Spec env) (host : HostState)
    (policy : HostPolicy) (characteristic : policy.characteristic = p) (context : HostReadContext) :
    execute deferred policy context (((view deferred index).edge env).1.apply deferred host) (index, env) =
      some (((view deferred index).edge env).2.apply deferred host) := by
  cases index with
  | none => exact congrArg some (terminal_apply (valueFromOffset State 0 env) deferred host)
  | some slot =>
    exact commit_effect deferred slot (valueFromOffset Inputs 0 env) valid host policy characteristic context

private theorem fold_of_walk (deferred : Bool) (policy : HostPolicy)
    (characteristic : policy.characteristic = p) (context : HostReadContext) (host : HostState)
    (initial final : State (ZMod p)) (path : List (Row (p := p)))
    (valid : ∀ row ∈ path, (view deferred row.1).component.Spec row.2)
    (walk : Walk.IsWalk (edge deferred) initial final path) :
    path.foldlM (execute deferred policy context) (initial.apply deferred host) =
      some (final.apply deferred host) := by
  induction path generalizing initial with
  | nil =>
    change initial = final at walk
    subst final
    rfl
  | cons row rest ih =>
    obtain ⟨source, tail⟩ := walk
    have step := view_executes deferred row.1 row.2 (valid row (List.mem_cons_self ..))
      host policy characteristic context
    change ((view deferred row.1).edge row.2).1 = initial at source
    rw [source] at step
    simp only [List.foldlM_cons, step]
    exact ih _ (fun other member => valid other (List.mem_cons_of_mem _ member)) tail

private theorem history_of_balance (deferred : Bool) (rows : List (Row (p := p)))
    (initial final : State (ZMod p))
    (valid : ∀ row ∈ rows, (view deferred row.1).component.Spec row.2)
    (balanced : EndpointBalanced (↑rows) (edge deferred) initial final)
    (policy : HostPolicy) (characteristic : policy.characteristic = p)
    (context : HostReadContext) (host : HostState) :
    ∃ path : List (Row (p := p)), path.Perm rows ∧ Walk.IsWalk (edge deferred) initial final path ∧
      path.foldlM (execute deferred policy context) (initial.apply deferred host) =
        some (final.apply deferred host) := by
  obtain ⟨path, walk, exhaustive⟩ := exists_exhaustiveTrail_of_endpointBalanced (↑rows) (edge deferred)
    (fun state => Semantics.clkNat state.clk_high state.clk_low) initial final balanced
    (fun row member => view_strict deferred row.1 row.2 (valid row (Multiset.mem_coe.mp member)))
  have perm : path.Perm rows := Multiset.coe_eq_coe.mp exhaustive
  refine ⟨path, perm, walk, fold_of_walk deferred policy characteristic context host initial final path ?_ walk⟩
  intro row member
  exact valid row (perm.mem_iff.mp member)

/-- The fixed genesis and public final words determine a history of every physical bank row.
Local specifications are derived from constraints and Byte guarantees, including at the terminal. -/
theorem ordered_history (deferred : Bool) (tables : List (Table (ZMod p)))
    (values : Vector (Word (ZMod p)) 8)
    (aligned : List.Forall₂ (fun index table => (view deferred index).component = table.component) indices tables)
    (constraints : ∀ table ∈ tables, table.Constraints)
    (byte : ∀ table ∈ tables, table.ChannelGuarantees Channels.byteChannel.toRaw)
    (balanced : BalancedInteractions
      ([(stateChannel deferred).pushedValue HostCommitBoundary.initial,
        (stateChannel deferred).pulledValue (HostCommitBoundary.final values)] ++
        tables.flatMap (·.interactionsWith (stateChannel deferred).toRaw)))
    (policy : HostPolicy) (characteristic : policy.characteristic = p)
    (context : HostReadContext) (host : HostState) :
    ∃ path : List (Row (p := p)),
      path.Perm (TransitionView.readIndexedRows indices tables) ∧
      Walk.IsWalk (edge deferred) HostCommitBoundary.initial (HostCommitBoundary.final values) path ∧
      path.foldlM (execute deferred policy context) ((HostCommitBoundary.initial (p := p)).apply deferred host) =
        some ((HostCommitBoundary.final values).apply deferred host) := by
  have alignment : List.Forall₂ (fun view table => view.component = table.component) (views deferred) tables := by
    simpa only [views, List.forall₂_map_left_iff] using aligned
  have specs : ∀ table ∈ tables, table.Spec := by
    intro table member row rowMember
    have allSame : indices.map (fun index => (view deferred index).component) = tables.map (·.component) := by
      have mapped : List.Forall₂ (· = ·) (indices.map (fun index => (view deferred index).component))
          (tables.map (·.component)) := by
        simpa only [List.forall₂_map_left_iff, List.forall₂_map_right_iff] using aligned
      simpa only [List.forall₂_eq_eq_eq] using mapped
    have componentMem := List.mem_map_of_mem (f := fun table : Table (ZMod p) => table.component) member
    rw [← allSame] at componentMem
    obtain ⟨index, _, same⟩ := List.mem_map.mp componentMem
    have checked := constraints table member row rowMember
    have bytes := byte table member row rowMember
    rw [← same] at checked bytes ⊢
    exact view_spec_of_byte deferred index _ checked bytes
  have localSpecs := TransitionView.readIndexedRows_spec indices (view deferred) tables alignment specs
  have projected := TransitionView.readRows_interactions (views deferred) tables alignment
  rw [views, TransitionView.readRows_eq_indexed] at projected
  simp only [List.flatMap_map] at projected
  rw [projected] at balanced
  change BalancedInteractions ((stateChannel deferred).transitionLedger HostCommitBoundary.initial
    (HostCommitBoundary.final values) (TransitionView.readIndexedRows indices tables) (edge deferred)) at balanced
  have endpoints := ((stateChannel deferred).transitionLedger_balanced_iff _ _ _ _).mp balanced
  have endpointBalance : EndpointBalanced (↑(TransitionView.readIndexedRows indices tables)) (edge deferred)
      HostCommitBoundary.initial (HostCommitBoundary.final values) := by
    simpa only [EndpointBalanced, Multiset.map_coe, Multiset.cons_coe, Multiset.coe_eq_coe] using endpoints.2
  exact history_of_balance deferred _ _ _ localSpecs endpointBalance policy characteristic context host

end SP1Clean.Soundness.HostCommitBank
