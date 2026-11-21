import SP1Clean.Soundness.HostObservedLedger
import SP1Clean.Soundness.HostObservedConsumer

/-! # Extracting the selected physical ordinary-history terminal

All ordinary rows and terminal inputs have clock high limbs below the sentinel. Filtering the
balanced occurrence permutation on this clock range therefore isolates exactly the physical
terminal whose normalized outgoing state the verifier requested.
-/

namespace SP1Clean.Soundness.HostObserved

open SP1Clean.Soundness.OrdinaryObservation (terminalEdge)

open Circuit Air.Flat Semantics Channels
open SP1Clean.OrdinaryObservation (Inputs State Mode TerminalInputs startFor finalFor)

private theorem below_filter {δ γ : Type*} (high : γ → Bool) (rows : List δ) (key : δ → γ)
    (below : ∀ r ∈ rows, high (key r) = false) : (rows.map key).filter high = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro item member
  obtain ⟨r, occurs, rfl⟩ := List.mem_map.mp member
  simp [below r occurs]

private theorem isolate_terminal {α β γ : Type*} (high : γ → Bool)
    (first last : γ) (ordinary : List α) (terminals : List β)
    (edge : α → γ × γ) (finish : β → γ × γ)
    (initial : high first = false) (target : high last = true)
    (normal : ∀ row ∈ ordinary, high (edge row).1 = false ∧ high (edge row).2 = false)
    (sentinel : ∀ row ∈ terminals, high (finish row).1 = false ∧ high (finish row).2 = true)
    (balanced : (first :: (ordinary.map (fun row => (edge row).2) ++ terminals.map (fun row => (finish row).2))).Perm
      (last :: (ordinary.map (fun row => (edge row).1) ++ terminals.map (fun row => (finish row).1)))) :
    ∃ terminal, terminals = [terminal] ∧ (finish terminal).2 = last ∧
      (first :: ordinary.map (fun row => (edge row).2)).Perm
        ((finish terminal).1 :: ordinary.map (fun row => (edge row).1)) := by
  have allHigh : ((terminals.map fun r => (finish r).2).filter high) = terminals.map (fun r => (finish r).2) := by
    apply List.filter_eq_self.mpr
    intro item member
    obtain ⟨r, occurs, rfl⟩ := List.mem_map.mp member
    exact (sentinel r occurs).2
  have single := balanced.filter high
  simp only [List.filter_cons, initial, target, Bool.false_eq_true, ↓reduceIte, List.filter_append,
    below_filter high ordinary (fun r => (edge r).2) (fun r m => (normal r m).2), below_filter high ordinary (fun r => (edge r).1) (fun r m => (normal r m).1),
    below_filter high terminals (fun r => (finish r).1) (fun r m => (sentinel r m).1), allHigh, List.nil_append] at single
  have one := List.perm_singleton.mp single
  cases terminals with
  | nil => cases one
  | cons row rest =>
    simp only [List.map_cons, List.cons.injEq, List.map_eq_nil_iff] at one
    obtain ⟨targetEq, rfl⟩ := one
    refine ⟨row, rfl, targetEq, ?_⟩
    simp only [List.map_cons, List.map_nil, targetEq] at balanced
    exact ((List.perm_append_singleton last (first :: _)).symm.trans
      (balanced.trans ((List.perm_append_singleton (finish row).1 _).cons last))).cons_inv

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
/-- Use the finite-field equality used by the canonical physical ledger. -/
local instance observationFieldDecidableEq : DecidableEq (ZMod p) := FiniteField.instDecidableEq

variable {image : ProgramImage} {source target : ExecutionSnapshot} {final : HostHintQueue.State (ZMod p)}

private abbrev Step (p : ℕ) := Sum (Inputs (ZMod p) × ZMod p) (Mode × TerminalInputs (ZMod p))

private def weight : Step p → ZMod p
  | .inl row => row.2
  | .inr _ => 1

private def link : Step p → State (ZMod p) × State (ZMod p)
  | .inl row => OrdinaryObservation.edge row.1
  | .inr tagged => terminalEdge tagged.1 tagged.2

private def physicalSteps (witness : EnsembleWitness (ensemble image source target final)) : List (Step p) :=
  ((OrdinaryObservation.rows (observationTable witness 0) witness.data).map Sum.inl) ++ (terminals witness).map Sum.inr

private theorem step_ledger (witness : EnsembleWitness (ensemble image source target final)) :
    witness.interactionsWith SP1Clean.OrdinaryObservation.stateChannel.toRaw =
    SP1Clean.OrdinaryObservation.stateChannel.gatedTransitionLedger (startFor source.sail) (finalFor source.sail target.sail)
      (physicalSteps witness) weight link := by
  rw [state_rows]
  simp only [Channel.gatedTransitionLedger, physicalSteps, List.flatMap_append, List.flatMap_map,
    weight, link, OrdinaryObservation.edge, List.append_assoc]
  rfl

private def isSentinel (s : State (ZMod p)) := decide (2 ^ 24 ≤ s.clkHigh.val)

private theorem sentinel_high (mode : Mode) : 2 ^ 24 ≤ (mode.sentinel (R := ZMod p)).val := by
  have hp := Fact.out (p := 2 ^ 25 < p)
  cases mode <;> simp only [Mode.sentinel] <;> rw [ZMod.val_ofNat_of_lt (lt_trans (by norm_num) hp)] <;> norm_num

/-- The same physical witness has exactly one selected terminal across all three tables.
Its incoming state balances the guarded ordinary consumer on the verifier's actual start. -/
theorem selected_terminal (witness : EnsembleWitness (ensemble image source target final)) (checked : witness.Constraints)
    (funded : DeclarationsOpen witness) :
    ∃ tagged, terminals witness = [tagged] ∧ (terminalEdge tagged.1 tagged.2).2 = finalFor source.sail target.sail ∧
      BalancedInteractions ([SP1Clean.OrdinaryObservation.stateChannel.pushedValue (startFor source.sail),
        SP1Clean.OrdinaryObservation.stateChannel.pulledValue tagged.2.previous] ++
        (observationTable witness 0).interactionsWith SP1Clean.OrdinaryObservation.stateChannel.toRaw) := by
  have valid := consumer_spec witness checked funded
  have balanced : witness.BalancedChannel SP1Clean.OrdinaryObservation.stateChannel.toRaw := by
    apply funded
    · change _ ∈ (producers image source target final).channels
      change _ ∈ (_ ++ [_])
      apply List.mem_append_left
      change _ ∈ ((_ ++ [_]) ++ [_])
      apply List.mem_append_left
      apply List.mem_append_left
      change _ ∈ (_ ++ [_])
      apply List.mem_append_left
      exact List.mem_append_right _ (List.mem_cons_of_mem _ (by simp [HostFinalMemory.sourceChannels]))
    · simp [SP1Clean.OrdinaryObservation.stateChannel, CommitmentDeclaration.channel, Channel.toRaw]
  let table := observationTable witness 0
  let ordinary := OrdinaryObservation.rows table witness.data
  let active := ordinary.filter fun row => decide (row.2 = 1)
  let terms := terminals witness
  have specs := OrdinaryObservation.rows_spec table witness.data ((observationSlot 0).table_component witness) valid
  have binary (row) (member : row ∈ ordinary) : row.2 = 0 ∨ row.2 = 1 := (specs row member).1
  have perStep (row) (member : row ∈ physicalSteps witness) : weight row = 0 ∨ weight row = 1 := by
    simp only [physicalSteps, List.mem_append, List.mem_map] at member
    rcases member with ⟨_, occurs, rfl⟩ | ⟨_, _, rfl⟩
    · exact binary _ occurs
    · exact Or.inr rfl
  change BalancedInteractions (witness.interactionsWith _) at balanced
  rw [step_ledger] at balanced
  have endpoints := (SP1Clean.OrdinaryObservation.stateChannel.gatedTransitionLedger_balanced_iff
    _ _ _ _ _ perStep).mp balanced
  have activeSteps : ((physicalSteps witness).filter fun row => decide (weight row = 1)) =
      active.map Sum.inl ++ terms.map Sum.inr := by
    simp [physicalSteps, active, ordinary, table, terms, List.filter_map, Function.comp_def, weight]
    apply congrArg (List.map Sum.inl)
    apply List.filter_congr
    intro row _
    exact decide_eq_decide.mpr Iff.rfl
  rw [activeSteps] at endpoints
  simp only [List.map_append, List.map_map, Function.comp_def, link] at endpoints
  have first : isSentinel (startFor (p := p) source.sail) = false := by
    simp [isSentinel, startFor, SP1Clean.OrdinaryObservation.start]
  have last : isSentinel (finalFor (p := p) source.sail target.sail) = true :=
    decide_eq_true (sentinel_high (Mode.of source.sail target.sail))
  have small (row) (member : row ∈ active) : isSentinel (OrdinaryObservation.edge row.1).1 = false ∧
      isSentinel (OrdinaryObservation.edge row.1).2 = false := by
    obtain ⟨physical, live⟩ := List.mem_filter.mp member
    have bounds := ((specs row physical).2 (of_decide_eq_true live)).1
    exact ⟨decide_eq_false (Nat.not_le.mpr bounds.1), decide_eq_false (Nat.not_le.mpr bounds.2.2.1)⟩
  have high (tag) (member : tag ∈ terms) : isSentinel (terminalEdge tag.1 tag.2).1 = false ∧
      isSentinel (terminalEdge tag.1 tag.2).2 = true := by
    have bounds := terminals_valid witness checked tag member
    exact ⟨decide_eq_false (Nat.not_le.mpr bounds.2.2.1), decide_eq_true (sentinel_high tag.1)⟩
  obtain ⟨tag, alone, endpoint, ordinaryOrder⟩ := isolate_terminal isSentinel (startFor source.sail)
    (finalFor source.sail target.sail) active terms (fun row => OrdinaryObservation.edge row.1)
    (fun row => terminalEdge row.1 row.2) first last small high endpoints
  refine ⟨tag, alone, endpoint, ?_⟩
  rw [OrdinaryObservation.state_ledger (observationTable witness 0) witness.data ((observationSlot 0).table_component witness)]
  exact (SP1Clean.OrdinaryObservation.stateChannel.gatedTransitionLedger_balanced_iff (startFor source.sail)
    tag.2.previous ordinary Prod.snd (fun row => OrdinaryObservation.edge row.1) binary).mpr ordinaryOrder

private theorem sentinel_injective : Function.Injective (Mode.sentinel (R := ZMod p)) := by
  intro left right equal
  have hp := Fact.out (p := 2 ^ 25 < p)
  have numeric := congrArg ZMod.val equal
  have encoded (mode : Mode) : (mode.sentinel (R := ZMod p)).val = mode.sentinel (R := ℕ) := by
    cases mode <;> simp only [Mode.sentinel] <;> exact ZMod.val_ofNat_of_lt (lt_trans (by norm_num) hp)
  rw [encoded, encoded] at numeric
  cases left <;> cases right <;> first | rfl | contradiction

/-- The ordered ordinary inputs and unique terminal selected by the accepted observation ledger. -/
structure OrderedHistory (source target : SailSnapshot) (inventory : List (Inputs (ZMod p)))
    (endRows : List (Mode × TerminalInputs (ZMod p))) where
  /-- Every active input, in increasing source clock order. -/
  path : List (Inputs (ZMod p))
  /-- The sole physical terminal across all modes. -/
  terminal : TerminalInputs (ZMod p)
  sole : endRows = [(Mode.of source target, terminal)]
  valid : terminal.Valid (Mode.of source target)
  output : (terminalEdge (Mode.of source target) terminal).2 = finalFor source target
  exhaustive : path.Perm inventory
  walk : Walk.IsWalk OrdinaryObservation.edge (startFor source) terminal.previous path
  sorted : (path.map (fun input => OrdinaryObservation.rank input.next)).Pairwise (· < ·)
  counter : Word.toBitVec64 terminal.previous.counter =
    Word.toBitVec64 (startFor (p := p) source).counter + BitVec.ofNat 64 (path.length * (startFor (p := p) source).enabled.val)
  inputs : ∀ row ∈ path, SP1Clean.OrdinaryObservation.Spec row

/-- The actual ledger recovers the verifier-selected mode and a complete ordered walk ending at
the incoming state of its sole terminal. The count includes only active ordinary inputs. -/
theorem ordered_history (witness : EnsembleWitness (ensemble image source target final))
    (checked : witness.Constraints) (funded : DeclarationsOpen witness) :
    Nonempty (OrderedHistory source.sail target.sail
      (OrdinaryObservation.activeRows (observationTable witness 0) witness.data) (terminals witness)) := by
  obtain ⟨⟨mode, terminal⟩, sole, output, linkBalance⟩ := selected_terminal witness checked funded
  have sameMode : mode = Mode.of source.sail target.sail := sentinel_injective
    (congrArg SP1Clean.OrdinaryObservation.State.clkHigh output)
  subst mode
  have terminalValid := terminals_valid witness checked (Mode.of source.sail target.sail, terminal) (by rw [sole]; simp)
  let table := observationTable witness 0
  have validTable := consumer_spec witness checked funded
  have registered : table.component = OrdinaryObservation.consumer := (observationSlot 0).table_component witness
  obtain ⟨path, exhaustive, walk, sorted, _, counter, _⟩ := OrdinaryObservation.ordered_history table witness.data
    registered validTable (startFor source.sail) terminal.previous linkBalance
  have specs := OrdinaryObservation.rows_spec table witness.data registered validTable
  refine ⟨⟨path, terminal, sole, terminalValid, output, exhaustive, walk, sorted, ?_, ?_⟩⟩
  · rwa [exhaustive.length_eq]
  · intro row member
    obtain ⟨pair, live, rfl⟩ := List.mem_map.mp (exhaustive.mem_iff.mp member)
    obtain ⟨occurs, active⟩ := List.mem_filter.mp live
    exact (specs pair occurs).2 (of_decide_eq_true active)

variable {s t : SailSnapshot} {inventory : List (Inputs (ZMod p))} {stored : List (Mode × TerminalInputs (ZMod p))}

omit [Fact (2 ^ 25 < p)] in
private theorem OrderedHistory.last_input (h : OrderedHistory s t inventory stored) :
    (h.path = [] ∧ h.terminal.previous = startFor s) ∨
      ∃ before last, h.path = before ++ [last] ∧ h.terminal.previous = last.next ∧
        ¬ (h.terminal.previous.clkHigh = 0 ∧ h.terminal.previous.clkLow = 0) := by
  have walk := h.walk
  rcases h.path.eq_nil_or_concat' with none | ⟨before, last, tape⟩
  · rw [none] at walk
    exact Or.inl ⟨none, walk.symm⟩
  · rw [tape] at walk
    obtain ⟨_, _, _, adjacent⟩ := (Walk.isWalk_append OrdinaryObservation.edge before [last] _ _).mp walk
    have lastEq : h.terminal.previous = last.next := adjacent.symm
    refine Or.inr ⟨before, last, tape, lastEq, ?_⟩
    have valid := h.inputs last (by rw [tape]; simp)
    have strict : OrdinaryObservation.rank last.previous < OrdinaryObservation.rank last.next :=
      valid.1.2.2.2.2
    intro zero
    rw [← lastEq] at strict
    simp only [OrdinaryObservation.rank, clkNat, zero.1, zero.2, ZMod.val_zero, zero_mul, zero_add] at strict
    omega

omit [Fact (2 ^ 25 < p)] in
/-- The two zero clock limbs witnessed by the terminal denote exactly an empty ordinary tape. -/
theorem OrderedHistory.zero_iff (h : OrderedHistory s t inventory stored) :
    (h.terminal.previous.clkHigh = 0 ∧ h.terminal.previous.clkLow = 0) ↔ h.path.length = 0 := by
  rcases h.last_input with ⟨empty, first⟩ | ⟨before, last, tape, _, nonzero⟩
  · simp [empty, first, startFor, SP1Clean.OrdinaryObservation.start]
  · simp [tape, nonzero]

/-- The supplied target nextPC is the last chronological ordinary receipt's decoded successor,
with the precise optional incoming register retained when every event is a host call. -/
theorem OrderedHistory.nextPC (h : OrderedHistory s t inventory stored)
    (modes : SP1Clean.OrdinaryObservation.quiet s t = true ∨ SP1Clean.OrdinaryObservation.refreshed s t = true)
    (bounds : ∀ row ∈ h.path, row.receipt.pc1.val < 65536 ∧ row.receipt.pc2.val < 65536) :
    t.registers.get? LeanRV64D.Register.nextPC =
      (h.path.map (·.receipt)).foldl (fun _ m => some (StateMsg.pcBits m)) (s.registers.get? LeanRV64D.Register.nextPC) := by
  rcases h.last_input with ⟨empty, first⟩ | ⟨before, last, tape, lastEq, nonzero⟩
  · have quiet := (OrdinaryObservation.terminal_bookkeeping modes h.valid).1
      (by rw [first]; exact ⟨rfl, rfl⟩)
    simpa only [empty, List.map_nil, List.foldl_nil] using ((SP1Clean.OrdinaryObservation.quiet_iff ..).mp quiet).2.2.2
  · have limbs := bounds last (by rw [tape]; simp)
    have terminalPC := OrdinaryObservation.terminal_nextPC_entry modes h.valid
      (by rw [lastEq]; exact limbs.1) (by rw [lastEq]; exact limbs.2) (congrArg SP1Clean.OrdinaryObservation.State.pc h.output)
    rw [ite_eq_right nonzero, lastEq] at terminalPC
    simpa only [tape, List.map_append, List.map_cons, List.map_nil, List.foldl_append, List.foldl_cons,
      List.foldl_nil, Inputs.next, StateMsg.pcBits, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ] using terminalPC

end SP1Clean.Soundness.HostObserved
