import SP1Clean.Proofs.Completeness.HostControlHistory
import SP1Clean.Soundness.HostCallReceivers
import ToClean.Air.GuardedLedger

/-! # The two original control slots from an admitted mixed tape

A real HALT terminates the segment, so its unguarded table can have only zero or one row.
The no-effect table can contain many calls and materializes Clean's full demand padding.
The physical signed host handoffs are projections of the same compiled instruction tape.
-/

namespace SP1Clean.TraceGen.ControlHandlers
open Circuit Air.Flat Semantics Machine FormalModel.Shard Soundness WitnessGeneration
private abbrev F := ZMod SP1Prime

variable {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
  (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events) (data : ProverData F)

include run in
private theorem noop_height : demandHeight (noopRows events).length ≤ 2^16 := by
  have cost (es : List ExecutionEvent) : 264 * (calls .noop es).length ≤ (es.map ExecutionEvent.duration).sum := by
    induction es with
    | nil => simp [calls]
    | cons ev es ih =>
      cases ev with
      | ordinary =>
        change 264 * (calls .noop es).length ≤ 8 + (es.map ExecutionEvent.duration).sum
        omega
      | syscall c =>
        cases used : Bucket.noop.accepts c.rawCode <;>
          simp only [calls, List.filterMap_cons, used, Bool.false_eq_true, ↓reduceIte, List.length_cons,
            List.map_cons, List.sum_cons, ExecutionEvent.duration_syscall] at ih ⊢ <;> omega
  have paid := run.2.2.1 .ticks
  rw [run.1.2.resources_ticks] at paid
  change (events.map ExecutionEvent.duration).sum ≤ 2^24 at paid
  apply demandHeight_le_pow
  rw [noopRows, List.length_map]
  have used := cost events
  omega

/-- The original HALT table. Its actual singleton or empty height already equals demand padding. -/
def haltTable : Table F :=
  Table.ofInputs HostCallReceivers.halt.component (haltRows events) data ((halt_length run).trans (by decide)) (fun _ => trivial)

/-- Populate the original shared no-effect slot, with inactive rows at every padding position. -/
def noopTable : Table F :=
  Table.ofInputs (HostNoopChip.component true) (guardedRows (noopRows events)) data
    ((guardedRows_length _).trans_le ((noop_height run).trans (by decide))) (fun _ => trivial)

/-- Both generated tables meet the sound and complete component contracts at their actual demand heights. -/
theorem tables_checked :
    let h := haltTable run data
    let n := noopTable run data
    h.Constraints ∧ h.Guarantees ∧ n.Constraints ∧ n.Guarantees ∧
    h.length = demandHeight (haltRows events).length ∧ h.length ≤ 1 ∧
    n.length = demandHeight (noopRows events).length ∧ n.length ≤ 2^16 := by
  dsimp only
  obtain ⟨halt, noop⟩ := honest run
  obtain ⟨hc, hg⟩ := Table.ofInputs_valid HostCallReceivers.halt.component (haltRows events) data ((halt_length run).trans (by decide)) (fun _ => trivial) halt
  let rs := guardedRows (F := F) (noopRows events)
  have active : ∀ r ∈ rs, (HostNoopChip.component true).circuit.ProverAssumptions r
      ((HostNoopChip.component true).inputData rs data) (.empty _) := by
    exact guardedRows_all (F := F) (HostNoopChip.ChoiceSpec (p := SP1Prime)) noop
  obtain ⟨nc, ng⟩ := Table.ofInputs_valid (HostNoopChip.component true) rs data ((guardedRows_length _).trans_le ((noop_height run).trans (by decide))) (fun _ => trivial) active
  have hh : (haltTable run data).length = (haltRows events).length := List.length_map ..
  have nh : (noopTable run data).length = demandHeight (noopRows events).length := (List.length_map ..).trans (guardedRows_length _)
  refine ⟨hc, hg, nc, ng, ?_, hh.le.trans (halt_length run), nh, nh.le.trans (noop_height run)⟩
  rw [hh]
  have fixed (n : Nat) (bound : n ≤ 1) : n = demandHeight n := by interval_cases n <;> rfl
  exact fixed _ (halt_length run)

/-- All HALT header calls and all complete terminal words are unconditionally active on these actual tables. -/
theorem halt_ledgers :
    let t := haltTable run data
    t.interactionsWith HostCallChip.channel.toRaw = ((haltRows events).map (·.call)).map HostCallChip.channel.pulledValue ∧
    t.interactionsWith HostExitBoundary.channel.toRaw = ((haltRows events).map (·.call.arg1)).map HostExitBoundary.channel.pushedValue := by
  dsimp only
  constructor
  · rw [List.map_map, List.map_eq_flatMap]
    apply Table.ofInputs_ledger
    intro env
    have rows := HostCallReceivers.halt.interactions env
    rw [HostCallReceivers.halt_message] at rows
    exact rows
  · rw [List.map_map, List.map_eq_flatMap]
    apply Table.ofInputs_ledger
    intro env
    simp only [Operations.interactionValuesWith, Component.interactionsWith_eq]
    change ((HostHaltChip.main (varFromOffset HostHaltChip.Inputs 0)).operations (size HostHaltChip.Inputs)).interactionValuesWith HostExitBoundary.channel.toRaw env = _
    rw [HostHaltChip.terminal_values]
    have field (r : Var HostHaltChip.Inputs F) : eval env r.call.arg1 = (eval env r).call.arg1 := by
      rcases r with ⟨⟨_, _, _, _, _, _, _⟩, _⟩
      simp only [circuit_norm]
    rw [field, eval_varFromOffset_valueFromOffset]
    rfl

/-- The guarded host pull on *every* physical row, including Clean's inactive padding. -/
theorem noop_ledger :
    (noopTable run data).interactionsWith HostCallChip.channel.toRaw =
      (guardedRows (F := F) (noopRows events)).map (fun r => HostCallChip.channel.pulledIfValue r.2 r.1) := by
  rw [List.map_eq_flatMap]
  apply Table.ofInputs_ledger
  intro env
  have law := (HostCallReceivers.profileNoop (p := SP1Prime) true).interactions env
  rw [HostCallReceivers.profileNoop_message] at law
  have activity : env (HostCallReceivers.profileNoop (p := SP1Prime) true).activity =
      (valueFromOffset HostNoopChip.RowInput 0 env).2 := by
    rw [← eval_varFromOffset_valueFromOffset HostNoopChip.RowInput 0 env, ← Guarded.eval_activity]
    rfl
  exact activity ▸ law

/-- The true mixed CPU constructor contributes this exact unit message for each selected real ECALL. -/
def instructionMessage? (k : Bucket) : MixedCompiledRow → Option (HostCallChip.Message F)
  | .ordinary _ => none
  | .syscall frontier _ call =>
    if k.accepts call.rawCode then some (HostCallChip.message (syscallInstruction frontier call)) else none

include run in
private theorem cpu_messages {compiled : List MixedCompiledRow}
    (built : routeMixedRows? (policy SP1Prime image) image.program AccessFrontier.initial source.realize events = some compiled) (k : Bucket) :
    compiled.filterMap (instructionMessage? k) = (calls k events).map eventHostMessage := by
  obtain ⟨other, same, size⟩ := admissibleExecution_routeMixedRows run
  cases Option.some.inj (built.symm.trans same)
  let selected (e : ExecutionEvent) : Option (HostCallChip.Message F) :=
    match e with
    | .ordinary => none
    | .syscall call => if k.accepts call.rawCode then some (eventHostMessage call) else none
  have atCut {i : Nat} {event : ExecutionEvent} {entry : MixedCompiledRow}
      (ev : events[i]? = some event) (row : compiled[i]? = some entry) :
      instructionMessage? k entry = selected event := by
    obtain ⟨_, frontier, _, _, _, found⟩ := routeMixedRows?_at built ev
    cases event with
    | ordinary =>
      obtain ⟨_, r, _, _, atRow⟩ := found
      cases Option.some.inj (row.symm.trans atRow)
      rfl
    | syscall c =>
      cases Option.some.inj (row.symm.trans found)
      cases h : k.accepts c.rawCode <;> simp [h, selected, instructionMessage?, syscallInstruction_eventMessage]
  have same : compiled.map (instructionMessage? k) = events.map selected := by
    apply List.ext_getElem
    · simpa using size
    intro i hl hr
    simp only [List.getElem_map]
    exact atCut (List.getElem?_eq_getElem (i := i) (by simpa using hr)) (List.getElem?_eq_getElem (by simpa using hl))
  have compact := congrArg (List.filterMap id) same
  simp only [List.filterMap_map, Function.id_comp] at compact
  rw [compact, calls, List.map_filterMap]
  apply List.filterMap_congr
  intro e _
  cases e with
  | ordinary => rfl
  | syscall c => cases h : k.accepts c.rawCode <;> simp [selected, h]

/-- The raw HALT and ENTER/VERIFY pulls spend precisely the real CPU pushes selected from the
single chronological compiled tape. Repeated inputs and every zero-weight padding site survive. -/
theorem host_handoffs :
    ∃ compiled, routeMixedRows? (policy SP1Prime image) image.program AccessFrontier.initial source.realize events = some compiled ∧
    ∀ msg,
      balanceOf ((haltTable run data).interactionsWith HostCallChip.channel.toRaw) msg =
        balanceOf ((compiled.filterMap (instructionMessage? .halt)).map HostCallChip.channel.pulledValue) msg ∧
      balanceOf ((noopTable run data).interactionsWith HostCallChip.channel.toRaw) msg =
        balanceOf ((compiled.filterMap (instructionMessage? .noop)).map HostCallChip.channel.pulledValue) msg := by
  obtain ⟨compiled, built, _⟩ := admissibleExecution_routeMixedRows run
  refine ⟨compiled, built, fun msg => ?_⟩
  rw [cpu_messages run built .halt, cpu_messages run built .noop, (halt_ledgers run data).1, noop_ledger]
  constructor
  · simp [haltRows, List.map_map, Function.comp_def, HostHaltChip.populate]
  · exact guarded_pull_sum HostCallChip.channel (noopRows events) id msg |>.trans (by simp [noopRows])

/-- Clean pads zero, one and three raw requests to zero, one and four rows on both
installed demand modes. Three HALT requests cannot come from an admitted segment. -/
theorem raw_heights (state : WitnessGeneration.ComponentState F)
    (registered : state.component = HostCallReceivers.halt.component ∨ state.component = HostNoopChip.component true) :
    (state.rows.size = 0 → state.targetHeight = 0) ∧ (state.rows.size = 1 → state.targetHeight = 1) ∧
    (state.rows.size = 3 → state.targetHeight = 4) := by
  have demand : state.targetHeight = demandHeight state.rows.size := by
    cases state with
    | mk component multiplicity operations interactions rows messageRows =>
      rcases registered with r | r <;> change component = _ at r <;> subst component <;>
        exact WitnessGeneration.ComponentState.targetHeight_of_demand _ rfl
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;> rw [demand, h] <;> rfl

/-- Each receiver balances the pushes of the matching instruction route separately, with
the raw physical height included in the count check for both components. -/
theorem host_matches :
    ∃ compiled, routeMixedRows? (policy SP1Prime image) image.program AccessFrontier.initial source.realize events = some compiled ∧
      ∀ k, let sends := (compiled.filterMap (instructionMessage? k)).map HostCallChip.channel.pushedValue
           let t := match k with | .halt => haltTable run data | .noop => noopTable run data
           let ledger := sends ++ t.interactionsWith HostCallChip.channel.toRaw
           ledger.length = (calls k events).length + t.length ∧ LogUpBalanced ledger ∧
             (Balance.logUp (F := F)).fits ledger.length = true ∧ BalancedInteractions ledger := by
  obtain ⟨compiled, built, sums⟩ := host_handoffs run data
  refine ⟨compiled, built, ?_⟩
  intro k
  dsimp only
  let ms := compiled.filterMap (instructionMessage? k)
  let t := match k with | .halt => haltTable run data | .noop => noopTable run data
  let ledger := ms.map HostCallChip.channel.pushedValue ++ t.interactionsWith HostCallChip.channel.toRaw
  change ledger.length = _ ∧ LogUpBalanced ledger ∧ _
  have active : ms.length = (calls k events).length := by rw [show ms = _ from cpu_messages run built k, List.length_map]
  have occurrences : (t.interactionsWith HostCallChip.channel.toRaw).length = t.length := by
    cases k with
    | halt =>
      rw [show t = haltTable run data from rfl, (halt_ledgers run data).1, List.length_map, List.length_map]
      exact (List.length_map ..).symm
    | noop =>
      rw [show t = noopTable run data from rfl, noop_ledger, List.length_map]
      exact (List.length_map ..).symm
  have count : ledger.length = (calls k events).length + t.length := by
    simp only [ledger, List.length_append, List.length_map, active, occurrences]
  have signed : LogUpBalanced ledger := by
    intro msg
    have same := HostCallChip.channel.logUp_unit_of_perm (List.Perm.refl ms) msg
    rw [balanceOf_append] at same
    rw [show ledger = _ ++ _ from rfl, balanceOf_append]
    have get : balanceOf (t.interactionsWith HostCallChip.channel.toRaw) msg =
        balanceOf (ms.map HostCallChip.channel.pulledValue) msg := by
      cases k with | halt => exact (sums msg).1 | noop => exact (sums msg).2
    rwa [get]
  have sizes := tables_checked run data
  have small : ledger.length < SP1Prime := by
    rw [count]
    have room : 2 * 2^16 < SP1Prime := by decide
    cases k with
    | halt =>
      have h := halt_length run
      simp only [haltRows, List.length_map] at h
      exact (Nat.add_le_add h sizes.2.2.2.2.2.1).trans_lt (by decide)
    | noop =>
      have h := (demandHeight_bounds (noopRows events).length).1.trans (noop_height run)
      simp only [noopRows, List.length_map] at h
      exact (Nat.add_le_add h sizes.2.2.2.2.2.2.2).trans_lt (by decide)
  have fit : (Balance.logUp (F := F)).fits ledger.length = true := by
    simpa only [Balance.logUp, decide_eq_true_eq, ComputableRingChar.char_eq, ZMod.ringChar_zmod_n] using small
  exact ⟨count, signed, fit, Balance.logUp.balancedInteractions_of_balanced _ fit signed⟩

/-- The actual terminal handler and the actual optional host endpoint close their one
terminal-word protocol, with at most two physical sites even on a stopped identity. -/
theorem terminal_closed (env : Environment F) (offset : Nat) :
    let fromHandler := (haltTable run data).interactionsWith HostExitBoundary.channel.toRaw
    let endpoint := ((HostExitBoundary.main source.host.exitCode target.host.exitCode ()).operations offset).interactionValuesWith
      HostExitBoundary.channel.toRaw env
    let ledger := fromHandler ++ endpoint
    ledger.length ≤ 2 ∧ LogUpBalanced ledger ∧ (Balance.logUp (F := F)).fits ledger.length = true ∧ BalancedInteractions ledger := by
  dsimp only
  rw [(halt_ledgers run data).2, exit_words run, HostExitBoundary.values, ite_eq_left rfl]
  let raw (before after : Option (BitVec 32)) : List (Interaction F) :=
    (((if before = none then after else none).toList.map HostExitBoundary.encode).map HostExitBoundary.channel.pushedValue) ++
      [HostExitBoundary.channel.pulledIfValue (if before = none ∧ after.isSome then 1 else 0)
        (HostExitBoundary.encode (after.getD 0))]
  have short (before after : Option (BitVec 32)) : (raw before after).length ≤ 2 := by
    cases before <;> cases after <;> simp [raw]
  have disabled (w : Word F) : LogUpBalanced [HostExitBoundary.channel.pulledIfValue 0 w] := by
    intro msg
    rw [balanceOf_cons]
    simp [Channel.pulledIfValue, Interaction.signedMult, balanceOf]
  have accepted (w : Word F) : LogUpBalanced [HostExitBoundary.channel.pushedValue w, HostExitBoundary.channel.pulledIfValue 1 w] :=
    HostExitBoundary.channel.logUp_unit_of_perm (List.Perm.refl [w])
  have signed (before after : Option (BitVec 32)) : LogUpBalanced (raw before after) := by
    cases before <;> cases after <;> first | exact disabled _ | exact accepted _
  let ledger := raw source.host.exitCode target.host.exitCode
  have fit : (Balance.logUp (F := F)).fits ledger.length = true := by
    simp only [Balance.logUp, decide_eq_true_eq, ComputableRingChar.char_eq, ZMod.ringChar_zmod_n]
    exact (short _ _).trans_lt (by decide : 2 < SP1Prime)
  exact ⟨short _ _, signed _ _, fit, Balance.logUp.balancedInteractions_of_balanced ledger fit (signed _ _)⟩

end SP1Clean.TraceGen.ControlHandlers
