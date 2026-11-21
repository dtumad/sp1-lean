import SP1Clean.Proofs.Completeness.OrdinaryObservation
import SP1Clean.Proofs.Completeness.StateInventory
import SP1Clean.FormalModel.Contracts.OrdinaryObservationBoundary
import ToClean.Air.UnitBalance

/-! # Construct the ordinary observation history from the compiler's routed events

Each routed event supplies its original, unnormalized successor State message. The consumer
population carries the retirement counter and flag across exactly those messages in execution
order. Chronological bounded source clocks suffice for every constructed consumer row.
-/

namespace SP1Clean.OrdinaryObservation

open Circuit Air.Flat Semantics TraceGen

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

/-- Build consumer inputs from their original State messages and return the terminal's held link. -/
def historyFromReceipts (initial : State (ZMod p)) :
    List (Channels.StateMsg (ZMod p)) → List (Inputs (ZMod p)) × State (ZMod p)
  | [] => ([], initial)
  | receipt :: rest =>
    let input := populate initial receipt
    let tail := historyFromReceipts input.next rest
    (input :: tail.1, tail.2)

/-- Construct the ordinary history from the same raw successors used by the event compiler. -/
def history (initial : State (ZMod p)) (events : List RoutedEvent) :=
  historyFromReceipts initial (events.map (·.rawPushState.toMessage))

omit [Fact (2 ^ 25 < p)] in
private theorem history_nil (initial : State (ZMod p)) : history initial [] = ([], initial) := rfl

omit [Fact (2 ^ 25 < p)] in
private theorem history_cons (initial : State (ZMod p)) (event : RoutedEvent) (events : List RoutedEvent) :
    history initial (event :: events) =
      let input := populate initial event.rawPushState.toMessage
      let tail := history input.next events
      (input :: tail.1, tail.2) := rfl

omit [Fact (2 ^ 25 < p)] in
/-- Each routed family uses the same uncarried eight-tick successor clock. -/
private theorem raw_clocks (event : RoutedEvent) :
    event.rawPushState.clkHigh = event.clock / 2 ^ 24 ∧
    event.rawPushState.clkLow = event.clock % 2 ^ 24 + 8 := by
  obtain ⟨id, event⟩ := event
  cases id <;> exact ⟨rfl, rfl⟩

/-- Recover the exact natural source timestamp, including at low-limb carry boundaries. -/
private theorem next_clock (initial : State (ZMod p)) (event : RoutedEvent) (bound : event.clock < 2 ^ 48) :
    let next := (populate initial event.rawPushState.toMessage).next
    next.clkHigh.val = event.clock / 2 ^ 24 ∧ next.clkLow.val = event.clock % 2 ^ 24 := by
  have field := Fact.out (p := 2 ^ 25 < p)
  dsimp only [Inputs.next, populate, StateRecord.toMessage]
  rw [(raw_clocks event).1, (raw_clocks event).2, Nat.cast_add, Nat.cast_ofNat, add_sub_cancel_right]
  exact ⟨ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)⟩

omit [Fact (2 ^ 25 < p)] in
/-- A consumer exists for every event, using its exact raw State-bus successor. -/
theorem history_receipts (initial : State (ZMod p)) (events : List RoutedEvent) :
    (history initial events).1.map (·.receipt) = events.map (·.rawPushState.toMessage) := by
  induction events generalizing initial with
  | nil => rfl
  | cons event rest ih => simp only [history_cons, List.map_cons, populate, ih]

omit [Fact (2 ^ 25 < p)] in
/-- The consumer adds precisely one physical row per ordinary instruction. -/
theorem history_length (initial : State (ZMod p)) (events : List RoutedEvent) :
    (history initial events).1.length = events.length := by
  simpa only [List.length_map] using congrArg List.length (history_receipts initial events)

private theorem history_valid (initial : State (ZMod p)) (events : List RoutedEvent)
    (flag : IsBool initial.enabled) (counter : Word.isU64 initial.counter)
    (high : initial.clkHigh.val < 2 ^ 24) (low : initial.clkLow.val < 2 ^ 24)
    (later : ∀ event ∈ events, clkNat initial.clkHigh initial.clkLow < event.clock)
    (bounded : ∀ event ∈ events, event.clock < 2 ^ 48)
    (ordered : events.Pairwise (fun a b => a.clock < b.clock)) :
    ∀ input ∈ (history initial events).1, Spec input := by
  induction events generalizing initial with
  | nil => simp [history_nil]
  | cons event rest ih =>
    let input := populate initial (event.rawPushState.toMessage (p := p))
    have bounds := bounded event (.head _)
    obtain ⟨hi, lo⟩ := next_clock initial event bounds
    have rank : clkNat input.next.clkHigh input.next.clkLow = event.clock := by
      unfold clkNat
      rw [hi, lo, Nat.div_add_mod']
    have valid : Spec input := by
      apply populate_spec _ _ flag counter
      refine ⟨high, low, hi.trans_lt (by omega), lo.trans_lt (Nat.mod_lt _ (by decide)), ?_⟩
      change clkNat initial.clkHigh initial.clkLow < clkNat input.next.clkHigh input.next.clkLow
      rw [rank]
      exact later event (.head _)
    obtain ⟨allLater, sorted⟩ := List.pairwise_cons.mp ordered
    intro row member
    change row ∈ input :: (history input.next rest).1 at member
    rcases List.mem_cons.mp member with rfl | tail
    · exact valid
    · exact ih input.next flag valid.2.2.2.1 (hi.trans_lt (by omega)) (lo.trans_lt (Nat.mod_lt _ (by decide)))
        (fun other inside => rank.trans_lt (allLater _ inside)) (fun other inside => bounded _ (.tail _ inside)) sorted row tail

/-- The supplied snapshot initializes a valid chain for any strictly ordered bounded ordinary
source times; host steps may occur between any two of them. -/
theorem history_spec (source : SailSnapshot) (events : List RoutedEvent)
    (positive : ∀ event ∈ events, 0 < event.clock) (bounded : ∀ event ∈ events, event.clock < 2 ^ 48)
    (ordered : events.Pairwise (fun a b => a.clock < b.clock)) :
    ∀ input ∈ (history (startFor (p := p) source) events).1, Spec input := by
  apply history_valid _ events _ _ _ _ _ bounded ordered
  · change IsBool (flagFor (p := p) source)
    unfold flagFor
    split <;> simp [IsBool]
  · exact Soundness.Target.isU64_bitVecToWord _
  · change (0 : ZMod p).val < 2 ^ 24
    simp
  · change (0 : ZMod p).val < 2 ^ 24
    simp
  · simpa only [startFor, start, clkNat, ZMod.val_zero, Nat.zero_mul, Nat.add_zero] using positive

omit [Fact (2 ^ 25 < p)] in
/-- The generated state ledger balances from the supplied initial link to the genuine final
consumer link even for an empty sequence or a repeated receipt. -/
theorem history_states (initial : State (ZMod p)) (events : List RoutedEvent) :
    BalancedInteractions (stateChannel.transitionLedger initial (history initial events).2
      (history initial events).1 (fun input => (input.previous, input.next))) := by
  rw [Channel.transitionLedger_balanced_iff]
  induction events generalizing initial with
  | nil => exact .refl _
  | cons event rest ih =>
    let input := populate initial (event.rawPushState.toMessage (p := p))
    let tail := history input.next rest
    exact ((ih input.next).cons initial).trans (List.Perm.swap _ _ _)

omit [Fact (2 ^ 25 < p)] in
/-- Segment concatenation computes the same held observation link as a single pass. -/
theorem history_append (initial : State (ZMod p)) (left right : List RoutedEvent) :
    history initial (left ++ right) =
      let first := history initial left
      let last := history first.2 right
      (first.1 ++ last.1, last.2) := by
  induction left generalizing initial with
  | nil => rfl
  | cons event rest ih => simp only [List.cons_append, history_cons, ih]

/-- The terminal mode is satisfied exactly when its empty/nonempty case agrees with the
actual number of routed ordinary instructions. The unrestricted mode accepts either case. -/
theorem history_terminal (source : SailSnapshot) (events : List RoutedEvent) (mode : Mode)
    (positive : ∀ event ∈ events, 0 < event.clock) (bounded : ∀ event ∈ events, event.clock < 2 ^ 48) :
    TerminalSpec mode (history (startFor (p := p) source) events).2 ↔
      match mode with
      | .empty => events = []
      | .nonempty => events ≠ []
      | .any => True := by
  induction events using List.reverseRecOn with
  | nil =>
    cases mode <;> simp [TerminalSpec, history_nil, startFor, start]
  | append_singleton before last _ =>
    let initial := (history (startFor (p := p) source) before).2
    let result := (populate initial last.rawPushState.toMessage).next
    have pos := positive last (by simp)
    have bound := bounded last (by simp)
    obtain ⟨high, low⟩ := next_clock initial last bound
    have canonical : result.clkHigh.val < 2^24 ∧ result.clkLow.val < 2^24 :=
      ⟨high.trans_lt (by omega), low.trans_lt (Nat.mod_lt _ (by decide))⟩
    have nonzero : ¬ (result.clkHigh = 0 ∧ result.clkLow = 0) := by
      rintro ⟨h, l⟩
      have hi : result.clkHigh.val = 0 := by rw [h, ZMod.val_zero]
      have lo : result.clkLow.val = 0 := by rw [l, ZMod.val_zero]
      change result.clkHigh.val = _ at high
      change result.clkLow.val = _ at low
      omega
    rw [history_append]
    cases mode <;>
      simp only [history_cons, history_nil, TerminalSpec, List.append_eq_nil_iff, List.cons_ne_self, and_false]
    · exact ⟨fun checked => nonzero checked.2.2, False.elim⟩
    · exact ⟨fun _ => by simp, fun _ => ⟨canonical.1, canonical.2, nonzero⟩⟩
    · exact iff_true_intro ⟨canonical.1, canonical.2, trivial⟩

/-- Clean's physical table builder satisfies all consumer constraints directly from the routed
execution times. Canonical table data and the builder's 64-bit physical index bound are explicit. -/
theorem history_constraints {generation : WitnessGeneration.DemandMode (ZMod p) Inputs}
    (source : SailSnapshot) (events : List RoutedEvent) (data : ProverData (ZMod p))
    (positive : ∀ event ∈ events, 0 < event.clock) (bounded : ∀ event ∈ events, event.clock < 2 ^ 48)
    (ordered : events.Pairwise (fun a b => a.clock < b.clock))
    (sizeBound : events.length ≤ UInt64.size)
    (canonical : data.tables (circuit (p := p)).name (size Inputs) =
      ((history (startFor source) events).1.map toElements).toArray) :
    (construct (generation := generation) (history (startFor source) events).1 data
      (by rwa [history_length]) canonical).Constraints :=
  construct_constraints _ _ _ _ (history_spec source events positive bounded ordered)

/-- The generated physical consumer table balances the routed instruction receipts and the
endpoint ledger for the entire generated chain, preserving every duplicate occurrence. -/
theorem history_physical_ledgers {generation : WitnessGeneration.DemandMode (ZMod p) Inputs}
    (initial : State (ZMod p)) (events : List RoutedEvent) (data : ProverData (ZMod p))
    (sizeBound : events.length ≤ UInt64.size)
    (canonical : data.tables (circuit (p := p)).name (size Inputs) =
      ((history initial events).1.map toElements).toArray) :
    let table := construct (generation := generation) (history initial events).1 data
      (by rwa [history_length]) canonical
    BalancedInteractions ((events.map fun event => InstructionReceipt.channel.pushedValue event.rawPushState.toMessage) ++
      table.interactionsWith InstructionReceipt.channel.toRaw) ∧
    BalancedInteractions ([stateChannel.pushedValue initial, stateChannel.pulledValue (history initial events).2] ++
      table.interactionsWith stateChannel.toRaw) := by
  dsimp only
  rw [construct_receipts, construct_states]
  refine ⟨?_, history_states initial events⟩
  have same := (InstructionReceipt.channel (p := p)).balanced_unit_iff
    (events.map fun event => event.rawPushState.toMessage)
    ((history initial events).1.map Inputs.receipt)
  simpa only [List.map_map, Function.comp_def] using same.mpr (by rw [history_receipts])

end SP1Clean.OrdinaryObservation
