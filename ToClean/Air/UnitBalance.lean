module

public import Clean.Air.Balance

/-! # Exact message balance for unit transitions

Clean proves counting facts for constant-multiplicity interactions, but does not expose the
typed message permutation of a ledger of unit transitions. This addition derives that
permutation from `BalancedInteractions` and proves the converse. Verifier-specific count
bounds are checked separately on the complete physical ledger. It is independent of row semantics, ordering, and any particular machine.

The intended upstream home is `Clean/Air/Balance.lean`, beside its constant-multiplicity
counting lemmas. No existing Clean declaration is changed.
-/

@[expose] public section

/-- Removing disabled interactions preserves exactly the abstract balance facts.
Count bounds belong to the chosen verifier balance check, before this projection. -/
theorem BalancedInteractions.filter_nonzero_iff {F : Type} [FiniteField F]
    {interactions : List (Interaction F)} :
    BalancedInteractions (interactions.filter fun i => decide (i.mult ≠ 0)) ↔
      BalancedInteractions interactions := by
  have counts (direction : Channel.Direction) (msg : Array F) :
      activeCount (interactions.filter fun i => decide (i.mult ≠ 0)) direction msg =
        activeCount interactions direction msg := by
    simp only [activeCount, List.countP_filter]
    apply List.countP_congr
    intro i _
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    tauto
  constructor
  · intro balanced
    constructor
    · intro a ha pull
      have ha' : a ∈ interactions.filter fun i => decide (i.mult ≠ 0) := by
        simp [ha, pull.2]
      obtain ⟨b, hb, msg, push⟩ := balanced.exists_push_of_pull a ha' pull
      exact ⟨b, (List.mem_filter.mp hb).1, msg, push⟩
    · intro msg binary
      rw [← counts .push, ← counts .pull]
      exact balanced.activeCount_push_eq_activeCount_pull_of_isBool msg
        (fun i hi => binary i (List.mem_filter.mp hi).1)
  · intro balanced
    constructor
    · intro a ha pull
      obtain ⟨b, hb, msg, push⟩ :=
        balanced.exists_push_of_pull a (List.mem_filter.mp ha).1 pull
      exact ⟨b, by simp [hb, push.1], msg, push⟩
    · intro msg binary
      rw [counts, counts]
      apply balanced.activeCount_push_eq_activeCount_pull_of_isBool
      intro i hi hmsg
      by_cases zero : i.mult = 0
      · exact .inl zero
      · exact binary i (by simp [hi, zero]) hmsg

/-- Erase zero occurrences only when projecting the physical ledger to active messages. -/
theorem BalancedInteractions.filter_nonzero {F : Type} [FiniteField F]
    {interactions : List (Interaction F)} (balanced : BalancedInteractions interactions) :
    BalancedInteractions (interactions.filter fun i => decide (i.mult ≠ 0)) :=
  filter_nonzero_iff.mpr balanced

/-- Abstract balance also supplies signed field balance when every multiplicity is Boolean. -/
theorem BalancedInteractions.logUp_of_isBool {F : Type} [FiniteField F]
    {interactions : List (Interaction F)} (balanced : BalancedInteractions interactions)
    (binary : ∀ i ∈ interactions, IsBool i.mult) : LogUpBalanced interactions := by
  intro msg
  rw [balanceOf_eq_sub_of_isBool (fun i hi _ => binary i hi),
    balanced.activeCount_push_eq_activeCount_pull_of_isBool msg (fun i hi _ => binary i hi), sub_self]

namespace Channel

variable {F : Type} [FiniteField F]
variable {Message : TypeMap} [ProvableType Message]

/-- The actual unit interactions of a boundary and a list of transitions. -/
def transitionLedger {Row : Type*} (channel : Channel F Message)
    (initial final : Message F) (rows : List Row) (edge : Row → Message F × Message F) :
    List (Interaction F) :=
  [channel.pushedValue initial, channel.pulledValue final] ++
    rows.flatMap (fun row => [channel.pulledValue (edge row).1,
      channel.pushedValue (edge row).2])

/-- Collecting unit transition pairs preserves every interaction occurrence. -/
theorem pairedLedger_perm {Row : Type*} (channel : Channel F Message)
    (rows : List Row) (edge : Row → Message F × Message F) :
    (rows.flatMap (fun row => [channel.pulledValue (edge row).1,
      channel.pushedValue (edge row).2])).Perm
      ((rows.map (fun row => channel.pushedValue (edge row).2)) ++
       (rows.map (fun row => channel.pulledValue (edge row).1))) := by
  induction rows with
  | nil => exact .refl _
  | cons row rest ih =>
    simp only [List.flatMap_cons, List.map_cons, List.cons_append, List.nil_append]
    exact ((ih.cons _).cons _).trans
      ((List.Perm.swap _ _ _).trans (List.perm_middle.symm.cons _))

/-- Collecting unit pushes and pulls changes only the order of the real interaction list. -/
theorem transitionLedger_perm {Row : Type*} (channel : Channel F Message)
    (initial final : Message F) (rows : List Row) (edge : Row → Message F × Message F) :
    (channel.transitionLedger initial final rows edge).Perm
      (((initial :: rows.map (fun row => (edge row).2)).map channel.pushedValue) ++
       ((final :: rows.map (fun row => (edge row).1)).map channel.pulledValue)) := by
  unfold transitionLedger
  have split := channel.pairedLedger_perm rows edge
  simpa only [List.map_cons, List.map_map, Function.comp_def, List.cons_append, List.nil_append] using
    (split.cons (channel.pulledValue final) |>.cons (channel.pushedValue initial)).trans
      (List.perm_middle.symm.cons _)

/-- Unit balance is exactly a permutation of typed messages, independently of the
balance check that supplied the abstract facts. -/
theorem balanced_unit_iff (channel : Channel F Message) (produced consumed : List (Message F)) :
    BalancedInteractions (produced.map channel.pushedValue ++ consumed.map channel.pulledValue) ↔
      produced.Perm consumed := by
  have encode_injective : Function.Injective (fun value : Message F => (toElements value).toArray) := by
    intro a b equal
    have vectors := Vector.toArray_inj.mp equal
    simpa only [ProvableType.fromElements_toElements] using congrArg fromElements vectors
  have binary : ∀ i ∈ produced.map channel.pushedValue ++ consumed.map channel.pulledValue,
      IsBool i.mult := by
    intro i hi
    rcases List.mem_append.mp hi with hi | hi <;>
      obtain ⟨value, _, rfl⟩ := List.mem_map.mp hi <;> exact .inr rfl
  have messages (direction : Channel.Direction) :
      activeMessages (produced.map channel.pushedValue ++ consumed.map channel.pulledValue) direction =
        (if direction = .push then produced else consumed).map
          (fun value => (toElements value).toArray) := by
    cases direction <;>
      simp [activeMessages, List.filter_map, Function.comp_def, pushedValue, pulledValue]
  constructor
  · intro balanced
    apply (List.map_perm_map_iff encode_injective).mp
    rw [List.perm_iff_count]
    intro msg
    have counts := balanced.activeCount_push_eq_activeCount_pull_of_isBool msg
      (fun i hi _ => binary i hi)
    simpa [← count_activeMessages, messages] using counts
  · intro perm
    apply Balance.multiset.balancedInteractions_of_balanced _ rfl
    refine ⟨binary, ?_⟩
    simpa [messages] using perm.map (fun value => (toElements value).toArray)

/-- A closed unit-transition ledger has exactly the same produced and consumed typed messages. -/
theorem pairedLedger_balanced_iff {Row : Type*} (channel : Channel F Message)
    (rows : List Row) (edge : Row → Message F × Message F) :
    BalancedInteractions (rows.flatMap (fun row =>
      [channel.pulledValue (edge row).1, channel.pushedValue (edge row).2])) ↔
      (rows.map (fun row => (edge row).2)).Perm (rows.map (fun row => (edge row).1)) := by
  have perm := channel.pairedLedger_perm rows edge
  have transport : BalancedInteractions (rows.flatMap (fun row =>
      [channel.pulledValue (edge row).1, channel.pushedValue (edge row).2])) ↔
      BalancedInteractions ((rows.map (fun row => channel.pushedValue (edge row).2)) ++
        (rows.map (fun row => channel.pulledValue (edge row).1))) :=
    ⟨fun valid => BalancedInteractions.of_perm valid perm,
      fun valid => BalancedInteractions.of_perm valid perm.symm⟩
  rw [transport]
  simpa only [List.map_map, Function.comp_def] using
    channel.balanced_unit_iff (rows.map fun row => (edge row).2) (rows.map fun row => (edge row).1)

/-- A balanced transition ledger yields the endpoint permutation needed by a ranked walk. -/
theorem transitionLedger_balanced_iff {Row : Type*} (channel : Channel F Message)
    (initial final : Message F) (rows : List Row) (edge : Row → Message F × Message F) :
    BalancedInteractions (channel.transitionLedger initial final rows edge) ↔
      (initial :: rows.map (fun row => (edge row).2)).Perm
          (final :: rows.map (fun row => (edge row).1)) := by
  have perm := transitionLedger_perm channel initial final rows edge
  have transport : BalancedInteractions (channel.transitionLedger initial final rows edge) ↔
      BalancedInteractions (((initial :: rows.map (fun row => (edge row).2)).map channel.pushedValue) ++
        ((final :: rows.map (fun row => (edge row).1)).map channel.pulledValue)) :=
    ⟨fun valid => BalancedInteractions.of_perm valid perm,
      fun valid => BalancedInteractions.of_perm valid perm.symm⟩
  rw [transport, balanced_unit_iff]

/-- Removing zero contributions from Boolean-gated producers selects their unit occurrences. -/
theorem pushedIfValues_filter_nonzero {Row : Type*} (channel : Channel F Message)
    (rows : List Row) (gate : Row → F) (message : Row → Message F)
    (binary : ∀ row ∈ rows, gate row = 0 ∨ gate row = 1) :
    ((rows.map fun row => channel.pushedIfValue (gate row) (message row)).filter
      fun interaction => decide (interaction.mult ≠ 0)) =
      (rows.filter fun row => decide (gate row = 1)).map (fun row => channel.pushedValue (message row)) := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    have tail := ih (fun other member => binary other (List.mem_cons_of_mem _ member))
    rcases binary row (List.mem_cons_self ..) with equal | equal <;>
      simp only [List.map_cons, List.filter_cons, pushedIfValue, equal, ne_eq,
        not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte,
        zero_ne_one, one_ne_zero, not_false_eq_true, decide_true, List.map_cons,
        pushedValue]
    · exact tail
    · exact congrArg (List.cons _) tail

/-- Removing zero contributions from Boolean-gated consumers selects their unit occurrences. -/
theorem pulledIfValues_filter_nonzero {Row : Type*} (channel : Channel F Message)
    (rows : List Row) (gate : Row → F) (message : Row → Message F)
    (binary : ∀ row ∈ rows, gate row = 0 ∨ gate row = 1) :
    ((rows.map fun row => channel.pulledIfValue (gate row) (message row)).filter
      fun interaction => decide (interaction.mult ≠ 0)) =
      (rows.filter fun row => decide (gate row = 1)).map (fun row => channel.pulledValue (message row)) := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    have tail := ih (fun other member => binary other (List.mem_cons_of_mem _ member))
    rcases binary row (List.mem_cons_self ..) with equal | equal <;>
      simp only [List.map_cons, List.filter_cons, pulledIfValue, equal, ne_eq,
        not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte,
        zero_ne_one, one_ne_zero, not_false_eq_true, decide_true, List.map_cons,
        pulledValue]
    · exact tail
    · exact congrArg (List.cons _) tail

/-- A binary-gated producer inventory and unit consumers agree on complete typed messages.
Disabled physical rows may remain in the original ledger and its count bound. -/
theorem gated_unit_perm_of_balanced {Row : Type*} (channel : Channel F Message)
    (rows : List Row) (gate : Row → F) (message : Row → Message F) (consumed : List (Message F))
    (binary : ∀ row ∈ rows, gate row = 0 ∨ gate row = 1)
    (balanced : BalancedInteractions
      (rows.map (fun row => channel.pushedIfValue (gate row) (message row)) ++
        consumed.map channel.pulledValue)) :
    ((rows.filter fun row => decide (gate row = 1)).map message).Perm consumed := by
  have producers := channel.pushedIfValues_filter_nonzero rows gate message binary
  have consumers : ((consumed.map channel.pulledValue).filter
      fun interaction => decide (interaction.mult ≠ 0)) = consumed.map channel.pulledValue := by
    apply List.filter_eq_self.mpr
    intro interaction member
    obtain ⟨value, _, rfl⟩ := List.mem_map.mp member
    simp [pulledValue]
  have selected := balanced.filter_nonzero
  rw [List.filter_append, producers, consumers] at selected
  apply (channel.balanced_unit_iff _ consumed).mp
  simpa only [List.map_map, Function.comp_def] using selected

/-- Boolean-gated physical producers and consumers match exactly on their active messages.
The verifier checks its count bound on the physical ledger, including padding on both sides. -/
theorem gated_perm_of_balanced {Produced Consumed : Type*} (channel : Channel F Message)
    (produced : List Produced) (produceGate : Produced → F) (produceMessage : Produced → Message F)
    (consumed : List Consumed) (consumeGate : Consumed → F) (consumeMessage : Consumed → Message F)
    (producerBinary : ∀ row ∈ produced, produceGate row = 0 ∨ produceGate row = 1)
    (consumerBinary : ∀ row ∈ consumed, consumeGate row = 0 ∨ consumeGate row = 1)
    (balanced : BalancedInteractions
      (produced.map (fun row => channel.pushedIfValue (produceGate row) (produceMessage row)) ++
        consumed.map (fun row => channel.pulledIfValue (consumeGate row) (consumeMessage row)))) :
    ((produced.filter fun row => decide (produceGate row = 1)).map produceMessage).Perm
      ((consumed.filter fun row => decide (consumeGate row = 1)).map consumeMessage) := by
  have selected := balanced.filter_nonzero
  rw [List.filter_append, channel.pushedIfValues_filter_nonzero produced produceGate produceMessage producerBinary,
    channel.pulledIfValues_filter_nonzero consumed consumeGate consumeMessage consumerBinary] at selected
  apply (channel.balanced_unit_iff _ _).mp
  simpa only [List.map_map, Function.comp_def] using selected

/-- The physical ledger of Boolean-gated transitions, including both disabled occurrences. -/
def gatedTransitionLedger {Row : Type*} (channel : Channel F Message)
    (initial final : Message F) (rows : List Row) (gate : Row → F)
    (edge : Row → Message F × Message F) : List (Interaction F) :=
  [channel.pushedValue initial, channel.pulledValue final] ++
    rows.flatMap (fun row => [channel.pulledIfValue (gate row) (edge row).1,
      channel.pushedIfValue (gate row) (edge row).2])

theorem gatedTransitionLedger_length {Row : Type*} (channel : Channel F Message)
    (initial final : Message F) (rows : List Row) (gate : Row → F)
    (edge : Row → Message F × Message F) :
    (channel.gatedTransitionLedger initial final rows gate edge).length = 2 * (rows.length + 1) := by
  have pairs : (rows.flatMap (fun row =>
      [channel.pulledIfValue (gate row) (edge row).1,
        channel.pushedIfValue (gate row) (edge row).2])).length = 2 * rows.length := by
    induction rows with
    | nil => simp
    | cons row rest ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_nil, ih]
      omega
  simp only [gatedTransitionLedger, List.length_append, List.length_cons, List.length_nil, pairs]
  omega

/-- Active transition pairs are exactly the nonzero occurrences of their physical ledger. -/
theorem gatedPairs_filter_nonzero {Row : Type*} (channel : Channel F Message)
    (rows : List Row) (gate : Row → F) (edge : Row → Message F × Message F)
    (binary : ∀ row ∈ rows, gate row = 0 ∨ gate row = 1) :
    ((rows.flatMap fun row => [channel.pulledIfValue (gate row) (edge row).1,
      channel.pushedIfValue (gate row) (edge row).2]).filter
      fun interaction => decide (interaction.mult ≠ 0)) =
    (rows.filter fun row => decide (gate row = 1)).flatMap
      (fun row => [channel.pulledValue (edge row).1, channel.pushedValue (edge row).2]) := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    have tail := ih (fun other member => binary other (List.mem_cons_of_mem _ member))
    simp only [List.flatMap_cons, List.filter_append]
    rw [tail]
    rcases binary row (List.mem_cons_self ..) with disabled | active
    · simp [pulledIfValue, pushedIfValue, disabled]
    · simp [pulledIfValue, pushedIfValue, pulledValue, pushedValue, active]

/-- Erasing zero contributions is an explicit semantic projection of the original ledger. -/
theorem gatedTransitionLedger_filter_nonzero {Row : Type*} (channel : Channel F Message)
    (initial final : Message F) (rows : List Row) (gate : Row → F)
    (edge : Row → Message F × Message F)
    (binary : ∀ row ∈ rows, gate row = 0 ∨ gate row = 1) :
    ((channel.gatedTransitionLedger initial final rows gate edge).filter
      fun interaction => decide (interaction.mult ≠ 0)) =
      channel.transitionLedger initial final (rows.filter fun row => decide (gate row = 1)) edge := by
  have pairs := channel.gatedPairs_filter_nonzero rows gate edge binary
  simp only [gatedTransitionLedger, transitionLedger, List.filter_append, pairs]
  simp [pushedValue, pulledValue]

/-- Abstract physical balance is equivalent to an active endpoint permutation. -/
theorem gatedTransitionLedger_balanced_iff {Row : Type*} (channel : Channel F Message)
    (initial final : Message F) (rows : List Row) (gate : Row → F)
    (edge : Row → Message F × Message F)
    (binary : ∀ row ∈ rows, gate row = 0 ∨ gate row = 1) :
    BalancedInteractions (channel.gatedTransitionLedger initial final rows gate edge) ↔
      (initial :: ((rows.filter fun row => decide (gate row = 1)).map fun row => (edge row).2)).Perm
          (final :: ((rows.filter fun row => decide (gate row = 1)).map fun row => (edge row).1)) := by
  rw [← BalancedInteractions.filter_nonzero_iff,
    channel.gatedTransitionLedger_filter_nonzero initial final rows gate edge binary,
    channel.transitionLedger_balanced_iff]

end Channel
