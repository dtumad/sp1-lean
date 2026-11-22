import SP1Clean.Proofs.Completeness.EventBuckets
import SP1Clean.Soundness.StateCanon
import SP1Clean.FormalModel.TraceGen.Bump
import SP1Clean.Machine.Ledger.InteractionProjection

/-!
# Canonical State inventories

Instruction occurrences are compiled chronologically but stored physically in twenty-five
chip-indexed tables.  State refreshes are stored in one further table.  This module keeps those
orders separate:

* `RoutedEvent.pullState` and `RoutedEvent.rawPushState` are the field-free State records emitted
  by one instruction occurrence;
* `stateBumpEvents` inserts a real `StateBump` exactly when the raw pushed limbs are not already
  canonical;
* `chronologicalStateLinks` interleaves every refresh immediately after the instruction which
  requires it; and
* `physicalStateLinks_perm_chronological` proves that the chip-bucketed instruction links followed
  by the separate bump-table links are a permutation of that chronological stream.

No channel balance or AIR witness is used in the construction. The separate `StateHistory`
adapter connects these projections to built tables. Keeping the semantic inventory below assembly
lets the native compiler derive physical capacity from the existing execution limit.
-/

namespace SP1Clean.TraceGen

open SP1Clean.Channels
open SP1Clean.LookupAccessList

/-! ## Field-free State records -/

/-- The five naturals carried by one State-bus message, before embedding in a prime field. -/
structure StateRecord where
  clkHigh : ℕ
  clkLow : ℕ
  pc0 : ℕ
  pc1 : ℕ
  pc2 : ℕ
deriving DecidableEq, Repr

namespace StateRecord

/-- Canonical limb split of a semantic clock and program counter. -/
def canonical (clock pc : ℕ) : StateRecord where
  clkHigh := clock / 2 ^ 24
  clkLow := clock % 2 ^ 24
  pc0 := pc % 2 ^ 16
  pc1 := pc / 2 ^ 16 % 2 ^ 16
  pc2 := pc / 2 ^ 32 % 2 ^ 16

/-- The `StateBump` input which pulls this possibly drifted record. -/
def toBumpEvent (record : StateRecord) : StateBumpEvent where
  clkHigh := record.clkHigh
  clkLow := record.clkLow
  pc0 := record.pc0
  pc1 := record.pc1
  pc2 := record.pc2

/-- The canonical record obtained by running the `StateBump` carry cascade. -/
def normalize (record : StateRecord) : StateRecord where
  clkHigh := record.toBumpEvent.nextClkHigh
  clkLow := record.toBumpEvent.nextClkLow
  pc0 := record.toBumpEvent.nextPc0
  pc1 := record.toBumpEvent.nextPc1
  pc2 := record.toBumpEvent.nextPc2

/-- A field embedding used only at the interaction-ledger boundary. -/
def toMessage {p : ℕ} [NeZero p] (record : StateRecord) : StateMsg (ZMod p) :=
  ⟨record.clkHigh, record.clkLow, record.pc0, record.pc1, record.pc2⟩

/-- The exact Clean lookup key of the embedded State record. -/
def key {p : ℕ} [NeZero p] (record : StateRecord) : LookupKey :=
  msgToken Channels.stateChannel (record.toMessage (p := p))

end StateRecord

/-- Canonical public State endpoints, in the same five-limb representation used by the boundary
verifier row. -/
structure StateBoundary where
  initial : StateRecord
  final : StateRecord

namespace StateBoundary

/-- Construct both public endpoints from semantic clocks and program counters. -/
def canonical (initialClock initialPc finalClock finalPc : ℕ) : StateBoundary where
  initial := StateRecord.canonical initialClock initialPc
  final := StateRecord.canonical finalClock finalPc

end StateBoundary

namespace StateRecord

variable {p : ℕ} [Fact p.Prime]

/-- The generated StateBump row pulls exactly the raw field-free record. -/
@[simp] theorem pulledMessage_stateBumpCols (record : StateRecord) :
    Soundness.StateBumpChip.pulledMessage
        (stateBumpCols (p := p) record.toBumpEvent) = record.toMessage (p := p) := rfl

/-- The generated StateBump row pushes exactly the normalized field-free record. -/
@[simp] theorem pushedMessage_stateBumpCols (record : StateRecord) :
    Soundness.StateBumpChip.pushedMessage
        (stateBumpCols (p := p) record.toBumpEvent) = record.normalize.toMessage (p := p) := by
  unfold Soundness.StateBumpChip.pushedMessage stateBumpCols normalize toMessage
  congr 1
  · change
      ((record.toBumpEvent.nextClkHigh % 256 : ℕ) : ZMod p) +
          ((record.toBumpEvent.nextClkHigh / 256 : ℕ) : ZMod p) * 256 =
        ((record.toBumpEvent.nextClkHigh : ℕ) : ZMod p)
    simpa using congrArg (fun n : ℕ => (n : ZMod p))
      (Nat.mod_add_div' record.toBumpEvent.nextClkHigh 256)
  · change
      ((record.toBumpEvent.nextClkLow % 65536 : ℕ) : ZMod p) +
          ((record.toBumpEvent.nextClkLow / 65536 : ℕ) : ZMod p) * 65536 =
        ((record.toBumpEvent.nextClkLow : ℕ) : ZMod p)
    simpa using congrArg (fun n : ℕ => (n : ZMod p))
      (Nat.mod_add_div' record.toBumpEvent.nextClkLow 65536)

end StateRecord

/-! ## One instruction's State edge -/

/-- Fall-through instructions add four to the low PC limb and their duration to the low
clock limb. Carries are performed by the subsequent StateBump row. -/
def StateRecord.fallThrough (clock pc duration : ℕ) : StateRecord :=
  { StateRecord.canonical clock pc with clkLow := clock % 2 ^ 24 + duration, pc0 := pc % 2 ^ 16 + 4 }

/-- A selected destination supplies all three PC limbs and the clock still carries through StateBump. -/
def StateRecord.selected (clock target duration : ℕ) : StateRecord :=
  { StateRecord.canonical clock target with clkLow := clock % 2 ^ 24 + duration }

namespace RoutedEvent

/-- The canonical State record consumed by this instruction occurrence. -/
def pullState (routed : RoutedEvent) : StateRecord :=
  StateRecord.canonical routed.clock routed.pc

/-- The *uncanonicalized* State record emitted by the instruction row.

Straight-line chips add four only to `pc0`; the three control-flow chips emit their already-limbed
computed target.  Every chip adds eight to the low 24-bit clock without carrying. -/
def rawPushState : RoutedEvent → StateRecord
  | ⟨.jal, event⟩ => StateRecord.selected event.clk event.jalTarget 8
  | ⟨.jalr, event⟩ =>
      StateRecord.selected event.clk (event.jalrTarget - event.jalrTarget % 2) 8
  | ⟨.branch, event⟩ => StateRecord.selected event.clk event.branchNextPc 8
  | ⟨.add, event⟩ => StateRecord.fallThrough event.clk event.pc 8
  | ⟨.addi, event⟩ => StateRecord.fallThrough event.clk event.pc 8
  | ⟨.addw, event⟩ => StateRecord.fallThrough event.clk event.pc 8
  | ⟨.sub, event⟩ => StateRecord.fallThrough event.clk event.pc 8
  | ⟨.subw, event⟩ => StateRecord.fallThrough event.clk event.pc 8
  | ⟨.bitwise, event⟩ => StateRecord.fallThrough event.clk event.pc 8
  | ⟨.lt, event⟩ => StateRecord.fallThrough event.clk event.pc 8
  | ⟨.shiftLeft, event⟩ => StateRecord.fallThrough event.clk event.pc 8
  | ⟨.shiftRight, event⟩ => StateRecord.fallThrough event.clk event.pc 8
  | ⟨.uType, event⟩ => StateRecord.fallThrough event.clk event.pc 8
  | ⟨.loadByte, event⟩ => StateRecord.fallThrough event.clk event.pc 8
  | ⟨.loadHalf, event⟩ => StateRecord.fallThrough event.clk event.pc 8
  | ⟨.loadWord, event⟩ => StateRecord.fallThrough event.clk event.pc 8
  | ⟨.loadDouble, event⟩ => StateRecord.fallThrough event.clk event.pc 8
  | ⟨.loadX0, event⟩ => StateRecord.fallThrough event.clk event.pc 8
  | ⟨.storeByte, event⟩ => StateRecord.fallThrough event.clk event.pc 8
  | ⟨.storeHalf, event⟩ => StateRecord.fallThrough event.clk event.pc 8
  | ⟨.storeWord, event⟩ => StateRecord.fallThrough event.clk event.pc 8
  | ⟨.storeDouble, event⟩ => StateRecord.fallThrough event.clk event.pc 8
  | ⟨.mul, event⟩ => StateRecord.fallThrough event.clk event.pc 8
  | ⟨.divRem, event⟩ => StateRecord.fallThrough event.clk event.pc 8
  | ⟨.aluX0, event⟩ => StateRecord.fallThrough event.clk event.pc 8

private theorem controlRawPush_pc {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)] (clock target : ℕ) :
    Semantics.StateMsg.pcBits ((StateRecord.selected clock target 8).toMessage (p := p)) = BitVec.ofNat 64 (target % 2 ^ 48) := by
  have hp := Fact.out (p := 2 ^ 25 < p)
  have limb (n : ℕ) : n % 2 ^ 16 < p := by omega
  dsimp only [StateRecord.selected, StateRecord.canonical, StateRecord.toMessage, Semantics.StateMsg.pcBits, Semantics.pcBits]
  rw [ZMod.val_natCast_of_lt (limb target), ZMod.val_natCast_of_lt (limb (target / 2 ^ 16)),
    ZMod.val_natCast_of_lt (limb (target / 2 ^ 32))]
  congr 1
  omega

private theorem straightRawPush_pc {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)] (clock pc : ℕ) :
    Semantics.StateMsg.pcBits ((StateRecord.fallThrough clock pc 8).toMessage (p := p)) = BitVec.ofNat 64 (pc % 2 ^ 48 + 4) := by
  have hp := Fact.out (p := 2 ^ 25 < p)
  have limb (n : ℕ) : n % 2 ^ 16 < p := by omega
  have low : pc % 2 ^ 16 + 4 < p := by omega
  dsimp only [StateRecord.fallThrough, StateRecord.canonical, StateRecord.toMessage, Semantics.StateMsg.pcBits, Semantics.pcBits]
  rw [ZMod.val_natCast_of_lt low, ZMod.val_natCast_of_lt (limb (pc / 2 ^ 16)),
    ZMod.val_natCast_of_lt (limb (pc / 2 ^ 32))]
  congr 1
  omega

/-- Decode any emitted successor at its actual raw limbs. Straight-line rows add four after the
source's 48-bit split, so a carry from the low limb remains visible. Control rows split precisely
the selected destination, including JALR's low-bit mask. -/
theorem rawPushState_pcBits {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)] (routed : RoutedEvent) :
    Semantics.StateMsg.pcBits (routed.rawPushState.toMessage (p := p)) = match routed with
      | ⟨.jal, event⟩ => BitVec.ofNat 64 (event.jalTarget % 2 ^ 48)
      | ⟨.jalr, event⟩ => BitVec.ofNat 64 ((event.jalrTarget - event.jalrTarget % 2) % 2 ^ 48)
      | ⟨.branch, event⟩ => BitVec.ofNat 64 (event.branchNextPc % 2 ^ 48)
      | other => BitVec.ofNat 64 (other.pc % 2 ^ 48 + 4) := by
  rcases routed with ⟨id, event⟩
  cases id <;> first | exact straightRawPush_pc _ _ | exact controlRawPush_pc _ _

/-- Canonical successor after the optional State refresh. -/
def nextState (routed : RoutedEvent) : StateRecord := routed.rawPushState.normalize

/-- Exactly one refresh when the instruction's raw push is not already canonical. -/
def stateBumpEvents (routed : RoutedEvent) : List StateBumpEvent :=
  if routed.rawPushState = routed.nextState then [] else [routed.rawPushState.toBumpEvent]

end RoutedEvent

/-- All canonical State refresh rows, in chronological instruction order. -/
def stateBumpEvents (events : List RoutedEvent) : List StateBumpEvent :=
  events.flatMap RoutedEvent.stateBumpEvents

@[simp] theorem RoutedEvent.stateBumpEvents_eq_nil_iff (routed : RoutedEvent) :
    routed.stateBumpEvents = [] ↔ routed.rawPushState = routed.nextState := by
  by_cases canonical : routed.rawPushState = routed.nextState <;>
    simp [RoutedEvent.stateBumpEvents, canonical]

@[simp] theorem RoutedEvent.stateBumpEvents_length_le_one (routed : RoutedEvent) :
    routed.stateBumpEvents.length ≤ 1 := by
  by_cases canonical : routed.rawPushState = routed.nextState <;>
    simp [RoutedEvent.stateBumpEvents, canonical]

/-- State canonicalization adds at most one row per instruction occurrence. -/
theorem stateBumpEvents_length_le (events : List RoutedEvent) :
    (stateBumpEvents events).length ≤ events.length := by
  induction events with
  | nil => simp [stateBumpEvents]
  | cons event events ih =>
      have head := event.stateBumpEvents_length_le_one
      simp only [stateBumpEvents, List.flatMap_cons, List.length_append, List.length_cons] at *
      omega

/-- The exact semantic range assumptions needed by the StateBump table.  In particular this makes
the top-clock and top-pc no-overflow obligations visible rather than hiding them in trace assembly. -/
def StateBumpReady (events : List RoutedEvent) : Prop :=
  ∀ routed ∈ events, routed.rawPushState ≠ routed.nextState →
    routed.rawPushState.toBumpEvent.WellFormed

/-- Every event emitted by the deterministic State refresh compiler meets the provider registry's
row contract. -/
theorem stateBumpEvents_wellFormed {events : List RoutedEvent}
    (ready : StateBumpReady events) :
    ∀ event ∈ stateBumpEvents events, event.WellFormed := by
  intro event member
  rcases List.mem_flatMap.mp member with ⟨routed, routedMem, eventMem⟩
  by_cases canonical : routed.rawPushState = routed.nextState
  · simp [RoutedEvent.stateBumpEvents, canonical] at eventMem
  · simp [RoutedEvent.stateBumpEvents, canonical] at eventMem
    subst event
    exact ready routed routedMem canonical

/-! ## Chronological record and key links -/

/-- The instruction link followed immediately by its optional canonicalizing refresh. -/
def routedStateRecordLinks (routed : RoutedEvent) : List (StateRecord × StateRecord) :=
  [(routed.pullState, routed.rawPushState)] ++
    if routed.rawPushState = routed.nextState then []
    else [(routed.rawPushState, routed.nextState)]

/-- The one semantic execution order. -/
def chronologicalStateRecordLinks (events : List RoutedEvent) :
    List (StateRecord × StateRecord) :=
  events.flatMap routedStateRecordLinks

/-- Field-free adjacency and endpoint condition for the generated State stream. -/
def StateChronology : StateRecord → List RoutedEvent → StateRecord → Prop
  | held, [], final => held = final
  | held, routed :: rest, final =>
      routed.pullState = held ∧ StateChronology routed.nextState rest final

/-- Embed the chronological links into the exact Clean lookup-key representation. -/
def chronologicalStateLinks {p : ℕ} [NeZero p] (events : List RoutedEvent) :
    List (LookupKey × LookupKey) :=
  (chronologicalStateRecordLinks events).map fun link =>
    (link.1.key (p := p), link.2.key (p := p))

@[simp] theorem chronologicalStateLinks_cons {p : ℕ} [NeZero p]
    (routed : RoutedEvent) (rest : List RoutedEvent) :
    chronologicalStateLinks (p := p) (routed :: rest) =
      (routedStateRecordLinks routed).map (fun link =>
        (link.1.key (p := p), link.2.key (p := p))) ++
        chronologicalStateLinks (p := p) rest := by
  simp [chronologicalStateLinks, chronologicalStateRecordLinks]

/-- Field-free chronology implies the generic State-bus hand-off chain after field embedding. -/
theorem chronologicalStateLinks_isHandoffChain {p : ℕ} [NeZero p]
    {initial final : StateRecord} {events : List RoutedEvent}
    (chronology : StateChronology initial events final) :
    IsHandoffChain (initial.key (p := p)) (chronologicalStateLinks (p := p) events)
      (final.key (p := p)) := by
  induction events generalizing initial with
  | nil =>
      change initial.key (p := p) = final.key (p := p)
      exact congrArg (StateRecord.key (p := p)) chronology
  | cons routed rest ih =>
      obtain ⟨pullEq, tail⟩ := chronology
      rw [chronologicalStateLinks_cons]
      by_cases canonical : routed.rawPushState = routed.nextState
      · simp only [routedStateRecordLinks, canonical, ite_eq_left, List.append_nil,
          List.map_cons, List.map_nil]
        exact ⟨congrArg (StateRecord.key (p := p)) pullEq,
          by simpa [canonical] using ih tail⟩
      · simp only [routedStateRecordLinks, canonical, List.map_append,
          List.map_cons, List.map_nil]
        exact ⟨congrArg (StateRecord.key (p := p)) pullEq, rfl, ih tail⟩

/-! ## Physical table order versus chronological order -/

private def instructionStateLink {p : ℕ} [NeZero p] (routed : RoutedEvent) :
    LookupKey × LookupKey :=
  (routed.pullState.key (p := p), routed.rawPushState.key (p := p))

/-- Instruction links in physical chip-table order. -/
private def bucketInstructionStateLinks {p : ℕ} [NeZero p] :
    List InstructionChipId → List RoutedEvent → List (LookupKey × LookupKey)
  | [], _ => []
  | id :: ids, events =>
      (events.filter fun routed => routed.id = id).map (instructionStateLink (p := p)) ++
          bucketInstructionStateLinks (p := p) ids events

def physicalInstructionStateLinks {p : ℕ} [NeZero p] (events : List RoutedEvent) :
    List (LookupKey × LookupKey) :=
  bucketInstructionStateLinks (p := p) InstructionChipId.all events

/-- Refresh links in their separate physical table order. -/
def physicalStateBumpLinks {p : ℕ} [NeZero p] (events : List RoutedEvent) :
    List (LookupKey × LookupKey) :=
  events.flatMap fun routed =>
    if routed.rawPushState = routed.nextState then []
    else [(routed.rawPushState.key (p := p), routed.nextState.key (p := p))]

private theorem bucketInstructionStateLinks_cons_of_not_mem {p : ℕ} [NeZero p]
    (ids : List InstructionChipId) (routed : RoutedEvent) (rest : List RoutedEvent)
    (notMem : routed.id ∉ ids) :
    bucketInstructionStateLinks (p := p) ids (routed :: rest) =
      bucketInstructionStateLinks (p := p) ids rest := by
  induction ids with
  | nil => rfl
  | cons id ids ih =>
      have ne : routed.id ≠ id := fun eq => notMem (by simp [eq])
      have notTail : routed.id ∉ ids := fun mem => notMem (by simp [mem])
      simp [bucketInstructionStateLinks, ne, ih notTail]

/-- Adding one event to a complete, duplicate-free bucket inventory inserts its instruction link
at exactly one bucket; moving that link to the front is a permutation. -/
private theorem bucketInstructionStateLinks_cons_perm {p : ℕ} [NeZero p]
    (ids : List InstructionChipId) (routed : RoutedEvent) (rest : List RoutedEvent)
    (nodup : ids.Nodup) (member : routed.id ∈ ids) :
    (bucketInstructionStateLinks (p := p) ids (routed :: rest)).Perm
      (instructionStateLink (p := p) routed ::
        bucketInstructionStateLinks (p := p) ids rest) := by
  induction ids with
  | nil => simp at member
  | cons id ids ih =>
      have idNotMem : id ∉ ids := (List.nodup_cons.mp nodup).1
      have tailNodup : ids.Nodup := (List.nodup_cons.mp nodup).2
      by_cases routeEq : routed.id = id
      · have routeNotTail : routed.id ∉ ids := by simpa [routeEq] using idNotMem
        simp [bucketInstructionStateLinks, routeEq,
          bucketInstructionStateLinks_cons_of_not_mem ids routed rest routeNotTail,
          instructionStateLink]
      · have routeMem : routed.id ∈ ids := (List.mem_cons.mp member).resolve_left routeEq
        have tailPerm := ih tailNodup routeMem
        have moved := tailPerm.append_left
          ((rest.filter fun item => item.id = id).map (instructionStateLink (p := p)))
        have result := moved.trans
          (List.perm_middle
            (l₁ := (rest.filter fun item => item.id = id).map
              (instructionStateLink (p := p)))
            (l₂ := bucketInstructionStateLinks (p := p) ids rest)
            (a := instructionStateLink (p := p) routed))
        simpa [bucketInstructionStateLinks, instructionStateLink, routeEq] using result

/-- Stable registry bucketing is a permutation, not an execution ordering. -/
theorem physicalInstructionStateLinks_perm {p : ℕ} [NeZero p]
    (events : List RoutedEvent) :
    (physicalInstructionStateLinks (p := p) events).Perm
      (events.map fun routed =>
        (routed.pullState.key (p := p), routed.rawPushState.key (p := p))) := by
  induction events with
  | nil => simp [physicalInstructionStateLinks, InstructionChipId.all,
      bucketInstructionStateLinks]
  | cons routed rest ih =>
      exact (bucketInstructionStateLinks_cons_perm InstructionChipId.all routed rest
          InstructionChipId.all_nodup (InstructionChipId.mem_all routed.id)).trans
        (List.Perm.cons (instructionStateLink (p := p) routed) ih)

/-- The generic shuffle which moves each row's bump links out of the separate tail and places them
immediately after that row's instruction link. -/
private theorem separatedStateLinks_perm_chronological {p : ℕ} [NeZero p]
    (events : List RoutedEvent) :
    (events.map (instructionStateLink (p := p)) ++
        physicalStateBumpLinks (p := p) events).Perm
      (chronologicalStateLinks (p := p) events) := by
  induction events with
  | nil => simp [physicalStateBumpLinks, chronologicalStateLinks,
      chronologicalStateRecordLinks]
  | cons routed rest ih =>
      let bump : List (LookupKey × LookupKey) :=
        if routed.rawPushState = routed.nextState then []
        else [(routed.rawPushState.key (p := p), routed.nextState.key (p := p))]
      have moveBump :
          (rest.map (instructionStateLink (p := p)) ++ bump ++
              physicalStateBumpLinks (p := p) rest).Perm
            (bump ++ rest.map (instructionStateLink (p := p)) ++
              physicalStateBumpLinks (p := p) rest) :=
        (List.perm_append_comm (l₁ := rest.map (instructionStateLink (p := p)))
          (l₂ := bump)).append_right _
      have tailShuffled :
          (bump ++ rest.map (instructionStateLink (p := p)) ++
              physicalStateBumpLinks (p := p) rest).Perm
            (bump ++ chronologicalStateLinks (p := p) rest) := by
        simpa only [List.append_assoc] using ih.append_left bump
      have shuffled := (List.Perm.cons (instructionStateLink (p := p) routed) moveBump).trans
        (List.Perm.cons (instructionStateLink (p := p) routed) tailShuffled)
      change
        (instructionStateLink (p := p) routed ::
          rest.map (instructionStateLink (p := p)) ++ bump ++
            physicalStateBumpLinks (p := p) rest).Perm _ at shuffled
      by_cases canonical : routed.rawPushState = routed.nextState
      · simpa [physicalStateBumpLinks, chronologicalStateLinks_cons,
          routedStateRecordLinks, instructionStateLink, bump, canonical] using shuffled
      · simpa [physicalStateBumpLinks, chronologicalStateLinks_cons,
          routedStateRecordLinks, instructionStateLink, bump, canonical] using shuffled

/-- Separating all instruction rows from the bump table preserves the interleaved semantic order. -/
theorem physicalStateLinks_perm_chronological {p : ℕ} [NeZero p]
    (events : List RoutedEvent) :
    (physicalInstructionStateLinks (p := p) events ++
        physicalStateBumpLinks (p := p) events).Perm
      (chronologicalStateLinks (p := p) events) := by
  refine ((physicalInstructionStateLinks_perm (p := p) events).append_right _).trans ?_
  exact separatedStateLinks_perm_chronological (p := p) events

end SP1Clean.TraceGen
