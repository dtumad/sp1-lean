import SP1Clean.FormalModel.TraceGen.InstructionRegistry

/-!
# Chronological events and registry-indexed table buckets

The semantic compiler produces one instruction occurrence per located Sail transition, in
execution order.  The physical ensemble stores those occurrences table-by-table.  This file is
the single bridge between the two views: `RoutedEvent` is one dependent event paired with its
canonical `InstructionChipId`, and `EventBuckets.ofChronological` is a stable `filterMap` into the
registry-indexed family consumed by `SupportedCoreTraceWitness`.

The bucket family is derived, not stored beside the chronological list.  Consequently there is no
second routing table and no proof obligation saying two independently maintained representations
agree.  The lemmas below expose the exact membership and length properties needed by the compiler
and footprint arguments.
-/

namespace SP1Clean.TraceGen

/-- One semantic instruction event together with the native table selected for it. -/
structure RoutedEvent where
  id : InstructionChipId
  event : id.Event

namespace RoutedEvent

/-- Clock carried by the common CPU-state input of a routed event. -/
def clock : RoutedEvent → ℕ
  | ⟨.add, event⟩ => event.clk
  | ⟨.addi, event⟩ => event.clk
  | ⟨.addw, event⟩ => event.clk
  | ⟨.sub, event⟩ => event.clk
  | ⟨.subw, event⟩ => event.clk
  | ⟨.bitwise, event⟩ => event.clk
  | ⟨.lt, event⟩ => event.clk
  | ⟨.shiftLeft, event⟩ => event.clk
  | ⟨.shiftRight, event⟩ => event.clk
  | ⟨.jal, event⟩ => event.clk
  | ⟨.jalr, event⟩ => event.clk
  | ⟨.branch, event⟩ => event.clk
  | ⟨.uType, event⟩ => event.clk
  | ⟨.loadByte, event⟩ => event.clk
  | ⟨.loadHalf, event⟩ => event.clk
  | ⟨.loadWord, event⟩ => event.clk
  | ⟨.loadDouble, event⟩ => event.clk
  | ⟨.loadX0, event⟩ => event.clk
  | ⟨.storeByte, event⟩ => event.clk
  | ⟨.storeHalf, event⟩ => event.clk
  | ⟨.storeWord, event⟩ => event.clk
  | ⟨.storeDouble, event⟩ => event.clk
  | ⟨.mul, event⟩ => event.clk
  | ⟨.divRem, event⟩ => event.clk
  | ⟨.aluX0, event⟩ => event.clk

/-- Program counter carried by the common CPU-state input of a routed event. -/
def pc : RoutedEvent → ℕ
  | ⟨.add, event⟩ => event.pc
  | ⟨.addi, event⟩ => event.pc
  | ⟨.addw, event⟩ => event.pc
  | ⟨.sub, event⟩ => event.pc
  | ⟨.subw, event⟩ => event.pc
  | ⟨.bitwise, event⟩ => event.pc
  | ⟨.lt, event⟩ => event.pc
  | ⟨.shiftLeft, event⟩ => event.pc
  | ⟨.shiftRight, event⟩ => event.pc
  | ⟨.jal, event⟩ => event.pc
  | ⟨.jalr, event⟩ => event.pc
  | ⟨.branch, event⟩ => event.pc
  | ⟨.uType, event⟩ => event.pc
  | ⟨.loadByte, event⟩ => event.pc
  | ⟨.loadHalf, event⟩ => event.pc
  | ⟨.loadWord, event⟩ => event.pc
  | ⟨.loadDouble, event⟩ => event.pc
  | ⟨.loadX0, event⟩ => event.pc
  | ⟨.storeByte, event⟩ => event.pc
  | ⟨.storeHalf, event⟩ => event.pc
  | ⟨.storeWord, event⟩ => event.pc
  | ⟨.storeDouble, event⟩ => event.pc
  | ⟨.mul, event⟩ => event.pc
  | ⟨.divRem, event⟩ => event.pc
  | ⟨.aluX0, event⟩ => event.pc


/-- Project a routed event at one requested registry identity.  A mismatched identity is absent;
on a match the dependent payload is transported along the proved identity equality. -/
def forId? (routed : RoutedEvent) (requested : InstructionChipId) :
    Option requested.Event :=
  if h : routed.id = requested then
    some (cast (congrArg InstructionChipId.Event h) routed.event)
  else
    none

@[simp] theorem forId?_self (id : InstructionChipId) (event : id.Event) :
    (RoutedEvent.mk id event).forId? id = some event := by
  simp [forId?]

theorem forId?_eq_none_of_ne (routed : RoutedEvent) {requested : InstructionChipId}
    (ne : routed.id ≠ requested) : routed.forId? requested = none := by
  simp [forId?, ne]

theorem forId?_eq_some_iff {routed : RoutedEvent} {requested : InstructionChipId}
    {event : requested.Event} :
    routed.forId? requested = some event ↔
      ∃ h : routed.id = requested,
        cast (congrArg InstructionChipId.Event h) routed.event = event := by
  unfold forId?
  split
  · rename_i h
    simp only [Option.some.injEq]
    exact ⟨fun eq => ⟨h, eq⟩, fun ⟨_, eq⟩ => eq⟩
  · rename_i h
    constructor
    · intro impossible
      cases impossible
    · rintro ⟨eq, _⟩
      exact (h eq).elim

end RoutedEvent

/-- Registry-indexed event lists in physical instruction-table order. -/
abbrev EventBuckets := (id : InstructionChipId) → List id.Event

namespace EventBuckets

/-- Stable partition of a chronological routed stream into native instruction tables. -/
def ofChronological (events : List RoutedEvent) : EventBuckets :=
  fun id => events.filterMap fun routed => routed.forId? id

@[simp] theorem ofChronological_nil (id : InstructionChipId) :
    ofChronological [] id = [] := rfl

@[simp] theorem ofChronological_cons (routed : RoutedEvent) (events : List RoutedEvent)
    (id : InstructionChipId) :
    ofChronological (routed :: events) id =
      (routed.forId? id).toList ++ ofChronological events id := by
  unfold ofChronological
  cases projected : routed.forId? id <;> simp [List.filterMap, projected]

theorem ofChronological_cons_self (id : InstructionChipId) (event : id.Event)
    (events : List RoutedEvent) :
    ofChronological (RoutedEvent.mk id event :: events) id =
      event :: ofChronological events id := by
  simp [ofChronological]

theorem mem_ofChronological_iff {events : List RoutedEvent} {id : InstructionChipId}
    {event : id.Event} :
    event ∈ ofChronological events id ↔
      ∃ routed ∈ events, routed.forId? id = some event := by
  simp [ofChronological, List.mem_filterMap]

/-- Every bucket member comes from one chronological occurrence with the requested route. -/
theorem exists_chronological_of_mem {events : List RoutedEvent} {id : InstructionChipId}
    {event : id.Event} (member : event ∈ ofChronological events id) :
    ∃ routed ∈ events, ∃ h : routed.id = id,
      cast (congrArg InstructionChipId.Event h) routed.event = event := by
  rw [mem_ofChronological_iff] at member
  obtain ⟨routed, routedMem, projected⟩ := member
  exact ⟨routed, routedMem, RoutedEvent.forId?_eq_some_iff.mp projected⟩

/-- Stable bucketing never creates more occurrences than the chronological compiler emitted. -/
theorem length_le (events : List RoutedEvent) (id : InstructionChipId) :
    (ofChronological events id).length ≤ events.length := by
  induction events with
  | nil => simp [ofChronological]
  | cons routed events ih =>
      rw [ofChronological_cons]
      cases routed.forId? id <;> simp <;> omega

/-- Bucketing commutes with chronological concatenation. -/
theorem ofChronological_append (left right : List RoutedEvent) (id : InstructionChipId) :
    ofChronological (left ++ right) id =
      ofChronological left id ++ ofChronological right id := by
  simp [ofChronological]

/-- Reattach the known registry identifier to each event of the actual typed buckets. -/
def physical (events : List RoutedEvent) : List RoutedEvent :=
  InstructionChipId.all.flatMap fun id => (ofChronological events id).map (RoutedEvent.mk id)

private theorem one_per_registry (r : RoutedEvent) :
    (InstructionChipId.all.flatMap fun id => (r.forId? id).toList.map (RoutedEvent.mk id)) = [r] := by
  obtain ⟨chip,e⟩ := r
  have selection (ids : List InstructionChipId) :
      (ids.flatMap fun id => ((RoutedEvent.mk chip e).forId? id).toList.map (RoutedEvent.mk id)) =
        (ids.filter (· = chip)).map (fun _ => RoutedEvent.mk chip e) := by
    induction ids with
    | nil => rfl
    | cons id ids ih =>
      by_cases eqn : chip = id
      · subst id
        simp [ih]
      · rw [List.flatMap_cons,ih,RoutedEvent.forId?_eq_none_of_ne _ eqn]
        simp [Ne.symm eqn]
  rw [selection,List.filter_eq,InstructionChipId.all_nodup.count_of_mem (InstructionChipId.mem_all chip)]
  rfl

/-- The actual typed registry buckets partition the chronological stream with repetitions preserved. -/
theorem physical_perm (events : List RoutedEvent) : (physical events).Perm events := by
  induction events with
  | nil => simp [physical]
  | cons r rest ih =>
    let added (id : InstructionChipId) := (r.forId? id).toList.map (RoutedEvent.mk id)
    let old (id : InstructionChipId) := (ofChronological rest id).map (RoutedEvent.mk id)
    have shuffled := (List.flatMap_append_perm InstructionChipId.all added old).symm
    change (InstructionChipId.all.flatMap (fun id => added id ++ old id)).Perm
      (InstructionChipId.all.flatMap added ++ physical rest) at shuffled
    rw [show InstructionChipId.all.flatMap added = [r] from one_per_registry r] at shuffled
    simpa only [physical,ofChronological_cons,List.map_append] using shuffled.trans (List.Perm.cons r ih)

end EventBuckets

end SP1Clean.TraceGen
