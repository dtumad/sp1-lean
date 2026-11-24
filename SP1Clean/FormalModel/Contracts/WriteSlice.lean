import SP1Clean.Semantics.Host.WriteStreamBlocks
import SP1Clean.FormalModel.Contracts.WriteChronology

/-! # Aligned word window for native WRITE

A group begins at one of eight guest lanes, copies zero to eight consecutive bytes from that
word, and begins at one of eight offsets in the destination stream. Any nonempty group uses one
or two destination blocks. No field occurrence is indexed by an uncontrolled witness expression.
-/

namespace SP1Clean.WriteEffects

/-- Fixed lane masks and destination extents for one interval within a guest word. -/
structure SlicePlan (F : Type) where
  /-- Lane at which the selected guest interval begins. -/
  first : F
  /-- Final guest lane computed from the start and byte count using truncated subtraction. -/
  last : F
  /-- Number of guest bytes selected in this word. -/
  size : F
  /-- Starting lane in the first destination block. -/
  offset : F
  /-- One when at least one guest byte is selected. -/
  nonempty : F
  /-- One when selected bytes extend into a second destination block. -/
  second : F
  /-- Exclusive end of the covered lanes in the first destination block. -/
  firstExtent : F
  /-- Number of covered lanes at the beginning of the second destination block. -/
  secondExtent : F
  /-- One-hot mask for the first guest lane. -/
  guestSelect : fields 8 F
  /-- One-hot mask for the starting destination lane. -/
  streamSelect : fields 8 F
  /-- Prefix mask enabling exactly the selected number of bytes. -/
  used : fields 8 F
deriving ProvableStruct, DecidableEq
provable_struct_eval_lemmas SlicePlan

/-- A first/last selector for the actual interval, including a disabled row for the empty interval. -/
def SlicePlan.ofNat {p : Nat} (first size offset : Nat) : SlicePlan (ZMod p) :=
  ⟨first, (first + size - 1 : Nat), size, offset, if size = 0 then 0 else 1, if 8 < size + offset then 1 else 0,
    (min 8 (size + offset) : Nat), (size + offset - 8 : Nat), Vector.ofFn (fun i => if i.val = first then 1 else 0),
    Vector.ofFn (fun i => if i.val = offset then 1 else 0), Vector.ofFn (fun i => if i.val < size then 1 else 0)⟩

/-- Canonical fixed rows. Every selected interval stays in one real guest word. -/
def slicePlans {p : Nat} : List (SlicePlan (ZMod p)) :=
  (List.range 8).flatMap fun first => (List.range (9-first)).flatMap fun size =>
    (List.range 8).map fun offset => SlicePlan.ofNat first size offset

theorem slicePlans_iff {p : Nat} (plan : SlicePlan (ZMod p)) :
    plan ∈ slicePlans ↔ ∃ first size offset, first < 8 ∧ first + size ≤ 8 ∧ offset < 8 ∧ plan = .ofNat first size offset := by
  simp only [slicePlans,List.mem_flatMap,List.mem_range,List.mem_map]
  constructor
  · rintro ⟨first,small,size,bound,offset,off,rfl⟩
    exact ⟨first,size,offset,small,by omega,off,rfl⟩
  · rintro ⟨first,size,offset,small,bound,off,rfl⟩
    exact ⟨first,small,size,by omega,offset,off,rfl⟩

/-- The window at guest lane `first` runs through the payload limit or the current word boundary. -/
def window (address length word : Nat) : Nat × Nat :=
  let key := 8 * word
  let start := max address key
  (min 7 (start-key), min (address+length) (key+8) - start)

theorem window_spec (address length word : Nat) :
    (window address length word).1 < 8 ∧ (window address length word).1 + (window address length word).2 ≤ 8 ∧
    ∀ lane < 8, ((window address length word).1 ≤ lane ∧ lane < (window address length word).1 + (window address length word).2) ↔
      (address ≤ 8 * word + lane ∧ 8 * word + lane < address + length) := by
  dsimp only [window]
  constructor
  · omega
  constructor
  · omega
  · intro lane small; omega

/-- Supplies the fixed interval masks and extents used by word placement. -/
def sliceChannel {p : Nat} : Channel (ZMod p) SlicePlan where
  name := "sp1.native.write_slice_plan"
  Guarantees _ _ := True

end SP1Clean.WriteEffects
