import SP1Clean.FormalModel.Contracts.WriteSlice
import SP1Clean.FormalModel.Contracts.AddressDiv8

/-! # Physical input for a complete grouped WRITE

Each row consumes one genuine eight-lane observation. Guest positions span a single observed
word while destination byte positions can cross a block boundary. Both sources are addressed
by their own exact positional keys.
-/

namespace SP1Clean.WriteEffects

/-- Select one of eight lane values using its fixed one-hot mask. -/
def selectLane {F : Type} [Add F] [Mul F] (mask : fields 8 F) (value : Fin 8 → F) : F :=
  mask[0]*value 0 + mask[1]*value 1 + mask[2]*value 2 + mask[3]*value 3 +
    mask[4]*value 4 + mask[5]*value 5 + mask[6]*value 6 + mask[7]*value 7

/-- Guest byte at the given slot of a selected word window. -/
def SlicePlan.guestByte {F : Type} [Add F] [Mul F] (s : SlicePlan F) (guest : fields 8 F) (slot : Fin 8) : F :=
  selectLane s.guestSelect fun start => guest[(start.val + slot.val) % 8]

/-- Destination byte for a slot, advancing to the right block on a boundary crossing. -/
def SlicePlan.streamByte {F : Type} [Add F] [Mul F] (s : SlicePlan F) (left right : fields 8 F) (slot : Fin 8) : F :=
  selectLane s.streamSelect fun start =>
    if start.val + slot.val < 8 then left[(start.val + slot.val) % 8] else right[(start.val + slot.val) % 8]

/-- One observed guest word and the destination blocks covering its selected bytes. -/
structure Group (F : Type) where
  /-- Authenticated guest word bytes, address and incoming clock. -/
  octets : Octets F
  /-- Placement cursor immediately before this group. -/
  previous : Placement F
  /-- Fixed guest and destination lane selectors for this interval. -/
  plan : SlicePlan F
  /-- One when the placement sink discards the payload. -/
  ignored : F
  /-- Division witness limbs for the destination's eight-byte block address. -/
  quotients : fields 3 F
  /-- Index of the block containing the first destination byte. -/
  firstBlock : fields 3 F
  /-- Successor of the first destination block index. -/
  nextBlock : fields 3 F
  /-- Exclusive destination position after this word's selected bytes. -/
  nextPosition : fields 3 F
  /-- Number of occupied bytes in the first destination block. -/
  leftSize : F
  /-- Number of occupied bytes in the next destination block. -/
  rightSize : F
  /-- Eight byte lanes of the first destination block. -/
  left : fields 8 F
  /-- Eight byte lanes of the next destination block. -/
  right : fields 8 F
deriving ProvableStruct
provable_struct_eval_lemmas Group

/-- Placement cursor after consuming this guest word's selected bytes. -/
def Group.next {F : Type} [Add F] (r : Group F) : Placement F :=
  {r.previous with address := Address.offset r.octets.key r.plan.last, position := r.nextPosition}

/-- Form the first or second block request with its exact owner, index, extent and lanes. -/
def Group.block {F : Type} [Zero F] (r : Group F) (right : Bool) : StreamBlock F :=
  ⟨r.previous.sink, r.previous.owner, #v[0,0,0], if right then r.nextBlock else r.firstBlock,
    if right then r.rightSize else r.leftSize, if right then r.right else r.left⟩

/-- Inputs for decomposing the destination position into a block index and a lane. -/
def Group.division {F : Type} [Zero F] (r : Group F) : AddressDiv8.Inputs F :=
  ⟨Address.asWord r.previous.position, r.quotients⟩

end SP1Clean.WriteEffects
