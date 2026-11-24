import SP1Clean.FormalModel.Contracts.WriteSlice
import SP1Clean.FormalModel.Contracts.AddressDiv8

/-! # Physical input for a complete grouped WRITE

Each row consumes one genuine eight-lane observation. Guest positions span a single observed
word while destination byte positions can cross a block boundary. Both sources are addressed
by their own exact positional keys.
-/

namespace SP1Clean.WriteEffects

def selectLane {F : Type} [Add F] [Mul F] (mask : fields 8 F) (value : Fin 8 → F) : F :=
  mask[0]*value 0 + mask[1]*value 1 + mask[2]*value 2 + mask[3]*value 3 +
    mask[4]*value 4 + mask[5]*value 5 + mask[6]*value 6 + mask[7]*value 7

def SlicePlan.guestByte {F : Type} [Add F] [Mul F] (s : SlicePlan F) (guest : fields 8 F) (slot : Fin 8) : F :=
  selectLane s.guestSelect fun start => guest[(start.val + slot.val) % 8]

def SlicePlan.streamByte {F : Type} [Add F] [Mul F] (s : SlicePlan F) (left right : fields 8 F) (slot : Fin 8) : F :=
  selectLane s.streamSelect fun start =>
    if start.val + slot.val < 8 then left[(start.val + slot.val) % 8] else right[(start.val + slot.val) % 8]

structure Group (F : Type) where
  octets : Octets F
  previous : Placement F
  plan : SlicePlan F
  ignored : F
  quotients : fields 3 F
  firstBlock : fields 3 F
  nextBlock : fields 3 F
  nextPosition : fields 3 F
  leftSize : F
  rightSize : F
  left : fields 8 F
  right : fields 8 F
deriving ProvableStruct
provable_struct_eval_lemmas Group

def Group.next {F : Type} [Add F] (r : Group F) : Placement F :=
  {r.previous with address := Address.offset r.octets.key r.plan.last, position := r.nextPosition}

def Group.block {F : Type} [Zero F] (r : Group F) (right : Bool) : StreamBlock F :=
  ⟨r.previous.sink, r.previous.owner, #v[0,0,0], if right then r.nextBlock else r.firstBlock,
    if right then r.rightSize else r.leftSize, if right then r.right else r.left⟩

def Group.division {F : Type} [Zero F] (r : Group F) : AddressDiv8.Inputs F :=
  ⟨Address.asWord r.previous.position, r.quotients⟩

end SP1Clean.WriteEffects
