module

/-! # Link words represented by the released JAL and JALR chips -/

@[expose] public section

namespace SP1Clean.Semantics

/-- The pinned AIR represents an enabled `pc + 4` register write with three 16-bit limbs.
The decoded destination and the circuit gate supply the same write condition. -/
def JumpLinkFits (pc : Nat) (writesLink : Prop) : Prop := writesLink → pc + 4 < 2 ^ 48

end SP1Clean.Semantics
