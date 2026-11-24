module

/-! # Field-free Memory records for SP1 trace generation

Instruction predecessors, semantic access histories and ordered boundary providers share the same
record. The physical channel encoding of its clock, address and word is defined by the provider.
-/

@[expose] public section

namespace SP1Clean.TraceGen

/-- One memory-boundary record: a byte address, the 64-bit value, the access clock, and an explicit
boolean activity selector. The init side uses `clk = 0` (SP1's memory-init interaction passes
literal zeros for both clock limbs); the finalize side uses the chain's last access clock. -/
structure MemRecordEntry where
  addr : Nat
  value : Nat
  clk : Nat
  multiplicity : Bool
deriving DecidableEq

/-- An init record is well-formed when its clock is zero, which is what the provider circuit pins
both limbs to. -/
def MemRecordEntry.WellFormedInit (e : MemRecordEntry) : Prop := e.clk = 0

end SP1Clean.TraceGen
