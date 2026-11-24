import SP1Clean.Proofs.Completeness.EventBuckets
import SP1Clean.FormalModel.TraceGen.MemoryRecord
import SP1Clean.Semantics.Transition.AccessPlan

/-! # Original predecessor data carried by compiled instruction events

Each native adapter already carries the previous record of every real operand. This projection
reads those fields in the canonical RAM/C/B/A schedule, preserving register aliases and excluding
the immediate-C field. It only projects executor input data and does not evaluate an instruction.
-/

namespace SP1Clean.TraceGen

open Semantics

/-- The original displaced address, word and timestamp for one scheduled instruction role. -/
def operandPredecessor (touch : StampedTouch) : MemRecordEntry :=
  ⟨touch.touch.loc.busAddress, touch.touch.pulled.toNat, touch.previous, true⟩

/-- Three physical register predecessors in C/B/A order. -/
def RTypeEvent.predecessors (e : RTypeEvent) : List MemRecordEntry :=
  [⟨e.opC, e.c, e.prevTsC, true⟩, ⟨e.opB, e.b, e.prevTsB, true⟩, ⟨e.opA, e.prevA, e.prevTsA, true⟩]

/-- Two register inputs, including the A operand on branches and stores. -/
def ITypeEvent.predecessors (e : ITypeEvent) : List MemRecordEntry :=
  [⟨e.opB, e.b, e.prevTsB, true⟩, ⟨e.opA, e.prevA, e.prevTsA, true⟩]

/-- An ALU immediate suppresses exactly the C register occurrence. -/
def ALUTypeEvent.predecessors (e : ALUTypeEvent) : List MemRecordEntry :=
  (if e.immC = 0 then [⟨e.opC, e.c, e.prevTsC, true⟩] else []) ++
    [⟨e.opB, e.b, e.prevTsB, true⟩, ⟨e.opA, e.prevA, e.prevTsA, true⟩]

/-- The J/U adapter consumes only its destination's prior record. -/
def JTypeEvent.predecessors (e : JTypeEvent) : List MemRecordEntry :=
  [⟨e.opA, e.prevA, e.prevTsA, true⟩]

/-- The aligned RAM word precedes the two real I-type register operands. -/
def MemoryEvent.predecessors (e : MemoryEvent) : List MemRecordEntry :=
  ⟨e.addr / 8 * 8, e.prevMem, e.prevTsMem, true⟩ :: e.toITypeEvent.predecessors

/-- Recover all displaced register and RAM records from the actual routed event. -/
def RoutedEvent.predecessors : RoutedEvent → List MemRecordEntry
  | ⟨.add, e⟩ | ⟨.sub, e⟩ | ⟨.subw, e⟩ | ⟨.mul, e⟩ | ⟨.divRem, e⟩ => RTypeEvent.predecessors e
  | ⟨.addi, e⟩ | ⟨.jalr, e⟩ | ⟨.branch, e⟩ => ITypeEvent.predecessors e
  | ⟨.addw, e⟩ | ⟨.bitwise, e⟩ | ⟨.lt, e⟩ | ⟨.shiftLeft, e⟩ | ⟨.shiftRight, e⟩ | ⟨.aluX0, e⟩ => ALUTypeEvent.predecessors e
  | ⟨.jal, e⟩ | ⟨.uType, e⟩ => JTypeEvent.predecessors e
  | ⟨.loadByte, e⟩ | ⟨.loadHalf, e⟩ | ⟨.loadWord, e⟩ | ⟨.loadDouble, e⟩ | ⟨.loadX0, e⟩
    | ⟨.storeByte, e⟩ | ⟨.storeHalf, e⟩ | ⟨.storeWord, e⟩ | ⟨.storeDouble, e⟩ => MemoryEvent.predecessors e

end SP1Clean.TraceGen
