import SP1Clean.Semantics.Host.WriteStreamRecords
import SP1Clean.FormalModel.Contracts.WriteChronology
import SP1Clean.FormalModel.Contracts.HintNodeAllocate
import SP1Clean.FormalModel.Contracts.ClockParts

/-! # Native allocation messages for direct hints and hook replies

An allocating WRITE replaces one clocked queue state. Within that call, the number of
unallocated buffers decreases by one per fresh node. A hook allocates its returned buffers
in reverse order so that the first returned buffer becomes the new queue head.
-/

namespace SP1Clean.WriteAllocation

open WriteEffects Semantics.HintQueue

/-- Identity and guest byte length of a direct hint, or the reply ordinal of a hook. -/
structure Source (F : Type) where
  /-- One selects a direct hint and zero selects a supplied hook reply. -/
  direct : F
  /-- New pointer for a direct hint, consumed reply ordinal for a hook. -/
  owner : fields 3 F
  /-- Direct guest length, canonically zero for hook allocations. -/
  directLength : fields 3 F
deriving ProvableStruct, DecidableEq
provable_struct_eval_lemmas Source

/-- One position in the ordered list of allocations authorized by a single WRITE. -/
structure Cursor (F : Type) where
  /-- Authenticated source of this allocation batch. -/
  source : Source F
  /-- Number of returned buffers still to prepend. -/
  remaining : fields 3 F
  /-- Queue head and allocation frontier at this call's clock. -/
  state : HostHintQueue.State F
deriving ProvableStruct
provable_struct_eval_lemmas Cursor

/-- Internal state chain between the ticket receiver and its fresh nodes. -/
def cursorChannel {p : Nat} : Channel (ZMod p) Cursor where
  name := "sp1.native.hint_allocation_cursor"
  Guarantees _ _ := True

/-- Byte identity of one fresh node, including an empty buffer's padded final word. -/
structure Contents (F : Type) where
  /-- One for guest bytes, zero for the returned stream at the supplied ordinal/index. -/
  direct : F
  /-- Immutable identity allocated to this node. -/
  pointer : fields 3 F
  /-- Consumed hook reply ordinal, canonically zero on direct allocations. -/
  reply : fields 3 F
  /-- Position in the hook's returned list, zero for the single direct allocation. -/
  index : fields 3 F
  /-- Exact number of unpadded bytes. -/
  length : fields 3 F
deriving ProvableStruct, DecidableEq
provable_struct_eval_lemmas Contents

/-- One required byte witness for every authorized fresh node. -/
def contentsChannel {p : Nat} : Channel (ZMod p) Contents where
  name := "sp1.native.hint_allocation_contents"
  Guarantees _ _ := True

/-- Private boundary states and a shared timestamp decomposition for one allocating WRITE. -/
structure Open (F : Type) where
  /-- Ticket sent by the chronological dispatcher. -/
  ticket : QueueTicket F
  /-- The same timestamp in the encoding shared by both buses. -/
  timestamp : ClockParts F
  /-- Last state on the global hint queue. -/
  previous : HostHintQueue.State F
  /-- Head after all authorized nodes have been added. -/
  head : fields 3 F
  /-- Permanent allocation count at the end of this call. -/
  allocated : fields 3 F
deriving ProvableStruct
provable_struct_eval_lemmas Open

/-- Low three limbs scaled independently by a selection bit. -/
def scale {F : Type} [Mul F] (gate : F) (value : fields 3 F) : fields 3 F :=
  #v[gate * value[0],gate * value[1],gate * value[2]]

/-- Name and size used by the private allocation cursor. -/
def Open.source {F : Type} [Mul F] (r : Open F) : Source F :=
  ⟨r.ticket.direct, r.ticket.owner, scale r.ticket.direct r.ticket.length⟩

/-- The header authorizes one direct buffer or exactly the declared number of returned buffers. -/
def Open.count {F : Type} [Add F] [Sub F] [Mul F] [One F] (r : Open F) : fields 3 F :=
  let hook := 1 - r.ticket.direct
  #v[r.ticket.direct + hook*r.ticket.returned[0], hook*r.ticket.returned[1], hook*r.ticket.returned[2]]

/-- Global queue clock comparison for this one call. -/
def Open.order {F : Type} [Add F] [Mul F] [OfNat F 256] [OfNat F 65536] (r : Open F) : ClockOrder.Inputs F :=
  ⟨r.previous.clk_high, r.previous.clk_low, r.timestamp.high24, r.timestamp.low24⟩

/-- The queue after this call, at its authenticated CPU timestamp. -/
def Open.outgoing {F : Type} [Add F] [Mul F] [OfNat F 256] [OfNat F 65536] (r : Open F) : HostHintQueue.State F :=
  ⟨r.timestamp.high24,r.timestamp.low24,r.head,r.allocated⟩

/-- The first private cursor preserves the preceding head and allocation frontier. -/
def Open.first {F : Type} [Add F] [Sub F] [Mul F] [One F] [OfNat F 256] [OfNat F 65536] (r : Open F) : Cursor F :=
  ⟨r.source,r.count,{r.outgoing with head := r.previous.head, allocated := r.previous.allocated}⟩

/-- A call can release its outgoing state only after every buffer has been allocated. -/
def Open.last {F : Type} [Add F] [Mul F] [Zero F] [OfNat F 256] [OfNat F 65536] (r : Open F) : Cursor F :=
  ⟨r.source,#v[0,0,0],r.outgoing⟩

/-- One actual fresh node and its position in the allocation batch. -/
structure Step (F : Type) where
  /-- Existing checked prepend input. -/
  node : HintNodeAllocate.Inputs F
  /-- Source selector carried through the call. -/
  direct : F
  /-- Hook reply ordinal when the source is a hook. -/
  reply : fields 3 F
  /-- Number of buffers remaining before this node. -/
  remaining : fields 3 F
  /-- Number remaining afterwards and the returned buffer's zero-based index. -/
  index : fields 3 F
  /-- Total demand for this immutable metadata record. -/
  readers : F
deriving ProvableStruct
provable_struct_eval_lemmas Step

/-- Three-limb node length, whose fourth limb the allocation step constrains to zero. -/
def Step.length {F : Type} (r : Step F) : fields 3 F :=
  #v[r.node.node.length[0],r.node.node.length[1],r.node.node.length[2]]

/-- On the direct route the allocated pointer and length themselves name the authorization. -/
def Step.source {F : Type} [Add F] [Sub F] [Mul F] [One F] (r : Step F) : Source F :=
  ⟨r.direct, threeLimbs fun i => r.direct*r.node.node.pointer[i] + (1-r.direct)*r.reply[i], scale r.direct r.length⟩

/-- Allocate at the incoming frontier with the actual current head as the tail. -/
def Step.before {F : Type} [Add F] [Sub F] [Mul F] [One F] (r : Step F) : Cursor F :=
  ⟨r.source,r.remaining,r.node.previous⟩

/-- Publish the freshly allocated head and frontier and continue at the smaller ordinal. -/
def Step.after {F : Type} [Add F] [Sub F] [Mul F] [One F] (r : Step F) : Cursor F :=
  ⟨r.source,r.index,r.node.next⟩

/-- Fixed public metadata for exactly this returned buffer, including a zero-length buffer. -/
def Step.metadata {F : Type} [Zero F] [OfNat F 4] (r : Step F) : Record F :=
  ⟨4,0,r.reply,r.index,#v[0,0,0],r.length⟩

/-- The required word sequence of this particular fresh pointer. -/
def Step.contents {F : Type} [One F] [Sub F] [Mul F] (r : Step F) : Contents F :=
  ⟨r.direct,r.node.node.pointer,scale (1-r.direct) r.reply,r.index,r.length⟩

end SP1Clean.WriteAllocation
