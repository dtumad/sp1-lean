import SP1Clean.FormalModel.Contracts.WritePlacement

/-! # Private chronological state of native WRITE effects

A single cursor orders all WRITE calls and counts the bytes appended to each independent output
as well as the number of supplied hook replies consumed. Packet-local rows carry the same incoming
clock throughout. A queue ticket binds direct and returned allocations to the corresponding packet.
-/

namespace SP1Clean.WriteEffects

/-- State threaded through WRITE calls in increasing execution-clock order. -/
structure StreamCursor (F : Type) where
  /-- Earliest clock allowed for the next WRITE. -/
  clock : fields 3 F
  /-- Number of standard-output bytes appended in this shard. -/
  stdout : fields 3 F
  /-- Number of standard-error bytes appended in this shard. -/
  stderr : fields 3 F
  /-- Number of public-output bytes appended in this shard. -/
  publicOutput : fields 3 F
  /-- Number of supplied hook replies consumed in this shard. -/
  replies : fields 3 F
deriving ProvableStruct, DecidableEq
provable_struct_eval_lemmas StreamCursor

/-- Connects consecutive WRITE calls through their clock and four stream positions. -/
def cursorChannel {p : Nat} : Channel (ZMod p) StreamCursor where
  name := "sp1.native.write_output_cursor"
  Guarantees _ _ := True

/-- A direct hint carries a new node identity; a hook carries the verified reply ordinal
and the verifier-fixed number of buffers in that reply. -/
structure QueueTicket (F : Type) where
  /-- Incoming execution clock of the allocating WRITE. -/
  clock : fields 3 F
  /-- One for a direct hint and zero for a hook reply. -/
  direct : F
  /-- Private node pointer for a direct hint or public reply ordinal for a hook. -/
  owner : fields 3 F
  /-- Byte length of the guest payload passed to WRITE. -/
  length : fields 3 F
  /-- Number of buffers returned by the hook, zero for a direct hint. -/
  returned : fields 3 F
deriving ProvableStruct, DecidableEq
provable_struct_eval_lemmas QueueTicket

/-- Carries direct-hint and hook allocation requests from chronological dispatch. -/
def queueEffectChannel {p : Nat} : Channel (ZMod p) QueueTicket where
  name := "sp1.native.write_queue_effect"
  Guarantees _ _ := True

/-- Equality selectors for the five explicit WRITE route tags. -/
structure DispatchFlags (F : Type) where
  /-- One when the classified output is discarded. -/
  ignored : F
  /-- One for the standard-output descriptor. -/
  stdout : F
  /-- One for the standard-error descriptor. -/
  stderr : F
  /-- One for the public-values descriptor. -/
  publicOutput : F
  /-- One for direct writes to the hint queue. -/
  direct : F
deriving ProvableStruct, DecidableEq
provable_struct_eval_lemmas DispatchFlags

/-- Complement of the five explicit selectors on a classified route. -/
def DispatchFlags.hook {F : Type} [One F] [Sub F] (g : DispatchFlags F) : F :=
  1 - g.ignored - g.stdout - g.stderr - g.publicOutput - g.direct

/-- Placement tag shared by a call and all its observed words. -/
def DispatchFlags.sink {F : Type} [Add F] [Mul F] [Sub F] [OfNat F 2] [OfNat F 13] [OfNat F 14] [OfNat F 3] [One F] (g : DispatchFlags F) : F :=
  g.stdout + 2 * g.stderr + 13 * g.publicOutput + 14 * g.direct + 3 * g.hook

/-- Actual columns supplied for one call. Changes to the four output counters are constructed
from the incoming state and a single checked successor of the selected stream. -/
structure Dispatch (F : Type) where
  /-- Authenticated WRITE header and classified route. -/
  request : Request F
  /-- Selectors for the route named by the request. -/
  flags : DispatchFlags F
  /-- Clock and output positions received from the preceding dispatch or shard boundary. -/
  previous : StreamCursor F
  /-- Nonnegative difference from the preceding cursor clock to the incoming call clock. -/
  clockGap : fields 3 F
  /-- Incoming call clock plus one, enforcing strict order at the next dispatch. -/
  nextClock : fields 3 F
  /-- Three-limb length of the authenticated guest buffer. -/
  payloadLength : fields 3 F
  /-- Position of the first payload byte in the selected output, or zero for a fresh buffer. -/
  basePosition : fields 3 F
  /-- Value of the selected output or reply counter before processing the call. -/
  baseCounter : fields 3 F
  /-- Selected output's byte count increment, or one consumed hook reply. -/
  delta : fields 3 F
  /-- Address immediately preceding the first guest byte. -/
  beforeAddress : fields 3 F
  /-- Inclusive last byte position, equal to the preceding address for an empty payload. -/
  lastAddress : fields 3 F
  /-- Exclusive end of the destination byte interval. -/
  endPosition : fields 3 F
  /-- Selected counter after applying this call's increment. -/
  nextCounter : fields 3 F
  /-- Private node identity used on the direct-hint route. -/
  pointer : fields 3 F
  /-- Number of returned hint buffers authenticated for a hook request. -/
  returned : fields 3 F
deriving ProvableStruct
provable_struct_eval_lemmas Dispatch

/-- Low three limbs of the packet length, whose top limb the dispatcher checks is zero. -/
def Dispatch.length {F : Type} (d : Dispatch F) : fields 3 F :=
  #v[d.request.header.length[0], d.request.header.length[1], d.request.header.length[2]]

/-- Three independent limb expressions in an ordinary little-endian address. -/
def threeLimbs {F : Type} (f : Fin 3 → F) : fields 3 F := #v[f 0, f 1, f 2]

/-- Select the cumulative byte position for the chosen output stream. -/
def Dispatch.outputPosition {F : Type} [Add F] [Mul F] (d : Dispatch F) (g : DispatchFlags F) : fields 3 F :=
  threeLimbs fun i => g.stdout*d.previous.stdout[i] + g.stderr*d.previous.stderr[i] + g.publicOutput*d.previous.publicOutput[i]

/-- Select the byte counter of an output or the ordinal of the next hook reply. -/
def Dispatch.oldCounter {F : Type} [Add F] [Mul F] [Sub F] [One F] (d : Dispatch F) (g : DispatchFlags F) : fields 3 F :=
  threeLimbs fun i => (d.outputPosition g)[i] + g.hook * d.previous.replies[i]

/-- Advance by the payload length for outputs or by one for a hook reply. -/
def Dispatch.increment {F : Type} [Add F] [Mul F] [Sub F] [One F] (d : Dispatch F) (g : DispatchFlags F) : fields 3 F :=
  let output := g.stdout + g.stderr + g.publicOutput
  #v[output * d.length[0] + g.hook, output * d.length[1], output * d.length[2]]

/-- Select the direct-hint node pointer or the consumed hook reply ordinal. -/
def Dispatch.owner {F : Type} [Add F] [Mul F] [Sub F] [One F] (d : Dispatch F) (g : DispatchFlags F) : fields 3 F :=
  threeLimbs fun i => g.direct*d.pointer[i] + g.hook*d.previous.replies[i]

/-- Advance the clock and replace the selected output or reply counter. -/
def Dispatch.next {F : Type} [Add F] [Mul F] [Sub F] [One F] (d : Dispatch F) (g : DispatchFlags F) : StreamCursor F :=
  let update (flag : F) (old : fields 3 F) := threeLimbs fun i => old[i] + flag*(d.nextCounter[i] - old[i])
  ⟨d.nextClock, update g.stdout d.previous.stdout, update g.stderr d.previous.stderr,
    update g.publicOutput d.previous.publicOutput, update g.hook d.previous.replies⟩

/-- Placement cursor opened at the guest predecessor and first destination position. -/
def Dispatch.start {F : Type} [Add F] [Mul F] [Sub F] [OfNat F 2] [OfNat F 13] [OfNat F 14] [OfNat F 3] [One F] (d : Dispatch F) (g : DispatchFlags F) : Placement F :=
  ⟨d.request.header.clock, g.sink, d.owner g, d.beforeAddress, d.outputPosition g⟩

/-- Placement cursor expected after the final byte of the request. -/
def Dispatch.finish {F : Type} [Add F] [Mul F] [Sub F] [OfNat F 2] [OfNat F 13] [OfNat F 14] [OfNat F 3] [One F] (d : Dispatch F) (g : DispatchFlags F) : Placement F :=
  {d.start g with address := d.lastAddress, position := d.endPosition}

/-- Construct the queue request sharing this dispatch's clock, owner and payload size. -/
def Dispatch.ticket {F : Type} [Add F] [Mul F] [Sub F] [One F] (d : Dispatch F) (g : DispatchFlags F) : QueueTicket F :=
  ⟨d.request.header.clock, g.direct, d.owner g, d.length, threeLimbs fun i => g.hook*d.returned[i]⟩

end SP1Clean.WriteEffects
