import SP1Clean.FormalModel.Contracts.WritePlacement

/-! # Private chronological state of native WRITE effects

A single cursor orders all WRITE calls and counts the bytes appended to each independent output
as well as the number of supplied hook replies consumed. Packet-local rows carry the same incoming
clock throughout. A queue ticket binds direct and returned allocations to the corresponding packet.
-/

namespace SP1Clean.WriteEffects

structure StreamCursor (F : Type) where
  clock : fields 3 F
  stdout : fields 3 F
  stderr : fields 3 F
  publicOutput : fields 3 F
  replies : fields 3 F
deriving ProvableStruct, DecidableEq
provable_struct_eval_lemmas StreamCursor

def cursorChannel {p : Nat} : Channel (ZMod p) StreamCursor where
  name := "sp1.native.write_output_cursor"
  Guarantees _ _ := True

/-- A direct hint carries a new node identity; a hook carries the verified reply ordinal
and the verifier-fixed number of buffers in that reply. -/
structure QueueTicket (F : Type) where
  clock : fields 3 F
  direct : F
  owner : fields 3 F
  length : fields 3 F
  returned : fields 3 F
deriving ProvableStruct, DecidableEq
provable_struct_eval_lemmas QueueTicket

def queueEffectChannel {p : Nat} : Channel (ZMod p) QueueTicket where
  name := "sp1.native.write_queue_effect"
  Guarantees _ _ := True

structure DispatchFlags (F : Type) where
  ignored : F
  stdout : F
  stderr : F
  publicOutput : F
  direct : F
deriving ProvableStruct, DecidableEq
provable_struct_eval_lemmas DispatchFlags

def DispatchFlags.hook {F : Type} [One F] [Sub F] (g : DispatchFlags F) : F :=
  1 - g.ignored - g.stdout - g.stderr - g.publicOutput - g.direct

def DispatchFlags.sink {F : Type} [Add F] [Mul F] [Sub F] [OfNat F 2] [OfNat F 13] [OfNat F 14] [OfNat F 3] [One F] (g : DispatchFlags F) : F :=
  g.stdout + 2 * g.stderr + 13 * g.publicOutput + 14 * g.direct + 3 * g.hook

/-- Actual columns supplied for one call. Changes to the four output counters are constructed
from the incoming state and a single checked successor of the selected stream. -/
structure Dispatch (F : Type) where
  request : Request F
  flags : DispatchFlags F
  previous : StreamCursor F
  clockGap : fields 3 F
  nextClock : fields 3 F
  payloadLength : fields 3 F
  basePosition : fields 3 F
  baseCounter : fields 3 F
  delta : fields 3 F
  beforeAddress : fields 3 F
  lastAddress : fields 3 F
  endPosition : fields 3 F
  nextCounter : fields 3 F
  pointer : fields 3 F
  returned : fields 3 F
deriving ProvableStruct
provable_struct_eval_lemmas Dispatch

def Dispatch.length {F : Type} (d : Dispatch F) : fields 3 F :=
  #v[d.request.header.length[0], d.request.header.length[1], d.request.header.length[2]]

/-- Three independent limb expressions in an ordinary little-endian address. -/
def threeLimbs {F : Type} (f : Fin 3 → F) : fields 3 F := #v[f 0, f 1, f 2]

def Dispatch.outputPosition {F : Type} [Add F] [Mul F] (d : Dispatch F) (g : DispatchFlags F) : fields 3 F :=
  threeLimbs fun i => g.stdout*d.previous.stdout[i] + g.stderr*d.previous.stderr[i] + g.publicOutput*d.previous.publicOutput[i]

def Dispatch.oldCounter {F : Type} [Add F] [Mul F] [Sub F] [One F] (d : Dispatch F) (g : DispatchFlags F) : fields 3 F :=
  threeLimbs fun i => (d.outputPosition g)[i] + g.hook * d.previous.replies[i]

def Dispatch.increment {F : Type} [Add F] [Mul F] [Sub F] [Zero F] [One F] (d : Dispatch F) (g : DispatchFlags F) : fields 3 F :=
  let output := g.stdout + g.stderr + g.publicOutput
  #v[output * d.length[0] + g.hook, output * d.length[1], output * d.length[2]]

def Dispatch.owner {F : Type} [Add F] [Mul F] [Sub F] [One F] (d : Dispatch F) (g : DispatchFlags F) : fields 3 F :=
  threeLimbs fun i => g.direct*d.pointer[i] + g.hook*d.previous.replies[i]

def Dispatch.next {F : Type} [Add F] [Mul F] [Sub F] [One F] (d : Dispatch F) (g : DispatchFlags F) : StreamCursor F :=
  let update (flag : F) (old : fields 3 F) := threeLimbs fun i => old[i] + flag*(d.nextCounter[i] - old[i])
  ⟨d.nextClock, update g.stdout d.previous.stdout, update g.stderr d.previous.stderr,
    update g.publicOutput d.previous.publicOutput, update g.hook d.previous.replies⟩

def Dispatch.start {F : Type} [Add F] [Mul F] [Sub F] [OfNat F 2] [OfNat F 13] [OfNat F 14] [OfNat F 3] [One F] (d : Dispatch F) (g : DispatchFlags F) : Placement F :=
  ⟨d.request.header.clock, g.sink, d.owner g, d.beforeAddress, d.outputPosition g⟩

def Dispatch.finish {F : Type} [Add F] [Mul F] [Sub F] [OfNat F 2] [OfNat F 13] [OfNat F 14] [OfNat F 3] [One F] (d : Dispatch F) (g : DispatchFlags F) : Placement F :=
  {d.start g with address := d.lastAddress, position := d.endPosition}

def Dispatch.ticket {F : Type} [Add F] [Mul F] [Sub F] [One F] (d : Dispatch F) (g : DispatchFlags F) : QueueTicket F :=
  ⟨d.request.header.clock, g.direct, d.owner g, d.length, threeLimbs fun i => g.hook*d.returned[i]⟩

end SP1Clean.WriteEffects
