import SP1Clean.Native.Operations.WriteDispatch
import SP1Clean.Semantics.Execution.ExecutionSnapshot
import ToClean.Air.VerifierExtension
import ToClean.Air.HintIndex

/-! # Verifier-owned incoming and outgoing WRITE positions

One fixed terminal row consumes the last chronological cursor and proves that its clock is at
most the public target clock. Its four counters are derived from the public endpoint slices.
The terminal ticket is separate from internal cursor traffic so no intervening WRITE can fund it.
-/

namespace SP1Clean.WriteEffects
open Circuit Air.Flat Semantics
open scoped Classical

variable {p : Nat} [Fact p.Prime]

/-- Carries the terminal stream cursor checked against the public target. -/
def closeChannel : Channel (ZMod p) StreamCursor where
  name := "sp1.native.write_stream_end"
  Guarantees _ _ := True

/-- Start the four shard-local counters at zero at the incoming shard clock. -/
def initialCursor (clock : Nat) : StreamCursor (ZMod p) :=
  ⟨Address.ofNat clock, Address.ofNat 0, Address.ofNat 0, Address.ofNat 0, Address.ofNat 0⟩

/-- Expected final clock and four counter values derived from the public stream deltas. -/
def finalCursor (clock : Nat) (s : WriteStreams) : StreamCursor (ZMod p) :=
  ⟨Address.ofNat clock, Address.ofNat s.stdout.length, Address.ofNat s.stderr.length,
    Address.ofNat s.publicOutput.length, Address.ofNat s.hooks.length⟩

/-- Open the chronological cursor and consume its terminal ticket. -/
def cursorBoundaryMain (initial outgoing : StreamCursor (ZMod p)) (_ : Var unit (ZMod p)) : Circuit (ZMod p) Unit := do
  cursorChannel.push (const initial)
  closeChannel.pull (const outgoing)

/-- Verifier circuit publishing the incoming and outgoing stream positions. -/
def cursorBoundaryCircuit (initial outgoing : StreamCursor (ZMod p)) : GeneralFormalCircuit (ZMod p) unit unit where
  main := cursorBoundaryMain initial outgoing
  Spec _ _ _ := True
  ProverAssumptions _ _ _ := True
  channelsWithRequirements := [cursorChannel.toRaw]
  soundness := by circuit_proof_start [cursorBoundaryMain, cursorChannel, closeChannel]
  completeness := by circuit_proof_start [cursorBoundaryMain, cursorChannel, closeChannel]

theorem cursorBoundary_values (initial outgoing : StreamCursor (ZMod p)) (n : Nat) (env : Environment (ZMod p)) (ch : RawChannel (ZMod p)) :
    ((cursorBoundaryMain initial outgoing ()).operations n).interactionValuesWith ch env =
      [cursorChannel.pushedValue initial, closeChannel.pulledValue outgoing].filter (fun e => decide (e.channel = ch)) := by
  have pos : (cursorChannel.pushed (const initial)).toRaw.eval env = cursorChannel.pushedValue initial := by
    rw [Channel.eval_pushed, ProvableType.eval_const]
  have neg : (closeChannel.pulled (const outgoing)).toRaw.eval env = closeChannel.pulledValue outgoing := by
    rw [Channel.eval_pulled, ProvableType.eval_const]
  let raw := [(cursorChannel.pushed (const initial)).toRaw, (closeChannel.pulled (const outgoing)).toRaw]
  have values : raw.map (fun i => i.eval env) = [cursorChannel.pushedValue initial, closeChannel.pulledValue outgoing] := by
    simp only [raw, List.map_cons, List.map_nil, pos, neg]
  calc
    _ = (raw.map (fun i => i.eval env)).filter (fun e => decide (e.channel = ch)) := List.filter_map.symm
    _ = _ := congrArg (List.filter _) values

/-- Only the two native snapshots determine the verifier ledger. -/
def cursorEndpoint (source target : ExecutionSnapshot) : ClosedVerifier (ZMod p) where
  name := "write-output-positions"
  circuit := cursorBoundaryCircuit (initialCursor source.clock) (finalCursor target.clock (.fromEndpoints source.host target.host))
  assumptions := by intros; trivial
  lookups := by simp only [cursorBoundaryCircuit, cursorBoundaryMain, circuit_norm]
  public_interactions := by
    intro interaction member env
    simp only [cursorBoundaryCircuit, cursorBoundaryMain, circuit_norm, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;>
      simp [circuit_norm, ChannelInteraction.toRaw, AbstractInteraction.Requirements, Channel.toRaw, cursorChannel, closeChannel, Expression.eval]
  length_zero := rfl
  constraints := by intros; simp only [cursorBoundaryCircuit, cursorBoundaryMain, circuit_norm]
  interactions := by
    intro n env ch
    exact (cursorBoundary_values _ _ n env ch).trans (cursorBoundary_values _ _ 0 _ ch).symm

/-- Private last cursor clock and fixed ticket cells for the single terminal row. -/
structure CloseInput (F : Type) where
  /-- Fixed unit ticket requiring the terminal row to run. -/
  ticket : F
  /-- Publication multiplicity constrained to equal the unit ticket. -/
  count : F
  /-- Clock carried by the last internal stream cursor. -/
  prior : fields 3 F
  /-- Nonnegative difference from the last cursor clock to the public target clock. -/
  gap : fields 3 F
deriving ProvableStruct
provable_struct_eval_lemmas CloseInput

variable [Fact (2^17 < p)]

/-- Recover the last internal cursor using the certified final counter values. -/
def CloseInput.source {F : Type} (r : CloseInput F) (outgoing : StreamCursor F) : StreamCursor F :=
  {outgoing with clock := r.prior}

/-- Compare the private last clock to the target clock and publish the terminal ticket. -/
def closeMain (outgoing : StreamCursor (ZMod p)) (r : Var CloseInput (ZMod p)) : Circuit (ZMod p) Unit := do
  assertZero (r.ticket - 1)
  assertZero (r.count - r.ticket)
  assertion AddressSum.circuit ⟨r.prior, r.gap, const outgoing.clock⟩
  cursorChannel.pull (r.source (const outgoing))
  closeChannel.pushIf r.count (const outgoing)

/-- Formal circuit certifying the terminal clock and counters. -/
def closeCircuit (outgoing : StreamCursor (ZMod p)) : GeneralFormalCircuit (ZMod p) CloseInput unit where
  name := "sp1.native.write_output_terminal"
  main := closeMain outgoing
  Spec r _ _ := r.ticket = 1 ∧ r.count = 1 ∧ AddressSum.Spec ⟨r.prior, r.gap, outgoing.clock⟩
  ProverAssumptions r _ _ := r.ticket = 1 ∧ r.count = 1 ∧ AddressSum.Spec ⟨r.prior, r.gap, outgoing.clock⟩
  channelsWithRequirements := [closeChannel.toRaw]
  soundness := by
    circuit_proof_start [closeMain, AddressSum.circuit, cursorChannel, closeChannel]
    obtain ⟨ticket, count, clock⟩ := h_holds
    simp only [sub_eq_zero] at ticket count
    exact ⟨ticket,count.trans ticket,by simpa using clock⟩
  completeness := by
    circuit_proof_start [closeMain, AddressSum.circuit, cursorChannel, closeChannel]
    obtain ⟨ticket, count, clock⟩ := h_assumptions
    exact ⟨sub_eq_zero.mpr ticket, sub_eq_zero.mpr (count.trans ticket.symm), by simpa using clock⟩

/-- A singleton preallocation consumes exactly the verifier's final ticket. -/
def closeComponent (source target : ExecutionSnapshot) : Component (ZMod p) where
  circuit := closeCircuit (finalCursor target.clock (.fromEndpoints source.host target.host))
  generation := .preallocated {
    channel := closeChannel
    trigger := .pull
    height := 1
    input _ := pure ⟨.fixed 1, .multiplicity,
      Vector.ofFn (fun i : Fin 3 => .witness (.hintGet "sp1.native.write_output_terminal" 6 0 ⟨i.val,by omega⟩)),
      Vector.ofFn (fun i : Fin 3 => .witness (.hintGet "sp1.native.write_output_terminal" 6 0 ⟨3 + i.val,by omega⟩))⟩
    rowOf _ := 0 }

end SP1Clean.WriteEffects
