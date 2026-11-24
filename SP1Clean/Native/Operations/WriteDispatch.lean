import SP1Clean.Native.Operations.WriteRouteFlags
import SP1Clean.Native.Operations.AddressSum
import SP1Clean.Native.Operations.WriteStreamSource
import SP1Clean.Native.Operations.WriteStart

/-! # Chronological dispatch of one authenticated WRITE packet

Every header opens its byte interval and closes it at the exact length. The output cursor carries
four independent cumulative positions from the preceding WRITE. Hooks authenticate three metadata
records from the consumed reply ordinal, including empty requests and zero-return replies.
-/

namespace SP1Clean.WriteEffects
open Circuit

variable {p : Nat} [Fact p.Prime] [Fact (2^17 < p)]

/-- Hook metadata lookup keyed by the ordinal of the reply consumed by this call. -/
def Dispatch.metadata {F : Type} [OfNat F 3] [Zero F] (r : Dispatch F) (kind : F) (value : fields 3 F) : Record F :=
  ⟨3, kind, r.previous.replies, #v[0,0,0], #v[0,0,0], value⟩

/-- Consume the classified packet and advance its ordered stream and placement cursors. -/
def dispatchMain (r : Var Dispatch (ZMod p)) : Circuit (ZMod p) Unit := do
  requestChannel.pull r.request
  cursorChannel.pull r.previous
  let flags ← flagsCircuit r.request.route
  assertion (Gadgets.Equality.circuit DispatchFlags) (r.flags, flags)
  assertZero r.request.header.length[3]
  assertion (Gadgets.Equality.circuit (fields 3)) (r.payloadLength, r.length)
  assertion (Gadgets.Equality.circuit (fields 3)) (r.basePosition, r.outputPosition r.flags)
  assertion (Gadgets.Equality.circuit (fields 3)) (r.baseCounter, r.oldCounter r.flags)
  assertion (Gadgets.Equality.circuit (fields 3)) (r.delta, r.increment r.flags)
  assertion AddressSum.circuit ⟨r.previous.clock, r.clockGap, r.request.header.clock⟩
  assertion AddressSum.circuit ⟨r.request.header.clock, #v[1,0,0], r.nextClock⟩
  assertion WriteStart.circuit ⟨r.beforeAddress, r.request.header.address⟩
  assertion AddressSum.circuit ⟨r.beforeAddress, r.payloadLength, r.lastAddress⟩
  assertion AddressSum.circuit ⟨r.basePosition, r.payloadLength, r.endPosition⟩
  assertion AddressSum.circuit ⟨r.baseCounter, r.delta, r.nextCounter⟩
  recordChannel.pullIf r.flags.hook (r.metadata 2 #v[r.request.route,0,0])
  recordChannel.pullIf r.flags.hook (r.metadata 0 r.length)
  recordChannel.pullIf r.flags.hook (r.metadata 3 r.returned)
  queueEffectChannel.pushIf (r.flags.direct + r.flags.hook) (r.ticket r.flags)
  positionChannel.push (r.start r.flags)
  positionChannel.pull (r.finish r.flags)
  cursorChannel.push (r.next r.flags)

instance dispatchElaborated : ElaboratedCircuit (ZMod p) Dispatch unit dispatchMain := by elaborate_circuit

/-- A nonwrapping interval, a strictly increasing clock and the exact selected stream update. -/
def Dispatch.Valid (r : Dispatch (ZMod p)) : Prop :=
  r.flags = flagsFor r.request.route ∧ r.request.header.length[3] = 0 ∧
  r.payloadLength = r.length ∧ r.basePosition = r.outputPosition r.flags ∧
  r.baseCounter = r.oldCounter r.flags ∧ r.delta = r.increment r.flags ∧
  AddressSum.Spec ⟨r.previous.clock, r.clockGap, r.request.header.clock⟩ ∧
  AddressSum.Spec ⟨r.request.header.clock, #v[1,0,0], r.nextClock⟩ ∧
  WriteStart.Spec ⟨r.beforeAddress, r.request.header.address⟩ ∧
  AddressSum.Spec ⟨r.beforeAddress, r.payloadLength, r.lastAddress⟩ ∧
  AddressSum.Spec ⟨r.basePosition, r.payloadLength, r.endPosition⟩ ∧
  AddressSum.Spec ⟨r.baseCounter, r.delta, r.nextCounter⟩

private theorem flags_bool (r : ZMod p) :
    IsBool (flagsFor r).hook ∧ IsBool ((flagsFor r).direct + (flagsFor r).hook) := by
  have cases := flagsFor_choices r
  simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at cases
  rcases cases with h | h | h | h | h | h <;> simp [h.1, DispatchFlags.hook, IsBool]

/-- Formal circuit for dispatching one WRITE and accounting for its output positions. -/
def dispatchCircuit : GeneralFormalCircuit (ZMod p) Dispatch unit where
  name := "sp1.native.write_chronological_dispatch"
  main := dispatchMain
  elaborated := dispatchElaborated
  computableWitnesses := by computable_witnesses
  Spec r _ _ := r.Valid
  ProverAssumptions r _ _ := r.Valid
  channelsWithRequirements := [recordChannel.toRaw, queueEffectChannel.toRaw, positionChannel.toRaw, cursorChannel.toRaw]
  soundness := by
    circuit_proof_start [dispatchMain, flagsCircuit, Gadgets.Equality.circuit, WriteStart.circuit, AddressSum.circuit,
      requestChannel, cursorChannel, recordChannel, queueEffectChannel, positionChannel, Dispatch.oldCounter, Dispatch.outputPosition, Dispatch.increment, DispatchFlags.hook, Dispatch.length, threeLimbs, Nat.reduceMod, Fin.reduceFinMk, Fin.reduceEq, Fin.reduceOfNat]
    obtain ⟨g, same, length, payload, base, old, delta, clock, next, first, last, endPos, counter⟩ := h_holds
    have flagsEq : DispatchFlags.mk input_flags_ignored input_flags_stdout input_flags_stderr input_flags_publicOutput input_flags_direct = _ :=
      (DispatchFlags.mk.injEq ..).mpr same
    have route := flagsEq.trans g
    refine ⟨⟨route, length, Vector.toArray_inj.mp payload, Vector.toArray_inj.mp base, Vector.toArray_inj.mp old, Vector.toArray_inj.mp delta, clock, next, first, last, endPos, counter⟩, ?_⟩
    have hb := flags_bool input_request_route
    simp only [← route] at hb
    exact hb.1
  completeness := by
    circuit_proof_start [dispatchMain, flagsCircuit, Gadgets.Equality.circuit, WriteStart.circuit, AddressSum.circuit,
      requestChannel, cursorChannel, recordChannel, queueEffectChannel, positionChannel, Dispatch.oldCounter, Dispatch.outputPosition, Dispatch.increment, DispatchFlags.hook, Dispatch.length, threeLimbs, Nat.reduceMod, Fin.reduceFinMk, Fin.reduceEq, Fin.reduceOfNat]
    obtain ⟨g, length, payload, base, old, delta, clock, next, first, last, endPos, counter⟩ := h_assumptions
    exact ⟨(DispatchFlags.mk.injEq ..).mp (g.trans h_env.symm), length, Vector.toArray_inj.mpr payload, Vector.toArray_inj.mpr base, Vector.toArray_inj.mpr old, Vector.toArray_inj.mpr delta, clock, next, first, last, endPos, counter⟩

end SP1Clean.WriteEffects
