import SP1Clean.Proofs.Completeness.WriteDispatchRows
import SP1Clean.Proofs.Completeness.WriteProbeDemand

/-! # Incremental WRITE stream positions on the mixed CPU tape

The packed dispatcher needs only four lengths. The actual register observation advances
the selected byte count, and every accepted hook advances its reply ordinal once.
-/

namespace SP1Clean.WriteEffects.StreamCounts

open Semantics Machine FormalModel.Shard TraceGen

/-- Advance the four positions using the same event and packet as the original dispatcher. -/
def advance (s : StreamCounts) : ExecutionEvent → Option WriteObservations.Packet → StreamCounts
  | .syscall call, some p => match WriteRoute.ofDescriptor call.arg1 with
    | .stdout => {s with stdout := s.stdout + p.1.toNat}
    | .stderr => {s with stderr := s.stderr + p.1.toNat}
    | .publicValues => {s with publicValues := s.publicValues + p.1.toNat}
    | .hook _ => {s with hooks := s.hooks + 1}
    | _ => s
  | _, _ => s

private theorem same (earlier : WriteStreams) :
    ofStreams (earlier.append {}) = ofStreams earlier := by simp [ofStreams, WriteStreams.append]

private theorem write_count (earlier : WriteStreams) {source target : HostState} {call : CoreSyscallEvent}
    {bytes : Bytes} {packet : WriteObservations.Packet}
    (effect : (WriteRoute.ofDescriptor call.arg1).Effect source bytes target) (size : bytes.length = packet.1.toNat) :
    advance (ofStreams earlier) (.syscall call) (some packet) =
      ofStreams (earlier.append (WriteStreams.ofEvent (WriteRoute.ofDescriptor call.arg1) source bytes)) := by
  cases route : WriteRoute.ofDescriptor call.arg1 with
  | hook fd =>
    rw [route] at effect
    obtain ⟨_,_,head,_⟩ := effect
    simp [advance,ofStreams,route,WriteStreams.append,WriteStreams.ofEvent,head]
  | _ => simp [advance,ofStreams,route,WriteStreams.append,WriteStreams.ofEvent,size]

/-- Every real mixed step preserves the running-count invariant at the next host state. -/
theorem advance_correct {host : HostPolicy} {program : Soundness.Target.GuestProgram}
    {current next : ExecutionState} {event : ExecutionEvent} (step : ExecutionStep host program current event next)
    {packet : Option WriteObservations.Packet} (observed : WriteObservations.packetAt? current.sail event = some packet)
    {origin : HostState} {earlier : WriteStreams} (prior : earlier.Binds origin current.host) :
    (WriteStreams.fromEndpoints origin next.host).Binds origin next.host ∧
      advance (ofStreams earlier) event packet = ofStreams (WriteStreams.fromEndpoints origin next.host) := by
  suffices added : ∃ delta : WriteStreams, delta.Binds current.host next.host ∧
      advance (ofStreams earlier) event packet = ofStreams (earlier.append delta) by
    obtain ⟨delta,binds,count⟩ := added
    have result := prior.append binds
    rw [result.unique]
    exact ⟨result,count⟩
  cases event with
  | ordinary =>
    cases observed
    cases step
    exact ⟨{}, by constructor <;> simp, (same earlier).symm⟩
  | syscall call =>
    by_cases write : call.rawCode = SyscallKind.write.code
    · simp only [WriteObservations.packetAt?,ite_eq_left write,Option.map_eq_some_iff] at observed
      obtain ⟨⟨len,buffer⟩,read,rfl⟩ := observed
      have x12 := (WriteObservations.read?_eq_some_iff.mp read).2.1
      cases step with
      | syscall ran =>
        obtain ⟨pc,execution,_,_,success,hostEq,_,eventEq⟩ := HostState.step_observations ran
        subst call
        have kind : execution.kind = .write := SyscallKind.code_injective write
        have law := ((HostState.run_eq_some_iff ..).mp success).2.2.2.2.2
        rw [kind] at law
        obtain ⟨length,bytes,after,register,taken,output,changed⟩ := (HostState.execute_write_iff ..).mp law
        cases Option.some.inj (x12.symm.trans register)
        have size := ((HostReadContext.readGuest?_eq_some_iff ..).mp taken).2.2.1
        rw [hostEq,changed]
        have effect := (WriteRoute.effect_iff _ _ _ _).mpr output
        exact ⟨_,WriteStreams.ofEvent_binds effect,write_count earlier effect size⟩
    · simp only [WriteObservations.packetAt?,ite_eq_right write,Option.some.injEq] at observed
      subst packet
      exact ⟨{},nonwrite_streams step write,(same earlier).symm⟩

end SP1Clean.WriteEffects.StreamCounts
