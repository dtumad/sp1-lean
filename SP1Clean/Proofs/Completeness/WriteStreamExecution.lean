import SP1Clean.Native.Operations.WriteStreamBoundary
import SP1Clean.Proofs.Completeness.WriteStreamCapacity
import SP1Clean.Semantics.Host.HostExecutionLaws

/-! # The verifier's WRITE endpoints on arbitrary mixed execution paths -/

namespace SP1Clean.WriteEffects

open Semantics Machine FormalModel.Shard

private theorem of_run {host : HostState} {policy : HostPolicy} {context : HostReadContext} {call : HostExecution}
    (ran : host.run policy context = some call) : ∃ streams : WriteStreams, streams.Binds host call.effect.state := by
  have effect := ((HostState.run_eq_some_iff ..).mp ran).2.2.2.2.2
  cases kind : call.kind with
  | write =>
    rw [kind] at effect
    obtain ⟨_, bytes, next, _, _, output, same⟩ := (HostState.execute_write_iff ..).mp effect
    rw [same]
    exact ⟨_, WriteStreams.ofEvent_binds ((WriteRoute.effect_iff host next call.arg1 bytes).mpr output)⟩
  | hintRead =>
    rw [kind] at effect
    obtain ⟨_, rest, _, _, _, _, same⟩ := (HostState.execute_hintRead_iff ..).mp effect
    rw [same]
    exact ⟨{}, by constructor <;> simp⟩
  | _ =>
    rw [kind] at effect
    simp only [HostState.executeKind] at effect
    try split_ifs at effect
    all_goals
      rw [← Option.some.inj effect]
      exact ⟨{}, by constructor <;> simp⟩

/-- Outputs and requests keep their order through ordinary steps, WRITE, and each
of the other seven handlers. Every consumed hook reply comes from the supplied prefix. -/
theorem execution_streams {policy : HostPolicy} {program : Soundness.Target.GuestProgram} {source target : ExecutionState}
    {events : List ExecutionEvent} (path : ExecutionPath policy program source events target) :
    (WriteStreams.fromEndpoints source.host target.host).Binds source.host target.host := by
  induction path with
  | nil s =>
    have same : ({} : WriteStreams).Binds s.host s.host := by constructor <;> simp
    exact same.unique.symm ▸ same
  | @cons source middle _ _ _ step _ suffix =>
    obtain ⟨head, front⟩ : ∃ streams : WriteStreams, streams.Binds source.host middle.host := by
      cases step with
      | ordinary => exact ⟨{}, by constructor <;> simp⟩
      | syscall success =>
        obtain ⟨_, call, _, _, ran, reached, _, _⟩ := HostState.step_observations success
        rw [reached]
        exact of_run ran
    have entire := front.append suffix
    exact entire.unique.symm ▸ entire

/-- All native resource-admissible runs satisfy the complete fixed-record checker.
Both endpoint consistency and representability are consequences of the run. -/
theorem admissible_streams {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (ResourceLimits.native SP1Prime) SP1Prime image source target events) :
    boundarySpec source.host target.host :=
  ⟨execution_streams run.1.2, admissible_inventoryOK run⟩

end SP1Clean.WriteEffects
