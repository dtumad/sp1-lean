import SP1Clean.Export.SixCallResources

/-! # Complete release execution of an accepted short shard

A shard containing at most one event visits only the two checked endpoint states. Their
authenticated boundary occupancies therefore bound its peak payload. With the native preset,
the other nine resource dimensions follow from the recovered six-handler execution.
A public interval shorter than sixteen ticks admits only an empty tape or one ordinary step.
-/

namespace SP1Clean.Export.InstalledAssembly

open Semantics Machine FormalModel.Shard

private theorem boundaryBytes_of_one {policy : HostPolicy} {program : Soundness.Target.GuestProgram}
    {source target : ExecutionState} {events : List ExecutionEvent} {limit : ℕ}
    (path : ExecutionPath policy program source events target) (few : events.length ≤ 1)
    (incoming : source.resources .boundaryBytes ≤ limit) (outgoing : target.resources .boundaryBytes ≤ limit) :
    executionResources policy program source events .boundaryBytes ≤ limit := by
  cases events with
  | nil => exact Nat.zero_le _
  | cons event rest =>
    have nil : rest = [] := List.length_eq_zero_iff.mp (by simpa using few)
    subst rest
    cases path with
    | cons step suffix =>
      obtain rfl := ExecutionPath.nil_iff.mp suffix
      rw [executionResources_cons step [], executionResources_nil]
      have noCharge : source.eventResources policy event .boundaryBytes = 0 := by
        cases event <;> simp only [ExecutionState.eventResources, HostState.eventResources]
        split <;> rfl
      simp only [ResourceUsage.combine, ResourceKind.cumulative, Bool.false_eq_true, ↓reduceIte,
        noCharge, ResourceUsage.zero, Nat.max_zero, max_le_iff]
      exact ⟨incoming, outgoing⟩

/-- A recovered one-event tape may carry any of the six handlers. Its only observable
boundary occupancies belong to the checked source and target. -/
theorem ExecutionFacts.release_of_length_le_one {context : Context} {header : SP1PublicIO Fp}
    {events : List ExecutionEvent} (facts : ExecutionFacts context header events)
    (native : context.limits = ResourceLimits.native SP1Prime)
    (valid : ExecutionSourceValid context.image context.source)
    (committed : context.commitments.WellFormed SP1Prime) (few : events.length ≤ 1) :
    ReleaseStatementExecution context.limits SP1Prime context.commitments context.image context.source context.target events := by
  apply (facts.release_iff_fits valid committed).mpr
  intro kind
  by_cases payload : kind = .boundaryBytes
  · subst kind
    obtain ⟨incoming, outgoing, _⟩ := facts.resources.1
    rw [← context.source.resources_realize] at incoming
    rw [← context.target.resources_realize] at outgoing
    exact boundaryBytes_of_one (trace_iff_executionPath.mp facts.path) few (incoming _) (outgoing _)
  · obtain ⟨_, _, _, bounds⟩ := facts.native_prefix_resources native events.length
    simpa only [List.take_length] using (bounds kind payload).1

/-- Raw acceptance on the native preset and a public clock interval shorter than two ordinary
steps yield the entire release statement for the recovered tape. A syscall needs 264 ticks. -/
theorem native_release_of_short_statement (context : Context) {header : SP1PublicIO Fp} {heights : List ℕ}
    (native : context.limits = ResourceLimits.native SP1Prime)
    (short : clkNat header.final_clk_high header.final_clk_low - clkNat header.init_clk_high header.init_clk_low < 16)
    (accepted : (assembly context).Statement .logUp header heights) :
    ∃ events, ExecutionFacts context header events ∧ (events = [] ∨ events = [.ordinary]) ∧
      ReleaseStatementExecution context.limits SP1Prime context.commitments context.image context.source context.target events := by
  obtain ⟨valid, sourceFor, _, committed, events, facts⟩ := execution_of_statement context accepted
  rw [facts.resources.2.clock facts.resources.1.2.2.2.2.1, sourceFor.clock valid.2.2.1] at short
  have count := facts.count
  have few : events.length ≤ 1 := by omega
  refine ⟨events, facts, ?_, facts.release_of_length_le_one native valid committed.1 few⟩
  cases events with
  | nil => exact Or.inl rfl
  | cons event rest =>
    have nil : rest = [] := List.length_eq_zero_iff.mp (by simpa using few)
    subst rest
    cases event with
    | ordinary => exact Or.inr rfl
    | syscall call =>
      have duration := (trace_iff_executionPath.mp facts.path).clock
      change context.target.clock = context.source.clock + _ at duration
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero,
        ExecutionEvent.duration_syscall] at duration
      omega

/-- An accepted running-to-stopped interval shorter than HALT followed or preceded by any
other event has exactly one HALT. Its checked argument is the public exit code, and its
one-event execution satisfies the complete release statement. -/
theorem native_release_of_short_halt (context : Context) {header : SP1PublicIO Fp} {heights : List ℕ}
    {code : BitVec 32} (native : context.limits = ResourceLimits.native SP1Prime)
    (running : context.source.host.exitCode = none) (stopped : context.target.host.exitCode = some code)
    (short : clkNat header.final_clk_high header.final_clk_low - clkNat header.init_clk_high header.init_clk_low < 272)
    (accepted : (assembly context).Statement .logUp header heights) :
    ∃ call, ExecutionFacts context header [.syscall call] ∧ call.rawCode = 0 ∧
      call.arg1.setWidth 32 = code ∧ code.toNat = header.exit_code.val ∧
      ReleaseStatementExecution context.limits SP1Prime context.commitments context.image
        context.source context.target [.syscall call] := by
  obtain ⟨valid, sourceFor, _, committed, events, facts⟩ := execution_of_statement context accepted
  rw [facts.resources.2.clock facts.resources.1.2.2.2.2.1, sourceFor.clock valid.2.2.1] at short
  obtain ⟨⟨before, call, rfl, halt, argument⟩, publicExit, _⟩ := facts.halted running stopped
  have clock := (trace_iff_executionPath.mp facts.path).clock
  change context.target.clock = context.source.clock + _ at clock
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Nat.add_zero, ExecutionEvent.duration_syscall] at clock
  have count := event_count_le_ticks before
  obtain rfl := List.length_eq_zero_iff.mp (show before.length = 0 by omega)
  exact ⟨call, facts, halt, argument, publicExit, facts.release_of_length_le_one native valid committed.1 (by simp)⟩

end SP1Clean.Export.InstalledAssembly
