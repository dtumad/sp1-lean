import SP1Clean.Export.InstalledAssembly

/-! # Resource bounds of the six-handler execution recovered from raw acceptance

Every cut uses the actual intermediate state of the accepted execution. The native preset
covers nine of the ten semantic measures. The transient complete-boundary payload includes
guest RAM and Sail output as well as the host payload.
-/

namespace SP1Clean.Export.InstalledAssembly
open Semantics

variable {context : Context} {header : SP1PublicIO Fp} {events : List Machine.ExecutionEvent}

/-- Exact prefix charges and the four checked host occupancies on the tape recovered by
`execution_of_statement`. For arbitrary limits, `SixCallProfile.ResourceFacts.fits_iff`
retains the declared event and padded-write ceilings as independent comparisons. -/
theorem ExecutionFacts.prefix_resources (facts : ExecutionFacts context header events) (cut : ℕ) :
    let policy := FormalModel.Shard.policy SP1Prime context.image
    ∃ middle, ExecutionPath policy context.image.program context.source.realize (events.take cut) middle ∧
      ExecutionPath policy context.image.program middle (events.drop cut) context.target.realize ∧
      SixCallProfile.ResourceFacts context.limits context.source.realize middle (events.take cut)
        (executionResources policy context.image.program context.source.realize (events.take cut)) := by
  have path := FormalModel.Shard.trace_iff_executionPath.mp facts.path
  obtain ⟨middle, left, right⟩ := path.split cut
  refine ⟨middle, left, right, SixCallProfile.resourceFacts left
    (fun e mem => facts.handlers e ((List.take_sublist cut events).subset mem)) ?_ ?_⟩
  · rw [context.source.resources_realize]
    exact facts.resources.1.1
  · have combined := left.resources_append (events.drop cut)
    rw [List.take_append_drop] at combined
    have total := facts.ticks
    rw [combined] at total
    exact (ResourceUsage.le_combine_left _ _ .ticks).trans total

/-- On the native preset, both the accumulated prefix usage and the actual reached state meet
every semantic ceiling except peak complete-boundary bytes. -/
theorem ExecutionFacts.native_prefix_resources (facts : ExecutionFacts context header events)
    (native : context.limits = ResourceLimits.native SP1Prime) (cut : ℕ) :
    let policy := FormalModel.Shard.policy SP1Prime context.image
    ∃ middle, ExecutionPath policy context.image.program context.source.realize (events.take cut) middle ∧
      ExecutionPath policy context.image.program middle (events.drop cut) context.target.realize ∧
      ∀ kind, kind ≠ .boundaryBytes →
        executionResources policy context.image.program context.source.realize (events.take cut) kind ≤
          context.limits.ceiling kind ∧ middle.resources kind ≤ context.limits.ceiling kind := by
  obtain ⟨middle, left, right, charges⟩ := facts.prefix_resources cut
  rw [native] at charges ⊢
  exact ⟨middle, left, right, charges.native_bounds⟩

/-- Raw acceptance at the native preset supplies one complete six-handler tape satisfying
the nine usage bounds at every cut, including the entire segment and the empty prefix. -/
theorem native_resources_of_statement (context : Context) {header : SP1PublicIO Fp} {heights : List ℕ}
    (native : context.limits = ResourceLimits.native SP1Prime)
    (accepted : (assembly context).Statement .logUp header heights) :
    ∃ events, ExecutionFacts context header events ∧ ∀ cut kind, kind ≠ .boundaryBytes →
      executionResources (FormalModel.Shard.policy SP1Prime context.image) context.image.program
        context.source.realize (events.take cut) kind ≤ context.limits.ceiling kind := by
  obtain ⟨_, _, _, _, events, facts⟩ := execution_of_statement context accepted
  refine ⟨events, facts, fun cut kind checked => ?_⟩
  obtain ⟨_, _, _, bounds⟩ := facts.native_prefix_resources native cut
  exact (bounds kind checked).1

end SP1Clean.Export.InstalledAssembly
