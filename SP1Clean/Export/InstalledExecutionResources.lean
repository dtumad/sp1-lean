import SP1Clean.Export.InstalledAssembly
import SP1Clean.FormalModel.ShardRelease

/-! # Resource bounds of the seven-handler execution recovered from raw acceptance

Every cut uses the actual intermediate state of the accepted execution. The native preset
covers nine of the ten semantic measures. The transient complete-boundary payload includes
guest RAM and Sail output as well as the host payload.
-/

namespace SP1Clean.Export.InstalledAssembly
open Semantics

variable {context : Context} {header : SP1PublicIO Fp} {events : List Machine.ExecutionEvent}

/-- Exact prefix charges and the four checked host occupancies on the tape recovered by
`execution_of_statement`. For arbitrary limits, `HostReceiptProfile.ResourceFacts.fits_iff`
retains the declared event and padded-write ceilings as independent comparisons. -/
theorem ExecutionFacts.prefix_resources (facts : ExecutionFacts context header events) (cut : ℕ) :
    let policy := FormalModel.Shard.policy SP1Prime context.image
    ∃ middle, ExecutionPath policy context.image.program context.source.realize (events.take cut) middle ∧
      ExecutionPath policy context.image.program middle (events.drop cut) context.target.realize ∧
      HostReceiptProfile.ResourceFacts context.limits context.source.realize middle (events.take cut)
        (executionResources policy context.image.program context.source.realize (events.take cut)) := by
  have path := FormalModel.Shard.trace_iff_executionPath.mp facts.path
  obtain ⟨middle, left, right⟩ := path.split cut
  refine ⟨middle, left, right, HostReceiptProfile.resourceFacts left
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

/-- Raw acceptance at the native preset supplies one complete seven-handler tape satisfying
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

open FormalModel.Shard

/-- Given the source validity and commitment well-formedness recovered by `execution_of_statement`,
the complete release statement on its tape is equivalent to fitting the resource limits. -/
theorem ExecutionFacts.release_iff_fits (facts : ExecutionFacts context header events)
    (valid : ExecutionSourceValid context.image context.source)
    (commitments : context.commitments.WellFormed SP1Prime) :
    ReleaseStatementExecution context.limits SP1Prime context.commitments context.image
      context.source context.target events ↔
      (executionResources (policy SP1Prime context.image) context.image.program context.source.realize events).Fits
        context.limits := by
  refine ⟨fun execution => execution.1.1.2.2.1, fun fits => ?_⟩
  obtain ⟨incoming, outgoing, _, _, time, pc⟩ := facts.resources.1
  rw [← context.source.resources_realize] at incoming
  rw [← context.target.resources_realize] at outgoing
  exact ⟨⟨⟨⟨valid, trace_iff_executionPath.mp facts.path⟩, facts.encoded, fits, incoming, outgoing, time, pc⟩,
    facts.releaseLinks⟩, commitments, facts.commitments⟩

/-- At independently chosen public ceilings, the accepted tape meets the complete release
statement exactly when its event count, padded writes and peak boundary payload fit. -/
theorem release_statement_iff_of_statement (context : Context) {header : SP1PublicIO Fp} {heights : List ℕ}
    (accepted : (assembly context).Statement .logUp header heights) :
    ∃ events, ExecutionFacts context header events ∧
      (ReleaseStatementExecution context.limits SP1Prime context.commitments context.image
        context.source context.target events ↔
        let usage := executionResources (policy SP1Prime context.image) context.image.program context.source.realize events
        events.length ≤ context.limits.events ∧ usage .writeBytes ≤ context.limits.writeBytes ∧
        usage .boundaryBytes ≤ context.limits.boundaryBytes) := by
  obtain ⟨valid, _, _, commitments, events, facts⟩ := execution_of_statement context accepted
  have incoming := facts.resources.1.1
  rw [← context.source.resources_realize] at incoming
  have charges := HostReceiptProfile.resourceFacts (trace_iff_executionPath.mp facts.path) facts.handlers incoming facts.ticks
  refine ⟨events, facts, (facts.release_iff_fits valid commitments.1).trans ?_⟩
  constructor
  · intro fits
    obtain ⟨count, writes⟩ := charges.fits_iff.mp (fun kind _ => fits kind)
    exact ⟨count, writes, fits .boundaryBytes⟩
  · rintro ⟨count, writes, peak⟩ kind
    by_cases boundary : kind = .boundaryBytes
    · exact boundary ▸ peak
    · exact charges.fits_iff.mpr ⟨count, writes⟩ kind boundary

/-- Raw native acceptance recovers a complete seven-handler execution. All clauses of the release
statement on that tape reduce to one comparison with its measured peak boundary payload. -/
theorem native_release_statement_iff_peak (context : Context) {header : SP1PublicIO Fp} {heights : List ℕ}
    (native : context.limits = ResourceLimits.native SP1Prime)
    (accepted : (assembly context).Statement .logUp header heights) :
    ∃ events, ExecutionFacts context header events ∧
      (ReleaseStatementExecution context.limits SP1Prime context.commitments context.image
        context.source context.target events ↔
        executionResources (policy SP1Prime context.image) context.image.program context.source.realize events
          .boundaryBytes ≤ context.limits.boundaryBytes) := by
  obtain ⟨events, facts, characterization⟩ := release_statement_iff_of_statement context accepted
  obtain ⟨_, _, _, charges⟩ := facts.native_prefix_resources native events.length
  simp only [List.take_length] at charges
  have count := (trace_iff_executionPath.mp facts.path).resources_events
  refine ⟨events, facts, characterization.trans ⟨fun h => h.2.2, fun peak => ?_⟩⟩
  exact ⟨count ▸ (charges .events (by decide)).1, (charges .writeBytes (by decide)).1, peak⟩

end SP1Clean.Export.InstalledAssembly
