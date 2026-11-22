import SP1Clean.Export.InstalledExecutionResources
import SP1Clean.Export.InstalledFixedPreset
import SP1Clean.Semantics.Resources.BoundaryGrowth
import SP1Clean.Soundness.Shard.Contract

/-! # Complete release executions recovered with a public boundary-payload budget

Raw acceptance authenticates the source payload, elapsed clock and the installed handler
profile. Each ordinary retirement consumes eight ticks and can add at most eight live bytes.
The fixed-provider preset reserves enough room for their total in the native semantic ceiling.
-/

namespace SP1Clean.Export.InstalledAssembly
open Semantics Machine FormalModel.Shard

variable {context : Context} {header : SP1PublicIO Fp} {events : List ExecutionEvent}

/-- At each cut of the accepted tape, the actual reached state and the peak of the whole prefix
fit the incoming payload plus eight bytes per ordinary instruction in that prefix. -/
theorem ExecutionFacts.prefix_boundary_growth (facts : ExecutionFacts context header events)
    (valid : ExecutionSourceValid context.image context.source) (cut : ℕ) :
    let initialEvents := events.take cut
    let budget := context.source.resources .boundaryBytes + 8 * initialEvents.countP ExecutionEvent.isOrdinary
    ∃ middle, ExecutionPath (policy SP1Prime context.image) context.image.program context.source.realize initialEvents middle ∧
      ExecutionPath (policy SP1Prime context.image) context.image.program middle (events.drop cut) context.target.realize ∧
      middle.boundaryPayload ≤ budget ∧
      executionResources (policy SP1Prime context.image) context.image.program context.source.realize initialEvents
        .boundaryBytes ≤ budget := by
  obtain ⟨middle, left, right⟩ := (trace_iff_executionPath.mp facts.path).split cut
  refine ⟨middle, left, right, ?_⟩
  rw [context.image.program_eq valid.1.1] at left ⊢
  rw [← context.source.resources_realize]
  exact left.boundaryPayload_growth valid.1.1 (fun e mem => facts.handlers e ((List.take_sublist cut events).subset mem))
    (fun _ selected => selected) valid.configured valid.romLoaded

/-- The complete native release statement on an accepted tape. The accepting context may
tighten any native limits; the outgoing interpretation uses the specified native limits. -/
private theorem native_release_of_budget (facts : ExecutionFacts context header events)
    (valid : ExecutionSourceValid context.image context.source)
    (committed : context.commitments.WellFormed SP1Prime)
    (smaller : context.limits.LE (.native SP1Prime))
    (budget : context.source.resources .boundaryBytes + (context.target.clock - context.source.clock) ≤
      (ResourceLimits.native SP1Prime).boundaryBytes) :
    ReleaseStatementExecution (.native SP1Prime) SP1Prime context.commitments context.image
      context.source context.target events := by
  obtain ⟨incoming, outgoing, _, _, time, pc⟩ := facts.resources.1
  have sourceFits := incoming.mono smaller
  have targetFits := outgoing.mono smaller
  rw [← context.source.resources_realize] at sourceFits
  rw [← context.target.resources_realize] at targetFits
  have path := trace_iff_executionPath.mp facts.path
  have charges := HostReceiptProfile.resourceFacts path facts.handlers sourceFits (facts.ticks.trans smaller.2.1)
  refine ⟨⟨⟨⟨valid, path⟩, facts.encoded, ?_, sourceFits, targetFits, time, pc⟩, facts.releaseLinks⟩,
    committed, facts.commitments⟩
  intro kind
  by_cases peak : kind = .boundaryBytes
  · subst kind
    obtain ⟨_, _, _, _, growth⟩ := facts.prefix_boundary_growth valid events.length
    simp only [List.take_length] at growth
    have ordinary := List.countP_le_length (p := ExecutionEvent.isOrdinary) (l := events)
    have count := facts.count
    exact growth.trans (by change _ ≤ (ResourceLimits.native SP1Prime).boundaryBytes; omega)
  · exact (charges.native_bounds kind peak).1

/-- Soundness for arbitrary durations in the same native domain whenever the public incoming
payload and elapsed clock fit together. This sufficient endpoint check does not inspect a tape. -/
theorem native_soundnessTarget_of_boundary_budget (context : Context)
    (native : context.limits = ResourceLimits.native SP1Prime)
    (budget : context.source.resources .boundaryBytes + (context.target.clock - context.source.clock) ≤
      context.limits.boundaryBytes) :
    Soundness.Shard.SoundnessTarget (assembly context) context.limits context.commitments
      context.image context.source context.target := by
  intro header heights _ accepted
  obtain ⟨valid, _, _, committed, events, facts⟩ := execution_of_statement context accepted
  refine ⟨events, Soundness.Shard.interpretation_iff.mpr ⟨header_of_statement context accepted, ?_⟩⟩
  rw [native] at budget ⊢
  exact native_release_of_budget facts valid committed.1 (native ▸ ResourceLimits.LE.refl _) budget

/-- Raw acceptance at the fixed-provider preset yields a complete release execution at the
broader native limits for every duration. The preset itself covers the peak-payload budget. -/
theorem fixedProvider_native_soundnessTarget (context : Context) (fixed : context.limits = fixedProviderPreset) :
    Soundness.Shard.SoundnessTarget (assembly context) (ResourceLimits.native SP1Prime) context.commitments
      context.image context.source context.target := by
  intro header heights _ accepted
  obtain ⟨valid, _, _, committed, events, facts⟩ := execution_of_statement context accepted
  refine ⟨events, Soundness.Shard.interpretation_iff.mpr ⟨header_of_statement context accepted, ?_⟩⟩
  apply native_release_of_budget facts valid committed.1 (fixed ▸ fixedProviderPreset_le_native)
  have payload := facts.resources.1.1 .boundaryBytes
  have ticks := facts.resources.1.2.2.2.1
  rw [fixed] at payload ticks
  exact (Nat.add_le_add payload ticks).trans (by decide)

end SP1Clean.Export.InstalledAssembly
