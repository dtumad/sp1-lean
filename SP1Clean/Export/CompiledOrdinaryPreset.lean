import SP1Clean.Export.InstalledOrdinaryPreset
import SP1Clean.Proofs.Completeness.MixedInstructionTables

/-! # LogUp capacity at the heights of the constructed ordinary tables

The installed verifier, ten fixed providers and three HINT_READ tables share their channel
allowance with the 25 ordinary tables built from this same released execution.
-/

namespace SP1Clean.Export.InstalledAssembly
open Air.Flat Semantics Machine FormalModel.Shard TraceGen

/-- Rows charged to the named physical slots by the actual constructed table family. -/
def compiledOrdinaryHeights (physical : InstructionChipId → Table Fp) (component : Component Fp) : ℕ :=
  (InstructionChipId.all.map fun id => slotRows (physical id).component (physical id).length component).sum

/-- On the released mixed path, the 38-table preset fits the real compiler's ordinary tables at
precisely their constructed heights. Every table also retains its checks under canonicalization. -/
theorem fixedProviderPreset_compiled_ordinary_fits (ctx : Context) {events : List ExecutionEvent}
    (execution : ReleaseAdmissibleExecution ctx.limits SP1Prime ctx.image ctx.source ctx.target events)
    (preset : ctx.limits.LE fixedProviderPreset) :
    ∃ (rows : List RoutedEvent) (physical : InstructionChipId → Table Fp),
      routeObservations? (policy SP1Prime ctx.image) ctx.image.program AccessFrontier.initial ctx.source.realize events = some rows ∧
      rows.length = events.countP ExecutionEvent.isOrdinary ∧
      (∀ id, InstalledInstructionTables.Compiled id (EventBuckets.ofChronological rows id) (physical id)) ∧
      (∀ publicInput, InstalledInstructionTables.CanonicalBlock physical publicInput) ∧
      (assembly ctx).interactionsFit .logUp (physicalHeights ctx fun table =>
        fixedHeight table + hintReadHeights events table + compiledOrdinaryHeights physical table) := by
  obtain ⟨rows, physical, route, count, _, built, canonical⟩ := releaseAdmissibleExecution_instructionTables execution
  obtain ⟨same, routed, _, capacity⟩ := fixedProviderPreset_ordinary_base_fits ctx execution.1 preset
  obtain rfl := Option.some.inj (route.symm.trans routed)
  refine ⟨rows, physical, route, count, built, canonical, ?_⟩
  have heights : compiledOrdinaryHeights physical = ordinaryHeights rows := by
    funext component
    simp only [compiledOrdinaryHeights, ordinaryHeights, fun id => (built id).registered,
      fun id => (built id).height, EventBuckets.paddedHeight]
  simpa only [heights] using capacity

end SP1Clean.Export.InstalledAssembly
