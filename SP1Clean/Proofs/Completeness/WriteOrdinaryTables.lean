import SP1Clean.Proofs.Completeness.MixedInstructionTables
import SP1Clean.Soundness.WriteOrdinarySources

/-! # Physical WRITE sources on the compiled ordinary instruction block

Every released mixed path constructs the 25 predecessor-emitting tables on the same canonical
data as the original ordinary compiler. Their heights and original physical ledgers are exact.
-/

namespace SP1Clean.TraceGen

open Air.Flat Circuit Semantics Machine FormalModel.Shard Soundness WriteProbe

local notation "Fp" => ZMod SP1Prime

/-- Any verifier public input and every instruction family get the original canonical row arrays
with positive WRITE sources authenticated by genuine same-row Memory pulls. -/
theorem releaseAdmissibleExecution_writeOrdinary {limits : ResourceLimits}
    {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (execution : ReleaseAdmissibleExecution limits SP1Prime image source target events) :
    ∃ (rows : List RoutedEvent) (physical : InstructionChipId → Table Fp),
      routeObservations? (policy SP1Prime image) image.program AccessFrontier.initial source.realize events = some rows ∧
      rows.length = events.countP ExecutionEvent.isOrdinary ∧
      (InstructionChipId.all.map (fun id => (physical id).length)).sum ≤ 2 * rows.length ∧
      ∀ (publicInput : Array Fp) (id : InstructionChipId),
        ∃ original result : Table Fp,
          result.component = OrdinarySources.component id ∧ result.table = (physical id).table ∧
          result.data = deriveProverData (InstructionChipId.all.map physical) publicInput ∧ result.Constraints ∧
          result.length = WitnessGeneration.demandHeight (EventBuckets.ofChronological rows id).length ∧
          (result.interactionsWith readbackChannel.toRaw).length = result.length * OrdinarySources.accessCount (p := SP1Prime) id ∧
          result.Authenticates readbackChannel (OrdinarySources.FromPull id original) ∧
          original.table = result.table ∧ original.data = result.data ∧
          ∀ channel, channel ≠ readbackChannel.toRaw → result.interactionsWith channel = (physical id).interactionsWith channel := by
  obtain ⟨rows, physical, routed, counted, capacity, compiled, canonical⟩ := releaseAdmissibleExecution_instructionTables execution
  refine ⟨rows, physical, routed, counted, capacity, fun input id => ?_⟩
  obtain ⟨_, inBlock⟩ := canonical input
  obtain ⟨original, _, registered, same, data, checked, _, ledger⟩ := inBlock id
  let result := OrdinarySources.publish id original registered
  have height : original.length = WitnessGeneration.demandHeight (EventBuckets.ofChronological rows id).length :=
    (congrArg List.length same).trans (compiled id).height
  exact ⟨original, result, rfl, same, data, (OrdinarySources.publish_constraints id original registered).mpr checked,
    height, OrdinarySources.publication_count id original registered, OrdinarySources.publish_authenticates id original registered,
    rfl, rfl, fun channel other => (OrdinarySources.publish_interactions id original registered channel other).trans (ledger channel)⟩

end SP1Clean.TraceGen
