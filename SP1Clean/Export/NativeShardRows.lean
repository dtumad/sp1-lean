import SP1Clean.Export.NativeShardCommitments
import SP1Clean.Export.WriteByteProviderInstallation
import SP1Clean.Export.WriteByteConsumers

/-! # Installing the physical Byte tally into the public mixed-execution shard

The twenty-three original providers are constructed at their original positions from the
typed reads. The full observer and declaration source then share the public header and one
canonical prover data store. Balancing the Byte channel additionally requires identifying
this tally with the complete verifier, supervisor and observer demand.
-/

namespace SP1Clean.Export.NativeShard

open Circuit Air.Flat Machine Semantics TraceGen Soundness FormalModel.Shard
open WriteObservationAssembly WriteSourceRegistry
private abbrev F := ZMod SP1Prime

variable {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : ReleaseAdmissibleExecution (.native SP1Prime) SP1Prime image source target events)
    {rows : List MixedCompiledRow}
    (routed : routeMixedRows? (policy SP1Prime image) image.program AccessFrontier.initial source.realize events = some rows)
    (final : HostHintQueue.State F) (data : ProverData F) (hint : ProverHint F)
    (header : SP1PublicIO F) (packets : List WriteObservations.Packet)
    (reads : List (Interaction F)) (typed : WriteByteConsumers.Reads reads)

/-- Use the counted reader support for precisely the 23 Byte slots of the original supervisor. -/
noncomputable def supervisorFromReads : EnsembleWitness (base image source target final) :=
  let bank := WriteByteProviderInstallation.ofReaders image source target final data reads (fun i h => (typed i h).2)
  let controls := WriteMixedControlTables.install run routed data bank
  let fixed := WriteMixedFixedResources.install run routed data hint packets controls
  WriteMixedSourceTables.ofExecution run routed final data hint header (WriteMixedHostTables.install run.1 data fixed) packets

theorem supervisorFromReads_header : (supervisorFromReads run routed final data hint header packets reads typed).publicInput = header := by
  unfold supervisorFromReads
  apply WriteMixedSourceTables.ofExecution_publicInput

/-- All original supervisor constraints follow from the generators, including the installed
release Byte components. Both disabled and repeated reader occurrences enter their tally. -/
theorem supervisorFromReads_constraints : (supervisorFromReads run routed final data hint header packets reads typed).Constraints := by
  unfold supervisorFromReads
  apply WriteMixedHostTables.supervisor_constraints data run routed header hint packets
  apply WriteMixedFixedResources.install_valid run routed data hint packets
  apply WriteMixedControlTables.install_valid run routed data
  intro i a h f n
  exact WriteByteProviderInstallation.remaining_valid image source target final _ _ _ data i a h f n

variable {ctx : InstalledAssembly.Context}

/-- With the generated observer suffix and the original reader tally installed, every
physical row satisfies its circuit constraints at the canonical public header. -/
theorem compiled_row_constraints
    (execution : ReleaseStatementExecution ctx.limits SP1Prime ctx.commitments ctx.image ctx.source ctx.target events)
    (preset : ctx.limits.LE (.native SP1Prime)) {rows : List MixedCompiledRow}
    (routed : routeMixedRows? (policy SP1Prime ctx.image) ctx.image.program AccessFrontier.initial ctx.source.realize events = some rows)
    (data : ProverData F) (hint : ProverHint F) (packets : List WriteObservations.Packet)
    (reads : List (Interaction F)) (typed : WriteByteConsumers.Reads reads)
    (suffix : List (Table F)) (registered : suffix.map Table.component = tables ctx.source ctx.target)
    (checked : ∀ t ∈ suffix, t.Constraints) :
    let run : ReleaseAdmissibleExecution (.native SP1Prime) SP1Prime ctx.image ctx.source ctx.target events :=
      ⟨execution.1.1.mono preset, execution.1.2⟩
    let last := SP1Clean.HostHintQueueBoundary.initial (p := SP1Prime) ctx.target.host.io.hints
    let original := supervisorFromReads run routed last data hint ctx.header packets reads typed
    let observer := withPublicChecks (build original suffix registered)
    let full := statementWitness (ctx := ctx) execution observer data
    full.publicInput = ctx.header ∧ full.Constraints := by
  intro run last original observer full
  constructor
  · exact (statementWitness_header (ctx := ctx) execution observer data).trans
      ((withPublicChecks_publicInput (build original suffix registered)).trans ((build_publicInput original suffix registered).trans
        (supervisorFromReads_header run routed last data hint ctx.header packets reads typed)))
  · apply statementWitness_constraints
    exact build_constraints original suffix registered
      (supervisorFromReads_constraints run routed last data hint ctx.header packets reads typed) checked

end SP1Clean.Export.NativeShard
