import SP1Clean.Export.WriteInstalledHostExit
import SP1Clean.Export.WriteMixedExitLedger

/-! # Both native exit channels and the physical control-call receivers

The CPU exit-code channel links the header to all ECALL charges. The host terminal
channel separately closes the transition from a running host to its first exit. They
share the same padded mixed-execution witness and the same original CPU table.
-/

namespace SP1Clean.Export.WriteObservationAssembly

open Circuit Air.Flat Semantics Machine TraceGen FormalModel.Shard WriteMixedSourceTables

private abbrev F := ZMod SP1Prime
variable {image : ProgramImage} {source target : ExecutionSnapshot} {finish : HostHintQueue.State F}

/-- Physical control evidence from the original ECALL, HALT and shared ENTER/VERIFY rows. -/
structure ControlLedgers (full : EnsembleWitness (assembly image source target finish))
    (header : SP1PublicIO F) (events : List ExecutionEvent) (rows : List MixedCompiledRow) : Prop where
  /-- Physical CPU selection and both installed receiver tables. -/
  calls : ControlReceipts full events
  /-- The whole terminal channel contains one verifier occurrence and one site per HALT row. -/
  terminal : CheckedLedger (full.interactionsWith HostExitBoundary.channel.toRaw) (1 + (ControlHandlers.haltRows events).length)
  /-- The public exit-code bus closes for the exit value at the authenticated endpoints. -/
  exitCode : header.exit_code = (((SP1StateBoundary.haltCode source target).getD 0).toNat : F) →
    CheckedLedger (full.interactionsWith Channels.exitChannel.toRaw) (WriteMixedExitLedger.occurrences source target rows)

variable {events : List ExecutionEvent}
    (run : ReleaseAdmissibleExecution (.native SP1Prime) SP1Prime image source target events) {rows : List MixedCompiledRow}
    (routed : routeMixedRows? (policy SP1Prime image) image.program AccessFrontier.initial source.realize events = some rows)
    (data : ProverData F) (hint : ProverHint F) (packets : List WriteObservations.Packet) (header : SP1PublicIO F)
    (remaining : WriteMixedControlTables.Remaining image source target finish)
    (suffix : List (Table F)) (reg : suffix.map Table.component = tables source target)

/-- The public verifier and both original receivers use the rows of this mixed execution. -/
theorem installed_control_ledgers {limits : ResourceLimits}
    (execution : AdmissibleExecution limits SP1Prime image source target events)
    (preset : limits.LE InstalledAssembly.fixedProviderPreset) :
    let fixed := WriteMixedControlTables.install run routed data remaining
    let host := WriteMixedFixedResources.install run routed data hint packets fixed
    let w := ofExecution run routed finish data hint header (WriteMixedHostTables.install run.1 data host) packets
    ControlLedgers (withPublicChecks (build w suffix reg)) header events rows :=
  ⟨installed_control_receipts run routed data hint packets header remaining suffix reg,
    installed_host_exit run routed data hint packets header remaining suffix reg,
    fun correct => WriteMixedExitLedger.checked run routed data hint packets header remaining suffix reg correct execution preset⟩

end SP1Clean.Export.WriteObservationAssembly
