import SP1Clean.Export.NativeShardRows
import SP1Clean.Export.WriteInstalledDeclarationLanes
import SP1Clean.Export.WriteJointObservation
import SP1Clean.Export.WriteSparseByteCapacity

/-! # Compiling the public native shard from a release execution

The generated observer rows determine the final portion of the Byte demand. The original
providers then pay the whole demand on the final witness at the canonical public header.
-/

namespace SP1Clean.Export.NativeShard

open Circuit Air.Flat Machine Semantics Soundness TraceGen FormalModel.Shard Channels
open WriteObservationAssembly WriteSourceRegistry

private abbrev F := ZMod SP1Prime
private abbrev byte := (byteChannel (p := SP1Prime)).toRaw
private abbrev decl := (CommitmentDeclaration.channel (p := SP1Prime)).toRaw

variable {ctx : InstalledAssembly.Context} {events : List ExecutionEvent}
    (execution : ReleaseStatementExecution ctx.limits SP1Prime ctx.commitments ctx.image ctx.source ctx.target events)
    (bounds : ctx.limits.LE (.native SP1Prime))

private abbrev release : ReleaseAdmissibleExecution (.native SP1Prime) SP1Prime ctx.image ctx.source ctx.target events :=
  ⟨execution.1.1.mono bounds, execution.1.2⟩

private abbrev last (ctx : InstalledAssembly.Context) := SP1Clean.HostHintQueueBoundary.initial (p := SP1Prime) ctx.target.host.io.hints

private theorem byte_registered : byte ∈ (preprocessing ctx.image ctx.source ctx.target (last ctx)).channels := by
  let seen := preprocessing ctx.image ctx.source ctx.target (last ctx)
  let span : TableSlot seen.tables WriteBuffer.spanComponent := slot ctx.image ctx.source ctx.target (last ctx) 3
  exact seen.tables_channels _ (span.component_eq ▸ List.getElem_mem span.index.isLt)
    (show byte ∈ WriteBuffer.spanComponent.circuit.channels from List.mem_cons_self)

private theorem statementWitness_byte (pre : EnsembleWitness (preprocessing ctx.image ctx.source ctx.target (last ctx)))
    (data : ProverData F) :
    (statementWitness (ctx := ctx) execution (withPublicChecks pre) data).interactionsWith byte = pre.interactionsWith byte := by
  have registered := byte_registered (ctx := ctx)
  have publicByte : byte ∈ (observer ctx).channels := List.mem_append_left _ registered
  exact (statementWitness_other (ctx := ctx) execution (withPublicChecks pre) data byte publicByte
    (fun eq => Bool.noConfusion (congrArg (fun c => c.name == "SP1Byte") eq))).trans
    (withPublicChecks_ledger pre byte registered (of_decide_eq_true rfl))

variable {rows : List MixedCompiledRow}
    (routed : routeMixedRows? (policy SP1Prime ctx.image) ctx.image.program AccessFrontier.initial ctx.source.realize events = some rows)
    (data : ProverData F) (hint : ProverHint F) (packets : List WriteObservations.Packet)
    {entries : List WriteEffects.Witness.Entry} {suffix : List (Table F)}
    (prepared : ObserverRows ctx.source ctx.target ctx.limits entries suffix)

include execution in
private theorem header_limbs : ctx.header.LimbBounds :=
  ((releaseStatementExecution_iff ctx.commitments).mp execution).1.headerSpecs.1

/-- Complete the original provider window using the genuine physical requests, then attach
the read-only observer, immutable declarations and public header checks. -/
noncomputable def fundedWitness : EnsembleWitness (assembly ctx) :=
  let run := release (ctx := ctx) execution bounds
  let input := WriteGeneratedByteClients.demand run routed (last ctx) data hint ctx.header packets suffix
  let typed := WriteGeneratedByteClients.reads run routed (last ctx) data hint ctx.header packets (header_limbs (ctx := ctx) execution) suffix prepared.byteReads
  let original := supervisorFromReads run routed (last ctx) data hint ctx.header packets input typed
  statementWitness (ctx := ctx) execution (withPublicChecks (build original suffix prepared.registered)) data

/-- Every generated row on the final physical witness satisfies its installed circuit. -/
theorem fundedWitness_rows :
    let w := fundedWitness (ctx := ctx) execution bounds routed data hint packets prepared
    w.publicInput = ctx.header ∧ w.Constraints :=
  compiled_row_constraints (ctx := ctx) execution bounds routed data hint packets _ _ suffix
    prepared.registered (fun t member => (prepared.checked t member).1)

/-- The signed Byte ledger on the final physical witness balances at every message.
Its size includes every physical read and each padded provider row. -/
theorem fundedWitness_byte :
    let w := fundedWitness (ctx := ctx) execution bounds routed data hint packets prepared
    let input := WriteGeneratedByteClients.demand (release (ctx := ctx) execution bounds) routed (last ctx) data hint ctx.header packets suffix
    LogUpBalanced (w.interactionsWith byte) ∧ (w.interactionsWith byte).length = input.length +
      (ByteProviderDemand.all.map fun id => WitnessGeneration.demandHeight (ByteProviderDemand.keys (ByteProviderDemand.requested input) id).length).sum := by
  intro w input
  let run := release (ctx := ctx) execution bounds
  have limbs := header_limbs (ctx := ctx) execution
  let typed := WriteGeneratedByteClients.reads run routed (last ctx) data hint ctx.header packets limbs suffix prepared.byteReads
  let original := supervisorFromReads run routed (last ctx) data hint ctx.header packets input typed
  let pre := build original suffix prepared.registered
  have same : w.interactionsWith byte = pre.interactionsWith byte := statementWitness_byte (ctx := ctx) execution pre data
  rw [same]
  exact WriteFundedByteProviders.full run routed (last ctx) data hint ctx.header packets limbs suffix prepared.registered prepared.byteReads

/-- More than 2²⁴ distinct RAM words on the generated boundary prevent this witness from
meeting the public verifier's Byte capacity, including when the signed ledger balances. -/
theorem fundedWitness_byte_overflow
    (large : 2^24 < WriteSparseByteCapacity.ramCount ctx.source (MixedMemoryHistory.stream ctx.image ctx.source events rows)
      (WriteBoundaryBuild.demandKeys events packets) data hint) :
    SP1Prime ≤ ((fundedWitness (ctx := ctx) execution bounds routed data hint packets prepared).interactionsWith byte).length := by
  let run := release (ctx := ctx) execution bounds
  let input := WriteGeneratedByteClients.demand run routed (last ctx) data hint ctx.header packets suffix
  let typed := WriteGeneratedByteClients.reads run routed (last ctx) data hint ctx.header packets (header_limbs (ctx := ctx) execution) suffix prepared.byteReads
  let bank := WriteByteProviderInstallation.ofReaders ctx.image ctx.source ctx.target (last ctx) data input (fun i m => (typed i m).2)
  unfold fundedWitness
  rw [statementWitness_byte (ctx := ctx) execution]
  exact WriteSparseByteCapacity.assembled_overflow run routed (last ctx) data hint ctx.header packets bank suffix prepared.registered large

/-- Every header fails the raw statement at these generated heights if the sparse RAM
inventory alone exceeds the field. The claim is specific to this height vector. -/
theorem no_statement_at_funded_heights
    (large : 2^24 < WriteSparseByteCapacity.ramCount ctx.source (MixedMemoryHistory.stream ctx.image ctx.source events rows)
      (WriteBoundaryBuild.demandKeys events packets) data hint) (header : SP1PublicIO F) :
    let w := fundedWitness (ctx := ctx) execution bounds routed data hint packets prepared
    ¬ (assembly ctx).Statement .logUp header w.heights := by
  intro w accepted
  have publicByte : byte ∈ (observer ctx).channels := List.mem_append_left _ (byte_registered (ctx := ctx))
  have reg : byte ∈ (assembly ctx).channels := List.mem_append_left _ (List.mem_append_left _ publicByte)
  have fits := ((w.interactionsFit_iff .logUp).mp accepted.1) byte reg
  exact (Nat.not_lt_of_ge (fundedWitness_byte_overflow (ctx := ctx) execution bounds routed data hint packets prepared large))
    (of_decide_eq_true fits)

/-- The original sixteen bank lanes supply every declaration read of the physical witness. -/
theorem fundedWitness_declarations :
    CheckedLedger ((fundedWitness (ctx := ctx) execution bounds routed data hint packets prepared).interactionsWith decl)
      (CommitmentReaders.sites execution.1.1) := by
  let run := release (ctx := ctx) execution bounds
  let input := WriteGeneratedByteClients.demand run routed (last ctx) data hint ctx.header packets suffix
  let typed := WriteGeneratedByteClients.reads run routed (last ctx) data hint ctx.header packets (header_limbs (ctx := ctx) execution) suffix prepared.byteReads
  let original := supervisorFromReads run routed (last ctx) data hint ctx.header packets input typed
  let observed := withPublicChecks (build original suffix prepared.registered)
  apply checked_of_bank_ledger (ctx := ctx) execution observed data bounds
  let bank := WriteByteProviderInstallation.ofReaders ctx.image ctx.source ctx.target (last ctx) data input (fun i m => (typed i m).2)
  let controls := WriteMixedControlTables.install run routed data bank
  let fixed := WriteMixedFixedResources.install run routed data hint packets controls
  exact List.Perm.of_eq (installed_declaration_lanes run routed data hint ctx.header fixed packets suffix prepared.registered)

/-- Every release statement execution in the fixed-provider preset gives physical rows for all
118 tables at the public header, with all Byte requests and commitment declarations funded. -/
theorem compiled_rows
    (execution : ReleaseStatementExecution ctx.limits SP1Prime ctx.commitments ctx.image ctx.source ctx.target events)
    (preset : ctx.limits.LE InstalledAssembly.fixedProviderPreset) :
    ∃ w : EnsembleWitness (assembly ctx), w.publicInput = ctx.header ∧ w.Constraints ∧
      LogUpBalanced (w.interactionsWith byte) ∧ CheckedLedger (w.interactionsWith decl) (CommitmentReaders.sites execution.1.1) := by
  let data := ProverData.empty F
  let hint := ProverHint.empty F
  obtain ⟨rows, routed, packets, _, front, _, entries, _, _, _, _, alloc, _, _, cap, _, plan, _, _, _, _, _, _, _,
    prepared, _⟩ := native_observation_allocation (ctx := ctx) execution preset data hint
  have nativeBounds := preset.trans InstalledAssembly.fixedProviderPreset_le_native
  have built := fundedWitness_rows (ctx := ctx) execution nativeBounds routed data hint packets prepared
  exact ⟨_, built.1, built.2, (fundedWitness_byte (ctx := ctx) execution nativeBounds routed data hint packets prepared).1,
    fundedWitness_declarations (ctx := ctx) execution nativeBounds routed data hint packets prepared⟩

end SP1Clean.Export.NativeShard
