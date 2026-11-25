import SP1Clean.Export.NativeShardRows
import SP1Clean.Export.WriteJointObservation

/-! # Compiling the public native shard from a release execution

The generated observer rows determine the final portion of the Byte demand. The original
providers then pay the whole demand on the final witness at the canonical public header.
-/

namespace SP1Clean.Export.NativeShard

open Circuit Air.Flat Machine Semantics Soundness TraceGen FormalModel.Shard Channels
open WriteObservationAssembly WriteSourceRegistry

private abbrev F := ZMod SP1Prime
private abbrev byte := (byteChannel (p := SP1Prime)).toRaw

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
  let observed := withPublicChecks pre
  have registered := byte_registered (ctx := ctx)
  have publicByte : byte ∈ (observer ctx).channels := List.mem_append_left _ registered
  have same : w.interactionsWith byte = pre.interactionsWith byte :=
    (statementWitness_other (ctx := ctx) execution observed data byte publicByte
      (fun eq => Bool.noConfusion (congrArg (fun c => c.name == "SP1Byte") eq))).trans
      (withPublicChecks_ledger pre byte registered (of_decide_eq_true rfl))
  rw [same]
  exact WriteFundedByteProviders.full run routed (last ctx) data hint ctx.header packets limbs suffix prepared.registered prepared.byteReads

/-- Every release statement execution in the fixed-provider preset gives physical rows for all
118 tables at the public header, with all Byte requests funded. -/
theorem compiled_rows
    (execution : ReleaseStatementExecution ctx.limits SP1Prime ctx.commitments ctx.image ctx.source ctx.target events)
    (preset : ctx.limits.LE InstalledAssembly.fixedProviderPreset) :
    ∃ w : EnsembleWitness (assembly ctx), w.publicInput = ctx.header ∧ w.Constraints ∧
      LogUpBalanced (w.interactionsWith byte) := by
  let data := ProverData.empty F
  let hint := ProverHint.empty F
  obtain ⟨rows, routed, packets, _, front, _, entries, _, _, _, _, alloc, _, _, cap, _, plan, _, _, _, _, _, _, _,
    prepared, _⟩ := native_observation_allocation (ctx := ctx) execution preset data hint
  have nativeBounds := preset.trans InstalledAssembly.fixedProviderPreset_le_native
  have built := fundedWitness_rows (ctx := ctx) execution nativeBounds routed data hint packets prepared
  exact ⟨_, built.1, built.2, (fundedWitness_byte (ctx := ctx) execution nativeBounds routed data hint packets prepared).1⟩

end SP1Clean.Export.NativeShard
