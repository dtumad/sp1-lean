import SP1Clean.Export.WriteEndpointJoins
import SP1Clean.Export.WriteHostSourceGrounding
import SP1Clean.Export.WriteMixedControlTables
import SP1Clean.Proofs.Completeness.MixedExitDemand
import SP1Clean.Soundness.HostHintReadExit

/-! # The actual public Exit pull and both original physical producers -/

namespace SP1Clean.Export.WriteMixedExitLedger
open Circuit Air.Flat Channels Semantics Soundness Machine TraceGen FormalModel.Shard WriteSourceRegistry
private abbrev F := ZMod SP1Prime
private abbrev bus := (exitChannel (p := SP1Prime)).toRaw

variable {image : ProgramImage} {source target : ExecutionSnapshot} {finish : HostHintQueue.State F}
private abbrev core (w : EnsembleWitness (HostObserved.ensemble image source target finish)) :=
  HostFinalMemory.coreWitness (HostObserved.baseWitness w)

private def haltSlot (image : ProgramImage) (source target : ExecutionSnapshot) (finish : HostHintQueue.State F) :
    TableSlot (base image source target finish).tables (HaltPaddingChip.component (p := SP1Prime)) :=
  TableSlot.ofGetElem? (halt_at image source target finish)

attribute [local irreducible] HostObserved.ensemble HostObserved.baseWitness LocalCore.ensemble

private theorem halt_rows (w : EnsembleWitness (HostObserved.ensemble image source target finish)) :
    (LocalCore.systemTable (core w) 2).table = ((haltSlot image source target finish).table w).table := by
  let hw := hostWitness w
  let middle := HostFinalMemory.baseWitness (HostObserved.baseWitness w)
  have first := HostLocalCore.localWitness_table hw ⟨57,by decide⟩ (by decide)
  have arrays := (HostHintQueueBoundary.projected_rows middle).trans ((HostFinalMemory.baseWitness_rows (HostObserved.baseWitness w)).trans (HostObserved.baseWitness_rows w))
  have total := w.same_length.symm.trans (base_length image source target finish)
  have last := List.getElem_of_eq arrays (i := 57) (by rw [arrays,List.length_map,total]; decide)
  simp only [List.getElem_map] at last
  exact first.trans last

private def haltOutput (r : HaltChip.Inputs F) : List (Interaction F) :=
  [exitChannel.pushedIfValue r.is_real (HaltChip.exitMessage r),exitChannel.pushedIfValue (1-r.is_real) ⟨0⟩]

private theorem core_ledger (w : EnsembleWitness (HostObserved.ensemble image source target finish)) :
    (core w).interactionsWith bus = w.interactionsWith bus :=
  (HostHintReadCPU.local_exit_interactions (HostFinalMemory.baseWitness (HostObserved.baseWitness w))).trans
    (host_core_ledger w bus (by simp [LocalCore.baseEnsemble,sp1Ensemble_channels]))

private theorem core_header (w : EnsembleWitness (HostObserved.ensemble image source target finish)) :
    (core w).publicInput = w.publicInput := by
  rw [core,HostFinalMemory.coreWitness,HostLocalCore.localWitness_publicInput,HostHintQueueBoundary.projected_publicInput,
    HostFinalMemory.baseWitness_publicInput,HostObserved.baseWitness_publicInput]

private theorem core_calls (w : EnsembleWitness (HostObserved.ensemble image source target finish)) :
    (LocalCore.systemTable (core w) 3).table = (raw w (.host .ecall)).table.map (·.extract 0 (HostCallProjection.original (p := SP1Prime)).width) :=
  (HostLocalCore.hostCallTable_originalRows (hostWitness w)).trans
    (congrArg (List.map (·.extract 0 (HostCallProjection.original (p := SP1Prime)).width)) (ecall_rows w))

private theorem halt_data (old fresh : ProverData F) (cells : Array F) : haltRow old cells = haltRow fresh cells := rfl

private theorem producer_values (w : EnsembleWitness (HostObserved.ensemble image source target finish)) :
    (LocalCore.exitProducers (core w)).map (fun entry => exitChannel.pushedIfValue entry.1 entry.2) =
      ((haltSlot image source target finish).table w).table.flatMap (fun cells => haltOutput (haltRow w.data cells)) ++
      (raw w (.host .ecall)).table.map (fun cells => MixedExitDemand.emit (HostCallLedger.input (Environment.fromArray cells w.data))) := by
  rw [LocalCore.exitProducers,List.map_append,halt_rows w,core_calls w,List.map_flatMap,List.map_map,List.map_map]
  simp only [List.map_cons,List.map_nil]
  apply congrArg₂ List.append
  · apply List.flatMap_congr
    intro cells _
    rw [halt_data (core w).data w.data cells]
    rfl
  · apply List.map_congr_left
    intro cells _
    exact congrArg MixedExitDemand.emit (HostCallProjection.input_prefix cells w.data (core w).data)

/-- The entire original supervisor contributes one header pull, both physical legacy HALT
gates at slot 57 and the true ECALL HALT gate at slot 58. -/
theorem supervisor (w : EnsembleWitness (HostObserved.ensemble image source target finish)) :
    w.interactionsWith bus = [exitChannel.pulledValue ⟨w.publicInput.exit_code⟩] ++
      ((haltSlot image source target finish).table w).table.flatMap (fun cells => haltOutput (haltRow w.data cells)) ++
      (raw w (.host .ecall)).table.map (fun cells => MixedExitDemand.emit (HostCallLedger.input (Environment.fromArray cells w.data))) := by
  rw [← core_ledger w,LocalCore.exit_interactions,core_header,producer_values,List.append_assoc]

open WriteMixedSourceTables WriteObservationAssembly

variable {events : List ExecutionEvent}
    (run : ReleaseAdmissibleExecution (.native SP1Prime) SP1Prime image source target events) {rows : List MixedCompiledRow}
    (routed : routeMixedRows? (policy SP1Prime image) image.program AccessFrontier.initial source.realize events = some rows)
    (data : ProverData F) (hint : ProverHint F) (packets : List WriteObservations.Packet)
    (header : SP1PublicIO F) (remaining : WriteMixedControlTables.Remaining image source target finish)
    (suffix : List (Table F)) (registered : suffix.map Table.component = tables source target)

private def ledger (source target : ExecutionSnapshot) (rows : List MixedCompiledRow) (header : SP1PublicIO F) : List (Interaction F) :=
  [exitChannel.pulledValue ⟨header.exit_code⟩] ++ (MixedHaltPadding.inputs source target).flatMap haltOutput ++
    (MixedSyscallTable.inputs rows).map MixedExitDemand.emit

/-- Exact ordered physical Exit ledger on the full public assembly, at any supplied header. -/
theorem generated :
    let fixed := WriteMixedControlTables.install run routed data remaining
    let host := WriteMixedFixedResources.install run routed data hint packets fixed
    let w := ofExecution run routed finish data hint header (WriteMixedHostTables.install run.1 data host) packets
    (withPublicChecks (build w suffix registered)).interactionsWith bus = ledger source target rows header := by
  intro fixed host w
  have original : bus ∈ (base image source target finish).channels := (base image source target finish).tables_channels _
    (List.mem_of_getElem? (halt_at image source target finish)) (by
      repeat' first | exact List.mem_cons_self | apply List.mem_cons_of_mem)
  rw [public_original_ledger w suffix registered bus original (by apply ne_of_apply_ne RawChannel.name; decide) (of_decide_eq_true rfl) (by decide)]
  have full := supervisor (image := image) (source := source) (target := target) (finish := finish) w
  change w.interactionsWith bus = _ at full
  rw [full]
  have actual := WriteMixedControlTables.original_arrays run routed data hint packets header remaining .haltPadding
  let slot := haltSlot image source target finish
  have inside : slot.index.val < w.tables.length := w.same_length ▸ slot.index.isLt
  change (w.tables.map Table.table)[slot.index.val]? = some (MixedHaltPadding.table source target data).table at actual
  rw [List.getElem?_map,List.getElem?_eq_getElem inside,Option.map_some] at actual
  have usingHalt : (slot.table w).table.map (haltRow w.data) = MixedHaltPadding.inputs source target :=
    (congrArg (List.map (haltRow w.data)) (Option.some.inj actual)).trans (MixedHaltPadding.all_inputs source target data w.data)
  have usingCall : (raw w (.host .ecall)).table.map (fun c => HostCallLedger.input (Environment.fromArray c w.data)) = MixedSyscallTable.inputs rows := by
    rw [compiledSource_rows run routed data hint packets finish header _ (.host .ecall)]
    exact MixedSyscallTable.all_inputs rows data w.data hint (heights run routed).ecall
  have boundary : w.publicInput = header := rfl
  unfold ledger
  rw [boundary,← usingHalt,← usingCall,List.flatMap_map,List.map_map]
  rfl

/-- One public pull, both gates of the optional checkpoint row, and one gate on each physical ECALL row. -/
def occurrences (source target : ExecutionSnapshot) (rows : List MixedCompiledRow) :=
  1 + 2 * (MixedHaltPadding.inputs source target).length +
    WitnessGeneration.demandHeight (rows.filterMap (MixedCompiledRow.syscallInput? (p := SP1Prime))).length

private theorem ledger_count : (ledger source target rows header).length = occurrences source target rows := by
  have heights := MixedSyscallTable.input_height rows
  have legacy : ((MixedHaltPadding.inputs source target).flatMap haltOutput).length = 2 * (MixedHaltPadding.inputs source target).length := by
    unfold MixedHaltPadding.inputs
    split <;> rfl
  simp only [ledger,occurrences,List.length_append,List.length_cons,List.length_nil,List.length_map,legacy,heights]

private theorem halt_signed (source target : ExecutionSnapshot) (msg : Array F) :
    balanceOf ((MixedHaltPadding.inputs source target).flatMap haltOutput) msg =
      balanceOf ((MixedHaltPadding.inputs source target).map (fun _ => MixedExitDemand.push 0)) msg := by
  unfold MixedHaltPadding.inputs
  split
  · simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,List.map_cons,List.map_nil,haltOutput,
      show (HaltChip.paddingInputs (p := SP1Prime)).is_real = 0 from rfl,sub_zero,balanceOf_cons]
    simp [Interaction.signedMult,Channel.pushedIfValue,MixedExitDemand.push,HaltChip.exitMessage,HaltChip.paddingInputs,Channel.pushedValue,balanceOf]
    split
    · exact ite_eq_left (by assumption)
    · exact ite_eq_right (by assumption)
  · rfl

include run routed in
private theorem ledger_signed (correct : header.exit_code = (((SP1StateBoundary.haltCode source target).getD 0).toNat : F)) :
    LogUpBalanced (ledger source target rows header) := by
  intro msg
  have normalized := congrArg (List.map MixedExitDemand.push) (MixedHaltPadding.receipt run.1.1.2)
  simp only [List.map_append,List.map_map,List.map_cons,List.map_nil,Function.comp_def] at normalized
  have paid := congrArg (fun xs => balanceOf xs msg) normalized
  rw [balanceOf_append] at paid
  simp only [ledger,balanceOf_append,halt_signed,MixedExitDemand.signed run.1 routed,add_assoc,paid]
  rw [correct]
  simp only [MixedExitDemand.push,balanceOf_cons,Channel.pulledValue,Channel.pushedValue,Interaction.signedMult,
    show balanceOf ([] : List (Interaction F)) msg = 0 from rfl,add_zero]
  split <;> simp_all

include routed in
private theorem preset_bound {limits : ResourceLimits} (execution : AdmissibleExecution limits SP1Prime image source target events)
    (preset : limits.LE InstalledAssembly.fixedProviderPreset) : occurrences source target rows < SP1Prime := by
  obtain ⟨_,found,length⟩ := admissibleExecution_routeMixedRows execution
  cases Option.some.inj (found.symm.trans routed)
  have count := execution.work.1
  have max : limits.events ≤ 2^21 := preset.1
  have physical : WitnessGeneration.demandHeight (rows.filterMap (MixedCompiledRow.syscallInput? (p := SP1Prime))).length ≤ 2^21 :=
    WitnessGeneration.demandHeight_le_pow ((List.length_filterMap_le ..).trans (by rw [length]; exact count.trans max))
  have optional : (MixedHaltPadding.inputs source target).length ≤ 1 := by unfold MixedHaltPadding.inputs; split <;> decide
  unfold occurrences
  have := pow25_lt_sp1Prime
  omega

/-- The native public assembly authenticates the header Exit field with exact physical count,
signed balance, field fit and active matching. Only the supplied header field is specialized. -/
theorem checked (correct : header.exit_code = (((SP1StateBoundary.haltCode source target).getD 0).toNat : F))
    {limits : ResourceLimits} (execution : AdmissibleExecution limits SP1Prime image source target events)
    (preset : limits.LE InstalledAssembly.fixedProviderPreset) :
    let fixed := WriteMixedControlTables.install run routed data remaining
    let host := WriteMixedFixedResources.install run routed data hint packets fixed
    let w := ofExecution run routed finish data hint header (WriteMixedHostTables.install run.1 data host) packets
    CheckedLedger ((withPublicChecks (build w suffix registered)).interactionsWith bus) (occurrences source target rows) := by
  intro fixed host w
  rw [generated run routed data hint packets header remaining suffix registered]
  have count := ledger_count (source := source) (target := target) (rows := rows) header
  have signed := ledger_signed run routed header correct
  have fit : (Balance.logUp (F := F)).fits (ledger source target rows header).length = true := by
    simp only [Balance.logUp,decide_eq_true_eq,ComputableRingChar.char_eq,ZMod.ringChar_zmod_n,count]
    exact preset_bound routed execution preset
  exact ⟨count,signed,fit,Balance.logUp.balancedInteractions_of_balanced _ fit signed⟩

/-- Every choice of commitments uses the actual public header generated from this segment.
It meets all Exit checks for the physical witness, including an empty parked checkpoint. -/
theorem public_checked (statement : CommitmentStatement)
    {limits : ResourceLimits} (execution : AdmissibleExecution limits SP1Prime image source target events)
    (preset : limits.LE InstalledAssembly.fixedProviderPreset) :
    let header := SP1StateBoundary.ofExecution (p := SP1Prime) source target statement
    let fixed := WriteMixedControlTables.install run routed data remaining
    let host := WriteMixedFixedResources.install run routed data hint packets fixed
    let w := ofExecution run routed finish data hint header (WriteMixedHostTables.install run.1 data host) packets
    CheckedLedger ((withPublicChecks (build w suffix registered)).interactionsWith bus) (occurrences source target rows) :=
  checked run routed data hint packets _ remaining suffix registered rfl execution preset

end SP1Clean.Export.WriteMixedExitLedger
