import SP1Clean.Export.WriteInstalledControlReceipts

/-! # The native host terminal receipt on the whole public witness

The original HALT receiver at slot 64 supplies the sole physical table publication. The
verifier checks the optional incoming-to-outgoing exit change, with one disabled occurrence
when the endpoint was already stopped or remains running.
-/
namespace SP1Clean.Export.WriteObservationAssembly
open Circuit Air.Flat Semantics Soundness Machine TraceGen FormalModel.Shard WriteSourceRegistry WriteMixedSourceTables

private abbrev F := ZMod SP1Prime
private abbrev bus := (HostExitBoundary.channel (p := SP1Prime)).toRaw
variable {image : ProgramImage} {source target : ExecutionSnapshot} {finish : HostHintQueue.State F}

attribute [local irreducible] withSources preprocessing ofExecution

private theorem raw_halt (pre : EnsembleWitness (preprocessing image source target finish)) :
    (pre.interactionsWith bus).Perm ((hintHostTable pre 1).interactionsWith bus ++
      [HostExitBoundary.channel.pulledIfValue (if source.host.exitCode = none ∧ target.host.exitCode.isSome then 1 else 0)
        (HostExitBoundary.encode (target.host.exitCode.getD 0))]) := by
  let orig : EnsembleWitness (HostObserved.ensemble image source target finish) := supervisor pre
  let memory := HostObserved.baseWitness orig
  let boundary := HostFinalMemory.baseWitness memory
  let host := hostWitness orig
  have regs : bus ∈ HostLocalCore.registry image source
      (HintReadWordChip.stateChannel.toRaw :: HostFinalMemory.sourceChannels (p := SP1Prime) target.sail.memorySnapshot) := by
    simp [HostLocalCore.registry, HostFinalMemory.sourceChannels]
  have different {ch : RawChannel F} (h : (ch.name == bus.name) = false) : bus ≠ ch :=
    fun eq => by rw [← eq,beq_self_eq_true] at h; contradiction
  have mem := HostFinalMemory.baseWitness_silent_interactions memory bus (List.mem_append_left _ (List.mem_append_left _ regs))
    (different rfl) (different rfl) (different rfl)
  have obs := HostObserved.baseWitness_interactions orig bus
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ regs))) (different rfl) (different rfl)
  have projected := HostHintQueueBoundary.interactions_split boundary bus (List.mem_append_left _ regs)
  have core := HostLocalCore.interactions_split_new host bus regs (LocalCore.not_mem_baseEnsemble_channels (by
    simp [LocalCore.baseChannelNames,HostExitBoundary.channel,Channel.toRaw])) (different rfl)
    (by simp [bus,HostExitBoundary.channel,StaticTable.channel,ProgramImage.writePermissionTable,StaticTable.ofRows,Channel.toRaw])
  have silent : (HostLocalCore.hostCallTable host).interactionsWith bus = [] := by
    apply Table.interactionsWith_nil_of_channel_not_mem
    rw [HostLocalCore.hostCallTable_component]
    intro used
    have present := List.contains_iff_mem.mpr (List.mem_map_of_mem (f := RawChannel.name) used)
    change false = true at present
    exact Bool.noConfusion present
  rw [unchanged_ledger pre bus (different rfl) (of_decide_eq_true rfl)]
  change (orig.interactionsWith bus).Perm _
  rw [← obs,← mem]
  apply projected.trans
  change ((host.interactionsWith bus) ++ _).Perm _
  rw [core,silent,List.nil_append,halt_auxiliary pre,ClosedVerifier.interactionsWith,ClosedVerifier.operations,
    HostBoundary.closed_main,HostBoundary.terminal_values]

variable {events : List ExecutionEvent} (run : ReleaseAdmissibleExecution (.native SP1Prime) SP1Prime image source target events)
    {rows : List MixedCompiledRow}
    (routed : routeMixedRows? (policy SP1Prime image) image.program AccessFrontier.initial source.realize events = some rows)
    (data : ProverData F) (hint : ProverHint F) (packets : List WriteObservations.Packet) (header : SP1PublicIO F)
    (remaining : WriteMixedControlTables.Remaining image source target finish)
    (suffix : List (Table F)) (reg : suffix.map Table.component = tables source target)

/-- Every physical host-exit site on the full public witness is funded by the execution,
including the disabled pull of an empty or already stopped segment. -/
theorem installed_host_exit :
    let fixed := WriteMixedControlTables.install run routed data remaining
    let host := WriteMixedFixedResources.install run routed data hint packets fixed
    let prior := WriteMixedHostTables.install run.1 data host
    let w := ofExecution run routed finish data hint header prior packets
    CheckedLedger ((withPublicChecks (build w suffix reg)).interactionsWith bus) (1 + (ControlHandlers.haltRows events).length) := by
  intro fixed host prior w
  let pre := build w suffix reg
  let h := ControlHandlers.haltTable run.1 data
  have raw := raw_halt pre
  have cells := Option.some.inj ((built_hint_host_rows w suffix reg 1).symm.trans
    (WriteMixedControlTables.original_arrays run routed data hint packets header remaining .halt))
  have rows : (hintHostTable pre 1).interactionsWith bus = h.interactionsWith bus :=
    Table.interactionsWith_eq_of_rows _ _ _ cells (congrArg (fun (c : Component F) => c.operations.interactionsWith bus)
      (show (hintHostTable pre 1).component = h.component from hintHostTable_component pre 1))
  rw [rows] at raw
  have registered : bus ∈ (preprocessing image source target finish).channels := by
    obtain ⟨t,here,ct,_⟩ := WriteMixedControlTables.installed_at run routed data hint packets header remaining suffix reg .halt
    apply (preprocessing image source target finish).tables_channels _ (EnsembleWitness.component_mem_tables_of_mem (List.mem_of_getElem? here))
    rw [ct]
    change bus ∈ (HostHaltChip.circuit (p := SP1Prime)).channels
    simp [HostHaltChip.circuit, circuit_norm]
  rw [withPublicChecks_ledger pre bus registered (by decide)]
  have used := ControlHandlers.terminal_closed run.1 data pre.data.publicEnvironment 0
  simp only [HostExitBoundary.values] at used
  have count := raw.length_eq
  rw [show h.interactionsWith bus = _ from (ControlHandlers.halt_ledgers run.1 data).2,
    List.length_append,List.length_map,List.length_map,List.length_singleton,Nat.add_comm] at count
  refine ⟨count,?_,?_,?_⟩
  · intro msg
    rw [balanceOf_perm raw]
    exact used.2.1 msg
  · rw [raw.length_eq]
    exact used.2.2.1
  · exact BalancedInteractions.of_perm used.2.2.2 raw.symm

end SP1Clean.Export.WriteObservationAssembly
