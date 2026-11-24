import SP1Clean.Export.InstalledHintRows
import SP1Clean.Export.ImmutableQueueFunding

/-! # Immutable node and word funding on the joint observation witness -/

namespace SP1Clean.Export.WriteObservationAssembly

open Circuit Air.Flat Semantics Soundness Machine TraceGen FormalModel.Shard WriteSourceRegistry WriteMixedSourceTables
open HostHintQueue WriteEffects.Witness

private abbrev F := ZMod SP1Prime
variable {image : ProgramImage} {source target : ExecutionSnapshot} {finish : HostHintQueue.State F}
    {events : List ExecutionEvent} (run : ReleaseAdmissibleExecution (.native SP1Prime) SP1Prime image source target events)
    {rows : List MixedCompiledRow}
    (routed : routeMixedRows? (policy SP1Prime image) image.program AccessFrontier.initial source.realize events = some rows)
    (data : ProverData F) (hint : ProverHint F) (packets : List WriteObservations.Packet) (header : SP1PublicIO F)
    (remaining : WriteMixedControlTables.Remaining image source target finish)
    (suffix : List (Table F)) (reg : suffix.map Table.component = tables source target)

attribute [local irreducible] base withSources ofExecution

private theorem host_slot_ledger (w : EnsembleWitness (base image source target finish))
    (i : Fin 35) (t : Table F) (comp : (hintHostComponents source target)[i.val] = t.component)
    (atSlot : (w.tables.map Table.table)[(63 : Nat) + i.val]? = some t.table) (ch : RawChannel F) :
    (hintHostTable (build w suffix reg) i).interactionsWith ch = t.interactionsWith ch := by
  have cells := Option.some.inj ((built_hint_host_rows w suffix reg i).symm.trans atSlot)
  exact Table.interactionsWith_eq_of_rows _ _ _ cells
    (congrArg (fun c : Component F => c.operations.interactionsWith ch) ((hintHostTable_component _ _).trans comp))

private theorem word_rows (last : Bool) :
    let fixed := WriteMixedControlTables.install run routed data remaining
    let host := WriteMixedFixedResources.install run routed data hint packets fixed
    let prior := WriteMixedHostTables.install run.1 data host
    let w := ofExecution run routed finish data hint header prior packets
    (w.tables.map Table.table)[if last then 85 else 84]? = some (HintHandlers.transferTable run.1 last data).table := by
  intro fixed host prior w
  let id := WriteProbe.AccessInventory.Source.host (.word last)
  let sl := originalSlot image source target finish id
  have h := compiledSource_rows run routed data hint packets finish header prior id
  have physical : (w.tables.map Table.table)[sl.index.val]? = some (raw w id).table := by
    rw [List.getElem?_map,List.getElem?_eq_getElem (by rw [← w.same_length]; exact sl.index.isLt)]
    rfl
  have loc : sl.index.val = (if last then 85 else 84) := by cases last <;> rfl
  rw [← loc,physical,h]
  rfl

/-- The public verifier's entire node and word ledgers coincide with the actual ten funded
tables. The original header and word readers, fixed prefix, outgoing snapshot and fresh
publishers retain their order and every inactive occurrence. -/
theorem installed_immutable_ledgers {entries : List Entry} (s : SixTables entries source.host target.host)
    (snapshotAt : suffix[10]? = some (HostHintSnapshot.tableFor (HintQueueReaders.finalCursor run.1).1 (HintQueueReaders.finalCursor run.1).2
      target.host.io.hints (InstalledAssembly.admissible_hint_snapshot_fits run.1) data))
    (nodeAt : suffix[16]? = some (s.nodes data)) (wordAt : suffix[18]? = some (s.words data)) :
    let fixed := WriteMixedControlTables.install run routed data remaining
    let host := WriteMixedFixedResources.install run routed data hint packets fixed
    let w := ofExecution run routed finish data hint header (WriteMixedHostTables.install run.1 data host) packets
    let full := withPublicChecks (build w suffix reg)
    let ts := InstalledAssembly.immutableTables run.1 data s
    full.interactionsWith nodeChannel.toRaw = ts.flatMap (·.interactionsWith nodeChannel.toRaw) ∧
    full.interactionsWith wordChannel.toRaw = ts.flatMap (·.interactionsWith wordChannel.toRaw) ∧
    let ch := (HintReadWordChip.stateChannel (p := SP1Prime)).toRaw
    full.interactionsWith ch = (HintHandlers.readTable run.1 data).interactionsWith ch ++
      (HintHandlers.transferTable run.1 false data).interactionsWith ch ++ (HintHandlers.transferTable run.1 true data).interactionsWith ch := by
  intro fixed host w full ts
  let pre := build w suffix reg
  have port (ch : RawChannel F) (which : ch = nodeChannel.toRaw ∨ ch = wordChannel.toRaw) :
      full.interactionsWith ch = pre.interactionsWith ch := by
    apply withPublicChecks_ledger _ _ (immutable_registered ch which)
    rcases which with rfl | rfl <;> decide
  have head := host_slot_ledger suffix reg w 0 (HintHandlers.readTable run.1 data) rfl
    (WriteMixedControlTables.original_arrays run routed data hint packets header remaining .hintRead)
  have len := host_slot_ledger suffix reg w 19 (HintHandlers.lengthTable run.1 false data) rfl
    (WriteMixedControlTables.original_arrays run routed data hint packets header remaining (.hintLength false))
  have fixedN := host_slot_ledger suffix reg w 23 (HintQueueReaders.fixedNodes run.1 data) rfl
    (WriteMixedFixedResources.original_arrays run routed data hint packets header fixed (.hint false))
  have fixedW := host_slot_ledger suffix reg w 24 (HintQueueReaders.fixedWords run.1 data) rfl
    (WriteMixedFixedResources.original_arrays run routed data hint packets header fixed (.hint true))
  have cont := host_slot_ledger suffix reg w 21 (HintHandlers.transferTable run.1 false data) rfl
    (word_rows run routed data hint packets header remaining false)
  have last := host_slot_ledger suffix reg w 22 (HintHandlers.transferTable run.1 true data) rfl
    (word_rows run routed data hint packets header remaining true)
  have snap := build_slot_ledger w suffix reg 10 _ snapshotAt
  have freshN := build_slot_ledger w suffix reg 16 _ nodeAt
  have freshW := build_slot_ledger w suffix reg 18 _ wordAt
  have quiet {t : Table F} {ch : RawChannel F} (absent : ch.name ∉ t.component.circuit.channels.map RawChannel.name) :
      t.interactionsWith ch = [] := t.interactionsWith_nil_of_channel_not_mem (fun mem => absent (List.mem_map_of_mem mem))
  have noWords : (s.nodes data).interactionsWith wordChannel.toRaw = [] := quiet (of_decide_eq_true rfl)
  have noNodes : (s.words data).interactionsWith nodeChannel.toRaw = [] := quiet (of_decide_eq_true rfl)
  have fixedNoWords : (HintQueueReaders.fixedNodes run.1 data).interactionsWith wordChannel.toRaw = [] := quiet (of_decide_eq_true rfl)
  have fixedNoNodes : (HintQueueReaders.fixedWords run.1 data).interactionsWith nodeChannel.toRaw = [] := quiet (of_decide_eq_true rfl)
  obtain ⟨empty, lengths, transfers⟩ := HintHandlers.silent_records run.1 data
  refine ⟨?_,?_,?_⟩
  · rw [port _ (Or.inl rfl),hintNode_ledger,original_hint_nodes]
    simp only [pre,head,len,fixedN,snap,freshN,ts,InstalledAssembly.immutableTables,HintHandlers.readerTables,
      List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,empty,transfers,fixedNoNodes,noNodes,List.nil_append,List.append_assoc]
  · rw [port _ (Or.inr rfl),hintWord_ledger,original_hint_words]
    simp only [pre,head,cont,last,fixedW,snap,freshW,ts,InstalledAssembly.immutableTables,HintHandlers.readerTables,
      List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,lengths,fixedNoWords,noWords,List.nil_append,List.append_assoc]

  · intro ch
    have old : ch ∈ (base image source target finish).channels := by
      apply (base image source target finish).tables_channels _ (List.mem_of_getElem? (WriteMixedControlTables.registered_at image source target finish .hintRead))
      change ch ∈ HostHintReadChip.component.circuit.channels
      simp [ch,HostHintReadChip.component,HostHintReadChip.guardedCircuit,Guarded.circuit,HostHintReadChip.circuit,circuit_norm]
    have present : ch ∈ (preprocessing image source target finish).channels := by
      change ch ∈ channels ++ (withSources image source target finish).channels
      rw [channels_eq]
      exact List.mem_append_right _ (List.mem_cons_of_mem _ old)
    change (withPublicChecks pre).interactionsWith ch = _
    rw [withPublicChecks_ledger pre ch present (by decide),hintCursor_ledger,original_hint_cursors]
    simp only [pre,head,cont,last,ch,List.append_assoc]

end SP1Clean.Export.WriteObservationAssembly
