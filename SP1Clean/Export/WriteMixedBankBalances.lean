import SP1Clean.Export.WriteMixedHostData
import SP1Clean.Soundness.HostHintReadBanks
import SP1Clean.Soundness.HostObservedProducers

/-! # The complete WRITE observer balances both mutable commitment-bank channels

The original host registry identifies the only nine physical participants in each bank's state
channel. Neither receipt installation nor the appended observation components alter those signed
occurrences, and the original mixed execution supplies both endpoint banks.
-/

namespace SP1Clean.Export.WriteMixedHostTables

open Circuit Air.Flat Semantics Soundness Machine TraceGen FormalModel.Shard
open WriteSourceRegistry

private abbrev F := ZMod SP1Prime

variable {image : ProgramImage} {source target : ExecutionSnapshot} {finish : HostHintQueue.State F}

private abbrev boundary (w : EnsembleWitness (base image source target finish)) :=
  HostFinalMemory.baseWitness (HostObserved.baseWitness w)

private theorem boundary_ledger (w : EnsembleWitness (base image source target finish)) (d : Bool) :
    (boundary w).interactionsWith (HostCommitChip.stateChannel d).toRaw = w.interactionsWith (HostCommitChip.stateChannel d).toRaw := by
  let ch := (HostCommitChip.stateChannel (p := SP1Prime) d).toRaw
  have reg : ch ∈ HostLocalCore.registry image source (HintReadWordChip.stateChannel.toRaw ::
      HostFinalMemory.sourceChannels (p := SP1Prime) target.sail.memorySnapshot) := by
    cases d <;> simp [ch, HostLocalCore.registry, HostFinalMemory.sourceChannels]
  have eqn := HostFinalMemory.baseWitness_silent_interactions (HostObserved.baseWitness w) ch
    (List.mem_append_left _ (List.mem_append_left _ reg))
    (by apply ne_of_apply_ne RawChannel.name; cases d <;> decide)
    (by apply ne_of_apply_ne RawChannel.name; cases d <;> decide)
    (by apply ne_of_apply_ne RawChannel.name; cases d <;> decide)
  exact eqn.trans (HostObserved.baseWitness_interactions w ch
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ reg)))
    (by apply ne_of_apply_ne RawChannel.name; cases d <;> decide)
    (by apply ne_of_apply_ne RawChannel.name; cases d <;> decide))

private theorem bank_silent (d : Bool) (suffix : List (Table F))
    (physical : suffix.map Table.component = WriteObservationAssembly.tables source target) :
    suffix.flatMap (·.interactionsWith (HostCommitChip.stateChannel d).toRaw) = [] := by
  have absent : (HostCommitChip.stateChannel (p := SP1Prime) d).name ∉
      (WriteObservationAssembly.tables source target).flatMap (fun c => c.circuit.channels.map RawChannel.name) := by
    cases d <;> exact of_decide_eq_true rfl
  apply List.flatMap_eq_nil_iff.mpr
  intro t used
  apply Table.interactionsWith_nil_of_channel_not_mem
  exact fun member => absent (List.mem_flatMap.mpr ⟨t.component, physical ▸ List.mem_map_of_mem used, List.mem_map_of_mem member⟩)

variable {events : List ExecutionEvent} (run : ReleaseAdmissibleExecution (.native SP1Prime) SP1Prime image source target events)
    {rows : List MixedCompiledRow}
    (routed : routeMixedRows? (policy SP1Prime image) image.program AccessFrontier.initial source.realize events = some rows)
    (data : ProverData F) (hint : ProverHint F) (header : SP1PublicIO F) (remaining : Remaining image source target finish)
    (packets : List WriteObservations.Packet)

/-- The physical original verifier endpoints and every installed signed occurrence close on
both mutable commitment banks for any choice of the still-open component generators. -/
theorem installed_bank_balances (suffix : List (Table F)) (physical : suffix.map Table.component = WriteObservationAssembly.tables source target)
    (d : Bool) :
    let w := WriteMixedSourceTables.ofExecution run routed finish data hint header (install run.1 data remaining) packets
    let full := WriteObservationAssembly.build w suffix physical
    LogUpBalanced (full.interactionsWith (HostCommitChip.stateChannel d).toRaw) := by
  intro w full
  let ch := (HostCommitChip.stateChannel (p := SP1Prime) d).toRaw
  change LogUpBalanced ((WriteObservationAssembly.build w suffix physical).interactionsWith ch)
  rw [WriteObservationAssembly.build_ledger,
    show suffix.flatMap (·.interactionsWith ch) = [] from bank_silent d suffix physical, List.append_nil,
    installSources_ledger w _ (by apply ne_of_apply_ne RawChannel.name; cases d <;> decide), ← boundary_ledger w d]
  have ledger := HostHintReadBanks.interactions (extra := FinalMemoryChecks.checkTables target.sail.memorySnapshot)
    (sourceNames := HostFinalMemory.source_unique_names image source target.sail.memorySnapshot) d (boundary w)
  have arrays := (HostFinalMemory.baseWitness_rows (HostObserved.baseWitness w)).trans (HostObserved.baseWitness_rows w)
  have built (idx : HostCommitBank.Index) :
      let slot := HostTableRegistry.installedBankSlot image source finish target.host (FinalMemoryChecks.checkTables target.sail.memorySnapshot)
        (HostFinalMemory.sourceChannels target.sail.memorySnapshot)
        (sourceNames := HostFinalMemory.source_unique_names image source target.sail.memorySnapshot) d idx
      (slot.table (boundary w)).interactionsWith ch = (table run.1 data (.bank d idx)).interactionsWith ch := by
    intro slot
    have whereAt : slot.index.val = position (.bank d idx) :=
      HostTableRegistry.installedBankSlot_index image source finish target.host _ _
        (sourceNames := HostFinalMemory.source_unique_names image source target.sail.memorySnapshot) d idx
    have before := original_arrays run routed data hint header remaining packets (.bank d idx)
    change (w.tables.map Table.table)[position (.bank d idx)]? = _ at before
    have actual := congrArg (fun xs : List (List (Array F)) => xs[slot.index.val]?) arrays
    change ((boundary w).tables.map Table.table)[slot.index.val]? = (w.tables.map Table.table)[slot.index.val]? at actual
    rw [whereAt, before, ← whereAt, List.getElem?_map, List.getElem?_eq_getElem (by rw [← (boundary w).same_length]; exact slot.index.isLt)] at actual
    apply Table.interactionsWith_eq_of_rows (slot.table (boundary w)) (table run.1 data (.bank d idx)) ch (Option.some.inj actual)
    exact congrArg (fun c : Component F => c.operations.interactionsWith ch)
      ((slot.table_component (boundary w)).trans (registered run.1 data (.bank d idx)).symm)
  have family : (HostHintReadBanks.bankTables d (boundary w)).flatMap (·.interactionsWith ch) =
      HostCommitBank.indices.flatMap (fun idx => (table run.1 data (.bank d idx)).interactionsWith ch) := by
    rw [HostHintReadBanks.bankTables, List.flatMap_map]
    exact List.flatMap_congr fun idx _ => built idx
  intro msg
  have fromPhysical := balanceOf_perm (message := msg) ledger
  change balanceOf _ msg = _
  rw [fromPhysical, show (HostHintReadBanks.bankTables d (boundary w)).flatMap (·.interactionsWith (HostCommitChip.stateChannel d).toRaw) = _ from family]
  exact bank_state_balanced run.1 data d msg

end SP1Clean.Export.WriteMixedHostTables
