import SP1Clean.Export.WritePublicByteDemand
import SP1Clean.Export.OrdinaryRowCapacity
import SP1Clean.Export.WriteMixedSourceTables

/-! # Byte reader provenance outside the supervisor's provider window -/

namespace SP1Clean.Export.WriteByteConsumers
open Circuit Air.Flat Semantics Soundness Machine TraceGen FormalModel.Shard Channels
open WriteProbe.AccessInventory WriteSourceRegistry ByteProviderDemand
private abbrev F := ZMod SP1Prime

/-- Every live site is a genuine read of a complete, publishable native Byte message.
Disabled physical sites retain their position without acquiring a payload obligation. -/
def Reads (ledger : List (Interaction F)) : Prop :=
  ∀ i ∈ ledger, i.direction = .pull ∧ (i.mult ≠ 0 → ByteServable (messageKey i.msg))

/-- The signed reader contract of a physical table follows from its own local requirements,
generated row guarantees and the directions in its registered circuit. -/
theorem of_table (table : Table F) (requirements : table.ChannelRequirements byteChannel.toRaw)
    (guarantees : table.Guarantees)
    (directions : ∀ a ∈ table.component.operations.interactionsWith byteChannel.toRaw, a.direction = .pull) :
    Reads (table.interactionsWith byteChannel.toRaw) := by
  intro i seen
  have onByte := table.channel_eq_of_mem_interactionsWith seen
  have pull : i.direction = .pull := by
    obtain ⟨row,_,paid⟩ := List.mem_flatMap.mp seen
    obtain ⟨a,listed,rfl⟩ := List.mem_map.mp paid
    exact directions a listed
  have guar := (table.channelGuarantees_iff_forall byteChannel.toRaw).mp (table.channelGuarantees_of_requirements guarantees) i seen
  exact ⟨pull,checked_reader onByte pull table.data ((table.channelRequirements_iff_forall _).mp requirements i seen) guar⟩

/-- The old supervisor provides Boolean reader activity from the real table constraints.
The generated row guarantees then justify each active field payload. -/
theorem checked_table {image : ProgramImage} {source target : ExecutionSnapshot} {finish : HostHintQueue.State F}
    (table : Table F) (registered : table.component ∈ (base image source target finish).tables)
    (valid : table.Constraints ∧ table.Guarantees)
    (directions : ∀ a ∈ table.component.operations.interactionsWith byteChannel.toRaw, a.direction = .pull) :
    Reads (table.interactionsWith byteChannel.toRaw) := by
  apply of_table table _ valid.2 directions
  exact fun row inside => HostObserved.component_byte_requirements table.component registered (table.environment row) (valid.1 row inside)

/-- Every real or padded original instruction table supplies its own Byte reader contract on
the native compiler output, including all four protected stores. -/
theorem ordinary {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (release : ReleaseAdmissibleExecution (.native SP1Prime) SP1Prime image source target events)
    {rows : List MixedCompiledRow} (routed : routeMixedRows? (policy SP1Prime image) image.program AccessFrontier.initial source.realize events = some rows)
    (finish : HostHintQueue.State F) (data : ProverData F) (hint : ProverHint F) (id : InstructionChipId) :
    let t := WriteMixedSourceTables.table rows _ (WriteMixedSourceTables.heights release routed) data hint (.ordinary id)
      (by change 6 ≤ 7 + _; omega)
    Reads (t.interactionsWith byteChannel.toRaw) := by
  intro t
  have same : t.component = ProtectedOrdinaryReceipt.component id := rfl
  have registered : t.component ∈ (base image source target finish).tables := by
    rw [same]
    exact List.mem_of_getElem? (original_at image source target finish (.ordinary id))
  apply checked_table t registered (WriteMixedSourceTables.valid release routed data hint (.ordinary id) _)
  rw [same]
  exact fun _ used => InstalledAssembly.ordinary_byte_direction id used

end SP1Clean.Export.WriteByteConsumers
