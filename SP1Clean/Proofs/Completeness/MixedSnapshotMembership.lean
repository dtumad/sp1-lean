import SP1Clean.Proofs.Completeness.WriteSparseInitializers
import SP1Clean.Proofs.Completeness.SnapshotReadDirections
import ToClean.Air.StaticMembershipReaders

/-! # Funding the original source register and RAM membership providers

The sparse Memory compiler emits the real ordered initializer tables. Their physical positive
membership pulls determine the counts at each verifier-fixed register or interval index.
-/

namespace SP1Clean.WriteProbe.SparseBoundary
open Circuit Air.Flat Semantics Soundness TraceGen FormalModel.Shard SnapshotReadDirections

private abbrev F := ZMod SP1Prime

/-- The actual verifier-fixed payload type for one of the two source address spaces. -/
def MembershipRow (ram : Bool) : TypeMap := if ram then MemoryIntervalRow else RegisterSnapshotRow

instance (ram : Bool) : ProvableType (MembershipRow ram) := by
  cases ram <;> dsimp [MembershipRow] <;> infer_instance

/-- The component's fixed source inventory with its own private membership channel. -/
def members (snapshot : MemorySnapshot) (ram : Bool) : StaticTable F (MembershipRow ram) :=
  match ram with
  | false => snapshot.registerTable
  | true => InitialMemoryLookup.membership snapshot.memory (2^48) "sp1.native.initial_memory"

theorem members_fit (snapshot : MemorySnapshot) (ram : Bool) : (members snapshot ram).height < UInt64.size := by
  cases ram
  · exact SnapshotRegisterProvider.membership_height_lt_uint64 snapshot
  · exact InitialMemoryLookup.membership_height_lt_uint64 snapshot.memory _

private theorem member_name (snapshot : MemorySnapshot) (ram : Bool) :
    (members snapshot ram).channel.toRaw.name = (if ram then "sp1.native.initial_memory" else "sp1.native.source_registers") := by
  cases ram
  · simp only [members, MemorySnapshot.registerTable, StaticTable.channel, Channel.toRaw_name, StaticTable.ofRows, Bool.false_eq_true, ↓reduceIte]
  · rfl

private theorem reads (snapshot : MemorySnapshot) (ram : Bool) :
    ∀ a ∈ (source (p := SP1Prime) snapshot ram).operations.interactionsWith (members snapshot ram).channel.toRaw, a.direction = .pull := by
  classical
  have notByte : (members snapshot ram).channel.toRaw ≠ (Channels.byteChannel (p := SP1Prime)).toRaw := by
    intro same
    cases ram
    · exact (by decide : "sp1.native.source_registers" ≠ "SP1Byte") ((member_name snapshot _).symm.trans (congrArg RawChannel.name same))
    · exact (by decide : "sp1.native.initial_memory" ≠ "SP1Byte") ((member_name snapshot _).symm.trans (congrArg RawChannel.name same))
  have notOrder : (members snapshot ram).channel.toRaw ≠ (OrderedBoundary.channel (p := SP1Prime) SnapshotMemoryEnsemble.channelName).toRaw := by
    intro same
    cases ram
    · exact (by decide : "sp1.native.source_registers" ≠ "SP1NativeMemoryInitOrder") ((member_name snapshot _).symm.trans (congrArg RawChannel.name same))
    · exact (by decide : "sp1.native.initial_memory" ≠ "SP1NativeMemoryInitOrder") ((member_name snapshot _).symm.trans (congrArg RawChannel.name same))
  intro a used
  cases ram <;>
    simp only [source, Bool.false_eq_true, ↓reduceIte, SnapshotMemoryEnsemble.registerView, SnapshotMemoryEnsemble.ramView,
      OrderedMemoryEnsemble.providerView, Component.interactionsWith_eq, Component.rowOperations, OrderedMemoryProvider.circuit,
      Guarded.circuit] at used <;>
    rw [Guarded.main_interactionsWith] at used <;>
    simp only [OrderedMemoryProvider.activeCircuit] at used <;>
    rw [OrderedMemoryProvider.main_provider_interactions _ _ _ notByte notOrder] at used <;>
    simp only [List.mem_map] at used
  all_goals obtain ⟨x, present, rfl⟩ := used
  · obtain ⟨raw, same⟩ := List.mem_filter.mp present
    have all (i : Var SnapshotRegisterProvider.Inputs F) (n : ℕ) :
        ((SnapshotRegisterProvider.main snapshot i).operations n).interactions.all
          (fun a => a.direction == .pull || a.channel.name == "SP1Memory") = true := by rfl
    have checked := List.all_eq_true.mp (all _ _) x raw
    have ch : x.channel = (members snapshot false).channel.toRaw := of_decide_eq_true same
    rw [ch, member_name] at checked
    change (x.direction == .pull || "sp1.native.source_registers" == "SP1Memory") = true at checked
    simpa [AbstractInteraction.guard] using checked
  · obtain ⟨raw, same⟩ := List.mem_filter.mp present
    have all (i : Var Word F) (n : ℕ) : ((SnapshotRamProvider.main snapshot i).operations n).interactions.all (allowed false) = true := by
      have addr (i : Var AddressOperation.Inputs F) (n : ℕ) : ((AddressOperation.circuit.main i).operations n).interactions.all (allowed false) = true :=
        otherChannels false AddressOperation.circuit.base (by rfl) i n
      have word (i : Var Word F) (n : ℕ) : ((InitialMemoryRead.main snapshot.memory i).operations n).interactions.all (allowed false) = true :=
        wordAllowed false snapshot.memory i n
      simp only [SnapshotRamProvider.main, circuit_norm, GeneralFormalCircuit.toSubcircuit_interactions, InitialMemoryRead.circuit,
        InitialMemoryRead.circuitNamed, List.all_append, addr, word]
      rfl
    have checked := List.all_eq_true.mp (all _ _) x raw
    have ch : x.channel = (members snapshot true).channel.toRaw := of_decide_eq_true same
    change x.direction = .pull
    change (x.direction == .pull || x.channel.name != "sp1.native.initial_memory") = true at checked
    rw [ch,member_name] at checked
    simpa using checked

/-- For the actual initializer's ordered signed ledger, all physical preallocated membership
counts, original row checks and weighted balance are obtained from the generated Memory history. -/
theorem initial_memberships (snapshot : MemorySnapshot) (stream : List MemoryHistoryAccess) (requested : List Nat)
    (guest : MemoryAddressesInLayout stream) (data : ProverData F) (hint : ProverHint F) (ram : Bool) :
    let rows := terminals snapshot stream requested data hint
    let client := initialTable snapshot ram rows data (terminal_count_fit ram snapshot stream requested guest.canonical data hint)
    let fixed := members snapshot ram
    ∃ ids, fixed.readers? (client.interactionsWith fixed.channel.toRaw) = some ids ∧
      let physical := fixed.buildMembership (members_fit snapshot ram) (fun i => ((ReaderCounts.counts ids)[i] : F)) data
      physical.Constraints ∧ physical.Guarantees ∧ physical.length = fixed.height ∧
        LogUpBalanced (physical.interactionsWith fixed.channel.toRaw ++ client.interactionsWith fixed.channel.toRaw) := by
  intro rows client fixed
  have checked := compiled_boundaries_valid snapshot stream requested guest data hint ram
  apply fixed.fromClient _ client _ ⟨checked.1,checked.2.1⟩ _ data
  · cases ram <;> intro i h <;> exact fun _ => trivial
  · cases ram <;> exact reads snapshot _

end SP1Clean.WriteProbe.SparseBoundary
