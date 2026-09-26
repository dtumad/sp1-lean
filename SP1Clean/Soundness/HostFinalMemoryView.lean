import SP1Clean.Soundness.HostFinalMemoryByte
import SP1Clean.Soundness.FinalMemoryCheckSoundness

/-! # The installed Memory boundary as a physical proof view

The five tables below are selected from the actual host witness. They reuse the existing
boundary assembly, contracts and decoder. Byte guarantees are inherited from the enclosing
ledger; this smaller view need not have balanced Byte or Memory channels.
-/

namespace SP1Clean.Soundness.HostFinalMemory

open Circuit Air.Flat Channels Model.Core

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

variable {image : ProgramImage} {source : ExecutionSnapshot} {target : MemorySnapshot}
  {final : HostHintQueue.State (ZMod p)} {bankFinal : HostState}
  {others : List (HostLocalHandoff.Receiver (p := p))} {resources : List (Component (ZMod p))}
  {channels : List (RawChannel (ZMod p))}

/-- The original three final tables and two target consumers, without reconstructed rows. -/
def boundaryTables
    (witness : EnsembleWitness (ensemble image source target final bankFinal others resources channels)) :=
  [(finalSlot ⟨0, by decide⟩).table witness, (finalSlot ⟨1, by decide⟩).table witness,
   (finalSlot ⟨2, by decide⟩).table witness,
   (checkSlot ⟨0, by decide⟩).table witness, (checkSlot ⟨1, by decide⟩).table witness]

/-- Every boundary table is an unchanged physical table of the complete host assembly. -/
theorem boundaryTables_subset
    (witness : EnsembleWitness (ensemble image source target final bankFinal others resources channels)) :
    boundaryTables witness ⊆ witness.tables := by
  intro table member
  simp only [boundaryTables, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl <;> exact TableSlot.table_mem _ witness

/-- Reuse the boundary theorem's assembly as a proof view of the five registered tables. -/
def boundaryWitness
    (witness : EnsembleWitness (ensemble image source target final bankFinal others resources channels)) :
    EnsembleWitness (FinalMemoryChecks.ensemble (p := p) source.sail.memorySnapshot target [] []) :=
  EnsembleWitness.ofTables _ (boundaryTables witness) witness.data () (by
    simp only [boundaryTables, List.map_cons, List.map_nil, TableSlot.table_component]
    rfl) (fun table member => witness.same_data table (boundaryTables_subset witness member))

/-- The proof view retains the original shared fixed-lookup environment. -/
@[simp] theorem boundaryWitness_data
    (witness : EnsembleWitness (ensemble image source target final bankFinal others resources channels)) :
    (boundaryWitness witness).data = witness.data := rfl

/-- Decode the installed final inventory through the existing ordered boundary decoder. -/
def finalRecords
    (witness : EnsembleWitness (ensemble image source target final bankFinal others resources channels)) :
    List (MemoryMsg (ZMod p)) := FinalMemoryChecks.records (boundaryWitness witness)

/-- The proof view owns no independently supplied rows. -/
@[simp] theorem boundaryWitness_tables
    (witness : EnsembleWitness (ensemble image source target final bankFinal others resources channels)) :
    (boundaryWitness witness).tables = boundaryTables witness := rfl

private theorem boundary_verifier_constraints (data : ProverData (ZMod p)) :
    (FinalMemoryChecks.ensemble source.sail.memorySnapshot target [] []).VerifierConstraints () data := by
  rw [FinalMemoryChecks.ensemble, ClosedVerifier.verifier_constraints]
  constructor
  · change ((OrderedBoundaryVerifier.main OrderedFinalProvider.channelName
      OrderedMemoryEnsemble.startKey OrderedMemoryEnsemble.endKey ()).operations 0).ConstraintsHold _
    simp [OrderedBoundaryVerifier.main, Operations.ConstraintsHold, circuit_norm]
  · exact FinalMemoryChangeBoundary.closed_constraints source.sail.memorySnapshot target data

/-- Raw host acceptance supplies every local assertion and fixed lookup in the boundary view. -/
theorem boundaryWitness_constraints
    (witness : EnsembleWitness (ensemble image source target final bankFinal others resources channels))
    (checked : witness.Constraints) : (boundaryWitness witness).Constraints := by
  rw [EnsembleWitness.Constraints, EnsembleWitness.forall_mem_allTables_iff]
  constructor
  · rw [← EnsembleWitness.verifierConstraints_iff_verifierTable_constraints]
    exact boundary_verifier_constraints witness.data
  · intro table member
    exact checked table (witness.mem_allTables_of_mem_tables (boundaryTables_subset witness member))

/-- Byte facts are restricted from the full ledger, without asserting balance of this view. -/
theorem boundaryWitness_byte
    (witness : EnsembleWitness (ensemble image source target final bankFinal others resources channels))
    (guarantees : ∀ table ∈ witness.allTables, table.ChannelGuarantees byteChannel.toRaw) :
    ∀ table ∈ (boundaryWitness witness).allTables, table.ChannelGuarantees byteChannel.toRaw := by
  rw [EnsembleWitness.forall_mem_allTables_iff]
  constructor
  · rw [Table.channelGuarantees_iff_forall]
    intro interaction present
    have silent : (boundaryWitness witness).verifierTable.interactionsWith byteChannel.toRaw = [] := by
      rw [FinalMemoryChecks.verifier_values _ _ (by
        simp [byteChannel, OrderedBoundary.channel, OrderedFinalProvider.channelName, Channel.toRaw])]
      simp [byteChannel, FinalMemoryChange.channel, Channel.toRaw]
    rw [silent] at present
    contradiction
  · intro table member
    exact guarantees table (witness.mem_allTables_of_mem_tables (boundaryTables_subset witness member))

end SP1Clean.Soundness.HostFinalMemory
