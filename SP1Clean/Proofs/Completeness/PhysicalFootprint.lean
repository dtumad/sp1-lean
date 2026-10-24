module

public import SP1Clean.Proofs.Completeness.Assembly
public import ToClean.Air.Footprint
public import SP1Clean.Model.Core.ResourceLimits

/-! # Exact construction costs of the retained native compiler

The existing semantic event buckets and provider occurrence lists determine every physical height.
The Halt table has its required padding row; SyscallInstrs is empty only in this legacy ordinary
constructor. Actual circuit interaction widths then give an exact cost for every channel. This
equivalence replaces hand-picked channel counts, without promoting a sufficient estimate to an
acceptance condition. The mixed A4/A5/A6 construction must supply its own full inventory.
-/

@[expose] public section

namespace SP1Clean.Soundness.SupportedCoreTraceWitness
open Air.Flat TraceGen Model.Core

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
variable (trace : SupportedCoreTraceWitness p)

/-- Every instruction bucket builds exactly one row per event, with no hidden padding. -/
theorem instructionTableFor_length (id : InstructionChipId) :
    (trace.instructionTableFor id).length = (trace.instructionEvents id).length := by
  simp only [instructionTableFor, Table.build_length, instructionInputsFor_length]

/-- Provider demand, including all refresh/boundary occurrences, gives the exact built height. -/
theorem providerTableFor_length (id : ProviderTableId) :
    (trace.providerTableFor id).length = trace.providerHeight id := by
  simp only [providerTableFor, Table.build_length, providerInputsFor_length]

/-- Exact physical heights from event/occurrence inputs. The public verifier allocates no table. -/
def physicalHeights : List ℕ :=
  InstructionChipId.all.map (fun id => (trace.instructionEvents id).length) ++
    ProviderTableId.all.map trace.providerHeight

/-- Exact channel demand, including every actual public-verifier interaction and physical row. -/
noncomputable def channelDemand (channel : RawChannel (ZMod p)) : ℕ :=
  ((sp1Ensemble (p := p)).verifierOperations.interactionsWith channel).length +
    (InstructionChipId.all.map fun id =>
      (trace.instructionEvents id).length * (supportedChipFor (p := p) id).table.channelWidth channel).sum +
    (ProviderTableId.all.map fun id =>
      trace.providerHeight id * (Soundness.providerTableFor (p := p) id).channelWidth channel).sum

/-- Constructing row cells leaves the event-derived physical heights unchanged. -/
theorem physicalHeights_eq : trace.physicalHeights = trace.witness.tableHeights := by
  have preserved : (withDerivedData trace.tables).map Table.length = trace.tables.map Table.length := by
    simp only [withDerivedData, List.map_map, Function.comp_def, Table.length]
  rw [EnsembleWitness.tableHeights_eq, witness_tables, preserved]
  simp only [tables, instructionTables, providerTables, List.map_append, List.map_map, Function.comp_def, physicalHeights,
    instructionTableFor_length, providerTableFor_length]

/-- Construction costs are exactly the complete ledger lengths, for every raw channel. -/
theorem channelDemand_eq (channel : RawChannel (ZMod p)) :
    trace.channelDemand channel = trace.witness.channelOccurrences channel := by
  have preserved :
      (withDerivedData trace.tables).map (fun table => table.length * table.component.channelWidth channel) =
        trace.tables.map (fun table => table.length * table.component.channelWidth channel) := by
    simp only [withDerivedData, List.map_map, Function.comp_def, Table.length]
  rw [EnsembleWitness.channelOccurrences_eq, witness_tables, preserved]
  simp only [tables, instructionTables, providerTables, List.map_append,
    List.map_map, Function.comp_def, List.sum_append, instructionTableFor_length, providerTableFor_length,
    instructionTableFor_component, providerTableFor_component, channelDemand, Nat.add_assoc]

/-- Exact arithmetic admission of the existing constructor: this is an iff, not a conservative bound.
The event/provider lists already include the compiler's canonical provider closure and refreshes. -/
theorem physicalFits_iff (limits : ResourceLimits) :
    trace.witness.PhysicalFits limits.tableRows limits.channelOccurrences ↔
      (∀ height ∈ trace.physicalHeights, height ≤ limits.tableRows) ∧
        ∀ channel ∈ (sp1Ensemble (p := p)).channels, trace.channelDemand channel ≤ limits.channelOccurrences := by
  simp only [EnsembleWitness.PhysicalFits, physicalHeights_eq, channelDemand_eq]

/-- The exact construction demand is equivalent to the migrated all-channel capacity boundary. -/
theorem channelCapacity_iff : trace.witness.ChannelCapacity p ↔
    ∀ channel ∈ (sp1Ensemble (p := p)).channels, trace.channelDemand channel < p := by
  simp only [EnsembleWitness.ChannelCapacity, channelDemand_eq]

end SP1Clean.Soundness.SupportedCoreTraceWitness
