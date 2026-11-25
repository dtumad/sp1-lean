import SP1Clean.Export.WriteObservationBuild
import SP1Clean.Proofs.Completeness.WriteCountedCost
import ToClean.Air.AppendedAuthentication
import ToClean.Air.SelectedFootprint

/-! # Paying for native WRITE supply from the installed supervisor's Memory ledger

Every registered publisher decorates a distinct original table. The whole predecessor
inventory, with its padding and repeated pulls, therefore fits inside the original Memory
occurrence count. Only active records incur supply rows, independently of probe fan-out.
-/

namespace SP1Clean.Export.WriteSourceRegistry

open Circuit Air.Flat Semantics Channels WriteProbe AccessInventory

private abbrev F := ZMod SP1Prime

variable {image : ProgramImage} {source target : ExecutionSnapshot} {final : HostHintQueue.State F}

attribute [local irreducible] base

/-- Distinct registered slots pay for all source occurrences, including aliasing and
disabled rows, in the original supervisor's full signed Memory ledger. -/
theorem records_le_memory (w : EnsembleWitness (base image source target final)) :
    (records (raw w)).length ≤ (w.interactionsWith memoryChannel.toRaw).length := by
  let index (id : Source) : Fin w.tables.length :=
    ⟨(originalSlot image source target final id).index.val, by rw [← w.same_length]; exact (originalSlot image source target final id).index.isLt⟩
  let cost := fun t : Table F => t.length * t.component.channelWidth memoryChannel.toRaw
  have slot (id : Source) : w.tables[(index id).val] = raw w id := rfl
  have unique : (sources.map index).Nodup := by
    apply List.Nodup.of_map Fin.val
    simpa only [List.map_map, Function.comp_def, index, originalSlot_index] using distinct
  have sum := w.selected_table_cost_le (sources.map index) unique memoryChannel.toRaw
  rw [← w.channelOccurrences_eq_length]
  apply (records_le_source_memory (raw w) (raw_registered w)).trans
  change (sources.map (fun id => cost (raw w id))).sum ≤ _
  simpa only [List.map_map,Function.comp_def,slot,cost] using sum

/-- The real supplier always fits the row-index type when the original supervisor passed its own
physical capacity check. The bound also accounts for canonical power-of-two padding. -/
theorem supply_fits (w : EnsembleWitness (base image source target final)) (fit : w.InteractionsFit .logUp)
    (requests : List (Counted.Request (Counted.live (records (raw w))).length F)) :
    WitnessGeneration.demandHeight (Counted.allocated (Counted.live (records (raw w))) requests).length ≤ 2 ^ 31 := by
  have originalBound : (w.interactionsWith memoryChannel.toRaw).length < SP1Prime := by
    by_cases registered : memoryChannel.toRaw ∈ (base image source target final).channels
    · have bound := w.channelCapacity_of_interactionsFit fit _ registered
      rwa [w.channelOccurrences_eq_length, ZMod.ringChar_zmod_n] at bound
    · rw [w.interactionsWith_nil_of_not_registered _ registered]
      decide
  have available := (records_le_memory w).trans_lt originalBound
  have live : (Counted.live (records (raw w))).length ≤ (records (raw w)).length := by
    simpa only [Counted.live, List.length_map] using (List.length_filter_le (fun r : F × Readback F => r.1 = 1) (records (raw w)))
  apply WitnessGeneration.demandHeight_le_pow
  simp only [Counted.allocated, List.length_ofFn]
  exact live.trans (available.le.trans (by decide))

end SP1Clean.Export.WriteSourceRegistry
