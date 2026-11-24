import SP1Clean.Export.WriteObservationBuild
import SP1Clean.Proofs.Completeness.WriteCountedCost
import ToClean.Air.AppendedAuthentication
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Perm.Subperm
import Mathlib.Algebra.Order.BigOperators.Group.List

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

private theorem selected_cost {α : Type*} (xs : List α) (ids : List (Fin xs.length)) (unique : ids.Nodup) (cost : α → ℕ) :
    (ids.map (fun i => cost xs[i.val])).sum ≤ (xs.map cost).sum := by
  have inside : ids ⊆ List.finRange xs.length := fun i _ => List.mem_finRange i
  obtain ⟨ordered, equal, subset⟩ := unique.subperm inside
  let f := fun i : Fin xs.length => cost xs[i.val]
  have total := (subset.map f).sum_le_sum (fun _ _ => Nat.zero_le _)
  rw [(equal.map f).sum_eq, ← List.ofFn_eq_map, List.ofFn_getElem_eq_map] at total
  exact total

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
  have sum := selected_cost w.tables (sources.map index) unique cost
  have consumed : (sources.map (fun id => cost (raw w id))).sum ≤ (w.tables.map cost).sum := by
    simpa only [List.map_map, Function.comp_def, slot] using sum
  apply (records_le_source_memory (raw w) (raw_registered w)).trans
  apply consumed.trans
  rw [← w.channelOccurrences_eq_length]
  exact Nat.le_add_left _ _

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
