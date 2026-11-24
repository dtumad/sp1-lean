import SP1Clean.Proofs.Completeness.WriteDispatchRows
import ToClean.Air.TableBuild

/-! # Sealing the chronological WRITE cursor at the actual outgoing CPU clock -/

namespace SP1Clean.WriteEffects

open Air.Flat Circuit Semantics Machine FormalModel.Shard
private abbrev F := ZMod SP1Prime

/-- The singleton carries the most recent WRITE successor clock, starting at the
source clock if the segment has no WRITE. The gap covers all intervening CPU steps. -/
def closeInput (source target : ExecutionSnapshot) (events : List ExecutionEvent) : CloseInput F :=
  let last := events.foldl advanceWriteClock source.clock
  ⟨1,1,Address.ofNat last,Address.ofNat (target.clock - last)⟩

private theorem close_cells {T : Type} (r : CloseInput T) :
    (toElements r).toList = r.ticket :: r.count :: (r.prior.toList ++ r.gap.toList) := by
  simp only [toElements, ProvableStruct.structToElements_eq, ProvableStruct.toComponents,Vector.toList_cast]
  simp only [components,ProvableStruct.componentsToElements,Vector.toList_append,toElements_field,ProvableType.toElements_fields]
  change [r.ticket] ++ ([r.count] ++ (r.prior.toList ++ (r.gap.toList ++ []))) = _
  rw [List.append_nil]
  rfl

private theorem close_fixed (source target : ExecutionSnapshot) (events : List ExecutionEvent)
    (data : ProverData F) (hint : ProverHint F) :
    let c := closeComponent (p := SP1Prime) source target
    c.FixedRowsMatch ([closeInput source target events].map (c.buildRow · data hint)) := by
  intro c
  apply (c.fixedRowsMatch_buildRows _ _ _ (mode := closeGeneration) rfl).mpr
  refine ⟨rfl,?_⟩
  intro i hi
  change i < 1 at hi
  obtain rfl : i = 0 := by omega
  change (closeGeneration (p := SP1Prime)).FixedAt 0 (closeInput source target events)
  simp only [WitnessGeneration.PreallocatedMode.FixedAt,closeGeneration,Witgen.M.pure_def,close_cells,
    Vector.toList_ofFn,List.ofFn_succ,List.cons_append]
  repeat' apply List.Forall₂.cons
  all_goals first | rfl | trivial

/-- The original preallocated close table with its fixed ticket and the chronological clock gap. -/
def closeTable (source target : ExecutionSnapshot) (events : List ExecutionEvent) (data : ProverData F) : Table F :=
  let c := closeComponent (p := SP1Prime) source target
  let rows : List (c.Input F) := [closeInput source target events]
  let own := c.inputData rows data
  Table.build c rows own (.empty _) (by change 1 ≤ UInt64.size; decide)
    (close_fixed source target events own _) (c.inputData_consistent rows data)

/-- The replayed mixed tape supplies every local clock and multiplicity obligation of the terminal. -/
theorem closeTable_valid {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events) (data : ProverData F) :
    (closeTable source target events data).Constraints ∧ (closeTable source target events data).Guarantees := by
  let last := events.foldl advanceWriteClock source.clock
  have ordered : last ≤ target.clock := dispatch_clock_le run.1.2 source.clock (by rfl)
  have bounded := run.2.2.2.2.2.1
  change target.clock < 2^48 at bounded
  have gap : last + (target.clock-last) = target.clock := by omega
  have sum := AddressSum.spec_ofNat (p := SP1Prime) last (target.clock-last) (by omega)
  rw [gap] at sum
  have valid (own : ProverData F) : ∀ r ∈ [closeInput source target events],
      (closeComponent (p := SP1Prime) source target).circuit.ProverAssumptions r own (.empty _) := by
    intro r member
    obtain rfl := List.mem_singleton.mp member
    exact ⟨rfl,rfl,sum⟩
  unfold closeTable
  exact ⟨Table.build_constraints _ _ _ _ _ _ _ (valid _),Table.build_guarantees _ _ _ _ _ _ _ (valid _)⟩

end SP1Clean.WriteEffects
