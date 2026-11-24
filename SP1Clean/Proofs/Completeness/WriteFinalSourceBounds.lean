import SP1Clean.Proofs.Completeness.WriteSparseFinalizers
import SP1Clean.Proofs.Completeness.MixedMemoryValues

/-! # Clock bounds of all generated register and RAM finalizer receipts

Every unit row in either original provider decodes a real terminal. Occupied locations use the
last post in the mixed Memory history. A sparse row uses its genuine zero-clock incoming record.
-/

namespace SP1Clean.TraceGen.MixedMemoryHistory

open Circuit Air.Flat Semantics Soundness Machine FormalModel.Shard

/-- Every physical access post lies within the genuine released 48-bit execution clock space. -/
theorem posted_clock_bound {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (ResourceLimits.native SP1Prime) SP1Prime image source target events)
    {rows : List MixedCompiledRow}
    (routed : routeMixedRows? (policy SP1Prime image) image.program AccessFrontier.initial source.realize events = some rows)
    {a : MemoryHistoryAccess} (used : a ∈ stream image source events rows) : a.current < 2 ^ 48 := by
  obtain ⟨i, _, member⟩ := List.mem_flatMap.mp used
  obtain ⟨before, next, _, following, _, window⟩ := batch_values run routed i
  obtain ⟨actual, made, size⟩ := admissibleExecution_routeMixedRows run
  have length : rows.length = events.length := Option.some.inj (routed.symm.trans made) ▸ size
  have terminal : executionTrajectory (policy SP1Prime image) image.program source.realize events events.length = some target.realize := by
    simpa only [executionTrajectory, List.take_length] using run.1.2.replay
  have endClock := cut_clock_mono (Nat.succ_le_of_lt (i.isLt.trans_eq length)) following terminal
  exact ((window a member).2.trans endClock).trans_lt run.2.2.2.2.2.1

end SP1Clean.TraceGen.MixedMemoryHistory

namespace SP1Clean.WriteProbe.SparseBoundary

open Circuit Air.Flat Semantics Soundness TraceGen Channels AccessInventory

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
local instance finalSourceClockBound : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance finalSourceLimbBound : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

private theorem final_bounded (m : MemoryMsg (ZMod p))
    (high : m.clk_high.val < 2 ^ 24) (low : m.clk_low.val < 2 ^ 24) : Counted.Bounded (finalReadback m) := by
  have max : (16777215 : ZMod p).val = 16777215 := ZMod.val_natCast_of_lt (Nat.lt_trans (by decide : (16777215 : ℕ) < 2 ^ 25) (Fact.out (p := 2 ^ 25 < p)))
  have small : (16777215 : ZMod p).val < 2 ^ 24 := max.trans_lt (by decide)
  exact ⟨high, low, small, small⟩

/-- Every honest terminal has a bounded original predecessor time and the native maximum upper
clock, including a sparse authenticated genesis row and the last post of an occupied location. -/
theorem terminal_bounded (snapshot : MemorySnapshot) (stream : List MemoryHistoryAccess) (requested : List ℕ)
    (posted : ∀ a ∈ stream, a.current < 2 ^ 48) (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p))
    {r : Terminal (ZMod p)} (member : r ∈ terminals snapshot stream requested data hint) :
    Counted.Bounded (finalReadback r.record) := by
  obtain occupied | sparse := List.mem_append.mp (List.mem_mergeSort.mp member)
  · obtain ⟨entry, inside, rfl⟩ := List.mem_map.mp occupied
    obtain ⟨history, listed, rfl⟩ := List.mem_map.mp inside
    obtain ⟨item, _, rfl⟩ := List.mem_map.mp listed
    have member := List.getLast_mem (memoryHistoryAt_ne_nil_of_mem item.2)
    have small := posted _ (List.mem_filter.mp member).1
    have cast (n : ℕ) (bound : n < 2 ^ 24) : (n : ZMod p).val < 2 ^ 24 :=
      (ZMod.val_natCast_of_lt (bound.trans (Fact.out (p := 2 ^ 24 < p)))).trans_lt bound
    apply final_bounded
    · apply cast
      exact (Nat.div_lt_iff_lt_mul (by decide : 0 < 2 ^ 24)).mpr small
    · exact cast _ (Nat.mod_lt _ (by decide))
  · obtain ⟨row, inside, rfl⟩ := List.mem_map.mp sparse
    obtain ⟨i, fresh, made⟩ := (mem_buildAll_iff ..).mp inside
    obtain ⟨other, also, _, checked⟩ := build?_checked snapshot _ requested i fresh data hint
    obtain rfl := Option.some.inj (also.symm.trans made)
    let record := sourceRecord snapshot other.ram (Environment.fromArray other.initial data)
    have genesis : record.clk_high.val * 2 ^ 24 + record.clk_low.val = 0 := checked.2.2.1.1.2.2.1
    exact final_bounded record (by omega) (by omega)

/-- Conversely, every unit read-back on an actual constructed finalizer is one of its typed
terminal payloads. Inspecting the decoded guard excludes its zero rows. -/
theorem finalTable_bounded (ram : Bool) (rows : List (Terminal (ZMod p)))
    (ordered : rows.Pairwise (fun a b => a.key < b.key))
    (bounded : ∀ r ∈ rows, Counted.Bounded (finalReadback r.record)) (data evaluation : ProverData (ZMod p)) (fit)
    {cells : Array (ZMod p)} (present : cells ∈ (finalTable ram rows data fit).table) {r : Readback (ZMod p)}
    (unit : (1,r) ∈ rowRecords (.finalizer ram) (Environment.fromArray cells evaluation)) : Counted.Bounded r := by
  let c := originalFinal (p := p) ram
  let inputs := WitnessGeneration.guardedRows (F := ZMod p) (finalInputs ram 0 rows)
  obtain ⟨input, used, rfl⟩ := List.mem_map.mp present
  let env := Environment.fromArray (c.buildRow input (c.inputData inputs data) (.empty _)) evaluation
  have read : valueFromOffset (OrderedMemoryProvider.RowInput MemoryMsg) 0 env = input := c.rowInput_buildRow ..
  change (1,r) ∈ [((valueFromOffset (OrderedMemoryProvider.RowInput MemoryMsg) 0 env).2, finalReadback (finalRecordAt ram env))] at unit
  have payload : finalRecordAt ram env = input.1.payload := (finalRecordAt_eq ram env).trans
    (congrArg (fun i : OrderedMemoryProvider.RowInput MemoryMsg (ZMod p) => i.1.payload) read)
  simp only [List.mem_singleton, Prod.mk.injEq, read, payload] at unit
  have active := WitnessGeneration.guardedRows_all (F := ZMod p) (fun i => Counted.Bounded (finalReadback (F := ZMod p) i.payload))
    (inputs := finalInputs ram 0 rows) (orderedInputs_all ram _ rows 0 _ ordered (fun _ _ => Nat.zero_lt_succ _) (fun t mem _ _ _ => bounded t mem)) input used
  rw [unit.2]
  exact active.2 unit.1.symm

end SP1Clean.WriteProbe.SparseBoundary
