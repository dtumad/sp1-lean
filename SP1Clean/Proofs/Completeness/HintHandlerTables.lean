import SP1Clean.Proofs.Completeness.HintHandlerHistory
import SP1Clean.Proofs.Completeness.HintReadLedger
import SP1Clean.Soundness.HostHintReadLocalExecution
import ToClean.Air.GuardedLedger

/-! # Three guarded HINT headers and two transfer tables

The native tape determines each input, its route and its padding. The signed node and
word sites use the same projected queue storage and the active/disabled cells of each
original physical component.
-/

namespace SP1Clean.TraceGen.HintHandlers

open Circuit Air.Flat Semantics HintQueue Machine FormalModel.Shard Soundness HostHintQueue WitnessGeneration
private abbrev F := ZMod SP1Prime

/-- Original HINT_READ headers in tape order. -/
def readRows (rows : List Row) : List (HostHintReadChip.Inputs F) := rows.filterMap Row.read?

/-- Original HINT_LEN headers at the registered zero-head or nonzero-head table. -/
def lengthRows (empty : Bool) (rows : List Row) : List (HostHintLengthChip.Inputs F) := rows.filterMap fun
  | .length route r => if route = empty then some r else none
  | .read _ => none

variable {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
  (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events)

include run

private theorem read_height : demandHeight (readRows (history image source events)).length ≤ 2^16 :=
  demandHeight_le_pow ((List.length_filterMap_le ..).trans (history_bound run))

private theorem length_height (empty : Bool) : demandHeight (lengthRows empty (history image source events)).length ≤ 2^16 :=
  demandHeight_le_pow ((List.length_filterMap_le ..).trans (history_bound run))

private theorem transfer_height (last : Bool) :
    demandHeight (HintReadTransfers.selected last (HintReadTransfers.history image source events)).length ≤ 2^28 := by
  apply demandHeight_le_pow
  rw [HintReadTransfers.selected_length run]
  have paid := run.2.2.1 .writeBytes
  rw [HintReadDemand.writeBytes run.1.2] at paid
  change 8 * _ ≤ SP1Prime - 1 at paid
  have fieldSize : SP1Prime - 1 < 8 * 2^28 := by decide
  split <;> omega

/-- Registered HINT_READ demand table at its canonical populated height. -/
noncomputable def readTable (data : ProverData F) : Table F :=
  HostHintReadChip.tableFor (readRows (history image source events)) data ((read_height run).trans (by decide))

/-- Registered zero-head or nonzero-head HINT_LEN table. -/
noncomputable def lengthTable (empty : Bool) (data : ProverData F) : Table F :=
  HostHintLengthChip.tableFor empty (lengthRows empty (history image source events)) data ((length_height run empty).trans (by decide))

/-- One of the two registered transfer components, with all original mandatory last-word rows. -/
noncomputable def transferTable (last : Bool) (data : ProverData F) : Table F :=
  HintReadTransfers.wordTable last (HintReadTransfers.history image source events) data ((transfer_height run last).trans (by decide))

/-- All three original header tables and the two original transfer tables have valid
constraints and guarantees for these concrete generated witnesses. -/
theorem tables_checked (data : ProverData F) :
    let r := readTable run data
    r.Constraints ∧ r.Guarantees ∧
    (∀ empty, let t := lengthTable run empty data; t.Constraints ∧ t.Guarantees) ∧
    (∀ last, let t := transferTable run last data; t.Constraints ∧ t.Guarantees) := by
  obtain ⟨checked, guaranteed⟩ := HostHintReadChip.tableFor_valid (readRows (history image source events)) data
    ((read_height run).trans (by decide)) (by
      intro x hx
      obtain ⟨row, mem, routed⟩ := List.mem_filterMap.mp hx
      have ok := history_honest run row mem
      cases row with
      | length => contradiction
      | read r => exact Option.some.inj routed ▸ ok)
  refine ⟨checked, guaranteed, ?_, ?_⟩
  · intro empty
    apply HostHintLengthChip.tableFor_valid
    intro x hx
    obtain ⟨r, mem, routed⟩ := List.mem_filterMap.mp hx
    have ok := history_honest run r mem
    cases r with
    | read => contradiction
    | length tag row =>
      change (if tag = empty then some row else none) = some x at routed
      split at routed
      · rename_i same
        subst empty
        exact Option.some.inj routed ▸ ok
      · contradiction
  · intro last
    obtain ⟨_, valid⟩ := HintReadTransfers.tables_of_admissibleExecution run last data
    exact valid

/-- Exact physical heights and bounds from paid native ticks and padded HINT_READ bytes. -/
theorem tables_heights (data : ProverData F) :
    let hs := history image source events
    let ws := HintReadTransfers.history image source events
    (readTable run data).length = demandHeight (readRows hs).length ∧ (readTable run data).length ≤ 2^16 ∧
    (∀ empty, (lengthTable run empty data).length = demandHeight (lengthRows empty hs).length ∧
      (lengthTable run empty data).length ≤ 2^16) ∧
    (∀ last, (transferTable run last data).length = demandHeight (HintReadTransfers.selected last ws).length ∧
      (transferTable run last data).length ≤ 2^28) := by
  dsimp only
  have rd : (readTable run data).length = demandHeight (readRows (history image source events)).length := by
    exact (show (readTable run data).length = (guardedRows (F := F) (readRows (history image source events))).length
      from List.length_map ..).trans (guardedRows_length _)
  have ln (empty : Bool) : (lengthTable run empty data).length = demandHeight (lengthRows empty (history image source events)).length := by
    exact (show (lengthTable run empty data).length = (guardedRows (F := F) (lengthRows empty (history image source events))).length
      from List.length_map ..).trans (guardedRows_length _)
  have tr (last : Bool) := HintReadTransfers.wordTable_length last (HintReadTransfers.history image source events) data ((transfer_height run last).trans (by decide))
  exact ⟨rd, rd.le.trans (read_height run), fun e => ⟨ln e, (ln e).le.trans (length_height run e)⟩,
    fun l => ⟨tr l, (tr l).le.trans (transfer_height run l)⟩⟩

end SP1Clean.TraceGen.HintHandlers
