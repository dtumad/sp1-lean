import SP1Clean.Proofs.Completeness.MixedCommitHistory
import ToClean.Air.GuardedDemandTable

/-! # Physical commitment tables for a mixed native execution

The original eight lane components consume the selected inputs of their bank. Each bank uses the
real target words and the clock of its last update in its single physical terminal row.
-/

namespace SP1Clean.TraceGen.CommitBanks

open Circuit Air.Flat Machine Semantics Soundness FormalModel.Shard HostCommitChip
open WitnessGeneration

private abbrev F := ZMod SP1Prime

/-- Stable projection of the chronological stream onto the original lane. -/
def lane (slot : Fin 8) (rows : List Entry) : List (Inputs F) :=
  rows.filterMap fun entry => if entry.1 = slot then some entry.2 else none

theorem lane_mem (slot : Fin 8) (rows : List Entry) (input : Inputs F) :
    input ∈ lane slot rows ↔ (slot,input) ∈ rows := by
  constructor
  · intro seen
    obtain ⟨⟨i,r⟩, member, picked⟩ := List.mem_filterMap.mp seen
    dsimp only at picked
    split at picked
    · cases ‹i = slot›; cases picked; exact member
    · cases picked
  · intro seen
    exact List.mem_filterMap.mpr ⟨_, seen, ite_eq_left rfl⟩

/-- Normal Clean witness generation on the selected lane, including its inactive padding. -/
def laneTable (deferred : Bool) (slot : Fin 8) (rows : List Entry) (data : ProverData F)
    (fits : demandHeight (lane slot rows).length ≤ UInt64.size) : Table F :=
  Table.ofInputs (HostCommitHistory.view deferred slot).component (guardedRows (lane slot rows)) data
    ((guardedRows_length _).trans_le fits) (fun _ => trivial)

theorem laneTable_valid (deferred : Bool) (slot : Fin 8) (rows : List Entry) (data : ProverData F) (fits)
    (valid : ∀ r ∈ rows, ProverAssumptions deferred r.1 r.2) :
    (laneTable deferred slot rows data fits).Constraints ∧ (laneTable deferred slot rows data fits).Guarantees := by
  apply Table.ofInputs_valid
  exact guardedRows_all _ (fun input member => valid (slot,input) ((lane_mem ..).mp member))

/-- The bank terminal retains the private timestamp of its actual last update. -/
def terminalTable (deferred : Bool) (last : State F) (data : ProverData F) : Table F :=
  Table.ofInputs (HostCommitBank.terminalView deferred).component [last] data
    (by decide : 1 ≤ UInt64.size) (fun _ => trivial)

theorem terminalTable_valid (deferred : Bool) (last : State F) (data : ProverData F)
    (valid : HostCommitBoundary.TerminalSpec last) :
    (terminalTable deferred last data).Constraints ∧ (terminalTable deferred last data).Guarantees := by
  apply Table.ofInputs_valid
  intro i mem
  obtain rfl := List.mem_singleton.mp mem
  exact valid

/-- The per-lane physical heights are bounded by the original execution clock. -/
theorem lane_fits {limits : ResourceLimits} {image : ProgramImage} {source target : ExecutionSnapshot}
    {events : List ExecutionEvent} (run : AdmissibleExecution limits SP1Prime image source target events)
    (deferred : Bool) {rows : List Entry} (handoff : rows.map (fun r => r.2.call) = (calls deferred events).map message) (slot : Fin 8) :
    demandHeight (lane slot rows).length ≤ UInt64.size := by
  have size : rows.length = (calls deferred events).length := by simpa only [List.length_map] using congrArg List.length handoff
  have selected : (calls deferred events).length ≤ events.length := List.length_filterMap_le ..
  have assigned : (lane slot rows).length ≤ rows.length := List.length_filterMap_le ..
  have ticks := run.1.clock
  have count := event_count_le_ticks events
  have endBound : target.clock < 2 ^ 48 := run.2.2.2.2.2.1
  have upper := (demandHeight_bounds (lane slot rows).length).2
  change _ ≤ 2 ^ 64
  omega

/-- Both physical forms of an original bank component. -/
def bankTable (deferred : Bool) (rows : List Entry) (last : State F) (data : ProverData F)
    (fits : ∀ slot, demandHeight (lane slot rows).length ≤ UInt64.size) : HostCommitBank.Index → Table F
  | some slot => laneTable deferred slot rows data (fits slot)
  | none => terminalTable deferred last data

theorem bankTable_component (deferred : Bool) (rows : List Entry) (last : State F) (data : ProverData F) (fits)
    (index : HostCommitBank.Index) :
    (bankTable deferred rows last data fits index).component = (HostCommitBank.view deferred index).component := by
  cases index <;> rfl

/-- A real execution constructs all sixteen original receiver tables and both terminal tables.
Every lane has its own actual height and its original scheduler. -/
theorem physical_banks {limits : ResourceLimits} {image : ProgramImage} {source target : ExecutionSnapshot}
    {events : List ExecutionEvent} (run : AdmissibleExecution limits SP1Prime image source target events) (data : ProverData F)
    (deferred : Bool) :
    let selected := calls deferred events
    let clock := selected.foldl (fun _ c => c.clock) 0
    let last := stateAt clock (target.host.bank deferred)
    ∃ rows, rows? deferred 0 (source.host.bank deferred) selected = some rows ∧
      ∃ fits, (∀ index, let t := bankTable deferred rows last data fits index; t.Constraints ∧ t.Guarantees) ∧
        rows.map (fun row => row.2.call) = selected.map message ∧
        HostCommitBoundary.start (HostCommitEnsemble.sourceValues deferred source.host) :: rows.map (fun r => r.2.next r.1) =
          rows.map (fun row => row.2.previous) ++ [last] := by
  intro selected clock last
  obtain ⟨rows, built, valid, handoff, terminal, chain⟩ := of_execution run deferred
  refine ⟨rows, built, lane_fits run deferred handoff, ?_, handoff, chain⟩
  intro index
  cases index with
  | none => exact terminalTable_valid _ _ _ terminal
  | some slot => exact laneTable_valid deferred slot rows data (lane_fits run deferred handoff slot) valid

end SP1Clean.TraceGen.CommitBanks
