import SP1Clean.FormalModel.Shard
import SP1Clean.Semantics.Execution.ExecutionFrame
import SP1Clean.Semantics.Execution.ExecutionMemory

/-! # ROM preservation and official fetch for the shard's semantic domain

These are consequences of the existing `Executes` contract. Source validation and mandatory
ordinary write permission supply every premise of the mixed-path induction. No resource profile,
AIR witness or extra intermediate-state invariant is required. The final boundary may lie outside
ROM, and an empty identity, including a stopped one, needs no fetch.
-/

namespace SP1Clean.FormalModel.Shard.Executes
open Semantics Machine Soundness.Target LeanRV64D LeanRV64D.Functions

variable {characteristic : ℕ} {image : ProgramImage}
  {source target : ExecutionSnapshot} {events : List ExecutionEvent}

/-- The exact outgoing Sail state retains configuration, ROM and every protected incoming byte. -/
theorem frame (execution : Executes characteristic image source target events) :
    SailConfigured target.sail.realize ∧ RomLoaded image.program target.sail.realize ∧
      ∀ address, image.readOnly address = true →
        target.sail.realize.mem.get? address = source.sail.realize.mem.get? address := by
  obtain ⟨valid, path⟩ := execution
  rw [image.program_eq valid.1.1] at path ⊢
  exact path.frame valid.1.1 (fun _ selected => selected) valid.configured valid.romLoaded

/-- All actual prefix states, including the final and held endpoint, inherit authenticated ROM. -/
theorem frame_prefix (execution : Executes characteristic image source target events)
    {cut : ℕ} {current : ExecutionState}
    (replay : executionTrajectory (policy characteristic image) image.program
      source.realize events cut = some current) :
    SailConfigured current.sail ∧ RomLoaded image.program current.sail ∧
      ∀ address, image.readOnly address = true →
        current.sail.mem.get? address = source.sail.realize.mem.get? address := by
  obtain ⟨valid, path⟩ := execution
  rw [image.program_eq valid.1.1] at path replay ⊢
  exact path.frame_prefix valid.1.1 (fun _ selected => selected) valid.configured valid.romLoaded replay

/-- Every actual prefix has all bytes needed to materialize native RAM cells. This is derived
from complete incoming memory and actual writes, independently of final AIR grounding. -/
theorem memory_present_prefix (execution : Executes characteristic image source target events)
    {cut : ℕ} {current : ExecutionState}
    (replay : executionTrajectory (policy characteristic image) image.program
      source.realize events cut = some current)
    (address : ℕ) (inside : address < NativeLayout.sailMemory.upper) :
    (current.sail.mem.get? address).isSome := by
  obtain ⟨valid, path⟩ := execution
  rw [image.program_eq valid.1.1] at path replay
  exact path.memory_present_prefix valid.1.1 (fun _ selected => selected) valid.configured
    valid.romLoaded replay address inside

/-- Each executed position fetches its committed instruction through official Sail. The prefix
state and instruction are derived from the path, rather than supplied by a caller. -/
theorem fetch_at (execution : Executes characteristic image source target events)
    (cut : ℕ) (active : cut < events.length) :
    ∃ current pc word,
      executionTrajectory (policy characteristic image) image.program
        source.realize events cut = some current ∧
      current.sail.regs.get? Register.PC = some pc ∧ image.program.fetchWord pc = some word ∧
      (runSail (fetch ())) current.sail = .ok (FetchResult.F_Base word) current.sail := by
  obtain ⟨valid, path⟩ := execution
  rw [image.program_eq valid.1.1] at path ⊢
  exact path.fetch_at valid.1.1 (fun _ selected => selected) valid.configured valid.romLoaded cut active

end SP1Clean.FormalModel.Shard.Executes
