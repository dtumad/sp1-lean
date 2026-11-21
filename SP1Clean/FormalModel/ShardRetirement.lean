import SP1Clean.FormalModel.ShardNextPC
import SP1Clean.FormalModel.ShardDynamic

/-! # Ordinary retirement and interrupt bookkeeping along the complete local tape

Official retirement supplies the ordinary effects and the concrete host adapter frames them.
These folds also cover inhibited counting, 64-bit wraparound and local paths with no retirements.
-/

namespace SP1Clean.FormalModel.Shard.Executes
open Semantics Machine Soundness.Target LeanRV64D

private theorem bookkeeping_at {p : ℕ} {image : ProgramImage}
    {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (execution : Executes p image source target events)
    {cut : ℕ} {current next : ExecutionState} {e : ExecutionEvent} (present : events[cut]? = some e)
    (atCut : executionTrajectory (policy p image) image.program source.realize events cut = some current)
    (ran : replayStep? (policy p image) image.program current e = some next) :
    retirementObservation next.sail = retirementTick (retirementObservation current.sail) e.isOrdinary ∧
      platformObservation next.sail = platformTick (platformObservation current.sail) e.isOrdinary := by
  obtain ⟨s, t, reached, step⟩ := execution.2.step_at present
  obtain rfl := Option.some.inj (atCut.symm.trans reached)
  obtain rfl := Option.some.inj (ran.symm.trans step.replay)
  cases e with
  | ordinary =>
    have frame := execution.frame_prefix atCut
    have effects : OrdinaryBookkeeping current.sail next.sail := by
      cases step with
      | ordinary _ _ normal permission => exact (Advance.ordinary_normal_bookkeeping frame.1 frame.2.1 permission normal).2
    exact ⟨Prod.ext effects.enabled (Prod.ext effects.flag effects.counter),
      Prod.ext effects.refresh (Prod.ext effects.interrupts effects.eventIndex)⟩
  | syscall call =>
    cases step with
    | syscall success =>
      obtain ⟨pc, exec, _, _, _, _, moved, _⟩ := HostState.step_observations success
      exact moved ▸ ⟨exec.retirement_observation current.sail pc, exec.platform_observation current.sail pc⟩

/-- The actual complete execution satisfies every dynamic register equation used by the physical
Sail endpoint, with no additional resource, compiler or host-profile assumptions. -/
theorem dynamicMatch {p : ℕ} {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (execution : Executes p image source target events) : DynamicMatch source target events := by
  have replay : replayEvents? (policy p image) image.program source.realize (events.map id) = some target.realize := by
    simpa only [List.map_id] using execution.2.replay
  have retirement := replayEvents?_fold id (fun s => retirementObservation s.sail)
    (fun values e => retirementTick values e.isOrdinary) replay (fun _ _ _ _ listed reached ran =>
      (bookkeeping_at execution listed (by simpa only [List.map_id, executionTrajectory] using reached) ran).1)
  have platform := replayEvents?_fold id (fun s => platformObservation s.sail)
    (fun values e => platformTick values e.isOrdinary) replay (fun _ _ _ _ listed reached ran =>
      (bookkeeping_at execution listed (by simpa only [List.map_id, executionTrajectory] using reached) ran).2)
  rw [retirementTick_fold] at retirement
  rw [platformTick_fold] at platform
  exact ⟨execution.nextPC, (Prod.mk.inj (Prod.mk.inj retirement).2).1, (Prod.mk.inj (Prod.mk.inj retirement).2).2,
    (Prod.mk.inj (Prod.mk.inj platform).2).1, (Prod.mk.inj (Prod.mk.inj platform).2).2⟩

end SP1Clean.FormalModel.Shard.Executes
