import SP1Clean.Model.Machine.EventExecution
import SP1Clean.Model.Semantics.MicroTime

/-! # The transcript timeline

The timed grounding engine reads a shard through two functions of a step index `n`: the machine
state after `n` steps and the bus clock at which step `n` begins (`Semantics.Timeline.start`). The
state comes from the carrier's replay of `ExecutionStep`. `eventTimeline` derives the clock from the
transcript's own event durations by prefix sum: eight ticks for an ordinary instruction and
`CLK_INC + 256 = 264` for a syscall. `eventTimeline_allOrdinary` recovers `Timeline.ordinary`.

Past the end of a transcript the timeline keeps advancing at eight ticks per step. That is not a
claim about what the machine does there — nothing does — but it is what makes `Timeline`'s `gap`
field provable for every `n`, so a finite transcript still yields a total timeline. -/

namespace SP1Clean.Semantics

open SP1Clean.Machine
open SP1Clean.Soundness.Target (GuestProgram)

/-! ## The transcript's own timeline -/

/-- The clock width of the transcript's step `n`, defaulting to the ordinary eight ticks past the
end of the transcript. The default is what makes the timeline total. -/
def durationAt (events : List ExecutionEvent) (n : ℕ) : ℕ :=
  match events[n]? with
  | some event => event.duration
  | none => 8

theorem eight_le_durationAt (events : List ExecutionEvent) (n : ℕ) : 8 ≤ durationAt events n := by
  rw [durationAt]
  match hget : events[n]? with
  | none => exact Nat.le_refl 8
  | some event => cases event <;> simp

@[simp] theorem durationAt_of_ordinary (events : List ExecutionEvent) (n : ℕ)
    (ordinary : ∀ event ∈ events, event = ExecutionEvent.ordinary) :
    durationAt events n = 8 := by
  rw [durationAt]
  match hget : events[n]? with
  | none => rfl
  | some event =>
      have hmem : event ∈ events := List.mem_of_getElem? hget
      rw [ordinary event hmem]
      rfl

/-- **The transcript's timeline**: step `n` begins after the prefix-summed widths of the steps
before it. A shard of ordinary rows spaces its steps eight ticks apart; a shard that also commits
spaces the committing step by `264`, and this is the only definition that can say so. -/
def eventTimeline (events : List ExecutionEvent) (initialClock : ℕ) : Timeline where
  start n := initialClock + ((List.range n).map (durationAt events)).sum
  gap n := by
    rw [List.range_succ, List.map_append, List.sum_append]
    have := eight_le_durationAt events n
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega

@[simp] theorem eventTimeline_start (events : List ExecutionEvent) (initialClock n : ℕ) :
    (eventTimeline events initialClock).start n =
      initialClock + ((List.range n).map (durationAt events)).sum := rfl

/-- Within the transcript, the clock is the sum of the preceding semantic event widths. -/
theorem eventTimeline_start_le (events : List ExecutionEvent) (initialClock n : ℕ)
    (covered : n ≤ events.length) :
    (eventTimeline events initialClock).start n =
      initialClock + ((events.take n).map ExecutionEvent.duration).sum := by
  induction n with
  | zero => simp [eventTimeline_start]
  | succ n ih =>
    have inside : n < events.length := by omega
    have prior := ih (by omega)
    rw [eventTimeline_start, List.range_succ, List.map_append, List.sum_append,
      List.take_succ_eq_append_getElem inside, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      durationAt, List.getElem?_eq_getElem inside] at ⊢
    rw [eventTimeline_start] at prior
    omega

/-- **The bridge.** An all-ordinary transcript's timeline *is* the uniform eight-tick timeline —
including past the end of the transcript, which is why `durationAt` defaults to eight. -/
theorem eventTimeline_allOrdinary (events : List ExecutionEvent) (initialClock : ℕ)
    (ordinary : ∀ event ∈ events, event = ExecutionEvent.ordinary) :
    eventTimeline events initialClock = Timeline.ordinary initialClock := by
  have hstart : ∀ n, (eventTimeline events initialClock).start n =
      (Timeline.ordinary initialClock).start n := by
    intro n
    rw [eventTimeline_start, Timeline.ordinary_start]
    have hmap : (List.range n).map (durationAt events) = (List.range n).map (fun _ => 8) := by
      refine List.map_congr_left ?_
      intro i _
      exact durationAt_of_ordinary events i ordinary
    rw [hmap, List.map_const', List.sum_replicate, smul_eq_mul, List.length_range]
    omega
  cases hTimeline : eventTimeline events initialClock
  cases hOrdinary : Timeline.ordinary initialClock
  simp only [Timeline.mk.injEq]
  funext n
  have := hstart n
  rw [hTimeline, hOrdinary] at this
  exact this

/-- Every duration a transcript can carry divides the eight-tick alignment class, so a mid-shard
syscall row leaves the `align8` residue of every later row unchanged. This is the fact that lets a
non-uniform timeline reuse the alignment machinery unaltered: `264 = 8 * 33`. -/
theorem eight_dvd_durationAt (events : List ExecutionEvent) (n : ℕ) : 8 ∣ durationAt events n := by
  rw [durationAt]
  match hget : events[n]? with
  | none => exact ⟨1, rfl⟩
  | some event => cases event <;> simp

theorem eight_dvd_eventTimeline_sub (events : List ExecutionEvent) (initialClock n : ℕ) :
    8 ∣ (eventTimeline events initialClock).start n - initialClock := by
  rw [eventTimeline_start, Nat.add_sub_cancel_left]
  induction n with
  | zero => exact ⟨0, rfl⟩
  | succ n ih =>
      rw [List.range_succ, List.map_append, List.sum_append]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
      exact Nat.dvd_add ih (eight_dvd_durationAt events n)

end SP1Clean.Semantics
