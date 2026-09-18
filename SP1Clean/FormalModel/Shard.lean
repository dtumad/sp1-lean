import SP1Clean.Model.Core.SourceExecution

/-! # Complete-state semantics for the native shard capstone

This contract reuses the existing execution path and finite snapshots. It neither evaluates a
second machine nor replaces the official Sail step. All eight concrete host calls are part of
`ExecutionPath`. A shard may start at any checked local source, continue, halt, or be empty.
Padding and ledger administration are absent from the semantic event tape.

`Executes` is the semantic spine, before resource restrictions. `Profile` names the still-open
semantic domain of the bounded AIR: clock phase/ranges, actual writable store bytes, and finite
resource capacities must be fixed and enforced by that AIR before a capstone can be instantiated.
It must not be instantiated with compiler success, row readiness, or a witness-grounding premise.
There is deliberately no default profile and no claim that the current mixed assembly realizes
this complete-state contract. See `Soundness/Shard/Contract` for the two end-to-end targets.
-/

namespace SP1Clean.FormalModel.Shard

open Model.Core Machine

/-- Native host policy uses the AIR characteristic and the checked image's protected ROM bytes. -/
def policy (characteristic : ℕ) (image : ProgramImage) : HostPolicy :=
  ⟨{ readOnly := image.readOnly }, characteristic⟩

/-- One local execution, including literal equality with the complete outgoing realization. -/
def Executes (characteristic : ℕ) (image : ProgramImage)
    (source target : ExecutionSnapshot) (events : List ExecutionEvent) : Prop :=
  ∃ valid : ExecutionSourceValid image source,
    ExecutionPath (policy characteristic image) (image.toGuestProgram valid.1.1)
      source.realize events target.realize

/-- Semantic restrictions to be fixed by the native resource/permission policy, independently
of AIR rows and compiler internals. This is a target parameter, not a completed native profile. -/
abbrev Profile := ℕ → ProgramImage → ExecutionSnapshot → ExecutionSnapshot →
  List ExecutionEvent → Prop

/-- Both directions of the bounded capstone must use this same independently specified domain. -/
def AdmissibleExecution (profile : Profile) (characteristic : ℕ) (image : ProgramImage)
    (source target : ExecutionSnapshot) (events : List ExecutionEvent) : Prop :=
  Executes characteristic image source target events ∧
    profile characteristic image source target events

namespace Executes

variable {characteristic : ℕ} {image : ProgramImage}
  {source left right target : ExecutionSnapshot} {first second : List ExecutionEvent}

/-- Empty shards preserve the entire state, including stopped hosts and untouched memory. -/
theorem nil_iff : Executes characteristic image source target [] ↔
    ExecutionSourceValid image source ∧ source.equivalent target = true := by
  constructor
  · rintro ⟨valid, path⟩
    exact ⟨valid, (ExecutionSnapshot.equivalent_iff _ _).mpr
      (ExecutionPath.nil_iff.mp path).symm⟩
  · rintro ⟨valid, same⟩
    exact ⟨valid, ExecutionPath.nil_iff.mpr
      ((ExecutionSnapshot.equivalent_iff _ _).mp same).symm⟩

/-- Semantic composition uses the executable full-boundary comparison. Resource limits are
intentionally separate: two legal shards need not fit in a single shard. -/
theorem append (firstPath : Executes characteristic image source left first)
    (secondPath : Executes characteristic image right target second)
    (same : left.equivalent right = true) :
    Executes characteristic image source target (first ++ second) := by
  obtain ⟨sourceValid, firstPath⟩ := firstPath
  obtain ⟨_, secondPath⟩ := secondPath
  rw [← (ExecutionSnapshot.equivalent_iff _ _).mp same] at secondPath
  exact ⟨sourceValid, firstPath.append secondPath⟩

/-- Event duration, rather than padding or table height, determines the endpoint clock. -/
theorem clock (execution : Executes characteristic image source target first) :
    target.clock = source.clock + (first.map ExecutionEvent.duration).sum :=
  execution.2.clock

/-- A stopped incoming host admits only an identity execution. -/
theorem of_halted (execution : Executes characteristic image source target first)
    (halted : source.host.exitCode ≠ none) :
    first = [] ∧ source.equivalent target = true := by
  obtain ⟨empty, same⟩ := execution.2.of_halted halted
  exact ⟨empty, (ExecutionSnapshot.equivalent_iff _ _).mpr same.symm⟩

end Executes

end SP1Clean.FormalModel.Shard
