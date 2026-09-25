import SP1Clean.FormalModel.ShardResources
import SP1Clean.Model.SP1Field

/-! # A nonempty bounded complete-state shard

The source clock is deliberately not phase one. A real padded HINT_READ reaches the supplied
full finite target; lowering the tick or byte ceiling rejects this same semantic tape.
-/

namespace SP1CleanTest.Core.ShardResources
open SP1Clean SP1Clean.Model.Core SP1Clean.Machine SP1Clean.Soundness.Target LeanRV64D.Defs
open FormalModel.Shard

private def image : ProgramImage := ⟨[(65536, 0x73)], 65536, []⟩
private def source : ExecutionSnapshot where
  sail := {
    registers := (((configuredState 65536).regs.insert .x5 241).insert .x10 70000).insert .x11 8
    memory := ⟨[(65536, 0x73)]⟩ }
  host := { io.hints := [[1, 2, 3, 4, 5, 6, 7, 8]] }
  clock := 2

private theorem valid : ExecutionSourceValid image source :=
  (checkExecutionSource_iff _ _).mp (by native_decide)

private def execution : HostExecution :=
  ⟨.hintRead, 70000, 8, 241,
    ⟨{ source.host with io.hints := [] }, some ⟨70000, hintWriteBytes [1, 2, 3, 4, 5, 6, 7, 8]⟩⟩⟩
private def target : ExecutionSnapshot :=
  ⟨execution.applySnapshot source.sail 65536, execution.effect.state, source.clock + 264⟩
private def event : CoreSyscallEvent := execution.toEvent source.clock 65536
private def limits : ResourceLimits := ⟨1, 264, 0, 16, 0, 1, 8, 0, 0, 200, 4096, 65536⟩

private theorem step : ExecutionStep (policy SP1Prime image) (image.toGuestProgram valid.1.1)
    source.realize (.syscall event) target.realize :=
by
  apply ExecutionSnapshot.hostStep?_sound rfl
  have atPc : source.sail.registers.get? .PC = some 65536 := by native_decide
  have fetched : (image.toGuestProgram valid.1.1).fetchWord 65536 = some ECALL_ENC := by native_decide
  have loaded : InstructionBytes.check source.sail.readContext.byte 65536 ECALL_ENC = true := by native_decide
  have ran : source.host.run (policy SP1Prime image) source.sail.readContext = some execution := by native_decide
  simp only [ExecutionSnapshot.hostStep?, atPc, bind, Option.bind_some, fetched, loaded,
    and_self, ↓reduceIte, ran]
  rfl

private theorem measured :
    executionResources (policy SP1Prime image) (image.toGuestProgram valid.1.1)
      source.realize [.syscall event] =
        (source.resources.combine
          (source.host.eventResources (policy SP1Prime image) source.sail.readContext (.syscall event))).combine
          target.resources := by
  rw [executionResources_cons step, executionResources_nil, ResourceUsage.combine_zero,
    ExecutionSnapshot.resources_realize, ExecutionSnapshot.resources_realize,
    ExecutionSnapshot.eventResources_realize]

/-- Nonempty host execution inhabits the fixed native domain, with no compiler or witness premises. -/
theorem paddedHint_admissible : AdmissibleExecution limits SP1Prime image source target [.syscall event] := by
  refine ⟨⟨valid, .cons step (.nil _), ?_⟩, valid.1.1, ?_, ?_, ?_, ?_, by decide, by native_decide⟩
  · rw [ExecutionPath.writesPermitted_cons_iff step]
    simp only [reduceCtorEq, false_implies, ExecutionPath.writesPermitted_nil, and_self]
  · rw [ExecutionPath.encoded_cons_iff step]
    exact ⟨⟨by change 2 % 2 ^ 24 + 4 < 2 ^ 24; decide, by simp⟩, ExecutionPath.encoded_nil⟩
  · rw [measured]
    intro kind
    cases kind <;> native_decide
  · rw [ExecutionSnapshot.resources_realize]
    intro kind
    cases kind <;> native_decide
  · rw [ExecutionSnapshot.resources_realize]
    intro kind
    cases kind <;> native_decide

/-- Tight work limits reject the same actual path, independently of its endpoint or compiler. -/
theorem rejectsTickOverflow :
    ¬ AdmissibleExecution { limits with ticks := 263 } SP1Prime image source target [.syscall event] := by
  intro admitted
  have bound := admitted.work.2
  exact (by decide : ¬ (264 : ℕ) ≤ 263) bound

/-- The mandatory padding consumes the byte budget even when the hint length is word aligned. -/
theorem rejectsPaddingOverflow :
    ¬ AdmissibleExecution { limits with writeBytes := 15 } SP1Prime image source target [.syscall event] := by
  rintro ⟨_, _, _, fits, _⟩
  rw [measured] at fits
  have bound := fits .writeBytes
  have cost : (source.resources.combine
      (source.host.eventResources (policy SP1Prime image) source.sail.readContext (.syscall event))).combine
        target.resources .writeBytes = 16 := by native_decide
  rw [cost] at bound
  exact (by decide : ¬ (16 : ℕ) ≤ 15) bound

/-- Empty identities still account for incoming host state, with no active clock phase premise. -/
theorem stoppedIdentity :
    AdmissibleExecution limits SP1Prime image { source with host.exitCode := some 7 }
      { source with host.exitCode := some 7 } [] := by
  apply admissibleExecution_identity_iff.mpr
  refine ⟨(checkExecutionSource_iff _ _).mp (by native_decide), ?_⟩
  rw [ExecutionSnapshot.resources_realize]
  intro kind
  cases kind <;> native_decide

end SP1CleanTest.Core.ShardResources
