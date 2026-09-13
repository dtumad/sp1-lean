import SP1Clean.Model.Core.ExecutionReplay
import SP1Clean.Model.SP1Field
import SP1CleanTest.Audit.ActiveNativeCompleteness

/-! # Native local-path and terminal-boundary regressions

Two committed ECALLs execute ENTER followed by HALT from a non-boot clock, preserving nonempty
incoming host state and RAM. Each call is a separate semantic shard, and their joined path is the
same two-step execution. These test the semantic interface, not an AIR witness.
-/

namespace SP1CleanTest.Core.ExecutionPath

open SP1Clean SP1Clean.Model.Core SP1Clean.Machine SP1Clean.Soundness.Target
  LeanRV64D LeanRV64D.Defs

private def policy : HostPolicy := ⟨⟨fun _ => false, 65536, 2 ^ 48⟩, SP1Prime⟩

private def program : GuestProgram where
  rom := [(65536, 0x73), (65540, 0x73)]
  pc_start := 65536
  memImage := []
  rom_nodup := by decide
  rom_aligned := by simp
  rom_in_window := by simp
  rom_full_width := by simp

private def source : ExecutionState where
  sail := { (default : SailState) with
    regs := ((((default : SailState).regs.insert Register.PC 65536).insert Register.x5 3).insert
      Register.x10 70000).insert Register.x11 0
    mem := (∅ : Std.ExtHashMap ℕ (BitVec 8)).insert 65552 42 }
  host := { io := ⟨[[7, 8]], [9]⟩ }
  clock := 17

private def enter : SP1Clean.Model.Core.HostExecution :=
  ⟨.enterUnconstrained, 70000, 0, 0, ⟨source.host, none⟩⟩

private def middle : ExecutionState :=
  ⟨enter.apply source.sail 65536, enter.effect.state, source.clock + 264⟩

private def halt : SP1Clean.Model.Core.HostExecution :=
  ⟨.halt, 70000, 0, 0, ⟨{ middle.host with exitCode := some 70000 }, none⟩⟩

private def target : ExecutionState :=
  ⟨halt.apply middle.sail 65540, halt.effect.state, middle.clock + 264⟩

private theorem enter_run : source.host.run policy (.ofSail source.sail) = some enter := by
  native_decide

private theorem halt_run : middle.host.run policy (.ofSail middle.sail) = some halt := by
  native_decide

private theorem enter_step : ExecutionStep policy program source
    (.syscall (enter.toEvent source.clock 65536)) middle := by
  exact .syscall (HostState.step_of_run (by native_decide) (by native_decide) enter_run _)

private theorem halt_step : ExecutionStep policy program middle
    (.syscall (halt.toEvent middle.clock 65540)) target := by
  exact .syscall (HostState.step_of_run (by native_decide) (by native_decide) halt_run _)

/-- A continuing shard need not start at boot or end at HALT. -/
theorem continuingShard : ExecutionSegment policy program source 1 middle :=
  ⟨_, rfl, .cons enter_step (.nil _)⟩

/-- The terminal syscall is a single real step in the same local relation. -/
theorem terminalShard : ExecutionSegment policy program middle 1 target :=
  ⟨_, rfl, .cons halt_step (.nil _)⟩

theorem joinedShards : ExecutionSegment policy program source 2 target :=
  continuingShard.append terminalShard

theorem splitJoinedShards : ∃ boundary, ExecutionSegment policy program source 1 boundary ∧
    ExecutionSegment policy program boundary 1 target :=
  ExecutionSegment.add_iff.mp joinedShards

theorem polyFunPath : (executionSystem policy program).ReachableIn 2 source target :=
  ExecutionSegment.iff_reachableIn.mp joinedShards

/-- Identity at a terminal state adds no instruction and preserves every state component. -/
theorem terminalIdentity : ExecutionSegment policy program target 0 target := .refl target

private theorem target_halted : target.host.exitCode ≠ none := by native_decide

theorem rejectsAfterHalt (event : ExecutionEvent) (next : ExecutionState) :
    ¬ ExecutionStep policy program target event next :=
  ExecutionStep.not_of_halted target_halted

theorem rejectsPositiveTerminalSegment (steps : ℕ) (positive : 0 < steps)
    (next : ExecutionState) : ¬ ExecutionSegment policy program target steps next := by
  intro segment
  have stopped := segment.of_halted target_halted
  omega

/-- Host continuity cannot be replaced by equality of the PC and clock. -/
theorem rejectsForgedHost : ¬ ExecutionSegment policy program source 2
    { target with host := { target.host with io := ⟨[], [99]⟩ } } := by
  intro forged
  have equal := congrArg (fun state : ExecutionState => state.host.io.publicOutput)
    (joinedShards.deterministic forged)
  have wrong : target.host.io.publicOutput ≠ [99] := by native_decide
  exact wrong equal

/-- Even a zero-step shard cannot alter an unaccessed RAM location. -/
theorem rejectsForgedMemory : ¬ ExecutionSegment policy program target 0
    { target with sail := { target.sail with mem := target.sail.mem.insert 65552 99 } } := by
  intro forged
  have equal := congrArg (fun state : ExecutionState => state.sail.mem.get? 65552)
    (ExecutionSegment.zero_iff.mp forged)
  have wrong : (target.sail.mem.insert 65552 99).get? 65552 ≠ target.sail.mem.get? 65552 := by
    native_decide
  exact wrong equal

theorem observableResults : target.clock = 545 ∧ target.host.exitCode = some 70000 ∧
    target.host.io.hints = [[7, 8]] ∧ target.host.io.publicOutput = [9] ∧
    target.sail.mem.get? 65552 = some 42 ∧ target.sail.regs.get? Register.PC = some haltPc := by
  native_decide

/-- Direct replay threads ENTER's returned x5 into the next HALT dispatch. -/
theorem replayJoinedShards : replayEvents? policy program source
    [.syscall (enter.toEvent source.clock 65536), .syscall (halt.toEvent middle.clock 65540)] =
      some target :=
  (ExecutionPath.cons enter_step (.cons halt_step (.nil _))).replay

/-- Host replay rejects altered result and timestamp fields, rather than trusting event data. -/
theorem rejectsForgedEvent :
    replayHost? policy program source { enter.toEvent source.clock 65536 with result := 1 } = none ∧
    replayHost? policy program source { enter.toEvent source.clock 65536 with clock := 18 } = none := by
  native_decide

/-- The existing official-Sail/AIR self-jump anchor embeds as an ordinary local step. -/
theorem ordinaryContinues (host : HostState) (running : host.exitCode = none) (clock : ℕ) :
    ExecutionStep policy Audit.JointNonVacuity.anchorProgram
      ⟨Audit.JointNonVacuity.anchorState, host, clock⟩ .ordinary
      ⟨Audit.ActiveNativeCompleteness.activeTarget, host, clock + 8⟩ :=
  .ordinary running Audit.ActiveNativeCompleteness.anchor_notAboutToExecuteEcall
    Audit.ActiveNativeCompleteness.activeTarget_effect.normal

/-- A real normally-retiring Sail instruction is still forbidden after the host has halted. -/
theorem rejectsRunnableAfterHalt :
    SailRetiresNormally Audit.JointNonVacuity.anchorState Audit.ActiveNativeCompleteness.activeTarget ∧
      ¬ ExecutionStep policy Audit.JointNonVacuity.anchorProgram
        ⟨Audit.JointNonVacuity.anchorState, { exitCode := some 0 }, 17⟩ .ordinary
        ⟨Audit.ActiveNativeCompleteness.activeTarget, { exitCode := some 0 }, 25⟩ :=
  ⟨Audit.ActiveNativeCompleteness.activeTarget_effect.normal,
    ExecutionStep.not_of_halted (by decide)⟩

end SP1CleanTest.Core.ExecutionPath
