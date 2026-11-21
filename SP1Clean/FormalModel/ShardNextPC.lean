import SP1Clean.FormalModel.ShardPreservation
import SP1Clean.Semantics.Execution.SailBookkeeping

/-! # The semantic nextPC at a local segment boundary

Normal Sail retirement commits nextPC to PC. Host transitions preserve nextPC and authenticate
the incoming PC of their own event. Together these observations recover the entire local tape's
nextPC from its endpoints, including HALT and a trailing suffix of host calls.
-/

namespace SP1Clean.FormalModel.Shard.Executes
open Semantics Machine Soundness.Target LeanRV64D

/-- The outgoing register entry follows the actual ordinary and host labels of the execution. -/
theorem nextPC {characteristic : ℕ} {image : ProgramImage}
    {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (execution : Executes characteristic image source target events) :
    target.sail.registers.get? Register.nextPC =
      nextPcAfter events (source.sail.registers.get? Register.nextPC) (some target.pc) := by
  have result := replayEvents?_nextPC execution.2.replay (by
    intro n current next event present atCut ran
    obtain ⟨s, t, reached, step⟩ := execution.2.step_at present
    obtain rfl := Option.some.inj (atCut.symm.trans reached)
    obtain rfl := Option.some.inj (ran.symm.trans step.replay)
    have cfg := execution.frame_prefix atCut
    cases event with
    | ordinary =>
      cases step with
      | ordinary _ _ normal permitted => exact (Advance.ordinary_normal_bookkeeping cfg.1 cfg.2.1 permitted normal).1
    | syscall call =>
      cases step with
      | syscall success =>
        obtain ⟨pc, exec, _, _, _, _, targetEq, _⟩ := HostState.step_observations success
        exact targetEq ▸ exec.other_register_frame current.sail pc Register.nextPC (by decide) (by decide))
  have final := Std.ExtDHashMap.get?_eq_some_get (execution.frame.1.init Register.PC)
  have atPc : target.realize.sail.regs.get? Register.PC = some target.pc := by
    change target.sail.registers.get? Register.PC = some ((target.sail.registers.get? Register.PC).getD 0)
    change target.sail.registers.get? Register.PC = _ at final
    rw [final]
    rfl
  rwa [atPc] at result

private theorem nextPcAfter_bounded (events : List ExecutionEvent) (incoming : Option (BitVec 64))
    (outgoing : BitVec 64) (bounded : outgoing.toNat < 2 ^ 48)
    (hosts : ∀ call, ExecutionEvent.syscall call ∈ events → call.pc.toNat < 2 ^ 48)
    (nonempty : events.countP ExecutionEvent.isOrdinary ≠ 0) :
    ∃ pc, nextPcAfter events incoming (some outgoing) = some pc ∧ pc.toNat < 2 ^ 48 := by
  induction events using List.reverseRecOn generalizing outgoing with
  | nil => simp at nonempty
  | append_singleton before event ih =>
    cases event with
    | ordinary => exact ⟨outgoing, nextPcAfter_ordinary .., bounded⟩
    | syscall call =>
      rw [nextPcAfter_syscall]
      apply ih call.pc (hosts call (by simp))
      · intro other member
        exact hosts other (List.mem_append_left _ member)
      · simpa [List.countP_append, List.countP_cons] using nonempty

private theorem fetched_bound {program : GuestProgram} {pc : BitVec 64} {word : BitVec 32}
    (fetched : program.fetchWord pc = some word) : pc.toNat < 2 ^ 48 := by
  obtain ⟨entry, found, _⟩ := Option.map_eq_some_iff.mp fetched
  have address : entry.1 = pc := by simpa only [beq_iff_eq] using List.find?_some found
  have window := program.rom_in_window entry (List.mem_of_find?_eq_some found)
  rw [address] at window
  omega

/-- Each actual trajectory state has a 48-bit program counter. An interior state's next
instruction fetch authenticates the bound; the outgoing snapshot supplies the terminal bound. -/
theorem pc_at {limits : ResourceLimits} {characteristic : ℕ} {image : ProgramImage}
    {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (execution : AdmissibleExecution limits characteristic image source target events)
    {cut : ℕ} {state : ExecutionState}
    (reached : executionTrajectory (policy characteristic image) image.program source.realize events cut = some state)
    {pc : BitVec 64} (atPc : state.sail.regs.get? Register.PC = some pc) : pc.toNat < 2 ^ 48 := by
  by_cases inside : cut < events.length
  · obtain ⟨current, addr, _, same, address, fetched, _⟩ := execution.1.fetch_at cut inside
    obtain rfl := Option.some.inj (reached.symm.trans same)
    obtain rfl := Option.some.inj (atPc.symm.trans address)
    exact fetched_bound fetched
  · rw [executionTrajectory_after _ _ _ _ _ (by omega), execution.1.2.replay] at reached
    obtain rfl := Option.some.inj reached
    have bound : target.pc.toNat < 2 ^ 48 := execution.2.2.2.2.2.2
    change target.sail.registers.get? Register.PC = some pc at atPc
    simpa only [ExecutionSnapshot.pc, atPc, Option.getD_some] using bound

private theorem hostPC_bound {characteristic : ℕ} {image : ProgramImage}
    {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (execution : Executes characteristic image source target events) (call : CoreSyscallEvent)
    (present : ExecutionEvent.syscall call ∈ events) : call.pc.toNat < 2 ^ 48 := by
  obtain ⟨cut, atCut⟩ := List.mem_iff_getElem?.mp present
  obtain ⟨_, _, _, step⟩ := execution.2.step_at atCut
  cases step with
  | syscall ran =>
    obtain ⟨pc, exec, _, fetched, _, _, _, same⟩ := HostState.step_observations ran
    rw [same]
    exact fetched_bound fetched

/-- After any ordinary instruction, nextPC is present and representable in the physical
48-bit state limbs. A later syscall supplies its own ROM-bounded PC even if it halts. -/
theorem nextPC_bounded {limits : ResourceLimits} {characteristic : ℕ} {image : ProgramImage}
    {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (execution : AdmissibleExecution limits characteristic image source target events)
    (ordinary : events.countP ExecutionEvent.isOrdinary ≠ 0) :
    ∃ pc : BitVec 64, target.sail.registers.get? Register.nextPC = some pc ∧ pc.toNat < 2 ^ 48 := by
  rw [execution.1.nextPC]
  exact nextPcAfter_bounded _ _ _ execution.2.2.2.2.2.2 (hostPC_bound execution.1) ordinary

end SP1Clean.FormalModel.Shard.Executes
