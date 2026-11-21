import SP1Clean.Proofs.Chips.HostNoopChip.Formal
import SP1Clean.Semantics.Host.HostExecutionLaws

/-! # No-effect host execution from an authenticated handoff

The register observations belong to the matched instruction. ENTER and VERIFY preserve every
host field and produce no guest-memory write. The running host determines call availability.
-/

namespace SP1Clean.HostNoopChip

open SP1Clean.Semantics

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Complete semantic syscall selected by the physical control handler. -/
def Kind.syscall : Kind → SyscallKind
  | .enter => .enterUnconstrained
  | .verify => .verifyProof

/-- The authenticated arguments and result accompany the unchanged host and empty write plan. -/
def execution (kind : Kind) (input : Inputs (ZMod p)) (host : HostState) : HostExecution :=
  ⟨kind.syscall, Word.toBitVec64 input.arg1, Word.toBitVec64 input.arg2,
    Word.toBitVec64 input.result, ⟨host, none⟩⟩

private theorem code_value (kind : Kind) : Word.toBitVec64 (codeWord (p := p) kind) = kind.syscall.code := by
  have hp := Fact.out (p := 2 ^ 17 < p)
  cases kind with
  | enter =>
    have small : (3 : ZMod p).val = 3 := by
      change ((3 : ℕ) : ZMod p).val = 3
      exact ZMod.val_natCast_of_lt (by omega)
    simp [Word.toBitVec64, Word.toNat, codeWord, Kind.syscall, SyscallKind.code, small]
  | verify =>
    have small : (27 : ZMod p).val = 27 := by
      change ((27 : ℕ) : ZMod p).val = 27
      exact ZMod.val_natCast_of_lt (by omega)
    simp [Word.toBitVec64, Word.toNat, codeWord, Kind.syscall, SyscallKind.code, small]

/-- Matched register observations and the handler contract yield a complete zero-effect call. -/
theorem run_of_spec (kind : Kind) (input : Inputs (ZMod p)) (valid : Spec kind input)
    (host : HostState) (running : host.exitCode = none) (policy : HostPolicy) (context : HostReadContext)
    (code : context.register 5 = some (Word.toBitVec64 input.code))
    (arg1 : context.register 10 = some (Word.toBitVec64 input.arg1))
    (arg2 : context.register 11 = some (Word.toBitVec64 input.arg2)) :
    host.run policy context = some (execution kind input host) := by
  apply (host.run_eq_some_iff policy context (execution kind input host)).mpr
  refine ⟨running, ?_, arg1, arg2, ?_, by cases kind <;> rfl⟩
  · simpa only [valid.1, code_value, execution] using code
  · cases kind with
    | enter => simp [execution, valid.2.1, Kind.syscall, resultWord, HostState.result, Word.toBitVec64, Word.toNat]
    | verify => exact (congrArg Word.toBitVec64 valid.2.1).trans (code_value .verify)

end SP1Clean.HostNoopChip
