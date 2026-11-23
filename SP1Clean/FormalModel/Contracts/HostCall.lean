import SP1Clean.FormalModel.Contracts.CoreSyscall

/-! # Instruction-authenticated host calls

The released ECALL instruction supplies the incoming clock, full code in x5, x10 and x11,
and the returned x5 word. WRITE obtains x12 from the read-only observer at this clock.
-/

namespace SP1Clean.HostCallChip

open Circuit Channels

/-- The incoming event clock and the four words observed by the ECALL instruction. -/
structure Message (F : Type) where
  clk_high : F
  clk_low : F
  code : Word F
  arg1 : Word F
  arg2 : Word F
  result : Word F
deriving ProvableStruct
provable_struct_eval_lemmas Message

def channel {p : ℕ} [Fact p.Prime] : Channel (ZMod p) Message where
  name := "sp1.native.host_call"
  Guarantees _ _ := True

/-- Decode the handoff directly from the physical instruction inputs. -/
def message {R : Type} [Add R] [Mul R] [OfNat R 65536] (input : SyscallInstrsChip.Inputs R) : Message R :=
  ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536,
    input.op_a_memory.prev_value, input.op_b_memory.prev_value, input.op_c_memory.prev_value, input.op_a_value⟩

end SP1Clean.HostCallChip
