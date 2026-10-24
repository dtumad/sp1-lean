module

public import SP1Clean.Native.Chips.HintReadWordChip.Defs
public import ToClean.Circuit.Guarded

/-! # Soundness and completeness of physical hint word transfers

The complete row means a bounded physical RAM transfer and one successive immutable hint
word. Permission and content authenticity remain balance-derived facts, never channel guarantees.
-/

@[expose] public section

namespace SP1Clean.HintReadWordChip

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

def ProverAssumptions (last : Bool) (input : Inputs (ZMod p)) : Prop :=
  HostRamAccessChip.ProverAssumptions input.ram ∧ HintReadStep.Spec last (input.step last)

omit [Fact (2 ^ 25 < p)] in
private theorem eval_step (env : Environment (ZMod p)) (last : Bool) (input : Var Inputs (ZMod p)) :
    ProvableStruct.eval env (input.step last) = (ProvableStruct.eval env input).step last := by
  rcases input with ⟨ram, pointer, index, nextIndex, nextAddress⟩
  rcases ram with ⟨access, high, low0, low1, addr0, addr1, addr2, value⟩
  cases last <;> simp only [Inputs.step, Inputs.address, circuit_norm]

/-- One active RAM transfer and its successive authenticated hint-word cursor step. -/
def activeCircuit (last : Bool) : GeneralFormalCircuit (ZMod p) Inputs unit where
  name := if last then "sp1.native.hint_read_word.last" else "sp1.native.hint_read_word.next"
  main := main last
  elaborated := elaborated last
  Spec input _ _ := Spec last input
  ProverAssumptions input _ _ := ProverAssumptions last input
  channelsWithRequirements := [Channels.memoryChannel.toRaw, HostRamAccessChip.channel.toRaw,
    HostHintQueue.wordChannel.toRaw, WritePermissionProvider.channel.toRaw, stateChannel.toRaw]
  soundness := by
    circuit_proof_start [HostRamAccessChip.circuit, HintReadStep.circuit,
      HostRamAccessChip.channel, WritePermissionProvider.channel, stateChannel, eval_step]
    exact h_holds
  completeness := by
    circuit_proof_start [HostRamAccessChip.circuit, HintReadStep.circuit,
      HostRamAccessChip.channel, WritePermissionProvider.channel, stateChannel, eval_step]
    exact h_assumptions

/-- The word transfer has only channel interactions, with no legacy lookup operations. -/
@[circuit_norm] theorem main_lookups (last : Bool) (input : Var Inputs (ZMod p))
    (offset : ℕ) : ((main last input).operations offset).lookups = [] := by
  simp [main, HostRamAccessChip.circuit, HostRamAccessChip.main, HintReadStep.circuit,
    HintReadStep.main, WordRangeCheck.circuit, WordRangeCheck.main, AddressOperation.circuit,
    AddressOperation.main, Readers.MemoryAccess.circuit, Readers.MemoryAccess.main,
    AddrAddOperation.circuit, AddrAddOperation.main, Gadgets.ToBits.rangeCheck,
    Gadgets.toBits, Gadgets.ToBits.main, Gadgets.Equality.main, circuit_norm]

/-- Guarding preserves the declared guarantees and every physical channel occurrence. -/
instance guardSupported (last : Bool) : Guarded.Supported (activeCircuit (p := p) last) :=
  Guarded.Supported.of_emitted_requirements _
    (fun input offset => main_lookups last input offset)
    (by
      intro selected member
      have registered : selected = Channels.byteChannel.toRaw ∨
          selected = Channels.memoryChannel.toRaw ∨ selected = HostRamAccessChip.channel.toRaw ∨
          selected = HostHintQueue.wordChannel.toRaw ∨ selected = WritePermissionProvider.channel.toRaw ∨
          selected = stateChannel.toRaw := by
        cases last <;> simpa [GeneralFormalCircuit.channels, activeCircuit, elaborated, circuit_norm,
          or_assoc, or_left_comm, or_comm] using member
      rcases registered with rfl | rfl | rfl | rfl | rfl | rfl <;>
        infer_instance)
    (by
      intro _ _ selected required outside _ _
      exfalso
      apply outside
      cases last <;> simp_all [activeCircuit, elaborated, circuit_norm])

/-- Disabled padding retains its physical row while requesting no word, Memory or permissions. -/
def circuit (last : Bool) : GeneralFormalCircuit (ZMod p) RowInput unit :=
  Guarded.circuit (activeCircuit last) inferInstance

end SP1Clean.HintReadWordChip
