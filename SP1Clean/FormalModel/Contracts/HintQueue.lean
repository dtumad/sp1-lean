import SP1Clean.Model.Core.HintQueueRecords
import SP1Clean.FormalModel.Contracts.HostCall
import SP1Clean.FormalModel.Contracts.ClockOrder

/-! # Queue-head and node interfaces for native host calls

The state channel carries only clock limbs and a queue pointer. Node guarantees are local
representation bounds and descending links; actual byte identity and current-head truth must
be derived from the source/allocation and state ledgers. HINT_LEN preserves the head while
advancing its private queue clock. Its two component variants hide empty/nonempty routing.
-/

namespace SP1Clean.HostHintQueue

open Circuit SP1Clean.Model.Core.HintQueue

structure State (F : Type) where
  clk_high : F
  clk_low : F
  head : fields 3 F
deriving ProvableStruct

def stateChannel {p : ℕ} [Fact p.Prime] : Channel (ZMod p) State where
  name := "sp1.native.hint_queue_state"
  Guarantees _ _ := True

def nodeChannel {p : ℕ} [Fact p.Prime] : Channel (ZMod p) NodeRecord where
  name := "sp1.native.hint_node"
  Guarantees record _ := record.Valid

end SP1Clean.HostHintQueue

namespace SP1Clean.HostHintLengthChip

open SP1Clean.Model.Core SP1Clean.Soundness.Target

structure Inputs (F : Type) where
  call : HostCallChip.Message F
  previous : HostHintQueue.State F
  node : HintQueue.NodeRecord F
deriving ProvableStruct

def codeWord {p : ℕ} [Fact p.Prime] : Word (ZMod p) := bitVecToWord SyscallKind.hintLength.code

def emptyWord {p : ℕ} [Fact p.Prime] : Word (ZMod p) := bitVecToWord (BitVec.allOnes 64)

def Inputs.clock {R : Type} (input : Inputs R) : ClockOrder.Inputs R :=
  ⟨input.previous.clk_high, input.previous.clk_low, input.call.clk_high, input.call.clk_low⟩

def Inputs.next {R : Type} (input : Inputs R) : HostHintQueue.State R :=
  ⟨input.call.clk_high, input.call.clk_low, input.previous.head⟩

def HeadSpec {p : ℕ} [Fact p.Prime] (empty : Bool) (input : Inputs (ZMod p)) : Prop :=
  if empty then input.previous.head = 0 ∧ input.call.result = emptyWord
  else input.previous.head = input.node.pointer ∧ input.call.result = input.node.length ∧ input.node.Valid

def Spec {p : ℕ} [Fact p.Prime] (empty : Bool) (input : Inputs (ZMod p)) : Prop :=
  input.call.code = codeWord ∧ input.call.length = 0 ∧ ClockOrder.Spec input.clock ∧ HeadSpec empty input

end SP1Clean.HostHintLengthChip
