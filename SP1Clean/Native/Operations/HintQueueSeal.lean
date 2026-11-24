import SP1Clean.Native.Operations.HintQueueSnapshot
import SP1Clean.Native.Operations.HintQueueBoundary

/-! # Rebase the outgoing live queue at a shard boundary

The private state supplies the last access clock, head and historical allocation frontier.
The target walk starts at that head and must finish at the null pointer after the final fixed
word. The next shard can then number its source nodes from its own public snapshot.
-/

namespace SP1Clean.HostHintSnapshot.Seal

open Circuit Air.Flat Semantics HostHintQueue
open scoped Classical

variable {p : ℕ} [Fact p.Prime]

/-- Fixed singleton ticket, complete private final state, and outgoing multiplicity. -/
abbrev Inputs := ProvablePair field (ProvablePair HostHintQueue.State field)

/-- Component name and witness hint for the unique private cursor. -/
def name := "sp1.native.hint_target_seal"

/-- Read the actual final cursor and require an endpoint-to-endpoint walk of all target words. -/
def main (hints : List Bytes) (r : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  assertZero (r.1 - 1)
  assertZero (r.2.2 - r.1)
  stateChannel.pull r.2.1
  channel.push ⟨const (Address.ofNat 0), r.2.1.head, const (Address.ofNat 0)⟩
  channel.pull (const (endpoint (wordRows hints) 0))
  stateChannel.pushIf r.2.2 (const (HostHintQueueBoundary.initial hints))

instance elaborated (hints : List Bytes) : ElaboratedCircuit (ZMod p) Inputs unit (main hints) := by elaborate_circuit

/-- A single compulsory rebase with the actual private state passed to the word walk. -/
def circuit (hints : List Bytes) : GeneralFormalCircuit (ZMod p) Inputs unit where
  name := name
  main := main hints
  elaborated := elaborated hints
  Spec r _ _ := r.1 = 1 ∧ r.2.2 = 1
  ProverAssumptions r _ _ := r.1 = 1 ∧ r.2.2 = 1
  channelsWithRequirements := [stateChannel.toRaw, channel.toRaw]
  soundness := by
    circuit_proof_start [main, channel, stateChannel]
    subst input
    simp only [sub_eq_zero] at h_holds
    obtain ⟨ticket, count⟩ := h_holds
    simp [ticket, count]
  completeness := by
    circuit_proof_start [main, channel, stateChannel]
    subst input
    obtain ⟨ticket, count⟩ := h_assumptions
    dsimp only at ticket count
    simp [ticket, count]

/-- Clean materializes one fixed ticket. Its hint contains only the eight private state limbs. -/
def component (hints : List Bytes) : Component (ZMod p) where
  circuit := circuit hints
  generation := .preallocated {
    channel := stateChannel
    trigger := .pull
    height := 1
    input _ := pure (.fixed 1, fromElements (Vector.ofFn (fun i =>
      WitnessGeneration.Cell.witness (.hintGet name (size State) 0 i))), .multiplicity)
    rowOf _ := 0 }

/-- Physical endpoint substitution has two occurrences on each of the state and word-walk channels. -/
theorem ledger (hints : List Bytes) (r : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main hints r).operations offset).interactions =
      [(stateChannel.pulled r.2.1).toRaw,
       (channel.pushed ⟨const (Address.ofNat 0), r.2.1.head, const (Address.ofNat 0)⟩).toRaw,
       (channel.pulled (const (endpoint (wordRows hints) 0))).toRaw,
       (stateChannel.pushedIf r.2.2 (const (HostHintQueueBoundary.initial hints))).toRaw] := by
  rfl

end SP1Clean.HostHintSnapshot.Seal
