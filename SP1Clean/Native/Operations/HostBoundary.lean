import SP1Clean.Native.Operations.HintQueueBoundary
import SP1Clean.Native.Operations.HostCommitEndpoint

/-! # One native verifier boundary for hints and both commitment banks

The three existing boundary circuits run as true Clean subcircuits. Their fixed source and
target values are statement parameters, while the bank terminals remain physical tables.
The singleton adapter preserves every interaction and allocates no witness cells.
-/

namespace SP1Clean.HostBoundary

open Circuit Air.Flat Model.Core

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

def main (hints : List Bytes) (queueFinal : HostHintQueue.State (ZMod p))
    (source target : Bool → Vector (Word (ZMod p)) 8) (_ : Var unit (ZMod p)) :
    Circuit (ZMod p) Unit := do
  let _ ← HostHintQueueBoundary.circuit hints queueFinal ()
  let _ ← HostCommitEndpoint.circuit false (source false) (target false) ()
  let _ ← HostCommitEndpoint.circuit true (source true) (target true) ()
  pure ()

def circuit (hints : List Bytes) (queueFinal : HostHintQueue.State (ZMod p))
    (source target : Bool → Vector (Word (ZMod p)) 8) :
    GeneralFormalCircuit (ZMod p) unit unit where
  main := main hints queueFinal source target
  Spec _ _ _ := hints.length < 2 ^ 48
  ProverAssumptions _ _ _ := hints.length < 2 ^ 48
  channelsWithRequirements := [HostHintQueue.stateChannel.toRaw,
    (HostCommitChip.stateChannel false).toRaw, (HostCommitChip.stateChannel true).toRaw]
  soundness := by
    circuit_proof_all [main, HostHintQueueBoundary.circuit, HostCommitEndpoint.circuit]
  completeness := by
    circuit_proof_all [main, HostHintQueueBoundary.circuit, HostCommitEndpoint.circuit]

omit [Fact (2 ^ 25 < p)] in
theorem values (hints : List Bytes) (queueFinal : HostHintQueue.State (ZMod p))
    (source target : Bool → Vector (Word (ZMod p)) 8) (offset : ℕ)
    (env : Environment (ZMod p)) (channel : RawChannel (ZMod p)) :
    ((main hints queueFinal source target ()).operations offset).interactionValuesWith channel env =
      ((HostHintQueueBoundary.main hints queueFinal ()).operations offset).interactionValuesWith channel env ++
      ((HostCommitEndpoint.main false (source false) (target false) ()).operations offset).interactionValuesWith channel env ++
      ((HostCommitEndpoint.main true (source true) (target true) ()).operations offset).interactionValuesWith channel env := by
  simp only [main, Operations.interactionValuesWith, Operations.interactionsWith, circuit_norm,
    GeneralFormalCircuit.toSubcircuit_interactions, HostHintQueueBoundary.circuit,
    HostCommitEndpoint.circuit, List.filter_append, List.map_append, List.append_assoc]

/-- All three source/final pairs are invoked exactly once by the enclosing verifier. -/
def closed (hints : List Bytes) (queueFinal : HostHintQueue.State (ZMod p))
    (source target : Bool → Vector (Word (ZMod p)) 8) : ClosedVerifier (ZMod p) where
  circuit := circuit hints queueFinal source target
  length_zero := rfl
  constraints := by
    intros
    simp only [circuit, main, circuit_norm, GeneralFormalCircuit.toSubcircuit_constraints,
      GeneralFormalCircuit.toSubcircuit_lookups, HostHintQueueBoundary.circuit,
      HostHintQueueBoundary.main, HostCommitEndpoint.circuit, HostCommitEndpoint.main,
      HostCommitBoundary.verifier, HostCommitBoundary.verifierMain]
  interactions := by
    intro offset env channel
    rw [show (circuit hints queueFinal source target).main = main hints queueFinal source target from rfl,
      values, values]
    exact congrArg₂ List.append
      (congrArg₂ List.append ((HostHintQueueBoundary.closed hints queueFinal).interactions offset env channel)
        ((HostCommitEndpoint.closed false (source false) (target false)).interactions offset env channel))
      ((HostCommitEndpoint.closed true (source true) (target true)).interactions offset env channel)

omit [Fact (2 ^ 25 < p)] in
@[circuit_norm] theorem closed_main (hints : List Bytes) (queueFinal : HostHintQueue.State (ZMod p))
    (source target : Bool → Vector (Word (ZMod p)) 8) :
    (closed hints queueFinal source target).circuit.main = main hints queueFinal source target := rfl

omit [Fact (2 ^ 25 < p)] in
/-- The enlarged verifier retains the actual source-queue size check. -/
theorem source_bound (hints : List Bytes) (queueFinal : HostHintQueue.State (ZMod p))
    (source target : Bool → Vector (Word (ZMod p)) 8) (offset : ℕ) (env : Environment (ZMod p))
    (constraints : ((main hints queueFinal source target ()).operations offset).ConstraintsHold env) :
    hints.length < 2 ^ 48 := by
  simpa only [main, circuit_norm, GeneralFormalCircuit.toSubcircuit_constraints,
    GeneralFormalCircuit.toSubcircuit_lookups, HostHintQueueBoundary.circuit,
    HostHintQueueBoundary.main, HostCommitEndpoint.circuit, HostCommitEndpoint.main,
    HostCommitBoundary.verifier, HostCommitBoundary.verifierMain, ite_eq_left_iff,
    one_ne_zero, imp_false, not_not] using constraints

omit [Fact (2 ^ 25 < p)] in
/-- Bank endpoints leave the queue channel's two fixed boundary messages unchanged. -/
theorem queue_values (hints : List Bytes) (queueFinal : HostHintQueue.State (ZMod p))
    (source target : Bool → Vector (Word (ZMod p)) 8) (offset : ℕ) (env : Environment (ZMod p)) :
    ((main hints queueFinal source target ()).operations offset).interactionValuesWith HostHintQueue.stateChannel.toRaw env =
      [HostHintQueue.stateChannel.pushedValue (HostHintQueueBoundary.initial hints),
        HostHintQueue.stateChannel.pulledValue queueFinal] := by
  rw [values, HostHintQueueBoundary.values, HostCommitEndpoint.values, HostCommitEndpoint.values]
  simp [HostHintQueue.stateChannel, HostCommitChip.stateChannel, Channel.toRaw]

omit [Fact (2 ^ 25 < p)] in
/-- Each private bank receives precisely its own fixed source and final messages. -/
theorem bank_values (hints : List Bytes) (queueFinal : HostHintQueue.State (ZMod p))
    (source target : Bool → Vector (Word (ZMod p)) 8) (offset : ℕ)
    (env : Environment (ZMod p)) (deferred : Bool) :
    ((main hints queueFinal source target ()).operations offset).interactionValuesWith
      (HostCommitChip.stateChannel deferred).toRaw env =
      [(HostCommitChip.stateChannel deferred).pushedValue (HostCommitBoundary.start (source deferred)),
       (HostCommitChip.stateChannel deferred).pulledValue (HostCommitBoundary.final (target deferred))] := by
  rw [values, HostCommitEndpoint.values, HostCommitEndpoint.values]
  have queue : ((HostHintQueueBoundary.main hints queueFinal ()).operations offset).interactionValuesWith
      (HostCommitChip.stateChannel deferred).toRaw env = [] := by
    cases deferred <;> simp [HostHintQueueBoundary.main, Operations.interactionValuesWith,
      Operations.interactionsWith, circuit_norm, HostHintQueue.stateChannel,
      HostCommitChip.stateChannel, Channel.toRaw]
  rw [queue]
  cases deferred <;> simp [HostCommitChip.stateChannel, Channel.toRaw]

end SP1Clean.HostBoundary
