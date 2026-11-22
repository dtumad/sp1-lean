module

public import SP1Clean.Semantics.Host.HintQueueSuffix
public import SP1Clean.Semantics.Host.HostExecution

/-! # Outgoing host state for the installed handlers

The incoming hint store is immutable in this profile. Its terminal pointer identifies the
remaining ordered bytes. The commitment banks and exit status have their own ledgers. All
other host observations are preserved by these handlers.
-/

@[expose] public section

namespace SP1Clean.HostHintTarget

open Semantics

/-- Reconstruct the outgoing host from the terminal queue and the separately checked banks/exit. -/
def outgoing (source target : HostState) (hints : List Bytes) : HostState :=
  { source with
    io.hints := hints
    committed := target.committed
    deferred := target.deferred
    exitCode := target.exitCode }

/-- The verifier's terminal identifies the exact target suffix and the full host frame. -/
def Spec (source target : HostState) (head : ℕ) : Prop :=
  HintQueue.decode? (HintQueue.ofList source.io.hints).1 head = some target.io.hints ∧
    outgoing source target target.io.hints = target

/-- Finite validation of the suffix bytes and every preserved host field. -/
def check (source target : HostState) (head : ℕ) : Bool :=
  (HintQueue.decode? (HintQueue.ofList source.io.hints).1 head == some target.io.hints) &&
    (outgoing source target target.io.hints == target)

/-- The executable check is equivalent to exact byte and state equality. -/
theorem check_iff (source target : HostState) (head : ℕ) :
    check source target head = true ↔ Spec source target head := by
  simp only [check, Spec, Bool.and_eq_true, beq_iff_eq]

/-- Removing an ordered prefix supplies the exact head and bytes required by the verifier. -/
theorem spec_of_suffix (source target : HostState) (consumed : List Bytes)
    (queue : source.io.hints = consumed ++ target.io.hints)
    (frame : outgoing source target target.io.hints = target) :
    Spec source target target.io.hints.length := by
  exact ⟨queue ▸ HintQueue.decode_suffix consumed target.io.hints, frame⟩

/-- Any suffix read at this authenticated cursor gives the supplied outgoing host. -/
theorem Spec.outgoing_eq {source target : HostState} {head : ℕ} (spec : Spec source target head)
    {hints : List Bytes} (decoded : HintQueue.decode? (HintQueue.ofList source.io.hints).1 head = some hints) :
    outgoing source target hints = target := by
  rw [Option.some.inj (decoded.symm.trans spec.1)]
  exact spec.2

end SP1Clean.HostHintTarget
