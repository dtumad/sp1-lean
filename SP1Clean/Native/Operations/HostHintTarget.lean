import SP1Clean.FormalModel.Contracts.HostHintTarget
import SP1Clean.FormalModel.Contracts.PublicValues
import ToClean.Air.PublicVerifier

/-! # Verifier-owned target hint suffix and host frame

The snapshots and terminal pointer are fixed instance data. A single checked constant binds
their finite comparison in the public verifier.
-/

namespace SP1Clean.HostHintTarget

open Air.Flat Circuit Semantics

variable {p : ℕ} [Fact p.Prime]

/-- Assert the finite host comparison for the verifier-owned endpoint. -/
def main (source target : HostState) (head : ℕ) (_ : Var SP1PublicIO (ZMod p)) : Circuit (ZMod p) Unit :=
  assertZero (.const (if check source target head then 0 else 1))

/-- Bundled soundness and completeness of the fixed comparison. -/
def circuit (source target : HostState) (head : ℕ) : GeneralFormalCircuit (ZMod p) SP1PublicIO unit where
  main := main source target head
  Spec _ _ _ := Spec source target head
  ProverAssumptions _ _ _ := Spec source target head
  soundness := by
    circuit_proof_start [main]
    by_cases valid : check source target head = true
    · exact (check_iff ..).mp valid
    · simp [valid] at h_holds
  completeness := by
    circuit_proof_start [main]
    simp [(check_iff ..).mpr h_assumptions]

/-- One verifier assertion with a dedicated balance channel. -/
def checker (source target : HostState) (head : ℕ) : PublicVerifier (ZMod p) SP1PublicIO where
  name := "host_hint_target"
  circuit := circuit source target head
  assumptions := by intros; trivial
  length_zero := by intros; rfl
  lookups := by intros; rfl
  interactions := by intros; rfl

/-- The verifier contributes two occurrences on its assertion channel. -/
theorem count_bound [Fact (2 ^ 25 < p)] (source target : HostState) (head : ℕ) :
    (checker (p := p) source target head).CountBound := by
  change 2 * 1 < ringChar (ZMod p)
  rw [ZMod.ringChar_zmod_n]
  have := Fact.out (p := 2 ^ 25 < p)
  omega

/-- Raw verifier checks authenticate the full outgoing host frame at this queue head. -/
theorem checks_iff (source target : HostState) (head : ℕ) (header : SP1PublicIO (ZMod p))
    (data : ProverData (ZMod p)) : (checker source target head).Checks header data ↔ Spec source target head := by
  by_cases valid : check source target head = true <;>
    simp [PublicVerifier.Checks, checker, circuit, main, circuit_norm, seval,
      ← check_iff, valid]

end SP1Clean.HostHintTarget
