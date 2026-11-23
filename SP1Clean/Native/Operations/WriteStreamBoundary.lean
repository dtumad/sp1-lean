import SP1Clean.Semantics.Host.WriteEffects
import SP1Clean.FormalModel.Contracts.PublicValues
import ToClean.Air.PublicVerifier

/-! # Verifier binding for the ordered WRITE endpoints

The verifier checks the original prefixes and the unconsumed hook reply suffix. The derived
local byte and reply inventories depend solely on these snapshots. Their use at individual
packet clocks is handled by the physical effect tables.
-/

namespace SP1Clean.WriteEffects
open Circuit Air.Flat Semantics

variable {p : ℕ} [Fact p.Prime]

def boundaryMain (source target : HostState) (_ : Var SP1PublicIO (ZMod p)) : Circuit (ZMod p) Unit :=
  assertZero (.const (if WriteStreams.check source target then 0 else 1))

/-- One public assertion binds output prefixes, consumed supplied replies, and the request journal. -/
def boundaryCircuit (source target : HostState) : GeneralFormalCircuit (ZMod p) SP1PublicIO unit where
  main := boundaryMain source target
  Spec _ _ _ := (WriteStreams.fromEndpoints source target).Binds source target
  ProverAssumptions _ _ _ := (WriteStreams.fromEndpoints source target).Binds source target
  soundness := by
    circuit_proof_start [boundaryMain]
    by_cases h : WriteStreams.check source target = true
    · exact (WriteStreams.check_iff ..).mp h
    · simp [h] at h_holds
  completeness := by
    circuit_proof_start [boundaryMain]
    simp [(WriteStreams.check_iff ..).mpr h_assumptions]

/-- Installable public checker on the complete source and target host snapshots. -/
def checker (source target : HostState) : PublicVerifier (ZMod p) SP1PublicIO where
  name := "write_streams"
  circuit := boundaryCircuit source target
  assumptions := by intros; trivial
  length_zero := by intros; rfl
  lookups := by intros; rfl
  interactions := by intros; rfl

@[simp] theorem checker_checks (source target : HostState) (io : SP1PublicIO (ZMod p)) (data : ProverData (ZMod p)) :
    (checker source target).Checks io data ↔ (WriteStreams.fromEndpoints source target).Binds source target := by
  by_cases valid : WriteStreams.check source target = true <;>
    simp [PublicVerifier.Checks, checker, boundaryCircuit, boundaryMain, circuit_norm, seval,
      ← WriteStreams.check_iff, valid]

end SP1Clean.WriteEffects
