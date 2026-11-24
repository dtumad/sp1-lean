import SP1Clean.Semantics.Host.WriteStreamRecords
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

/-- The fixed inventory is checked together with the prefix/suffix relation. -/
def boundaryOK (source target : HostState) : Bool :=
  WriteStreams.check source target && inventoryOK (WriteStreams.fromEndpoints source target)

def boundarySpec (source target : HostState) : Prop :=
  (WriteStreams.fromEndpoints source target).Binds source target ∧ inventoryOK (WriteStreams.fromEndpoints source target) = true

theorem boundaryOK_iff (source target : HostState) : boundaryOK source target = true ↔ boundarySpec source target := by
  simp [boundaryOK, boundarySpec, WriteStreams.check_iff]

def boundaryMain (source target : HostState) (_ : Var SP1PublicIO (ZMod p)) : Circuit (ZMod p) Unit :=
  assertZero (.const (if boundaryOK source target then 0 else 1))

/-- One public assertion binds output prefixes, consumed supplied replies, and the request journal. -/
def boundaryCircuit (source target : HostState) : GeneralFormalCircuit (ZMod p) SP1PublicIO unit where
  main := boundaryMain source target
  Spec _ _ _ := boundarySpec source target
  ProverAssumptions _ _ _ := boundarySpec source target
  soundness := by
    circuit_proof_start [boundaryMain]
    by_cases h : boundaryOK source target = true
    · exact (boundaryOK_iff ..).mp h
    · simp [h] at h_holds
  completeness := by
    circuit_proof_start [boundaryMain]
    simp [(boundaryOK_iff ..).mpr h_assumptions]

/-- Installable public checker on the complete source and target host snapshots. -/
def checker (source target : HostState) : PublicVerifier (ZMod p) SP1PublicIO where
  name := "write_streams"
  circuit := boundaryCircuit source target
  assumptions := by intros; trivial
  length_zero := by intros; rfl
  lookups := by intros; rfl
  interactions := by intros; rfl

@[simp] theorem checker_checks (source target : HostState) (io : SP1PublicIO (ZMod p)) (data : ProverData (ZMod p)) :
    (checker source target).Checks io data ↔ boundarySpec source target := by
  by_cases valid : boundaryOK source target = true <;>
    simp [PublicVerifier.Checks, checker, boundaryCircuit, boundaryMain, circuit_norm, seval,
      ← boundaryOK_iff, valid]

end SP1Clean.WriteEffects
