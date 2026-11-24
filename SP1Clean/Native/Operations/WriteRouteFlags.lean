import SP1Clean.FormalModel.Contracts.WriteChronology
import Clean.Gadgets.IsZeroField

/-! # Classification gates for the chronological WRITE receiver

Each explicit gate is the field equality to its released dispatch tag. The authenticated
classifier maps every remaining recognized tag to one of the seven hooks.
-/

namespace SP1Clean.WriteEffects
open Circuit

variable {p : Nat} [Fact p.Prime]

/-- Field-valued equality indicator between a route and one explicit tag. -/
def flagValue (route tag : ZMod p) : ZMod p := if route = tag then 1 else 0

/-- Select the ignored, standard output, standard error, public output and direct-hint routes. -/
def flagsFor (route : ZMod p) : DispatchFlags (ZMod p) :=
  ⟨flagValue route 0, flagValue route 1, flagValue route 2, flagValue route 13, flagValue route 14⟩

/-- Compute the five route selectors with zero tests against their fixed tags. -/
def flagsMain (r : Expression (ZMod p)) : Circuit (ZMod p) (Var DispatchFlags (ZMod p)) := do
  let ignored ← Gadgets.IsZeroField.circuit r
  let stdout ← Gadgets.IsZeroField.circuit (r - 1)
  let stderr ← Gadgets.IsZeroField.circuit (r - 2)
  let output ← Gadgets.IsZeroField.circuit (r - 13)
  let direct ← Gadgets.IsZeroField.circuit (r - 14)
  return ⟨ignored, stdout, stderr, output, direct⟩

instance flagsElaborated : ElaboratedCircuit (ZMod p) field DispatchFlags flagsMain := by elaborate_circuit

/-- Formal circuit returning the exact selectors for a classified route. -/
def flagsCircuit : GeneralFormalCircuit (ZMod p) field DispatchFlags where
  main := flagsMain
  elaborated := flagsElaborated
  computableWitnesses := by computable_witnesses
  Spec r g _ := g = flagsFor r
  soundness := by
    circuit_proof_start [flagsMain, Gadgets.IsZeroField.circuit]
    obtain ⟨i, o, e, v, d⟩ := h_holds
    simp only [flagsFor, flagValue, sub_eq_zero] at *
    simp only [i, o, e, v, d]
  completeness := by circuit_proof_start [flagsMain, Gadgets.IsZeroField.circuit]

/-- At most one of the five special routes is active. Every remaining tag is a hook. -/
theorem flagsFor_choices [Fact (2^17 < p)] (r : ZMod p) :
    (flagsFor r, (flagsFor r).hook) ∈
      [(⟨1,0,0,0,0⟩,0), (⟨0,1,0,0,0⟩,0), (⟨0,0,1,0,0⟩,0), (⟨0,0,0,1,0⟩,0),
       (⟨0,0,0,0,1⟩,0), (⟨0,0,0,0,0⟩,1)] := by
  have hp : 2^17 < p := Fact.out
  have scalar (a : Nat) (small : a ≤ 14) : r = (a : ZMod p) ↔ r.val = a := by
    have eq := ZMod.val_natCast_of_lt (show a < p by omega)
    exact ⟨fun h => (congrArg ZMod.val h).trans eq, fun h => ZMod.val_injective p (h.trans eq.symm)⟩
  have z : r = 0 ↔ r.val = 0 := by simpa only [Nat.cast_zero] using scalar 0 (by decide)
  have o : r = 1 ↔ r.val = 1 := by simpa only [Nat.cast_one] using scalar 1 (by decide)
  have two : r = 2 ↔ r.val = 2 := scalar 2 (by decide)
  have values : r = 13 ↔ r.val = 13 := scalar 13 (by decide)
  have hint : r = 14 ↔ r.val = 14 := scalar 14 (by decide)
  simp only [flagsFor, flagValue, DispatchFlags.hook, z, o, two, values, hint]
  by_cases i : r.val = 0
  · simp [i]
  by_cases s : r.val = 1
  · simp [s]
  by_cases e : r.val = 2
  · simp [e]
  by_cases v : r.val = 13
  · simp [v]
  by_cases d : r.val = 14
  · simp [d]
  simp [i,s,e,v,d]

@[circuit_norm, computable_witnesses] theorem eval_flags_hook (env : Environment (ZMod p)) (g : Var DispatchFlags (ZMod p)) :
    g.hook.eval env = (eval env g).hook := by simp only [DispatchFlags.hook, circuit_norm]

end SP1Clean.WriteEffects
