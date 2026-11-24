import SP1Clean.Proofs.Completeness.HintReadCapacity
import SP1Clean.Soundness.HostCallReceivers
import SP1Clean.Math.SP1Field

/-! # Padding cannot be treated as an active hint syscall

Clean's demand generator rounds a bucket of three distinct syscall messages to four rows.
The native active HINT_LEN and HINT_READ implementations check a nonzero opcode in their
first constraint. An all-zero padding input therefore requires an explicit inactive guard.
-/

namespace SP1Clean.TraceGen.HintHandlerPadding
open Circuit Air.Flat
private abbrev F := ZMod SP1Prime

/-- Three distinct active calls in one Clean demand bucket require one additional physical row. -/
theorem three_calls : WitnessGeneration.demandHeight 3 - 3 = 1 := by decide

/-- Clean appends a physical row to each of these registered handler tables when its three actual
calls have been placed. Both length routes are covered. -/
theorem installed_three_calls (state : WitnessGeneration.ComponentState F)
    (handler : state.component = Soundness.HostHintReadCoverage.handler ∨
        ∃ empty, state.component = (Soundness.HostCallReceivers.hintLength empty).component)
    (three : state.rows.size = 3) : state.targetHeight - state.rows.size = 1 := by
  have demand : state.targetHeight = WitnessGeneration.demandHeight state.rows.size := by
    cases state with
    | mk component multiplicity operations interactions rows messageRows =>
      rcases handler with h | ⟨empty,h⟩ <;> change component = _ at h <;> subst component <;>
        exact WitnessGeneration.ComponentState.targetHeight_of_demand _ rfl
  rw [demand,three]
  exact three_calls

/-- Three successive HINT_LEN calls preserve the queue, for either the empty or occupied arm.
The host dispatcher places no power-of-two restriction on the number of calls. -/
theorem three_length_effects (host : Semantics.HostState) (policy : Semantics.HostPolicy)
    (context : Semantics.HostReadContext) :
    ([0,1,2].foldlM (m := Option) (fun (held : Semantics.HostState) (_ : Nat) =>
      Semantics.HostEffect.state <$> held.executeKind policy context .hintLength 0 0) host) = some host := rfl

/-- The first physical constraint of the active HINT_READ rejects a padding row, for every completion
of its auxiliary columns. -/
theorem read_zero_rejected (r : Var HostHintReadChip.Inputs F) (offset : Nat) (env : Environment F)
    (zero : r.call.code[0].eval env = 0) : ¬ ((HostHintReadChip.main r).operations offset).ConstraintsHold env := by
  intro valid
  have first : ((HostHintReadChip.main r).operations offset).constraints[0]? = some (r.call.code[0] - (Expression.const 241 : Expression F)) := by
    simp only [HostHintReadChip.main,circuit_norm,FormalAssertion.toSubcircuit_toFlat,Gadgets.Equality.circuit,Gadgets.Equality.main,Operations.constraints,ProvableType.toElements_fields,Vector.getElem_map,List.ofFn_succ,Vector.getElem_zip,List.getElem?_cons_zero,List.cons_append,List.nil_append]
    congr 3
  have eq := valid.1 _ (List.mem_of_getElem? first)
  dsimp only at eq
  rw [eval_sub,zero] at eq
  exact (by decide : (0 : F) - 241 ≠ 0) eq

/-- Both active HINT_LEN variants reject an all-zero padding input in exactly the same way. -/
theorem length_zero_rejected (empty : Bool) (r : Var HostHintLengthChip.Inputs F) (offset : Nat) (env : Environment F)
    (zero : r.call.code[0].eval env = 0) : ¬ ((HostHintLengthChip.main empty r).operations offset).ConstraintsHold env := by
  intro valid
  have first : ((HostHintLengthChip.main empty r).operations offset).constraints[0]? = some (r.call.code[0] - (Expression.const 240 : Expression F)) := by
    cases empty <;> simp only [HostHintLengthChip.main,circuit_norm,FormalAssertion.toSubcircuit_toFlat,Gadgets.Equality.circuit,Gadgets.Equality.main,Operations.constraints,ProvableType.toElements_fields,Vector.getElem_map,List.ofFn_succ,Vector.getElem_zip,List.getElem?_cons_zero,List.cons_append,List.nil_append] <;> congr 3
  have eq := valid.1 _ (List.mem_of_getElem? first)
  dsimp only at eq
  rw [eval_sub,zero] at eq
  exact (by decide : (0 : F) - 240 ≠ 0) eq

end SP1Clean.TraceGen.HintHandlerPadding
