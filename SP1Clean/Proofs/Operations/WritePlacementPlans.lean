import SP1Clean.Proofs.Operations.WriteGroup
import SP1Clean.Math.SP1Field

/-! # The exact slice plan request of each actual WRITE placement -/

namespace SP1Clean.WriteEffects
open Circuit Air.Flat
open scoped Classical
private abbrev F := ZMod SP1Prime

/-- A physical placement asks for precisely its lane selection plan with its original row
activity. This includes ignored groups and zero-length windows. -/
theorem group_plan_at (env : Environment F) :
    let r := valueFromOffset (ProvablePair Group field) 0 env
    (groupComponent (p := SP1Prime)).operations.interactionValuesWith sliceChannel.toRaw env =
      [sliceChannel.pulledIfValue r.2 r.1.plan] := by
  let I := ProvablePair Group field
  let input := varFromOffset I (F := F) 0
  rw [Operations.interactionValuesWith,Component.interactionsWith_eq]
  change ((Guarded.main groupCircuit groupGuardSupported input).operations (size I)).interactionValuesWith _ env = _
  rw [Guarded.main_interactionValuesWith]
  change (((groupMain input.1).operations (size I)).interactionValuesWith _ env).map _ = _
  have raw : ((groupMain input.1).operations (size I)).interactionsWith sliceChannel.toRaw =
      [(sliceChannel.pulled input.1.plan).toRaw] := by
    rw [Operations.interactionsWith,group_ledger]
    simp [octetsChannel,sliceChannel,positionChannel,blockChannel,circuit_norm]
  rw [Operations.interactionValuesWith,raw]
  have fit (r : Var I F) : eval env r.1.plan = (eval env r).1.plan := by simp only [I,circuit_norm]
  simp only [List.map_cons,List.map_nil,Channel.eval_pulled,Channel.pulledValue,Channel.pulledIfValue,mul_one,
    Guarded.eval_activity,fit,input,I,eval_varFromOffset_valueFromOffset]

end SP1Clean.WriteEffects
