import SP1Clean.Proofs.Completeness.MixedSyscallTable
import SP1Clean.Proofs.Completeness.MixedHaltPadding
import SP1Clean.Math.WordEquality

/-! # Signed Exit emissions from genuine mixed syscall instructions -/

namespace SP1Clean.TraceGen.MixedExitDemand
open Circuit Air.Flat Channels Semantics Soundness Machine FormalModel.Shard
private abbrev F := ZMod SP1Prime

/-- The actual gate and reduced x10 value emitted by each original ECALL row. -/
def emit (r : SyscallInstrsChip.Inputs F) : Interaction F :=
  exitChannel.pushedIfValue r.is_halt (SyscallInstrsChip.exitMessage r)

/-- The single verifier-visible exit word corresponding to a successful HALT. -/
def push (code : BitVec 32) : Interaction F := exitChannel.pushedValue ⟨(code.toNat : F)⟩

private theorem inactive (r : SyscallInstrsChip.Inputs F) (off : r.is_halt = 0) (msg : Array F) :
    balanceOf [emit r] msg = 0 := by
  rw [balanceOf_cons]
  simp [emit,off,Interaction.signedMult,Channel.pushedIfValue,balanceOf]

private theorem contribution {image : ProgramImage} {s t : ExecutionState} {call : CoreSyscallEvent}
    (step : ExecutionStep (policy SP1Prime image) image.program s (.syscall call) t) (frontier : AccessFrontier) (msg : Array F) :
    balanceOf [emit (syscallInstruction frontier call)] msg = balanceOf ((hostExitAfter none (.syscall call)).toList.map push) msg := by
  have canonical : ∃ k : SyscallKind, call.rawCode = k.code := by
    cases step with
    | syscall success =>
      obtain ⟨_,exec,_,_,_,_,_,rfl⟩ := HostState.step_observations success
      exact ⟨exec.kind,rfl⟩
  have selector : call.syscallId = haltSyscallId ↔ call.rawCode = 0 := by
    obtain ⟨k,law⟩ := canonical
    change call.rawCode.toNat % 256 = 0 ↔ _
    rw [law]
    cases k <;> decide
  let r := syscallInstruction (p := SP1Prime) frontier call
  have gate : r.is_halt = (if call.syscallId = haltSyscallId then 1 else 0) := rfl
  by_cases zero : call.rawCode = 0
  · have small := (step.halt_bounds zero).2
    have word : r.op_b_memory.prev_value = wordOfNat call.arg1.toNat := rfl
    have value : SyscallInstrsChip.exitMessage r = ⟨((call.arg1.setWidth 32).toNat : F)⟩ := by
      unfold SyscallInstrsChip.exitMessage
      rw [word,Word.reduce_eq_toBitVec64 _ (wordOfNat_isU64 _),toBitVec64_wordOfNat,BitVec.ofNat_toNat,BitVec.setWidth_eq,BitVec.toNat_setWidth,
        Nat.mod_eq_of_lt small]
    change balanceOf [exitChannel.pushedIfValue r.is_halt (SyscallInstrsChip.exitMessage r)] msg = _
    rw [gate,ite_eq_left (selector.mpr zero),value]
    simp only [hostExitAfter,show SyscallKind.halt.code = 0 from rfl,zero,↓reduceIte,Option.toList_some,List.map_cons,List.map_nil]
    rfl
  · have off : r.is_halt = 0 := gate.trans (ite_eq_right (fun h => zero (selector.mp h)))
    rw [inactive r off]
    have nonhalt : call.rawCode ≠ SyscallKind.halt.code := zero
    rw [hostExitAfter,ite_eq_right nonhalt]
    rfl

private def row (c : MixedCompiledRow) : List (Interaction F) := (c.syscallInput? (p := SP1Prime)).toList.map emit
private def event (e : ExecutionEvent) : List (Interaction F) := (hostExitAfter none e).toList.map push

/-- All generated physical ECALL rows contribute exactly the new terminal word on the
complete event tape. The ECALL shape padding remains physically present with zero weight. -/
theorem signed {limits : ResourceLimits} {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution limits SP1Prime image source target events) {compiled : List MixedCompiledRow}
    (routed : routeMixedRows? (policy SP1Prime image) image.program AccessFrontier.initial source.realize events = some compiled) (msg : Array F) :
    balanceOf ((MixedSyscallTable.inputs compiled).map emit) msg = balanceOf ((events.filterMap (hostExitAfter none)).map push) msg := by
  obtain ⟨_,rr,length⟩ := admissibleExecution_routeMixedRows run
  cases Option.some.inj (rr.symm.trans routed)
  have paired : List.Forall₂ (fun e c => balanceOf (row c) msg = balanceOf (event e) msg) events compiled := by
    apply List.forall₂_of_length_eq_of_get length.symm
    intro cut e c
    change balanceOf (row compiled[cut]) msg = balanceOf (event events[cut]) msg
    have atCut := List.getElem?_eq_getElem e
    cases kind : events[cut] with
    | ordinary =>
      rw [kind] at atCut
      obtain ⟨_,_,_,_,_,_,actual,_,_,rc⟩ := routeMixedRows?_at routed atCut
      rw [(List.getElem?_eq_some_iff.mp rc).2]
      rfl
    | syscall call =>
      rw [kind] at atCut
      obtain ⟨_,frontier,_,_,_,rc⟩ := routeMixedRows?_at routed atCut
      obtain ⟨_,_,_,_,_,step,_⟩ := admissibleExecution_syscall_from_prefix run atCut
      rw [(List.getElem?_eq_some_iff.mp rc).2]
      exact contribution step frontier msg
  have sums {es : List ExecutionEvent} {cs : List MixedCompiledRow}
      (pairs : List.Forall₂ (fun e c => balanceOf (row c) msg = balanceOf (event e) msg) es cs) :
      balanceOf (cs.flatMap row) msg = balanceOf (es.flatMap event) msg := by
    induction pairs with
    | nil => rfl
    | cons eq _ ih => rw [List.flatMap_cons,List.flatMap_cons,balanceOf_append,balanceOf_append,eq,ih]
  have padding (n : ℕ) : balanceOf ((List.replicate n MixedSyscallTable.padding).map emit) msg = 0 := by
    induction n with
    | zero => rfl
    | succ _ ih =>
      rw [List.replicate_succ,List.map_cons,← List.singleton_append,balanceOf_append,inactive _ rfl,ih,add_zero]
  rw [MixedSyscallTable.inputs,List.map_append,balanceOf_append,padding,add_zero]
  simp only [List.filterMap_eq_flatMap_toList,List.map_flatMap]
  exact sums paired

end SP1Clean.TraceGen.MixedExitDemand
