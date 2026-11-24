import SP1Clean.Proofs.Completeness.HintReadLedger
import SP1Clean.Proofs.Completeness.MixedPermissionDemand

/-! # Physical HINT_READ permission pulls at the exact emitted byte addresses

The two original word tables retain eight occurrences per padded physical row. Their signed
sum pays for exactly the guest bytes of successful reads, including every mandatory final word.
-/

namespace SP1Clean.TraceGen.MixedPermissionDemand

open Circuit Air.Flat Semantics Machine FormalModel.Shard HintQueue HintReadWordChip HintReadTransfers

private abbrev F := ZMod SP1Prime
private abbrev Entry := Bool × RowInput F

private def wordAddresses (r : RowInput F) := List.ofFn (fun i : Fin 8 => Address.offset r.1.address (i.val : F))
private def permissionValues (r : RowInput F) : List (Interaction F) :=
  (wordAddresses r).map (WritePermissionProvider.channel.pulledIfValue r.2)

private theorem byteRanges (start n : ℕ) :
    (List.range n).flatMap (fun i => List.range' (start + i * 8) 8) = List.range' start (8*n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, ih, Nat.mul_succ 8 n]
    simpa only [Nat.one_mul,Nat.mul_comm n 8] using (List.range'_append (s := start) (m := 8*n) (n := 8) (step := 1))

private theorem row_addresses (address : ℕ) (aligned : address % 8 = 0) :
    List.ofFn (fun i : Fin 8 => Address.offset (Address.ofNat (p := SP1Prime) address) (i.val : F)) =
      (List.range' address 8).map (Address.ofNat (p := SP1Prime)) := by
  apply List.ext_getElem
  · simp
  intro i lhs _
  have small : i < 8 := by simpa using lhs
  simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range', Nat.one_mul]
  exact Address.offset_ofNat _ _ (by omega)

private theorem request_addresses (req : Request) (frontier : AccessFrontier) (sail : SailState)
    (aligned : req.address % 8 = 0) :
    (req.rows frontier sail).flatMap (fun e => wordAddresses e.2) =
      (List.range' req.address (8 * wordCount req.bytes)).map (Address.ofNat (p := SP1Prime)) := by
  rw [← byteRanges,List.map_flatMap,Request.rows,List.flatMap_map]
  apply List.flatMap_congr
  intro i _
  exact row_addresses (req.destination i) (by unfold Request.destination; omega)

private theorem batch_addresses {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events) {i : ℕ} {e : ExecutionEvent}
    (atEvent : events[i]? = some e) :
    ((rowsAt? image source events i).getD []).flatMap (fun e => wordAddresses e.2) =
      (hint e).map (Address.ofNat (p := SP1Prime)) := by
  cases e with
  | ordinary => simp [rowsAt?,atEvent,hint]
  | syscall call =>
    by_cases read : call.rawCode = SyscallKind.hintRead.code
    · obtain ⟨current,_,frontier,cursor,_,payload,_,_,built,_,store,_,node,_,_,_,size,_,span,_⟩ :=
        of_admissibleExecution run atEvent read
      let req : Request := ⟨call.clock,cursor.2,call.arg1.toNat,payload⟩
      simpa [rowsAt?,atEvent,read,built,store,node,req,hint,wordCount,size] using
        request_addresses req frontier current.sail span.2.1
    · simp [rowsAt?,atEvent,read,hint]

/-- All actual active word-row addresses in order are the full concrete host write footprint. -/
theorem hint_addresses {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events) :
    (history image source events).flatMap (fun e => wordAddresses e.2) =
      (events.flatMap hint).map (Address.ofNat (p := SP1Prime)) := by
  rw [history,List.flatMap_assoc,List.map_flatMap]
  conv_rhs => rw [← List.map_getElem_finRange events,List.flatMap_map]
  exact List.flatMap_congr (fun i _ => batch_addresses run (List.getElem?_eq_getElem i.isLt))

private theorem values_off (msg : Array F) : balanceOf (permissionValues 0) msg = 0 := by
  let addrs := wordAddresses (0 : RowInput F)
  change balanceOf (addrs.map (WritePermissionProvider.channel.pulledIfValue 0)) msg = 0
  induction addrs with
  | nil => rfl
  | cons a rest ih =>
    rw [List.map_cons,balanceOf_cons,ih,add_zero]
    simp [Channel.pulledIfValue,Interaction.signedMult]

/-- The signed permission balance of both actual physical word clients, at each complete payload key. -/
theorem hint_sum {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events) (data : ProverData F) (next last)
    (msg : Array F) :
    let es := history image source events
    balanceOf ((wordTable false es data next).interactionsWith WritePermissionProvider.channel.toRaw) msg +
      balanceOf ((wordTable true es data last).interactionsWith WritePermissionProvider.channel.toRaw) msg =
      balanceOf (((events.flatMap hint).map (Address.ofNat (p := SP1Prime))).map WritePermissionProvider.channel.pulledValue) msg := by
  intro es
  have physical (kind : Bool) (height) : (wordTable kind es data height).interactionsWith WritePermissionProvider.channel.toRaw =
      (physicalInputs kind es).flatMap permissionValues := by
    rw [wordTable_permissions]
    apply List.flatMap_congr
    intro r _
    simp only [permissionValues,wordAddresses,List.map_ofFn,Function.comp_def]
  rw [physical,physical,physical_sum permissionValues es msg (values_off msg),← hint_addresses run,List.map_flatMap]
  apply congrArg (fun rs => balanceOf rs msg)
  apply List.flatMap_congr
  intro e inside
  exact congrArg (fun gate => (wordAddresses e.2).map (WritePermissionProvider.channel.pulledIfValue gate))
    (history_active run e inside)

end SP1Clean.TraceGen.MixedPermissionDemand
