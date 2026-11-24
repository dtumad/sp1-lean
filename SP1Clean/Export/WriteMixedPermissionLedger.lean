import SP1Clean.Export.WriteMixedFixedResources
import SP1Clean.Proofs.Completeness.HintPermissionLedger
import SP1Clean.Proofs.Completeness.StorePermissionLedger

/-! # The original permission guard funds all six physical byte-writing clients

The four generated STORE tables and the two HINT_READ word tables share one ordered multiset
of byte addresses with the generated permission guard. Each signed contribution comes from the
actual native table at its physical layout and demand-rounded height.
-/

namespace SP1Clean.Export.WriteMixedPermissionLedger

open Circuit Air.Flat Semantics Soundness TraceGen FormalModel.Shard Machine WritePermissionProvider
open WriteProbe.AccessInventory WriteSourceRegistry
open WriteMixedSourceTables

private abbrev F := ZMod SP1Prime

/-- The four original registry positions that request a byte permission during an ordinary step. -/
def stores : List InstructionChipId := [.storeByte,.storeHalf,.storeWord,.storeDouble]

private theorem balance_collect {α : Type} (xs : List α) (lhs rhs : α → List (Interaction F)) (msg : Array F)
    (same : ∀ x ∈ xs, balanceOf (lhs x) msg = balanceOf (rhs x) msg) :
    balanceOf (xs.flatMap lhs) msg = balanceOf (xs.flatMap rhs) msg := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    rw [List.flatMap_cons,List.flatMap_cons,balanceOf_append,balanceOf_append,same x List.mem_cons_self,
      ih (fun y used => same y (List.mem_cons_of_mem x used))]

private theorem only_stores (b : EventBuckets) :
    InstructionChipId.all.flatMap (fun id => (b id).flatMap (fun e => StorePermissionRows.requests ⟨id,e⟩)) =
      stores.flatMap (fun id => (b id).flatMap (fun e => StorePermissionRows.requests ⟨id,e⟩)) := by
  have quiet {α : Type} (xs : List α) : xs.flatMap (fun _ => ([] : List (Interaction F))) = [] :=
    List.flatMap_eq_nil_iff.mpr (fun _ _ => rfl)
  simp [InstructionChipId.all,stores,StorePermissionRows.requests,RoutedEvent.storeBytes,RoutedEvent.storeSpan?,quiet]

private theorem mixed_requests (rows : List MixedCompiledRow) :
    (rows.filterMap MixedCompiledRow.ordinaryObservation?).flatMap StorePermissionRows.requests =
      ((rows.flatMap MixedPermissionDemand.store).map (Address.ofNat (p := SP1Prime))).map channel.pulledValue := by
  induction rows with
  | nil => rfl
  | cons r rest ih =>
    cases r <;> simp [MixedCompiledRow.ordinaryObservation?,MixedPermissionDemand.store,
      StorePermissionRows.requests,List.filterMap_cons,ih]

variable {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : ReleaseAdmissibleExecution (.native SP1Prime) SP1Prime image source target events)
    {rows : List MixedCompiledRow}
    (routed : routeMixedRows? (policy SP1Prime image) image.program AccessFrontier.initial source.realize events = some rows)
    (data : ProverData F) (hint : ProverHint F) (packets : List WriteObservations.Packet)

private theorem ordinary_sum (msg : Array F) :
    balanceOf (stores.flatMap (fun id => (compiledSource run routed data hint packets (.ordinary id)).interactionsWith channel.toRaw)) msg =
      balanceOf (((rows.flatMap MixedPermissionDemand.store).map (Address.ofNat (p := SP1Prime))).map channel.pulledValue) msg := by
  obtain ⟨ordinary, seen, _, ready⟩ := releaseAdmissibleExecution_instructionBuckets run
  rw [routeObservations?,routed,Option.map_some] at seen
  cases Option.some.inj seen
  let es := rows.filterMap MixedCompiledRow.ordinaryObservation?
  let b := EventBuckets.ofChronological es
  have sums := balance_collect stores _ (fun id => (b id).flatMap (fun e => StorePermissionRows.requests ⟨id,e⟩)) msg
    (fun id _ => StorePermissionRows.table_sum id (bucket rows id) (ready id).2 data hint ((heights run routed).ordinary id) msg)
  change balanceOf (stores.flatMap fun id => (InstalledInstructionTables.table id (bucket rows id) data hint _).interactionsWith channel.toRaw) msg = _ at sums
  rw [← only_stores b] at sums
  have physical := (EventBuckets.physical_perm es).flatMap_right StorePermissionRows.requests
  rw [mixed_requests rows] at physical
  exact sums.trans (balanceOf_perm (message := msg) (by simpa only [EventBuckets.physical,List.flatMap_assoc,List.flatMap_map,Function.comp_def] using physical))

/-- The signed permission ledger on the physical guard, four ordinary stores and two HINT_READ
word tables balances for every released execution, with repeated keys and all padding counted. -/
theorem generated :
    let sources := compiledSource run routed data hint packets
    let guard := MixedPermissionDemand.guardTable run.1 routed data
    LogUpBalanced (guard.interactionsWith channel.toRaw ++
      stores.flatMap (fun id => (sources (.ordinary id)).interactionsWith channel.toRaw) ++
      (sources (.host (.word false))).interactionsWith channel.toRaw ++ (sources (.host (.word true))).interactionsWith channel.toRaw) := by
  intro sources guard msg
  have positives := PermissionTables.byte_sum image (MixedPermissionDemand.bytes events rows) data (MixedPermissionDemand.fit run.1 routed) msg
  have ordinary := ordinary_sum run routed data hint packets msg
  have words := MixedPermissionDemand.hint_sum run.1 data ((heights run routed).hint false) ((heights run routed).hint true) msg
  let keys := (MixedPermissionDemand.bytes events rows).map (Address.ofNat (p := SP1Prime))
  have matched := (channel.balanced_unit_iff keys keys).mpr List.Perm.rfl
  have paid := matched.logUp_of_isBool (by
    intro i present
    rcases List.mem_append.mp present with p | p <;>
      obtain ⟨_,_,rfl⟩ := List.mem_map.mp p <;> exact Or.inr rfl) msg
  rw [balanceOf_append] at paid
  change balanceOf (guard.interactionsWith channel.toRaw) msg = _ at positives
  change balanceOf ((sources (.host (.word false))).interactionsWith channel.toRaw) msg +
    balanceOf ((sources (.host (.word true))).interactionsWith channel.toRaw) msg = _ at words
  simp only [keys,MixedPermissionDemand.bytes,List.map_append,balanceOf_append] at paid
  simp only [balanceOf_append]
  rw [positives,ordinary]
  simp only [MixedPermissionDemand.bytes,List.map_append,balanceOf_append]
  linear_combination paid + words

end SP1Clean.Export.WriteMixedPermissionLedger
