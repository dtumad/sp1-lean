import SP1Clean.Proofs.Completeness.MixedCompiledRows
import SP1Clean.Proofs.Completeness.PermissionTables
import SP1Clean.Semantics.Resources.HintReadDemand
import SP1Clean.FormalModel.ShardPreservation
import SP1Clean.FormalModel.ShardResources

/-! # Byte-write demand of a complete mixed execution

The four protected stores retain their decoded width and effective address in the generated
instruction input. HINT_READ writes the complete padded span, including the final padding word.
All other instructions and host calls issue no byte-write permission.
-/

namespace SP1Clean.TraceGen.MixedPermissionDemand

open Circuit Air.Flat WitnessGeneration Semantics Soundness.Target Machine FormalModel.Shard

/-- Byte sequence of one original store input, including stores of unchanged bytes. -/
def store : MixedCompiledRow → List ℕ
  | .ordinary row => row.routed.storeBytes
  | .syscall .. => []

/-- Exact padded byte range requested from the released HINT_READ label. -/
def hint : ExecutionEvent → List ℕ
  | .ordinary => []
  | .syscall call => if call.rawCode = SyscallKind.hintRead.code then
      List.range' call.arg1.toNat (8 * (call.arg2.toNat / 8 + 1)) else []

/-- All active byte requests from both kinds of original physical client. -/
def bytes (events : List ExecutionEvent) (rows : List MixedCompiledRow) : List ℕ :=
  rows.flatMap store ++ events.flatMap hint

private theorem store_length (row : MixedCompiledRow) : (store row).length ≤ 8 := by
  cases row with
  | syscall => exact Nat.zero_le _
  | ordinary row =>
    obtain ⟨⟨id,e⟩,plan,schedule⟩ := row
    cases id <;> simp [store,RoutedEvent.storeBytes,RoutedEvent.storeSpan?]

private theorem stores_length (rows : List MixedCompiledRow) : (rows.flatMap store).length ≤ 8 * rows.length := by
  induction rows with
  | nil => simp
  | cons row tail ih =>
    simp only [List.flatMap_cons,List.length_append,List.length_cons]
    have := store_length row
    omega

private theorem hints_length (events : List ExecutionEvent) :
    (events.flatMap hint).length =
      8 * (HintReadDemand.continuing (events.filterMap HintReadDemand.length?) + (events.filterMap HintReadDemand.length?).length) := by
  induction events with
  | nil => rfl
  | cons e es ih =>
    cases e with
    | ordinary => simpa only [List.flatMap_cons, hint, List.nil_append, List.filterMap_cons, HintReadDemand.length?] using ih
    | syscall call =>
      by_cases read : call.rawCode = SyscallKind.hintRead.code <;>
        simp only [List.flatMap_cons, hint, read, ↓reduceIte, List.length_append, List.length_range', List.length_nil,
          List.filterMap_cons, HintReadDemand.length?, List.length_cons, HintReadDemand.continuing, List.map_cons, List.sum_cons] at * <;> omega

private theorem ordinary_avoids {program : GuestProgram} {located : LocatedTransition} {view : SP1TransitionView}
    {frontier : AccessFrontier} {clk : ℕ} {row : CompiledInstructionEvent} {span : MemorySpan}
    (projected : projectSP1Transition? program located = some view)
    (generated : compileInstructionEvent? view frontier clk = some row) (spanEq : row.routed.storeSpan? = some span)
    (configured : SailConfigured located.source) {mask : ℕ → Bool} (permitted : InstructionWrite.PermittedAt mask program located.source) :
    ByteMemory.Avoids mask span.address span.length := by
  obtain ⟨pc,word,decoded,atPc,fetched,decode,checked⟩ := permitted
  have found := decodeLocated?_eq_some_of (located := located) atPc fetched (decode _ configured)
  cases Option.some.inj (found.symm.trans (projectSP1Transition?_decode projected))
  exact compileInstructionEvent?_store_avoids projected generated checked spanEq

private theorem host_writable {image : ProgramImage} {before after : ExecutionState} {call : CoreSyscallEvent}
    (step : ExecutionStep (policy SP1Prime image) image.program before (.syscall call) after)
    {a : ℕ} (used : a ∈ hint (.syscall call)) : a < 2 ^ 48 ∧ image.readOnly a = false := by
  cases step with
  | syscall success =>
    obtain ⟨pc,exec,_,_,ran,_,_,rfl⟩ := HostState.step_observations success
    by_cases read : exec.kind = .hintRead
    · have effect := ((HostState.run_eq_some_iff ..).mp ran).2.2.2.2.2
      rw [read] at effect
      obtain ⟨payload,_,_,size,_,permitted,_⟩ := (HostState.execute_hintRead_iff ..).mp effect
      obtain ⟨_,upper,excludes⟩ := (HostMemoryPolicy.permits_iff ..).mp permitted
      simp only [hint, HostExecution.toEvent, read, ↓reduceIte, List.mem_range'_1] at used
      rw [hintWriteBytes_length, size] at upper excludes
      change _ ≤ 2 ^ 48 at upper
      exact ⟨by omega, by simpa only [Nat.add_sub_cancel' used.1, policy] using excludes (a - exec.arg1.toNat) (by omega)⟩
    · have other : exec.kind.code ≠ SyscallKind.hintRead.code := fun same => read (SyscallKind.code_injective same)
      simp [hint, HostExecution.toEvent, other] at used

variable {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events) {rows : List MixedCompiledRow}
    (routed : routeMixedRows? (policy SP1Prime image) image.program AccessFrontier.initial source.realize events = some rows)

include run routed in
/-- Each permission provider is justified by its real Sail STORE or the concrete HINT_READ effect. -/
theorem writable (a : ℕ) (used : a ∈ bytes events rows) : a < 2 ^ 48 ∧ image.readOnly a = false := by
  rcases List.mem_append.mp used with stores | hints
  · obtain ⟨r, listed, pulls⟩ := List.mem_flatMap.mp stores
    obtain ⟨cut,found⟩ := List.getElem?_of_mem listed
    obtain ⟨rs,same,len⟩ := admissibleExecution_routeMixedRows run
    cases Option.some.inj (same.symm.trans routed)
    have inEvents := (List.getElem?_eq_some_iff.mp found).1.trans_eq len
    have present := List.getElem?_eq_getElem inEvents
    cases tag : events[cut] with
    | ordinary =>
      rw [tag] at present
      obtain ⟨before,f,next,prefixAt,_,view,row,projected,generated,atRow⟩ := routeMixedRows?_at routed present
      cases Option.some.inj (atRow.symm.trans found)
      obtain ⟨span,fromRow,member⟩ := List.mem_flatMap.mp pulls
      have spanEq := Option.mem_toList.mp fromRow
      have window := List.mem_range'_1.mp member
      obtain ⟨actual,g,record,reached,_⟩ := admissibleExecution_mixedAccessPrefix run cut
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj (reached.symm.trans prefixAt))
      obtain ⟨s,t,prev,step⟩ := run.1.2.step_at present
      cases Option.some.inj (prev.symm.trans record)
      cases step with
      | ordinary _ _ _ permitted =>
        have cfg := (run.1.frame_prefix record).1
        have encoded := (run.2.1 _ _ _ present record).2 rfl
        have bounded := ordinary_avoids projected generated spanEq cfg encoded.outside_permission (a - span.address) (by omega)
        have allowed := ordinary_avoids projected generated spanEq cfg permitted (a - span.address) (by omega)
        simpa only [Nat.add_sub_cancel' window.1, decide_eq_false_iff_not, not_le, policy] using And.intro bounded allowed
    | syscall call =>
      rw [tag] at present
      obtain ⟨_,_,_,_,_,atRow⟩ := routeMixedRows?_at routed present
      cases Option.some.inj (atRow.symm.trans found)
      contradiction
  · obtain ⟨e,present,byte⟩ := List.mem_flatMap.mp hints
    obtain ⟨cut,atEvent⟩ := List.getElem?_of_mem present
    cases e with
    | ordinary => contradiction
    | syscall call =>
      obtain ⟨_,_,_,step⟩ := run.1.2.step_at atEvent
      exact host_writable step byte

include run routed in
/-- The independently rounded permission table fits Clean's physical row index. -/
theorem fit : demandHeight (bytes events rows).length ≤ UInt64.size := by
  obtain ⟨rs,same,len⟩ := admissibleExecution_routeMixedRows run
  cases Option.some.inj (same.symm.trans routed)
  have ordinary := stores_length rows
  have count := run.work.1
  change events.length ≤ 2 ^ 21 at count
  have host := run.2.2.1 .writeBytes
  change executionResources _ _ _ events .writeBytes ≤ SP1Prime - 1 at host
  rw [HintReadDemand.writeBytes run.1.2, ← hints_length] at host
  apply demandHeight_le_pow (exponent := 64)
  change (rows.flatMap store ++ events.flatMap hint).length ≤ 2 ^ 64
  rw [List.length_append]
  change (events.flatMap hint).length ≤ 2130706433 - 1 at host
  omega

variable (data : ProverData (ZMod SP1Prime))

/-- Original permission guard for every original store or host byte demand at its actual address. -/
def guardTable : Table (ZMod SP1Prime) :=
  PermissionTables.table image (bytes events rows) data (fit run routed)

/-- All rows of the permission guard satisfy their original circuit. -/
theorem guard_valid : (guardTable run routed data).Constraints ∧ (guardTable run routed data).Guarantees :=
  PermissionTables.valid image (bytes events rows) data _ (writable run routed)

private theorem selected :
    let t := image.writePermissionTable (p := SP1Prime)
    (t.readers? ((guardTable run routed data).interactionsWith t.channel.toRaw)).isSome := by
  obtain ⟨ids,found,_⟩ := PermissionTables.membership image (bytes events rows) data (fit run routed) (writable run routed)
  exact Option.isSome_iff_exists.mpr ⟨ids,found⟩

/-- Original fixed interval resource with actual counts inferred from the guard ledger. -/
noncomputable def membershipTable : Table (ZMod SP1Prime) :=
  let t := image.writePermissionTable (p := SP1Prime)
  let ids := (t.readers? ((guardTable run routed data).interactionsWith t.channel.toRaw)).get (selected run routed data)
  t.buildMembership (WritePermissionProvider.membership_height_lt_uint64 image)
    (fun i => ((ReaderCounts.counts ids)[i] : ZMod SP1Prime)) data

/-- The generated fixed inventory pays exactly the guard's interval membership pulls. -/
theorem membership_funded :
    let t := image.writePermissionTable (p := SP1Prime)
    let physical := membershipTable run routed data
    physical.Constraints ∧ physical.Guarantees ∧ physical.length = t.height ∧
      LogUpBalanced (physical.interactionsWith t.channel.toRaw ++ (guardTable run routed data).interactionsWith t.channel.toRaw) := by
  obtain ⟨ids,found,valid⟩ := PermissionTables.membership image (bytes events rows) data (fit run routed) (writable run routed)
  have get := Option.some_get (selected run routed data)
  have equal := Option.some.inj (get.trans found)
  simp only [membershipTable, equal]
  exact valid

end SP1Clean.TraceGen.MixedPermissionDemand
