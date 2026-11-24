import SP1Clean.Proofs.Completeness.WriteWitnessInputs
import SP1Clean.Proofs.Completeness.WriteAllocationWordTables
import SP1Clean.Proofs.Completeness.WriteDestination

/-! # Authenticating allocation-word block pulls against the supplied reply stream

A live hook pull uses the original reply ordinal, the reverse-prepend buffer ordinal, and its
own occupied word index. Empty buffers and the extra final word of an aligned buffer produce
zero-weight pulls. The argument uses the actual collector entry and both host endpoints.
-/

namespace SP1Clean.WriteEffects.Witness
open Semantics Machine FormalModel.Shard TraceGen WriteAllocation HintQueue
open scoped Classical

private abbrev F := ZMod SP1Prime

/-- Direct mode, original logical buffer ordinal and reply identity on every generated node row. -/
theorem step_source (b : Batch) (clk : Nat) (before : Store × Nat) (readers : Readers) {i : Nat} {s : Step F}
    (present : (b.steps clk before.1 before.2 readers.nodes)[i]? = some s) :
    s.contents.direct = (b.source before.1.size).direct ∧
    s.contents.index = Address.ofNat (b.buffers.length - (i+1)) ∧
    s.contents.reply = (match b with | .direct _ => 0 | .hook n _ _ => Address.ofNat n) := by
  simp only [Batch.steps,List.getElem?_map,List.getElem?_zipIdx] at present
  cases found : (HintNodeAllocate.compilePrepend (p := SP1Prime) clk before.1 before.2 b.buffers)[i]? with
  | none => simp [found] at present
  | some node =>
    simp [found] at present
    subst s
    cases b <;> simp [Batch.step,Batch.source,Step.contents,scale,Address.ofNat]
    rfl

private theorem hook_word {b : Batch} {clock previous : Nat} {before : Store × Nat} {readers : Readers}
    {node : NodeRows} (member : node ∈ (b.rows previous clock before readers).nodes)
    {row : Words.Row F} (inWord : row ∈ node.words) (active : row.hookGate ≠ 0) :
    ∃ reply input hints, b = .hook reply input hints ∧ ∃ k bytes j,
      hints[k]? = some bytes ∧ 8*j < bytes.length ∧ row.returned = encodeBlock (.returned reply k) bytes j := by
  obtain ⟨i,atNode⟩ := List.mem_iff_getElem?.mp member
  obtain ⟨s,bytes,step,byteAt,rfl⟩ := List.getElem?_zipWith_eq_some.mp atNode
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp inWord
  obtain ⟨mode,index,ordinal⟩ := step_source b clock before readers step
  cases b with
  | direct guest =>
    change ((1 : F)-s.contents.direct)*(Words.Payload.populate (p := SP1Prime) bytes j.val).mask[0] ≠ 0 at active
    have live : s.contents.direct = 1 := mode
    simp [live] at active
  | hook reply input hints =>
    let k := hints.length-(i+1)
    change hints.reverse[i]? = some bytes at byteAt
    have inside : i < hints.length := by simpa using (List.getElem?_eq_some_iff.mp byteAt).1
    have original : hints[k]? = some bytes := by
      rw [← List.getElem?_reverse' (show i+k+1 = hints.length by dsimp [k]; omega)]
      exact byteAt
    have positive : 8*j.val < bytes.length := by
      by_contra! empty
      have dead : Words.extent bytes j.val = 0 := by simp [Words.extent,Nat.sub_eq_zero_of_le empty]
      simp [Words.populate,Words.Row.hookGate,Words.Payload.populate,dead] at active
    exact ⟨reply,input,hints,rfl,k,bytes,j.val,original,positive,
      Words.populate_returned s.contents bytes j.val reply k _ _ ordinal index⟩

/-- The selected returned buffer remains at its original ordinal in the complete public transcript. -/
theorem lookup_return {route : WriteRoute} {current next : HostState} {payload : Bytes}
    (effect : route.Effect current payload next) {earlier later : WriteStreams} {b : Batch}
    (selected : batchFor route earlier current payload = some b) {reply input : Nat} {hints : List Bytes}
    (hook : b = .hook reply input hints) {k : Nat} {bytes : Bytes} (atHint : hints[k]? = some bytes) :
    (StreamKey.returned reply k).contents (earlier.append ((WriteStreams.ofEvent route current payload).append later)) = some bytes := by
  subst b
  cases route <;> simp [batchFor,batchAt] at selected
  case hook fd =>
    obtain ⟨returned,rest,front,_⟩ := effect
    rcases selected with ⟨rfl,rfl,rfl⟩
    simpa [StreamKey.contents,WriteStreams.append,WriteStreams.ofEvent,WriteRoute.allocations,front] using atHint

/-- Every active returned-block query in the physically generated allocation-word inputs is
covered by an eligible row of the verifier-fixed endpoint table with the same complete contents. -/
theorem native_returned_blocks {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events) (readers : Readers)
    {entries : List Entry} (collected : native? image source events readers = some entries)
    {row : Words.Row F} (member : row ∈ (inputs entries).words) (active : row.hookGate ≠ 0) :
    let provider := blockTable (p := SP1Prime) (WriteStreams.fromEndpoints source.host target.host)
    ∃ index : Fin provider.height, (provider.fixedEntry index.val).payload = row.returned ∧
      (provider.fixedEntry index.val).eligible = 1 := by
  obtain ⟨actual,built,ordered,_⟩ := native_inputs run readers
  cases Option.some.inj (collected.symm.trans built)
  obtain ⟨node,allocated,word⟩ := List.mem_flatMap.mp member
  obtain ⟨batch,opened,inBatch⟩ := List.mem_flatMap.mp allocated
  obtain ⟨entry,inTape,atBatch⟩ := List.mem_filterMap.mp opened
  rw [ordered] at inTape
  obtain ⟨⟨e,i⟩,indexed,emitted⟩ := List.mem_filterMap.mp inTape
  change position image source events readers e i = some entry at emitted
  have present := List.mk_mem_zipIdx_iff_getElem?.mp indexed
  have real := (native_position_active run readers present).1
  rw [emitted] at real
  cases e with
  | ordinary => contradiction
  | syscall call =>
    have write : call.rawCode = SyscallKind.write.code := of_decide_eq_true real.symm
    obtain ⟨current,_,_,_,len,buf,_,reached,_,_,_,read,occurs,_,_,_,alloc,_⟩ := native_position run readers present write
    cases Option.some.inj (emitted.symm.trans occurs)
    rw [alloc,Option.map_eq_some_iff] at atBatch
    obtain ⟨b,selected,rfl⟩ := atBatch
    obtain ⟨reply,input,hints,hook,k,bytes,j,atHint,live,exactBlock⟩ := hook_word inBatch word active
    obtain ⟨_,next,_,_,sameRead,atCurrent,atNext,effect,_⟩ := groups_of_admissibleExecution run present write
    cases Option.some.inj (reached.symm.trans atCurrent)
    cases Option.some.inj (read.symm.trans sameRead)
    obtain ⟨left,pre,_⟩ := run.1.2.split i
    obtain ⟨right,post,suffixPath⟩ := run.1.2.split (i+1)
    cases Option.some.inj (pre.replay.symm.trans reached)
    cases Option.some.inj (post.replay.symm.trans atNext)
    have full := ((execution_streams pre).append ((WriteStreams.ofEvent_binds effect).append (execution_streams suffixPath))).unique
    have obtainBytes := lookup_return (later := WriteStreams.fromEndpoints next.host target.host) effect selected hook atHint
    change WriteStreams.fromEndpoints source.host target.host = (WriteStreams.fromEndpoints source.host current.host).append
      ((WriteStreams.ofEvent _ current.host _).append (WriteStreams.fromEndpoints next.host target.host)) at full
    rw [← full] at obtainBytes
    apply (StaticTable.spec_iff_fixedEntry _ _).mp
    rw [exactBlock]
    exact block_available (admissible_inventoryOK run) obtainBytes live

end SP1Clean.WriteEffects.Witness
