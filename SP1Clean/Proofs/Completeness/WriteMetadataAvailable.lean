import SP1Clean.Proofs.Completeness.WriteMetadataDemand
import SP1Clean.Proofs.Completeness.WriteFixedDataCapacity
import SP1Clean.Proofs.Completeness.WriteReturnedBlocks

/-! # Fixed endpoint ownership of native hook metadata

A WRITE dispatcher looks up the current reply at the number of earlier hook calls. Fresh nodes
reverse the physical allocation order, so each buffer length uses the original logical ordinal
within that same reply. Both indices come from the collector at the genuine execution cut.
-/

namespace SP1Clean.WriteEffects.Witness.Metadata

open Circuit Air.Flat Semantics Machine FormalModel.Shard TraceGen Soundness.Target WriteAllocation HintQueue
private abbrev F := ZMod SP1Prime

private theorem descriptor_limb {fd : BitVec 64} {hook : BitVec 32}
    (selected : WriteRoute.ofDescriptor fd = .hook hook) :
    Address.ofNat (p := SP1Prime) hook.toNat = #v[(hook.toNat : F),0,0] := by
  have supported : hook ∈ hookDescriptors := by
    unfold WriteRoute.ofDescriptor at selected
    split_ifs at selected with _ _ _ _ member; cases selected
    exact member
  simp only [hookDescriptors,List.mem_cons,List.not_mem_nil,or_false] at supported
  rcases supported with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem hook_of_flag (fd : BitVec 64) (live : (routeFlags (WriteRoute.ofDescriptor fd)).hook = 1) :
    ∃ k, WriteRoute.ofDescriptor fd = .hook k := by
  cases route : WriteRoute.ofDescriptor fd
  case hook k => exact ⟨k,rfl⟩
  all_goals simp [route,routeFlags,DispatchFlags.hook] at live

private def hookKeys (n : Nat) (k : BitVec 32) (size count : Nat) : List (Record F) :=
  [(Query.descriptor n).encode k.toNat,(Query.length (.request n)).encode size,(Query.returnCount n).encode count]

private theorem hook_keys_available {source target : HostState} (n : Nat) (k : BitVec 32) (bytes : Bytes) (hints : List Bytes)
    (checked : inventoryOK (.fromEndpoints source target) = true)
    (reply : (WriteStreams.fromEndpoints source target).hooks[n]? = some ⟨⟨k,bytes⟩,hints⟩) :
    ∀ key ∈ hookKeys n k bytes.length hints.length, (streamTable (p := SP1Prime) source target).Spec key := by
  intro key used
  simp only [hookKeys,List.mem_cons,List.not_mem_nil,or_false] at used
  rcases used with h | h | h
  · exact h ▸ metadata_available (q := .descriptor n) trivial checked (by simp [Query.lookup,reply])
  · exact h ▸ metadata_available (q := .length (.request n)) trivial checked (by simp [Query.lookup,StreamKey.contents,reply])
  · exact h ▸ metadata_available (q := .returnCount n) trivial checked (by simp [Query.lookup,reply])

private theorem hook_encoding (r : Dispatch F) {n size count : Nat} {fd : BitVec 64} {k : BitVec 32}
    (route : WriteRoute.ofDescriptor fd = .hook k) (ordinal : r.previous.replies = Address.ofNat n)
    (tag : r.request.route = (k.toNat : F)) (length : r.length = Address.ofNat size) (returned : r.returned = Address.ofNat count) :
    r.metadataReads = hookKeys n k size count := by
  have zero : Address.ofNat (p := SP1Prime) 0 = #v[0,0,0] := by decide
  simp only [Dispatch.metadataReads,Dispatch.metadata,ordinal,tag,length,returned,hookKeys,Query.encode,Query.coordinates,
    StreamKey.coordinates,zero,descriptor_limb route,Nat.cast_ofNat,Nat.cast_zero]

private theorem dispatch_tag (fd address len : BitVec 64) (clock previous : Nat) (earlier : WriteStreams)
    (current : HostState) (store : Store) :
    (dispatchRow fd address len clock previous earlier current store).request.route = ((WriteRoute.ofDescriptor fd).tag : F) := by
  change ((WriteRoute.ofDescriptor (bitVecToWord (p := SP1Prime) fd).toBitVec64).tag : F) = _
  rw [toBitVec64_bitVecToWord]

private theorem dispatch_available {source target current next : HostState} (fd address len : BitVec 64)
    (clock previous : Nat) (earlier later : WriteStreams) (store : Store) (bytes : Bytes) (size : bytes.length = len.toNat)
    (effect : (WriteRoute.ofDescriptor fd).Effect current bytes next)
    (joined : WriteStreams.fromEndpoints source target = earlier.append ((WriteStreams.ofEvent (WriteRoute.ofDescriptor fd) current bytes).append later))
    (checked : inventoryOK (.fromEndpoints source target) = true)
    (r : Dispatch F) (emitted : r = dispatchRow fd address len clock previous earlier current store)
    (live : r.flags.hook = 1) {key : Record F} (used : key ∈ r.metadataReads) :
    (streamTable (p := SP1Prime) source target).Spec key := by
  have flags : r.flags = routeFlags (WriteRoute.ofDescriptor fd) := congrArg Dispatch.flags emitted
  obtain ⟨k,route⟩ := hook_of_flag fd ((congrArg DispatchFlags.hook flags).symm.trans live)
  rw [route] at effect joined
  obtain ⟨hints,rest,front,_⟩ := effect
  have reply : (WriteStreams.fromEndpoints source target).hooks[earlier.hooks.length]? = some ⟨⟨k,bytes⟩,hints⟩ := by
    simp [joined,WriteStreams.append,WriteStreams.ofEvent,front]
  have ordinal : r.previous.replies = Address.ofNat earlier.hooks.length := congrArg (fun x => x.previous.replies) emitted
  have tag := (congrArg (fun x => x.request.route) emitted).trans (dispatch_tag fd address len clock previous earlier current store)
  rw [route] at tag
  have length := (congrArg Dispatch.length emitted).trans (dispatchRow_length fd address len clock previous earlier current store)
  rw [← size] at length
  have returned : r.returned = Address.ofNat ((current.replies.head?.map (·.hints.length)).getD 0) := congrArg Dispatch.returned emitted
  rw [front] at returned
  exact hook_keys_available _ _ _ _ checked reply key (hook_encoding r route ordinal tag length returned ▸ used)

private theorem node_available {source target current next : HostState} {route : WriteRoute} {payload : Bytes}
    {earlier later : WriteStreams} (effect : route.Effect current payload next)
    (joined : WriteStreams.fromEndpoints source target = earlier.append ((WriteStreams.ofEvent route current payload).append later))
    (checked : inventoryOK (.fromEndpoints source target) = true) {b : Batch}
    (chosen : batchFor route earlier current payload = some b) {clock previous : Nat} {before : Store × Nat} {after : Store}
    (paid : b.Publishes clock before after) (readers : Readers) {node : NodeRows}
    (used : node ∈ (b.rows previous clock before readers).nodes) (gate : 1-node.step.direct = 1) :
    (streamTable (p := SP1Prime) source target).Spec node.step.metadata := by
  obtain ⟨i,atNode⟩ := List.mem_iff_getElem?.mp used
  have fit : i < b.buffers.length := by
    simpa only [Batch.rows_length] using (List.getElem?_eq_some_iff.mp atNode).1
  obtain ⟨actual,found,_,_,_,_,size,_⟩ := b.rows_at previous clock before after paid readers ⟨i,fit⟩
  cases Option.some.inj (atNode.symm.trans found)
  obtain ⟨step,bytes,atStep,atBytes,same⟩ := List.getElem?_zipWith_eq_some.mp atNode
  subst node
  obtain ⟨mode,index,reply⟩ := step_source b clock before readers atStep
  change 1 - step.direct = 1 at gate
  change step.length = _ at size
  cases b with
  | direct guest =>
    change step.direct = 1 at mode
    simp [mode] at gate
  | hook n input hints =>
    let k := hints.length - (i+1)
    change hints.reverse[i]? = some bytes at atBytes
    have within : i < hints.length := fit
    have bytesAt : hints[k]? = some bytes := by
      rw [← List.getElem?_reverse' (show i+k+1 = hints.length by dsimp [k]; omega)]
      exact atBytes
    have length : step.length = Address.ofNat bytes.length := by
      have eq := (List.getElem?_eq_some_iff.mp atBytes).2
      change step.length = Address.ofNat (hints.reverse[i]'(by simpa using within)).length at size
      rwa [eq] at size
    have logical : step.index = Address.ofNat k := index
    have ordinal : step.reply = Address.ofNat n := by
      change scale (1-step.direct) step.reply = Address.ofNat n at reply
      rw [gate] at reply
      have one (x : fields 3 F) : scale 1 x = x := by
        ext j hj
        interval_cases j <;> simp [scale]
      rwa [one] at reply
    have content := lookup_return (later := later) effect chosen rfl bytesAt
    rw [← joined] at content
    have encoded : step.metadata = (Query.length (.returned n k)).encode bytes.length := by
      simp only [Step.metadata,Query.encode,Query.coordinates,StreamKey.coordinates,ordinal,logical,length]
      rfl
    change (streamTable source target).Spec step.metadata
    rw [encoded]
    exact metadata_available trivial checked (by simp [Query.lookup,content])

private theorem entry_available {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events) (readers : Readers)
    {e : ExecutionEvent} {i : Nat} (present : events[i]? = some e) {entry : Entry}
    (emitted : position image source events readers e i = some entry) :
    let fixed := streamTable (p := SP1Prime) source.host target.host
    (entry.dispatch.flags.hook = 1 → ∀ key ∈ entry.dispatch.metadataReads, fixed.Spec key) ∧
      ∀ batch ∈ entry.allocation, ∀ node ∈ batch.nodes, 1-node.step.direct = 1 → fixed.Spec node.step.metadata := by
  intro fixed
  have real := (native_position_active run readers present).1
  rw [emitted] at real
  cases e with
  | ordinary => contradiction
  | syscall call =>
    have write : call.rawCode = SyscallKind.write.code := of_decide_eq_true real.symm
    obtain ⟨current,next,cursor,after,len,buf,actual,atCurrent,atNext,_,_,read,atEntry,_,dispatch,_,alloc,active⟩ :=
      native_position run readers present write
    cases Option.some.inj (emitted.symm.trans atEntry)
    obtain ⟨_,_,_,_,sameRead,atCurrent',atNext',effect,_⟩ := groups_of_admissibleExecution run present write
    cases Option.some.inj (atCurrent.symm.trans atCurrent')
    cases Option.some.inj (atNext.symm.trans atNext')
    cases Option.some.inj (read.symm.trans sameRead)
    obtain ⟨_,left,_⟩ := run.1.2.split i
    obtain ⟨_,right,tail⟩ := run.1.2.split (i+1)
    cases Option.some.inj (left.replay.symm.trans atCurrent)
    cases Option.some.inj (right.replay.symm.trans atNext)
    have full := ((execution_streams left).append ((WriteStreams.ofEvent_binds effect).append (execution_streams tail))).unique
    have size := WriteObservations.payload_length (WriteObservations.read?_eq_some_iff.mp read).2.2.2.2.1
    constructor
    · intro hook key used
      exact dispatch_available call.arg1 call.arg2 len _ _ _ _ cursor.1 _ size effect full (admissible_inventoryOK run)
        _ dispatch hook used
    · intro batch member node used gate
      rw [alloc] at member
      obtain ⟨b,selected,rfl⟩ := Option.map_eq_some_iff.mp member
      exact node_available effect full (admissible_inventoryOK run) selected (active b selected).publishes readers used gate

/-- All active fixed-stream requests from the collected dispatches and allocations are eligible
rows of the verifier-owned metadata inventory at their exact complete field payloads. -/
theorem available {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events) (readers : Readers)
    {entries : List Entry} (collected : native? image source events readers = some entries) :
    ∀ k ∈ records entries, (streamTable (p := SP1Prime) source.host target.host).Spec k := by
  obtain ⟨actual,built,ordered,_⟩ := native_inputs run readers
  cases Option.some.inj (collected.symm.trans built)
  have authentic (e : Entry) (member : e ∈ entries) :
      let fixed := streamTable (p := SP1Prime) source.host target.host
      (e.dispatch.flags.hook = 1 → ∀ key ∈ e.dispatch.metadataReads, fixed.Spec key) ∧
      ∀ batch ∈ e.allocation, ∀ node ∈ batch.nodes, 1-node.step.direct = 1 → fixed.Spec node.step.metadata := by
    rw [ordered] at member
    obtain ⟨⟨event,i⟩,atEvent,atEntry⟩ := List.mem_filterMap.mp member
    exact entry_available run readers (List.mk_mem_zipIdx_iff_getElem?.mp atEvent) atEntry
  intro k used
  rcases List.mem_append.mp used with ds | ns
  · obtain ⟨row,fromEntry,read⟩ := List.mem_flatMap.mp ds
    obtain ⟨e,inside,rfl⟩ := List.mem_map.mp fromEntry
    split at read
    · exact (authentic e inside).1 (by assumption) k read
    · contradiction
  · obtain ⟨row,fromNode,read⟩ := List.mem_flatMap.mp ns
    obtain ⟨node,allocated,rfl⟩ := List.mem_map.mp fromNode
    obtain ⟨batch,emitted,inBatch⟩ := List.mem_flatMap.mp allocated
    obtain ⟨e,inside,owns⟩ := List.mem_filterMap.mp emitted
    split at read
    · cases List.mem_singleton.mp read
      exact (authentic e inside).2 batch owns node inBatch (by assumption)
    · contradiction

end SP1Clean.WriteEffects.Witness.Metadata
