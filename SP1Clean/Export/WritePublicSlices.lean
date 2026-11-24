import SP1Clean.Export.WritePublicBlockLanes
import SP1Clean.Export.WriteDispatchOrigin
import SP1Clean.Proofs.Operations.WriteClassifiedRoute

/-! # Source-authenticated stdout, stderr, public-output and hook-request byte slices -/

namespace SP1Clean.Export.WriteObservationAssembly
open Circuit Air.Flat Semantics Soundness WriteEffects WriteSourceRegistry
private abbrev F := ZMod SP1Prime
variable {image : ProgramImage} {source target : ExecutionSnapshot}

private theorem stream_of_route (route : WriteRoute) (streams : WriteStreams) (ordinal length : Nat)
    (hook : ∀ fd, route = .hook fd → ∃ reply, streams.hooks[ordinal]? = some reply ∧ reply.request.input.length = length)
    {key : StreamKey} (selected : destinationKey route ordinal = some key) :
    ∃ bytes, key.contents streams = some bytes ∧ (∀ r, key = .request r → bytes.length = length) := by
  cases route <;> simp only [destinationKey,Option.some.injEq,reduceCtorEq] at selected
  all_goals subst key
  case stdout | stderr | publicValues => exact ⟨_,rfl,fun _ e => by cases e⟩
  case hook fd =>
    obtain ⟨reply,found,size⟩ := hook fd rfl
    exact ⟨reply.request.input,by simp only [StreamKey.contents,found,Option.map_some],fun _ _ => size⟩

private theorem hook_reply (w : EnsembleWitness (native image source target)) (ok : w.Constraints)
    (fit : w.InteractionsFit .logUp) (raw : w.Balanced .logUp) (d : Dispatch F) (md : d ∈ physicalDispatches (observed w))
    {fd : BitVec 32} (route : d.route = .hook fd) :
    ∃ reply, (WriteStreams.fromEndpoints source.host target.host).hooks[Address.toNat d.previous.replies]? = some reply ∧
      reply.request.descriptor = fd ∧ reply.request.input.length = Address.toNat d.length := by
  obtain ⟨v,alloc⟩ := physical_dispatch_valid w ok fit raw d md
  have classified := (native_dispatch_origin w ok fit raw d md).1
  have shape := v.route_flags classified
  have flags : d.flags.hook = 1 := by rw [shape,route]; simp [routeFlags,DispatchFlags.hook]
  have allocated := alloc (by rw [shape,route]; simp [routeFlags,DispatchFlags.hook])
  obtain ⟨reply,found,_,desc,size⟩ := native_hook_reply w ok fit raw d allocated flags
  rw [d.tag_val classified,route] at desc
  exact ⟨reply,found,BitVec.eq_of_toNat_eq desc,size⟩

private theorem published (w : EnsembleWitness (native image source target)) (ok : w.Constraints)
    (fit : w.InteractionsFit .logUp) (raw : w.Balanced .logUp) (d : Dispatch F) (md : d ∈ physicalDispatches (observed w))
    {key : StreamKey} (selected : destinationKey d.route (Address.toNat d.previous.replies) = some key) :
    ∃ stream, key.contents (.fromEndpoints source.host target.host) = some stream ∧
      (∀ r, key = .request r → stream.length = Address.toNat d.length) := by
  refine stream_of_route d.route _ _ _ ?_ selected
  intro fd route
  obtain ⟨reply,found,_,size⟩ := hook_reply w ok fit raw d md route
  exact ⟨reply,found,size⟩

/-- A slice of the named endpoint stream whose occupied bytes are all backed by the original guest memory. -/
def StreamSliceAt (w : EnsembleWitness (native image source target)) (d : Dispatch F) (key : StreamKey) (offset length : Nat) : Prop :=
  ∃ stream, key.contents (.fromEndpoints source.host target.host) = some stream ∧
    (∀ r, key = .request r → stream.length = length) ∧
    let slice := (stream.drop offset).take length
    slice.length = length ∧ ∀ i : Fin slice.length, GuestByteAt w d i.val slice[i.val]

/-- The complete selected public slice has precisely x12 bytes. All of those bytes are
sampled from the incoming guest memory at x11 plus their index. A hook owns its full
request input, including an empty input. -/
def PublicSliceAt (w : EnsembleWitness (native image source target)) (d : Dispatch F) : Prop :=
  let counters := StreamCounts.ofCursor d.previous
  ∀ key, destinationKey d.route counters.hooks = some key → StreamSliceAt w d key (counters.offset d.route) d.request.header.length.toNat

/-- The selected destination for each physical CPU WRITE is determined by its released
semantic descriptor. Both partial ends of each source word use real occupied public bytes. -/
theorem native_public_slice (w : EnsembleWitness (native image source target)) (ok : w.Constraints)
    (fit : w.InteractionsFit .logUp) (raw : w.Balanced .logUp) (d : Dispatch F) (md : d ∈ physicalDispatches (observed w)) :
    PublicSliceAt w d := by
  intro key selected
  obtain ⟨stream,found,requestLength⟩ := published w ok fit raw d md selected
  have valid := (physical_dispatch_valid w ok fit raw d md).1
  rw [valid.guest_length]
  have released := (native_dispatch_origin w ok fit raw d md).1
  obtain ⟨start,tag,owner,hint,keep,fixed⟩ := valid.public_coordinates released selected
  let basePos := (StreamCounts.ofCursor d.previous).offset d.route
  let n := Address.toNat d.length
  have byte (i : Nat) (bound : i < n) :
      ∃ k : Fin stream.length, k.val = basePos + i ∧ GuestByteAt w d i stream[k.val] := by
    obtain ⟨g,mg,sink,content,j,small,index,guest⟩ := native_guest_lane w ok fit raw d md i bound
    obtain ⟨bytes,publishedBytes,k,pos,same⟩ := native_public_group_lane w ok fit raw g mg key
      ((congrArg ZMod.val sink).trans tag) ((congrArg Address.toNat content).trans owner) hint keep fixed j small
    obtain rfl : bytes = stream := Option.some.inj (publishedBytes.symm.trans found)
    exact ⟨k,pos.trans (index.trans (congrArg (fun x => x + i) start)),same ▸ guest⟩
  have size : n ≤ stream.length - basePos := by
    by_cases zero : n = 0
    · omega
    obtain ⟨k,idx,_⟩ := byte (n-1) (by omega)
    have := k.isLt
    omega
  let slice := (stream.drop basePos).take n
  have len : slice.length = n := by simp only [slice,List.length_take,List.length_drop,Nat.min_eq_left size]
  refine ⟨stream,found,requestLength,len,?_⟩
  intro i
  have hi : i.val < n := len ▸ i.isLt
  obtain ⟨k,pos,guest⟩ := byte i.val hi
  have same : slice[i.val] = stream[k.val] := by
    simp only [slice,List.getElem_take,List.getElem_drop]
    let atPos : Fin stream.length := ⟨basePos + i.val,pos ▸ k.isLt⟩
    have sameIndex : k = atPos := Fin.ext pos
    exact (congrArg (fun j : Fin stream.length => stream[j.val]) sameIndex).symm
  exact same.symm ▸ guest

/-- An actual hook matches its supplied reply, the full guest request and the appended
request journal entry at the same exact ordinal. Empty buffers are included. -/
def HookRequestAt (w : EnsembleWitness (native image source target)) (d : Dispatch F) (fd : BitVec 32) : Prop :=
  let ordinal := Address.toNat d.previous.replies
  ∃ reply, source.host.replies[ordinal]? = some reply ∧
    target.host.requests[source.host.requests.length + ordinal]? = some reply.request ∧ reply.request.descriptor = fd ∧
    reply.request.input.length = d.request.header.length.toNat ∧ ∀ i : Fin reply.request.input.length, GuestByteAt w d i.val reply.request.input[i.val]

/-- Every physical hook consumes and journals precisely the original guest request bytes and descriptor. -/
theorem native_hook_request (w : EnsembleWitness (native image source target)) (ok : w.Constraints)
    (fit : w.InteractionsFit .logUp) (raw : w.Balanced .logUp) (d : Dispatch F) (md : d ∈ physicalDispatches (observed w))
    {fd : BitVec 32} (route : d.route = .hook fd) : HookRequestAt w d fd := by
  let s := WriteStreams.fromEndpoints source.host target.host
  let ordinal := Address.toNat d.previous.replies
  obtain ⟨reply,found,descriptor,size⟩ := hook_reply w ok fit raw d md route
  change s.hooks[ordinal]? = some reply at found
  have ordinalFits : ordinal < s.hooks.length := (List.getElem?_eq_some_iff.mp found).1
  have binds : s.Binds source.host target.host := (native_stream_boundary w fit raw).1
  have input : source.host.replies[ordinal]? = some reply := by
    rw [binds.replies,List.getElem?_append_left ordinalFits,found]
  have journal : target.host.requests[source.host.requests.length + ordinal]? = some reply.request := by
    rw [binds.requests,List.getElem?_append_right (by omega),Nat.add_sub_cancel_left,List.getElem?_map,found]
    rfl
  have selected : destinationKey d.route ordinal = some (.request ordinal) := by rw [route]; rfl
  obtain ⟨bytes,pub,_,_,guest⟩ := native_public_slice w ok fit raw d md _ selected
  change (s.hooks[ordinal]?).map (fun h => h.request.input) = some bytes at pub
  rw [found,Option.map_some] at pub
  obtain rfl := Option.some.inj pub
  have zeros : (StreamCounts.ofCursor d.previous).offset d.route = 0 := by rw [route]; rfl
  have fullLength := size.trans (physical_dispatch_valid w ok fit raw d md).1.guest_length.symm
  have slice : (reply.request.input.drop ((StreamCounts.ofCursor d.previous).offset d.route)).take d.request.header.length.toNat = reply.request.input := by
    rw [zeros,List.drop_zero,← fullLength,List.take_length]
  let observedBytes (bytes : Bytes) := ∀ i : Fin bytes.length, GuestByteAt w d i.val bytes[i.val]
  change observedBytes _ at guest
  rw [slice] at guest
  exact ⟨reply,input,journal,descriptor,fullLength,guest⟩

end SP1Clean.Export.WriteObservationAssembly
