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

private theorem published (w : EnsembleWitness (native image source target)) (ok : w.Constraints)
    (fit : w.InteractionsFit .logUp) (raw : w.Balanced .logUp) (d : Dispatch F) (md : d ∈ physicalDispatches (observed w))
    {key : StreamKey} (selected : destinationKey d.route (Address.toNat d.previous.replies) = some key) :
    ∃ stream, key.contents (.fromEndpoints source.host target.host) = some stream ∧
      (∀ r, key = .request r → stream.length = Address.toNat d.length) := by
  have valid := (physical_dispatch_valid w ok fit raw d md).1
  have shape := valid.route_flags ((native_dispatch_origin w ok fit raw d md).1)
  refine stream_of_route d.route _ _ _ ?_ selected
  intro fd route
  have flags : d.flags.hook = 1 := by rw [shape,route]; simp [routeFlags,DispatchFlags.hook]
  have allocated := (physical_dispatch_valid w ok fit raw d md).2 (by rw [shape,route]; simp [routeFlags,DispatchFlags.hook])
  obtain ⟨reply,found,_,_,size⟩ := native_hook_reply w ok fit raw d allocated flags
  exact ⟨reply,found,size⟩

/-- The complete selected public slice has precisely x12 bytes. All of those bytes are
sampled from the incoming guest memory at x11 plus their index. A hook owns its full
request input, including an empty input. -/
def PublicSliceAt (w : EnsembleWitness (native image source target)) (d : Dispatch F) : Prop :=
  let counters := StreamCounts.ofCursor d.previous
  ∀ key, destinationKey d.route counters.hooks = some key →
    ∃ stream, key.contents (.fromEndpoints source.host target.host) = some stream ∧
      (∀ r, key = .request r → stream.length = Address.toNat d.length) ∧
      let slice := (stream.drop (counters.offset d.route)).take (Address.toNat d.length)
      slice.length = Address.toNat d.length ∧ ∀ i : Fin slice.length, GuestByteAt w d i.val slice[i.val]

/-- The selected destination for each physical CPU WRITE is determined by its released
semantic descriptor. Both partial ends of each source word use real occupied public bytes. -/
theorem native_public_slice (w : EnsembleWitness (native image source target)) (ok : w.Constraints)
    (fit : w.InteractionsFit .logUp) (raw : w.Balanced .logUp) (d : Dispatch F) (md : d ∈ physicalDispatches (observed w)) :
    PublicSliceAt w d := by
  intro key selected
  obtain ⟨stream,found,requestLength⟩ := published w ok fit raw d md selected
  have valid := (physical_dispatch_valid w ok fit raw d md).1
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

end SP1Clean.Export.WriteObservationAssembly
