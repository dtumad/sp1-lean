import SP1Clean.Export.WriteRealizedReplay
import SP1Clean.Export.WriteObservedStreams

/-! # The host interpreter's exact WRITE buffer at every actual CPU cut -/

namespace SP1Clean.Export.WriteObservationAssembly
open Circuit Air.Flat Semantics Soundness WriteEffects WriteSourceRegistry
private abbrev F := ZMod SP1Prime
variable {image : ProgramImage} {source target : ExecutionSnapshot}

/-- The standard host interpreter's register and byte readers, at one clock of a
single physical replay with its realized Sail source. -/
def MemoryPaths.context (paths : MemoryPaths) (s : ExecutionSnapshot) (clock : Nat) : HostReadContext where
  register i := paths.wordAt s (.reg i) clock
  byte := paths.byteAt s clock

/-- Perform both interpreter reads for an actual WRITE: x12 first, then its full
guest byte interval at x11 under the release's native memory policy. -/
def MemoryPaths.writeBytes? (paths : MemoryPaths) (image : ProgramImage) (s : ExecutionSnapshot) (d : Dispatch F) : Option Bytes := do
  let ctx := paths.context s (Address.toNat d.request.header.clock)
  let length ← ctx.register 12
  ctx.readGuest? (FormalModel.Shard.policy SP1Prime image).memory d.request.header.address.toBitVec64.toNat length.toNat

/-- With an evaluated guest buffer, the complete WRITE arm of the host interpreter
performs exactly its released descriptor effect and produces no guest memory write. -/
theorem MemoryPaths.execute_write_iff {paths : MemoryPaths} {image : ProgramImage} {s : ExecutionSnapshot} {d : Dispatch F} {bytes : Bytes}
    (read : paths.writeBytes? image s d = some bytes) (before after : HostState) :
    before.executeKind (FormalModel.Shard.policy SP1Prime image) (paths.context s (Address.toNat d.request.header.clock)) .write
      d.request.header.descriptor.toBitVec64 d.request.header.address.toBitVec64 = some ⟨after,none⟩ ↔
      d.route.Effect before bytes after := by
  obtain ⟨length,x12,buffer⟩ := Option.bind_eq_some_iff.mp read
  rw [HostState.execute_write_iff,Dispatch.route,WriteRoute.effect_iff]
  constructor
  · rintro ⟨n,b,next,hn,hb,out,e⟩
    obtain rfl := Option.some.inj (hn.symm.trans x12)
    obtain rfl := Option.some.inj (hb.symm.trans buffer)
    exact out.trans (congrArg some (congrArg HostEffect.state e).symm)
  · exact fun out => ⟨length,bytes,after,x12,buffer,out,rfl⟩

/-- The incoming x12 read uses the same realized-source Memory history as all guest bytes. -/
theorem RealizedMemoryReplay.x12 {w : EnsembleWitness (native image source target)} {paths : MemoryPaths}
    (replay : RealizedMemoryReplay w paths) {d : Dispatch F} (origin : DispatchOrigin w d) :
    (paths.context source (Address.toNat d.request.header.clock)).register 12 = some d.request.header.length.toBitVec64 := by
  obtain ⟨_,p,_,header,_,found,_⟩ := origin
  have read := replay.read found
  change paths.wordAt source (keyLocation #v[12,0,0]) (Address.toNat p.header.clock) = some p.header.length.toBitVec64 at read
  have reg : keyLocation (#v[12,0,0] : fields 3 F) = MemLoc.reg 12 := by decide
  rw [reg,header] at read
  exact read

private theorem read_interval (ctx : HostReadContext) (policy : HostMemoryPolicy) (addr len : Word F) (bytes : Bytes)
    (x12 : ctx.register 12 = some len.toBitVec64) (a : addr.isU64) (n : len.isU64)
    (lo : policy.lower ≤ addr.toNat) (hi : addr.toNat + len.toNat ≤ policy.upper)
    (size : bytes.length = len.toNat) (reads : ctx.ObservesBytes addr.toNat bytes) :
    (ctx.register 12).bind (fun v => ctx.readGuest? policy addr.toBitVec64.toNat v.toNat) = some bytes := by
  rw [x12]
  change ctx.readGuest? policy addr.toBitVec64.toNat len.toBitVec64.toNat = some bytes
  rw [Word.toBitVec64_toNat a,Word.toBitVec64_toNat n]
  exact (HostReadContext.readGuest?_eq_some_iff ..).mpr ⟨lo,hi,size,reads⟩

private theorem assemble_bytes (n : Nat) (P : Nat → BitVec 8 → Prop) (values : ∀ i : Fin n, ∃ b, P i.val b) :
    ∃ bytes : Bytes, bytes.length = n ∧ ∀ i : Fin bytes.length, P i.val bytes[i.val] := by
  choose f reads using values
  have size : (List.ofFn f).length = n := List.length_ofFn
  exact ⟨List.ofFn f,size,fun i => by simpa only [List.getElem_ofFn] using reads ⟨i.val,i.isLt.trans_eq size⟩⟩

/-- The host read returns any complete sequence of the authenticated original bytes.
The checked span supplies both memory-window bounds even for an empty read. -/
theorem RealizedMemoryReplay.read_buffer {w : EnsembleWitness (native image source target)} {paths : MemoryPaths}
    (replay : RealizedMemoryReplay w paths) (ok : w.Constraints) (fit : w.InteractionsFit .logUp) (raw : w.Balanced .logUp)
    {d : Dispatch F} (md : d ∈ physicalDispatches (observed w)) {bytes : Bytes}
    (size : bytes.length = d.request.header.length.toNat) (read : ∀ i : Fin bytes.length, GuestByteAt w d i.val bytes[i.val]) :
    paths.writeBytes? image source d = some bytes := by
  obtain ⟨_,span,valid,header⟩ := (native_dispatch_headers w ok fit raw).2 d md
  obtain ⟨addr,length,_,lower,finish,upper,_⟩ := valid
  rw [header] at addr length lower finish
  have x12 := replay.x12 (native_dispatch_origin w ok fit raw d md)
  exact read_interval _ (FormalModel.Shard.policy SP1Prime image).memory d.request.header.address d.request.header.length bytes x12 addr length lower
    ((le_of_eq finish.symm).trans upper) size (fun i hi => replay.guest_byte (read ⟨i,hi⟩))

/-- Every physical dispatcher completes the actual interpreter reads. Ignored descriptors
and empty intervals occur here as well as the four transcript routes and direct hints. -/
theorem RealizedMemoryReplay.buffer_exists {w : EnsembleWitness (native image source target)} {paths : MemoryPaths}
    (replay : RealizedMemoryReplay w paths) (ok : w.Constraints) (fit : w.InteractionsFit .logUp) (raw : w.Balanced .logUp)
    {d : Dispatch F} (md : d ∈ physicalDispatches (observed w)) :
    ∃ bytes, paths.writeBytes? image source d = some bytes ∧ bytes.length = d.request.header.length.toNat ∧
      ∀ i : Fin bytes.length, GuestByteAt w d i.val bytes[i.val] := by
  let n := d.request.header.length.toNat
  have length := (physical_dispatch_valid w ok fit raw d md).1.guest_length
  have values (i : Fin n) : ∃ b, GuestByteAt w d i.val b := by
    obtain ⟨_,_,_,_,_,_,_,b⟩ := native_guest_lane w ok fit raw d md i.val (length ▸ i.isLt)
    exact ⟨_,b⟩
  obtain ⟨bytes,size,guest⟩ := assemble_bytes n (GuestByteAt w d) values
  exact ⟨bytes,replay.read_buffer ok fit raw md size guest,size,guest⟩

end SP1Clean.Export.WriteObservationAssembly
