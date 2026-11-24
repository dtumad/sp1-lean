import SP1Clean.Export.WriteRealizedBuffers
import SP1Clean.Export.WriteOutputTranscript

/-! # Chronological host WRITE buffers evaluated on the realized-source Memory replay -/

namespace SP1Clean.Export.WriteObservationAssembly
open Circuit Air.Flat Semantics Semantics.HintQueue Soundness WriteEffects
private abbrev F := ZMod SP1Prime
variable {image : ProgramImage} {source target : ExecutionSnapshot}

private def gather {R : Type} (selected : R → Bool) (read : R → Option Bytes) : List R → Option Bytes
  | [] => some []
  | r :: rs => do
    if selected r then
      let bytes ← read r
      return bytes ++ (← gather selected read rs)
    else gather selected read rs

/-- Re-read each selected output call directly from guest memory and concatenate it
in CPU order. Failure to read any selected guest interval propagates to the result. -/
def MemoryPaths.output? (paths : MemoryPaths) (image : ProgramImage) (s : ExecutionSnapshot) (route : WriteRoute) (rows : List (Dispatch F)) : Option Bytes :=
  gather (fun d => decide (d.route = route)) (paths.writeBytes? image s) rows

private theorem gather_eq {R : Type} (selected : R → Bool) (read : R → Option Bytes) (payload : R → Bytes) (rows : List R)
    (agree : ∀ r ∈ rows, (selected r = false → payload r = []) ∧ (selected r = true → read r = some (payload r))) :
    gather selected read rows = some (rows.flatMap payload) := by
  induction rows with
  | nil => rfl
  | cons r rows ih =>
    have tail := ih (fun x m => agree x (List.mem_cons_of_mem _ m))
    have head := agree r List.mem_cons_self
    cases e : selected r
    · simp [gather,e,tail,head.1 e]
    · simp [gather,e,tail,head.2 e]

private theorem read_output {w : EnsembleWitness (native image source target)} {paths : MemoryPaths} {rows : List (Dispatch F)}
    (replay : RealizedMemoryReplay w paths) (ok : w.Constraints) (fit : w.InteractionsFit .logUp) (raw : w.Balanced .logUp)
    (all : rows.Perm (physicalDispatches (observed w))) {route : WriteRoute} {stream : Bytes} (emitted : OutputTranscript w rows route stream) :
    paths.output? image source route rows = some stream := by
  obtain ⟨payload,rfl,each⟩ := emitted
  apply gather_eq
  intro d m
  obtain ⟨absent,kept⟩ := each d m
  refine ⟨fun no => absent (of_decide_eq_false no),fun yes => ?_⟩
  obtain ⟨length,reads⟩ := kept (of_decide_eq_true yes)
  exact replay.read_buffer ok fit raw (all.mem_iff.mp m) length reads

/-- The literal interpreter reads at this WRITE fix the input; direct allocation and
the external hook request both use that same value, including an empty buffer. -/
def RealizedWriteInput (paths : MemoryPaths) (image : ProgramImage) (source target : ExecutionSnapshot)
    (store : Store) (d : Dispatch F) : Prop :=
  (paths.context source (Address.toNat d.request.header.clock)).register 12 = some d.request.header.length.toBitVec64 ∧
  ∃ bytes, paths.writeBytes? image source d = some bytes ∧ bytes.length = d.request.header.length.toNat ∧
    (d.route = .hint → ∃ node, node? store (Address.toNat d.pointer) = some node ∧ node.bytes = bytes) ∧
    (∀ fd, d.route = .hook fd → ∃ reply, source.host.replies[Address.toNat d.previous.replies]? = some reply ∧
      target.host.requests[source.host.requests.length + Address.toNat d.previous.replies]? = some reply.request ∧
        reply.request = ⟨fd,bytes⟩)

private theorem read_input {w : EnsembleWitness (native image source target)} {paths : MemoryPaths} {store : Store} {rows : List (Dispatch F)}
    (replay : RealizedMemoryReplay w paths) (tape : ObservedWriteTape w store rows) (ok : w.Constraints)
    (fit : w.InteractionsFit .logUp) (raw : w.Balanced .logUp) (d : Dispatch F) (mr : d ∈ rows) :
    RealizedWriteInput paths image source target store d := by
  have md := tape.exhaustive.mem_iff.mp mr
  obtain ⟨bytes,read,size,_⟩ := replay.buffer_exists ok fit raw md
  refine ⟨replay.x12 (tape.origin d mr),bytes,read,size,?_,?_⟩
  · intro hint
    obtain ⟨node,found,length,guest⟩ := tape.direct d mr hint
    have full := length.trans (physical_dispatch_valid w ok fit raw d md).1.guest_length.symm
    exact ⟨node,found,Option.some.inj ((replay.read_buffer ok fit raw md full guest).symm.trans read)⟩
  · intro fd hook
    obtain ⟨reply,found,journal,desc,length,guest⟩ := tape.requests d mr fd hook
    have same := Option.some.inj ((replay.read_buffer ok fit raw md length guest).symm.trans read)
    exact ⟨reply,found,journal,by cases reply with | mk req _ => cases req; simp_all⟩

/-- The actual chronological CPU tape, one persistent hint store and one source-realized
physical replay jointly determine the complete interpreter reads, output streams, indexed
hook requests, direct hints and hook return batches of an accepted native witness. -/
theorem native_realized_write_tape (w : EnsembleWitness (native image source target)) (ok : w.Constraints)
    (fit : w.InteractionsFit .logUp) (raw : w.Balanced .logUp) :
    ∃! store, PersistentQueue w store ∧ ∃ (rows : List (Dispatch F)) (paths : MemoryPaths),
      ObservedWriteTape w store rows ∧ RealizedMemoryReplay w paths ∧
      (∀ d ∈ rows, RealizedWriteInput paths image source target store d) ∧
      let streams := WriteStreams.fromEndpoints source.host target.host
      paths.output? image source .stdout rows = some streams.stdout ∧ paths.output? image source .stderr rows = some streams.stderr ∧
        paths.output? image source .publicValues rows = some streams.publicOutput := by
  obtain ⟨store,⟨stored,rows,tape⟩,unique⟩ := native_observed_write_tape w ok fit raw
  obtain ⟨paths,replay⟩ := native_realized_memory w ok fit raw
  obtain ⟨out,err,pub⟩ := tape.outputs
  refine ⟨store,⟨stored,rows,paths,tape,replay,read_input replay tape ok fit raw,
    read_output replay ok fit raw tape.exhaustive out,read_output replay ok fit raw tape.exhaustive err,
    read_output replay ok fit raw tape.exhaustive pub⟩,?_⟩
  rintro other ⟨persisted,tape,_,seen,_⟩
  exact unique other ⟨persisted,tape,seen⟩

end SP1Clean.Export.WriteObservationAssembly
