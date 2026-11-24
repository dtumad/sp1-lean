import ToClean.Air.ReaderCounts
import SP1Clean.Proofs.Completeness.WriteDirectBlocks
import SP1Clean.Proofs.Completeness.WriteFixedDataCapacity

/-! # Original occurrences of direct placement and returned-block requests

Retaining the left and right group sites separately counts repeated requests at a boundary.
The proof assigns every live occurrence to an eligible existing physical source index.
-/

namespace SP1Clean.WriteEffects.Witness
open Circuit Air.Flat Semantics Machine FormalModel.Shard TraceGen WriteAllocation HintQueue
open scoped Classical
private abbrev F := ZMod SP1Prime

/-- Live private block queries for the two physical pull sites of one group. -/
def directRequests (g : Group F) : List (StreamBlock F) :=
  (if g.leftGate = 1 then [g.block false] else []) ++ (if g.rightGate = 1 then [g.block true] else [])

/-- A returned buffer requests only its occupied words, in the existing physical order. -/
def returnedRequests (rows : List (Words.Row F)) : List (StreamBlock F) :=
  (rows.filter (fun r => r.hookGate = 1)).map Words.Row.returned

/-- Total indices of the occupied words and fixed reply blocks funding the entire chronological
collection, preserving order, repeated requests and independent left/right occurrences. -/
theorem native_block_indices {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events) (readers : Readers)
    {entries : List Entry} (collected : native? image source events readers = some entries) :
    let groups := entries.flatMap Entry.directGroups
    let words := (inputs entries).words
    let provider := blockTable (p := SP1Prime) (WriteStreams.fromEndpoints source.host target.host)
    (∃ ids : List (Fin words.length),
      ids.map (fun i => words[i].direct) = groups.flatMap directRequests ∧ ∀ i ∈ ids, words[i].directGate = 1) ∧
    ∃ ids : List (Fin provider.height),
      ids.map (fun i => (provider.fixedEntry i.val).payload) = returnedRequests words ∧
      ∀ i ∈ ids, (provider.fixedEntry i.val).eligible = 1 := by
  dsimp only
  constructor
  · apply Air.Flat.ReaderCounts.assign
    intro b occurrence
    obtain ⟨g,mem,side⟩ := List.mem_flatMap.mp occurrence
    have selected (right : Bool) (on : (if right then g.rightGate else g.leftGate) = 1) :
        ∃ i : Fin (inputs entries).words.length, ((inputs entries).words[i]).directGate = 1 ∧
          ((inputs entries).words[i]).direct = g.block right := by
      obtain ⟨r,word,live,same,_⟩ := native_direct_blocks run readers collected mem right on
      obtain ⟨i,found⟩ := List.mem_iff_getElem?.mp word
      obtain ⟨inside,eq⟩ := List.getElem?_eq_some_iff.mp found
      exact ⟨⟨i,inside⟩,eq ▸ live,eq ▸ same⟩
    rcases List.mem_append.mp side with left | right
    · split at left
      next enabled => exact List.mem_singleton.mp left ▸ selected false enabled
      next => contradiction
    · split at right
      next enabled => exact List.mem_singleton.mp right ▸ selected true enabled
      next => contradiction
  · apply Air.Flat.ReaderCounts.assign
    intro b occurrence
    obtain ⟨r,member,rfl⟩ := List.mem_map.mp occurrence
    obtain ⟨used,one⟩ := List.mem_filter.mp member
    have nonzero : r.hookGate ≠ 0 := by rw [of_decide_eq_true one]; exact one_ne_zero
    obtain ⟨i,message,eligible⟩ := native_returned_blocks run readers collected used nonzero
    exact ⟨i,eligible,message⟩

/-- The private grouped placements are honest physical circuit inputs for the actual guest
address, length and bytes in the collected entry. -/
theorem native_direct_groups_valid {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events) (readers : Readers)
    {entries : List Entry} (collected : native? image source events readers = some entries) :
    ∀ g ∈ entries.flatMap Entry.directGroups, g.Valid ∧ g.HonestCoordinates := by
  intro g member
  obtain ⟨entry,inTape,group⟩ := List.mem_flatMap.mp member
  obtain ⟨actual,built,ordered,_⟩ := native_inputs run readers
  cases Option.some.inj (collected.symm.trans built)
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
    obtain ⟨_,_,_,_,len,buf,_,_,_,_,_,read,occurs,packet,dispatch,_⟩ := native_position run readers present write
    cases Option.some.inj (emitted.symm.trans occurs)
    obtain ⟨_,_,lower,upper,count,_⟩ := WriteObservations.read?_eq_some_iff.mp read
    unfold Entry.directGroups at group
    split at group
    next =>
      rw [packet,dispatch] at group
      change g ∈ packetGroups _ (Soundness.Target.bitVecToWord (p := SP1Prime) call.arg2).toBitVec64.toNat len.toNat
        14 _ buf 0 (WriteObservations.payload buf (Soundness.Target.bitVecToWord (p := SP1Prime) call.arg2).toBitVec64.toNat len.toNat) at group
      simp only [Soundness.Target.toBitVec64_bitVecToWord] at group
      apply packetGroups_honest _ _ _ _ _ buf [] [] (by dsimp; omega) lower upper count
      simpa only [List.length_nil,List.nil_append,List.append_nil] using group
    next => contradiction

/-- Every private group costs one actual guest-word observation; other descriptors have no
private group. The semantic native budget also covers Clean's full padded table. -/
theorem native_direct_height {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events) (readers : Readers)
    {entries : List Entry} (collected : native? image source events readers = some entries) :
    WitnessGeneration.demandHeight (entries.flatMap Entry.directGroups).length ≤ 2^28 := by
  have cost (es : List Entry) : (es.flatMap Entry.directGroups).length ≤ WriteObservations.wordProbes (es.map Entry.packet) := by
    induction es with
    | nil => simp [WriteObservations.wordProbes]
    | cons entry rest ih =>
      simp only [List.flatMap_cons,List.length_append,List.map_cons,WriteObservations.wordProbes,List.sum_cons] at *
      apply Nat.add_le_add _ ih
      unfold Entry.directGroups
      split
      · exact (packetGroups_length ..).le
      · simp
  obtain ⟨actual,built,_,observed,_⟩ := native_inputs run readers
  cases Option.some.inj (collected.symm.trans built)
  have ticks := run.2.2.1 .ticks
  rw [run.1.2.resources_ticks] at ticks
  have bound := (WriteObservations.packets_native_bound run.1.2 observed ticks (run.2.2.1 .readBytes)).2.1
  exact WitnessGeneration.demandHeight_le_pow ((cost entries).trans (bound.trans (by decide)))

end SP1Clean.WriteEffects.Witness
