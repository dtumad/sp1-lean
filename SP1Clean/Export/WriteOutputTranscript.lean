import SP1Clean.Export.WriteObservedStreams

/-! # Reassemble the three released output streams from chronological guest writes -/

namespace SP1Clean.Export.WriteObservationAssembly
open Circuit Air.Flat Semantics Semantics.HintQueue Soundness WriteEffects
private abbrev F := ZMod SP1Prime
variable {image : ProgramImage} {source target : ExecutionSnapshot}

private theorem split_stream {R C B : Type} (stream : List B) (position width : R → Nat)
    (count : C → Nat) (step : C → R → C) (advance : ∀ c r, count (step c r) = count c + width r)
    (rows : List R) (start : C) (positions : ∀ i : Fin rows.length, position rows[i.val] = count ((rows.take i.val).foldl step start)) :
    (rows.flatMap fun r => (stream.drop (position r)).take (width r)) ++ stream.drop (count (rows.foldl step start)) =
      stream.drop (count start) := by
  induction rows generalizing start with
  | nil => rfl
  | cons r rows ih =>
    have head := positions ⟨0,by simp⟩
    change position r = count start at head
    have tail := ih (step start r) (fun i => positions ⟨i.val+1,Nat.succ_lt_succ i.isLt⟩)
    simp only [List.flatMap_cons,List.foldl_cons,List.append_assoc,tail,head,advance,List.drop_take_append_drop]

private theorem count_output (wanted : WriteRoute)
    (output : wanted = .stdout ∨ wanted = .stderr ∨ wanted = .publicValues) (c : StreamCounts) (route : WriteRoute) (n : Nat) :
    (c.record route n).offset wanted = c.offset wanted + (if route = wanted then n else 0) := by
  rcases output with rfl | rfl | rfl <;> cases route <;> simp [StreamCounts.record,StreamCounts.offset]

/-- Each matching call contributes its entire x12-byte guest buffer. Their ordered concatenation
is exactly the local output stream, including the zero-call and zero-length cases. -/
def OutputTranscript (w : EnsembleWitness (native image source target)) (path : List (Dispatch F)) (wanted : WriteRoute) (stream : Bytes) : Prop :=
  ∃ payload : Dispatch F → Bytes, stream = path.flatMap payload ∧ ∀ d ∈ path,
    (d.route ≠ wanted → payload d = []) ∧ (d.route = wanted → (payload d).length = d.request.header.length.toNat ∧
      ∀ i : Fin (payload d).length, GuestByteAt w d i.val (payload d)[i.val])

private theorem ordered_output {w : EnsembleWitness (native image source target)} {store : Store} {path : List (Dispatch F)}
    (tape : ObservedWriteTape w store path) (wanted : WriteRoute) (key : StreamKey) (stream : Bytes)
    (output : wanted = .stdout ∨ wanted = .stderr ∨ wanted = .publicValues)
    (selected : ∀ n, destinationKey wanted n = some key) (found : key.contents (.fromEndpoints source.host target.host) = some stream)
    (length : (StreamCounts.ofStreams (.fromEndpoints source.host target.host)).offset wanted = stream.length) :
    OutputTranscript w path wanted stream := by
  let position (d : Dispatch F) := (StreamCounts.ofCursor d.previous).offset wanted
  let width (d : Dispatch F) := if d.route = wanted then d.request.header.length.toNat else 0
  let start : StreamCounts := ⟨0,0,0,0⟩
  have zero : start.offset wanted = 0 := by rcases output with rfl|rfl|rfl <;> rfl
  have chunks := split_stream stream position width (fun c => c.offset wanted)
    (fun c d => c.record d.route d.request.header.length.toNat) (fun c d => count_output wanted output c d.route _)
    path start (fun i => congrArg (fun (c : StreamCounts) => c.offset wanted) (tape.positions i))
  change _ ++ stream.drop ((dispatchCounts path).offset wanted) = stream.drop (start.offset wanted) at chunks
  rw [tape.totals,length,List.drop_length,List.append_nil,zero,List.drop_zero] at chunks
  refine ⟨fun d => (stream.drop (position d)).take (width d),chunks.symm,?_⟩
  intro d md
  refine ⟨fun no => by simp [width,no],?_⟩
  intro route
  obtain ⟨bytes,pub,_,len,guest⟩ := tape.published d md key (route ▸ selected _)
  obtain rfl := Option.some.inj (pub.symm.trans found)
  let authenticated (bytes : Bytes) := bytes.length = d.request.header.length.toNat ∧ ∀ i : Fin bytes.length, GuestByteAt w d i.val bytes[i.val]
  change authenticated _
  have slice : authenticated ((bytes.drop ((StreamCounts.ofCursor d.previous).offset d.route)).take d.request.header.length.toNat) := ⟨len,guest⟩
  simpa only [position,width,route,ite_true] using slice

/-- All three appended byte strings are the ordered concatenations of the corresponding
physical CPU guest buffers, starting after the incoming snapshot's existing bytes. -/
theorem ObservedWriteTape.outputs {w : EnsembleWitness (native image source target)} {store : Store} {path : List (Dispatch F)}
    (tape : ObservedWriteTape w store path) :
    let streams := WriteStreams.fromEndpoints source.host target.host
    OutputTranscript w path .stdout streams.stdout ∧ OutputTranscript w path .stderr streams.stderr ∧
      OutputTranscript w path .publicValues streams.publicOutput := by
  exact ⟨ordered_output tape .stdout .stdout _ (Or.inl rfl) (fun _ => rfl) rfl rfl,
    ordered_output tape .stderr .stderr _ (Or.inr (Or.inl rfl)) (fun _ => rfl) rfl rfl,
    ordered_output tape .publicValues .publicOutput _ (Or.inr (Or.inr rfl)) (fun _ => rfl) rfl rfl⟩

end SP1Clean.Export.WriteObservationAssembly
