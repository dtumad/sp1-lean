import SP1Clean.Proofs.Completeness.WriteBlockRequests
import SP1Clean.Proofs.Completeness.WriteWitnessAllocationAssembly
import ToClean.Air.ReaderCounts
import ToClean.Air.StaticPayloadTable

/-! # Funding occupied allocation words and the fixed returned-block source

After collecting the original row values, only the word's block-reader count is filled.
All queue payloads, word-reader counts, and the word-walk cursor are preserved at the
same physical positions. The preallocated endpoint source uses the verifier's fixed rows.
-/

namespace SP1Clean.WriteEffects.Witness
open Circuit Air.Flat Semantics Machine FormalModel.Shard TraceGen WriteAllocation
private abbrev F := ZMod SP1Prime

/-- Place the one-pass count of assigned tag-14 queries in its genuine allocation word.
Array access retains the original order and gives constant-time access to each input. -/
def fundedWords (words : List (Words.Row F)) (uses : List (Fin words.length)) : List (Words.Row F) :=
  let rows := words.toArray
  let counts := ReaderCounts.counts uses
  List.ofFn fun i : Fin words.length => { rows[i.val]'(by simp [rows]) with blockReads := (counts[i] : F) }

theorem fundedWords_length (words : List (Words.Row F)) (uses : List (Fin words.length)) :
    (fundedWords words uses).length = words.length := List.length_ofFn

/-- The physical position, original contents and exact natural number of occurrences. -/
theorem fundedWords_at (words : List (Words.Row F)) (uses : List (Fin words.length)) (i : Fin words.length) :
    (fundedWords words uses)[i.val]'(by rw [fundedWords_length]; exact i.isLt) =
      {words[i] with blockReads := (uses.count i : F)} := by
  simp only [fundedWords,List.getElem_ofFn,List.getElem_toArray,ReaderCounts.counts_at]
  rfl

/-- Reader multiplicities have no effect on the genuine word constraints or guarantees. -/
theorem fundedWords_valid (words : List (Words.Row F)) (uses : List (Fin words.length))
    (valid : ∀ r ∈ words, r.Valid) : ∀ r ∈ fundedWords words uses, r.Valid := by
  intro r mem
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp mem
  exact valid words[i] (List.getElem_mem ..)

private theorem maps {α : Type} (words : List (Words.Row F)) (uses : List (Fin words.length)) (f : Words.Row F → α)
    (stable : ∀ r n, f {r with blockReads := n} = f r) :
    (fundedWords words uses).map f = words.map f := by
  simp only [fundedWords,List.map_ofFn,Function.comp_def,List.getElem_toArray,stable]
  exact List.ofFn_getElem_eq_map words f

/-- All returned-block queries remain in physical order, including repeated payloads. -/
theorem fundedWords_returns (words : List (Words.Row F)) (uses : List (Fin words.length)) :
    returnedRequests (fundedWords words uses) = returnedRequests words := by
  let query := fun r : Words.Row F => (r.hookGate,r.returned)
  have eq := maps words uses query (by intros; rfl)
  let active := fun l : List (F × StreamBlock F) => (l.filter (fun x => x.1 = 1)).map Prod.snd
  simpa only [query,active,List.filter_map,Function.comp_def,List.map_map,returnedRequests]
    using congrArg active eq

/-- Filling the placement counts preserves all immutable queue-word messages and the
independent multiplicities needed by subsequent queue consumers. -/
theorem fundedWords_queue (words : List (Words.Row F)) (uses : List (Fin words.length)) :
    (fundedWords words uses).map (fun r => (r.wordReads,r.word)) = words.map (fun r => (r.wordReads,r.word)) :=
  maps words uses _ (by intros; rfl)

/-- Funding the external block bus preserves every occurrence on the internal cursor bus,
including the final zero-weight cursor and all guarded padding. -/
theorem fundedWords_cursors (words : List (Words.Row F)) (uses : List (Fin words.length))
    (data : ProverData F) (fit : WitnessGeneration.demandHeight words.length ≤ UInt64.size) :
    (Words.wordTable (fundedWords words uses) data (by rwa [fundedWords_length])).interactionsWith Words.cursorChannel.toRaw =
      (Words.wordTable words data fit).interactionsWith Words.cursorChannel.toRaw := by
  simp only [Words.wordTable_cursors,WitnessGeneration.guardedRows,List.flatMap_append,List.flatMap_map,fundedWords_length]
  congr 1
  exact congrArg List.flatten (maps words uses (fun r => Words.wordCursors (r,1)) (by intros; rfl))

/-- Every assigned unit read contributes its natural count at its chosen live word.
Unchosen physical words remain in the list with zero multiplicity even if payloads repeat. -/
theorem fundedWords_emits (words : List (Words.Row F)) (uses : List (Fin words.length))
    (enabled : ∀ i ∈ uses, words[i].directGate = 1) :
    (fundedWords words uses).map (fun r => blockChannel.emittedValue (r.directGate*r.blockReads) r.direct) =
      List.ofFn (fun i : Fin words.length => blockChannel.emittedValue ((ReaderCounts.counts uses)[i] : F) (words[i].direct)) := by
  simp only [fundedWords,List.map_ofFn,Function.comp_def,List.getElem_toArray]
  apply congrArg List.ofFn
  funext i
  change blockChannel.emittedValue ((words[i]).directGate*((ReaderCounts.counts uses)[i] : F)) words[i].direct = _
  by_cases used : i ∈ uses
  · rw [enabled i used,one_mul]
  · rw [ReaderCounts.counts_at,List.count_eq_zero.mpr used,Nat.cast_zero,mul_zero]

/-- An index unused by the hook word walk contributes zero to its actual fixed row. -/
theorem fixedCounts_eligible {t : StaticTable F StreamBlock} (uses : List (Fin t.height))
    (enabled : ∀ i ∈ uses, (t.fixedEntry i.val).eligible = 1) (i : Fin t.height) :
    ((ReaderCounts.counts uses)[i] : F) = 0 ∨ (t.fixedEntry i.val).eligible = 1 := by
  by_cases member : i ∈ uses
  · exact Or.inr (enabled i member)
  · exact Or.inl (by rw [ReaderCounts.counts_at,List.count_eq_zero.mpr member,Nat.cast_zero])

end SP1Clean.WriteEffects.Witness
