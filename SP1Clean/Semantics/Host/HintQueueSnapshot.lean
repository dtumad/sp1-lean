module

public import SP1Clean.Semantics.Host.HintQueueWordRecords

/-! # Reading a full outgoing hint queue from a persistent store

The final pointer can refer to a source node or to a surviving allocation. Metadata supplies
the next pointer and length. Reading the padded last word fixes the true natural length, and
reading every word fixes the entire payload. Unreachable nodes do not affect the snapshot.
-/

@[expose] public section

namespace SP1Clean.Semantics.HintQueue

open Soundness.Target
variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The actual lookup messages for a claimed node in the outgoing host snapshot. -/
def ReadsNode (p : ℕ) [Fact p.Prime] (store : Store) (head tail : ℕ) (bytes : Bytes) : Prop :=
  (NodeRecord.encode (p := p) head ⟨bytes, tail⟩).Binds store ∧
    ∀ i < wordCount bytes, (WordRecord.encode (p := p) head bytes i).Binds store

/-- Even an empty hint has a final padded word. Its marker excludes a longer node with
the same length word modulo 2^64 or the same byte prefix. -/
theorem readsNode_iff {store : Store} {head tail : ℕ} {bytes : Bytes}
    (address : head < 2 ^ 48) (descends : tail < head) (positions : wordCount bytes ≤ 2 ^ 48) :
    ReadsNode p store head tail bytes ↔ node? store head = some ⟨bytes, tail⟩ := by
  constructor
  · rintro ⟨metadata, words⟩
    obtain ⟨node, found, next, size⟩ := metadata
    simp only [NodeRecord.encode, Address.toNat_ofNat _ address, Address.toNat_ofNat _ (descends.trans address),
      toBitVec64_bitVecToWord] at found next size
    have last := wordCount_pos bytes
    let i := wordCount bytes - 1
    have inside : i < wordCount bytes := by dsimp [i]; omega
    have lastEq : i + 1 = wordCount bytes := by dsimp [i]; omega
    have ended := (words i inside).isLast_iff (node := node) (by
      simpa only [WordRecord.encode, Address.toNat_ofNat _ address] using found)
    simp only [WordRecord.encode, lastEq, ite_true, Address.toNat_ofNat _ (inside.trans_le positions)] at ended
    have sameCount := ended.mp trivial
    simp only [wordCount] at positions sameCount lastEq
    have claimedFits : bytes.length < 2 ^ 64 := by omega
    have actualFits : node.bytes.length < 2 ^ 64 := by omega
    have length := congrArg BitVec.toNat size
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt claimedFits, Nat.mod_eq_of_lt actualFits] at length
    have exactBytes := bytes_eq_of_word_records (p := p) found bytes length (by
      intro j hj
      refine ⟨_, words j hj, Address.toNat_ofNat _ address, Address.toNat_ofNat _ (hj.trans_le ?_), ?_⟩
      · simpa only [wordCount] using positions
      · exact toBitVec64_bitVecToWord _)
    cases node
    simpa only [exactBytes, next] using found
  · intro found
    exact ⟨NodeRecord.encode_binds found address descends,
      fun i inside => WordRecord.encode_binds found address i inside (inside.trans_le positions)⟩

/-- One private tail pointer per public target buffer, in queue order. The walk finishes at
the null pointer. A nonempty target can be backed by any well-formed allocated chain. -/
def ReadsSnapshot (p : ℕ) [Fact p.Prime] (store : Store) : ℕ → List Bytes → List ℕ → Prop
  | head, [], [] => head = 0
  | head, bytes :: rest, tail :: tails => head < 2 ^ 48 ∧ tail < head ∧ wordCount bytes ≤ 2 ^ 48 ∧
      ReadsNode p store head tail bytes ∧ ReadsSnapshot p store tail rest tails
  | _, _, _ => False

theorem ReadsSnapshot.represents {store : Store} {head : ℕ} {hints : List Bytes} {tails : List ℕ}
    (read : ReadsSnapshot p store head hints tails) : Represents store head hints := by
  induction hints generalizing head tails with
  | nil =>
    cases tails with
    | nil => exact (show head = 0 from read) ▸ .nil
    | cons => contradiction
  | cons bytes rest ih =>
    cases tails with
    | nil => contradiction
    | cons tail tails =>
      obtain ⟨fits, down, positions, node, remaining⟩ := read
      exact .cons ((readsNode_iff fits down positions).mp node) down (ih remaining)

/-- A represented queue supplies every private pointer and lookup for its fixed target. -/
theorem Represents.readsSnapshot {store : Store} {head : ℕ} {hints : List Bytes}
    (queue : Represents store head hints) (frontier : store.size < 2 ^ 48)
    (width : ∀ bytes ∈ hints, wordCount bytes ≤ 2 ^ 48) :
    ∃ tails, ReadsSnapshot p store head hints tails := by
  induction queue with
  | nil => exact ⟨[], rfl⟩
  | @cons head tail bytes rest found down suffix ih =>
    have address := (node?_bound found).2.trans_lt frontier
    have positions := width bytes (.head _)
    obtain ⟨tails, remaining⟩ := ih (fun b hb => width b (.tail _ hb))
    exact ⟨tail :: tails, address, down, positions, (readsNode_iff address down positions).mpr found, remaining⟩

end SP1Clean.Semantics.HintQueue
