import SP1Clean.Proofs.Operations.HintNodeAllocatePopulate

/-! # Compiling an ordered hint prefix into fresh allocations

WRITE-to-hints adds one node; a hook may add any finite prefix. Both use the same constructor,
allocating from back to front to retain reply order. The proofs derive every local circuit
contract, the exact row count, and full cursor continuity from semantic queue representation and
one capacity bound. Matching these rows to the host call and its bytes remains AIR integration.
-/

namespace SP1Clean.HintNodeAllocate

open Circuit Semantics Semantics.HintQueue

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- After a nonempty allocation prefix its newest fresh pointer is the frontier. At
the first node the previous head may be an older surviving pointer. -/
def prefixState (clock head frontier count : ℕ) : HostHintQueue.State (ZMod p) :=
  HostHintQueue.State.encode clock (if count = 0 then head else frontier+count) (frontier+count)

private theorem prependHead (store : Store) (head : Nat) (buffers : List Bytes) :
    (prepend store head buffers).2 = if buffers.length = 0 then head else store.size + buffers.length := by
  cases buffers with
  | nil => rfl
  | cons bytes rest => simp [prepend,prepend_size,Nat.add_assoc]

/-- Compile each fresh node once, from the end of the returned list to its front. -/
def compilePrepend (clock : ℕ) (store : Store) (head : ℕ) (added : List Bytes) : List (Inputs (ZMod p)) :=
  added.reverse.zipIdx.map fun (bytes,i) => populate (prefixState clock head store.size i) bytes

omit [Fact (2 ^ 17 < p)] in
/-- Consing an earlier buffer adds one allocation after the existing suffix's genuine endpoint. -/
theorem compilePrepend_cons (clock : ℕ) (store : Store) (head : ℕ) (bytes : Bytes) (rest : List Bytes) :
    compilePrepend (p := p) clock store head (bytes :: rest) = compilePrepend clock store head rest ++
      [populate (HostHintQueue.State.encode clock (prepend store head rest).2 (prepend store head rest).1.size) bytes] := by
  simp [compilePrepend,List.zipIdx_append,prefixState,prependHead,prepend_size]

/-- Check full before/after cursor continuity, including clocks and the allocation frontier. -/
def replayCursors (initial : HostHintQueue.State (ZMod p)) (rows : List (Inputs (ZMod p))) :
    Option (HostHintQueue.State (ZMod p)) :=
  rows.foldlM (fun state row =>
    if toElements state = toElements row.previous then some row.next else none) initial

omit [Fact (2 ^ 17 < p)] in
theorem compilePrepend_length (clock : ℕ) (store : Store) (head : ℕ) (added : List Bytes) :
    (compilePrepend (p := p) clock store head added).length = added.length := by
  simp [compilePrepend]

/-- Successful semantic prepends require no extra row-readiness premise. -/
theorem compilePrepend_spec (clock : ℕ) (store : Store) (head : ℕ)
    (hints added : List Bytes) (current : Represents store head hints)
    (capacity : store.size + added.length < 2 ^ 48) :
    ∀ input ∈ compilePrepend (p := p) clock store head added, Spec input := by
  induction added with
  | nil => simp [compilePrepend]
  | cons bytes rest ih =>
    have count := prepend_size store head rest
    have small : store.size + rest.length < 2 ^ 48 := by
      simp only [List.length_cons] at capacity
      omega
    have represented := prepend_represents current rest
    intro input member
    simp only [compilePrepend_cons, List.mem_append, List.mem_singleton] at member
    rcases member with earlier | rfl
    · exact ih small input earlier
    · apply populate_spec _ bytes _ (rest ++ hints) (HostHintQueue.State.encode_binds clock represented (by omega))
      simp only [List.length_cons] at capacity
      omega

/-- The computed rows connect the complete input cursor to the semantic prepend's exact output. -/
theorem compilePrepend_replay (clock : ℕ) (store : Store) (head : ℕ) (added : List Bytes)
    (capacity : store.size + added.length < 2 ^ 48) :
    replayCursors (HostHintQueue.State.encode (p := p) clock head store.size)
      (compilePrepend clock store head added) =
        some (HostHintQueue.State.encode clock (HintQueue.prepend store head added).2
          (HintQueue.prepend store head added).1.size) := by
  induction added with
  | nil => rfl
  | cons bytes rest ih =>
    have count := prepend_size store head rest
    have small : store.size + rest.length < 2 ^ 48 := by
      simp only [List.length_cons] at capacity
      omega
    simp only [compilePrepend_cons, replayCursors, List.foldlM_append] at ih ⊢
    rw [ih small]
    simp only [Bind.bind, Option.bind_some, List.foldlM_cons, List.foldlM_nil, pure,
      populate, ite_true, Inputs.next, HostHintQueue.State.encode, NodeRecord.encode,
      Address.toNat_ofNat _ (show (HintQueue.prepend store head rest).1.size < 2 ^ 48 by omega),
      HintQueue.prepend, Array.size_push]

/-- The endpoint cursor still denotes every byte, in the original hook-reply order. -/
theorem compilePrepend_binds (clock : ℕ) (store : Store) (head : ℕ) (hints added : List Bytes)
    (current : Represents store head hints) (capacity : store.size + added.length < 2 ^ 48) :
    let next := HintQueue.prepend store head added
    (HostHintQueue.State.encode (p := p) clock next.2 next.1.size).Binds next.1 (added ++ hints) := by
  apply HostHintQueue.State.encode_binds clock (prepend_represents current added)
  rwa [prepend_size]

end SP1Clean.HintNodeAllocate
