module

public import Clean.Specs.BLAKE3

/-! # Unkeyed BLAKE3 message hashing

Clean supplies chunk processing and compression. This extension assembles the message tree
and sets the root flag on its final compression. Its result is eight 32-bit words in BLAKE3
output order. It can be retired when Clean supplies the unkeyed digest for arbitrary messages.
-/

@[expose] public section

namespace Specs.BLAKE3

/-- Byte offset of the right subtree. The left subtree is the largest complete power-of-two
group of chunks that leaves at least one byte on the right. -/
def leftSubtreeLen (length : Nat) : Nat :=
  2 ^ ((length - 1) / chunkLen).log2 * chunkLen

private theorem leftSubtreeLen_bounds {length : Nat} (h : chunkLen < length) :
    0 < leftSubtreeLen length ∧ leftSubtreeLen length < length := by
  unfold leftSubtreeLen chunkLen at *
  have quotient : (length - 1) / 1024 ≠ 0 := by omega
  have bound := Nat.log2_self_le quotient
  have positive : 0 < 2 ^ ((length - 1) / 1024).log2 := Nat.two_pow_pos _
  omega

/-- Evaluate a subtree at its absolute chunk counter. Interior nodes concatenate both
child chaining values. The root flag applies only to the node returning the digest. -/
def subtreeWords (input : List Nat) (firstChunk : Nat) (isRoot : Bool) : Vector Nat 8 :=
  if _h : chunkLen < input.length then
    let offset := leftSubtreeLen input.length
    let left := subtreeWords (input.take offset) firstChunk false
    let right := subtreeWords (input.drop offset) (firstChunk + offset / chunkLen) false
    (compress (iv.map UInt32.toNat) (left ++ right) 0 blockLen (parent ||| (if isRoot then root else 0))).take 8
  else
    processChunk (iv.map UInt32.toNat) firstChunk input (if isRoot then root else 0)
termination_by input.length
decreasing_by
  all_goals have bounds := leftSubtreeLen_bounds _h
  · simpa [List.length_take, Nat.min_eq_left (Nat.le_of_lt bounds.2)] using bounds.2
  · simp only [List.length_drop]
    omega

/-- Standard 256-bit unkeyed BLAKE3 digest, including the single empty chunk. -/
def blake3 (input : List (BitVec 8)) : Vector Nat 8 :=
  subtreeWords (input.map BitVec.toNat) 0 true

end Specs.BLAKE3
