import SP1Clean.Proofs.Operations.WriteAllocationWords
import SP1Clean.Proofs.Completeness.WriteAllocationWordRows
import SP1Clean.Proofs.Completeness.WriteGroupRows
import ToClean.Air.GuardedDemandTable

/-! # Producing both physical contents tables for an authorized WRITE allocation

These tables use the existing demand scheduler's guarded rows. The private block on either
side of a grouped guest placement is the same block as that allocation word's positive source.
-/

namespace SP1Clean.WriteAllocation.Words
open Circuit Air.Flat Semantics Semantics.HintQueue WriteEffects

variable {p : Nat} [Fact p.Prime] [Fact (2^17 < p)]

omit [Fact (2^17 < p)] in
/-- A grouped tag-14 placement consumes precisely the block carried by the corresponding
fresh word. Both sides of a cross-block placement retain their own occurrence. -/
theorem populate_direct_group (c : Contents (ZMod p)) (bytes : Bytes) (br wr : ZMod p)
    (octets : Octets (ZMod p)) (first size base : Nat) (right : Bool) :
    let i := if right then base/8+1 else base/8
    (populate c bytes i br wr).direct = (Group.populate octets 14 c.pointer first size base bytes).block right := by
  cases right <;> simp only [Bool.false_eq_true,↓reduceIte,populate_direct,Group.populate,Group.block,extent]
  all_goals rfl

/-- Compile the mandatory seed table for all authorized fresh nodes. -/
def seedTable (nodes : List (Contents (ZMod p))) (data : ProverData (ZMod p))
    (fit : WitnessGeneration.demandHeight nodes.length ≤ UInt64.size) : Table (ZMod p) :=
  Table.ofInputs seedComponent (WitnessGeneration.guardedRows nodes) data
    ((WitnessGeneration.guardedRows_length nodes).trans_le fit) (fun _ => trivial)

omit [Fact (2^17 < p)] in
/-- The generated seed table is checked for any list of actual node authorizations. -/
theorem seedTable_valid (nodes : List (Contents (ZMod p))) (data : ProverData (ZMod p)) (fit) :
    (seedTable nodes data fit).Constraints ∧ (seedTable nodes data fit).Guarantees := by
  apply Table.ofInputs_valid
  exact WitnessGeneration.guardedRows_all (fun _ => True) (by intros; trivial)

/-- Compile the consecutive words of all fresh nodes at the canonical demand height. -/
def wordTable (rows : List (Row (ZMod p))) (data : ProverData (ZMod p))
    (fit : WitnessGeneration.demandHeight rows.length ≤ UInt64.size) : Table (ZMod p) :=
  Table.ofInputs wordComponent (WitnessGeneration.guardedRows rows) data
    ((WitnessGeneration.guardedRows_length rows).trans_le fit) (fun _ => trivial)

omit [Fact (2^17 < p)] in
/-- A full walk of one actual fresh node fits the physical UInt64 row domain from its existing
48-bit length. Padding counts are derived here rather than supplied to the caller. -/
theorem walk_height (c : Contents (ZMod p)) (bytes : Bytes) (br wr : Nat → ZMod p)
    (length : bytes.length < 2^48) : WitnessGeneration.demandHeight (walk c bytes br wr).length ≤ UInt64.size := by
  rw [walk_length]
  apply (WitnessGeneration.demandHeight_le_pow (exponent := 48) ?_).trans (show 2^48 ≤ UInt64.size by decide)
  unfold wordCount
  omega

/-- Clean checks constraints and guarantees for every honest fresh word, including padding. -/
theorem walk_table_valid (c : Contents (ZMod p)) (bytes : Bytes) (br wr : Nat → ZMod p)
    (mode : IsBool c.direct) (pointer : Address.Bounded c.pointer) (positive : 0 < Address.toNat c.pointer)
    (length : bytes.length < 2^48) (data : ProverData (ZMod p)) :
    let table := wordTable (walk c bytes br wr) data (walk_height c bytes br wr length)
    table.Constraints ∧ table.Guarantees := by
  apply Table.ofInputs_valid
  apply WitnessGeneration.guardedRows_all Row.Valid
  intro r member
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp (show r ∈ List.ofFn _ from member)
  exact populate_valid c bytes i.val (br i.val) (wr i.val) mode pointer positive length i.isLt

end SP1Clean.WriteAllocation.Words
