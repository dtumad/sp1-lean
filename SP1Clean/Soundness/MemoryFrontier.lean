import SP1Clean.Soundness.TypedMemoryBalance

/-! # Memory frontiers for the timed grounding walk

This adapter turns the complete typed Memory ledger into the per-location equation used by
`TimedGrounding.walk`. Optional initial and final records come from unique boundary messages;
active ordinary rows and all refresh, HALT and syscall messages retain their multiplicities.
Every physical table is evaluated with the ensemble's canonical prover data.

Provider purity, boundary uniqueness and inactive-row silence are explicit premises of this
legacy SP1-assembly adapter. The authenticated native and local assemblies derive their boundary
facts separately; this algebraic transport does not discharge those semantic obligations.
The initial provider's value and clock contract establish the walk's `LiveOK` invariant.
-/
namespace SP1Clean.Soundness

open Air.Flat Circuit
open SP1Clean.Channels
open SP1Clean.Semantics
open SP1Clean.Soundness.Target
open SP1Clean.Soundness.TimedGrounding

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-! ## Generic list/multiset helpers -/

section Generic

/-- An optional boundary record is the coercion of a `≤ 1`-length list to a multiset. -/
lemma optMS_head?_eq_coe {α : Type} (xs : List α) (h : xs.length ≤ 1) :
    optMS xs.head? = (↑xs : Multiset α) := by
  match xs with
  | [] => rfl
  | [a] => rfl
  | a :: b :: t => simp at h

/-- Coerced-list filter distributes over append. -/
lemma filter_coe_append {α : Type*} (P : α → Prop) [DecidablePred P] (X Y : List α) :
    Multiset.filter P (↑(X ++ Y) : Multiset α) =
      Multiset.filter P (↑X : Multiset α) + Multiset.filter P (↑Y : Multiset α) := by
  rw [← Multiset.coe_add, Multiset.filter_add]

/-- Coerced-list filter distributes over `flatMap`, block by block. -/
lemma filter_coe_flatMap {α β : Type*} (P : β → Prop) [DecidablePred P]
    (l : List α) (f : α → List β) :
    Multiset.filter P (↑(l.flatMap f) : Multiset β) =
      (l.map (fun x => Multiset.filter P (↑(f x) : Multiset β))).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, List.map_cons, List.sum_cons, ← ih, filter_coe_append]

/-- A mapped-sum is unchanged by dropping elements whose image is zero. -/
lemma sum_map_eq_sum_filter {α : Type*} {β : Type*} [AddCommMonoid β]
    (l : List α) (q : α → Bool) (g : α → β)
    (h : ∀ x ∈ l, q x = false → g x = 0) :
    (l.map g).sum = ((l.filter q).map g).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, List.filter_cons]
    split_ifs with hq
    · rw [List.map_cons, List.sum_cons, ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    · rw [ih (fun x hx => h x (List.mem_cons_of_mem _ hx)),
        h a List.mem_cons_self (by simpa using hq), zero_add]

/-- A list pairwise-distinct under `f` has at most one element mapping to any given value. -/
lemma pairwise_distinct_filter_length_le_one {α : Type*} {γ : Type*} [DecidableEq γ]
    (f : α → γ) (l : List α) (loc : γ)
    (h : l.Pairwise (fun a b => f a ≠ f b)) :
    (l.filter (fun a => decide (f a = loc))).length ≤ 1 := by
  rcases hfilter : l.filter (fun a => decide (f a = loc)) with _ | ⟨a, _ | ⟨b, t⟩⟩
  · simp
  · simp
  · exfalso
    have hpw : (l.filter (fun a => decide (f a = loc))).Pairwise (fun a b => f a ≠ f b) :=
      List.Pairwise.sublist List.filter_sublist h
    rw [hfilter] at hpw
    have hne : f a ≠ f b := (List.pairwise_cons.mp hpw).1 b List.mem_cons_self
    have hloc : ∀ x ∈ a :: b :: t, f x = loc := fun x hx => by
      have hmem : x ∈ l.filter (fun a => decide (f a = loc)) := by rw [hfilter]; exact hx
      simpa using (List.mem_filter.mp hmem).2
    exact hne ((hloc a List.mem_cons_self).trans
      (hloc b (List.mem_cons_of_mem _ List.mem_cons_self)).symm)

end Generic

/-! ## The per-`MemLoc` genesis and final frontiers -/

/-! ## The frontier ↔ filtered-multiset bridges -/

/-! ## The active-row carrier and its per-key push/pull bridges -/

/-- The walk's ordinary `RowFacts` carrier: the active decoded rows' ordinary records. -/
noncomputable def memoryFrontierRows (witness : EnsembleWitness (sp1Ensemble (p := p))) :
    List (RowFacts p) :=
  (realDecodedInstructionRows witness.data witness.tables).map
    (fun decoded => decoded.ordinaryRowFacts witness.data)

/-- One active row's per-location pushes are its produced Memory messages, filtered. -/
lemma rowPushesAt_ordinaryRowFacts_coe (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) (loc : MemLoc) :
    (↑(rowPushesAt (decoded.ordinaryRowFacts data) loc) : Multiset (MemoryMsg (ZMod p))) =
      Multiset.filter (fun m => Semantics.MemoryMsg.locOf m = loc)
        (↑(decoded.producedMemoryMessages data) : Multiset (MemoryMsg (ZMod p))) := by
  rw [Multiset.filter_coe]
  simp only [rowPushesAt, DecodedInstructionRow.ordinaryRowFacts_memPushes]

/-- One active row's per-location pulls are its consumed Memory messages, filtered. -/
lemma rowPullsAt_ordinaryRowFacts_coe (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) (loc : MemLoc) :
    (↑(rowPullsAt (decoded.ordinaryRowFacts data) loc) : Multiset (MemoryMsg (ZMod p))) =
      Multiset.filter (fun m => Semantics.MemoryMsg.locOf m = loc)
        (↑(decoded.consumedMemoryMessages data) : Multiset (MemoryMsg (ZMod p))) := by
  have key : ((decoded.consumedMemoryMessages data).map
        (fun message => (message,
          StateMsg.timeNat (statePullMessage (decoded.toChipRow data))))).map (fun x => x.1)
      = decoded.consumedMemoryMessages data := by
    simp only [List.map_map, Function.comp_def, List.map_id_fun', id_eq]
  rw [Multiset.filter_coe]
  simp only [rowPullsAt, DecodedInstructionRow.ordinaryRowFacts_memPulls, key]

/-- Shared skeleton of the two active-carrier bridges below, over a loose per-row selector pair: the
active carrier's aggregate at `loc` is the filter of *all* decoded rows' messages, once each row's
per-location list is that row's filtered message list (`hrow`) and padding rows contribute nothing. -/
private lemma frontierRows_agg_eq (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (rowSel : RowFacts p → MemLoc → List (MemoryMsg (ZMod p)))
    (msgSel : DecodedInstructionRow p → ProverData (ZMod p) → List (MemoryMsg (ZMod p)))
    (hrow : ∀ (decoded : DecodedInstructionRow p) (loc : MemLoc),
      (↑(rowSel (decoded.ordinaryRowFacts witness.data) loc) : Multiset (MemoryMsg (ZMod p))) =
        Multiset.filter (fun m => Semantics.MemoryMsg.locOf m = loc)
          (↑(msgSel decoded witness.data) : Multiset (MemoryMsg (ZMod p))))
    (paddingEmpty : ∀ decoded ∈ decodedInstructionRows (p := p) witness.tables,
      (decoded.toChipRow witness.data).is_real ≠ 1 → msgSel decoded witness.data = [])
    (loc : MemLoc) :
    ((memoryFrontierRows witness).map
        (fun r => (↑(rowSel r loc) : Multiset (MemoryMsg (ZMod p))))).sum =
      Multiset.filter (fun m => Semantics.MemoryMsg.locOf m = loc)
        (↑((decodedInstructionRows (p := p) witness.tables).flatMap
          (fun decoded => msgSel decoded witness.data)) : Multiset (MemoryMsg (ZMod p))) := by
  have hL : ((memoryFrontierRows witness).map
        (fun r => (↑(rowSel r loc) : Multiset (MemoryMsg (ZMod p))))).sum =
      ((realDecodedInstructionRows witness.data witness.tables).map
        (fun decoded => Multiset.filter (fun m => Semantics.MemoryMsg.locOf m = loc)
          (↑(msgSel decoded witness.data) : Multiset (MemoryMsg (ZMod p))))).sum := by
    rw [memoryFrontierRows, List.map_map]
    exact congrArg List.sum (List.map_congr_left fun decoded _ => hrow decoded loc)
  have hR : Multiset.filter (fun m => Semantics.MemoryMsg.locOf m = loc)
      (↑((decodedInstructionRows (p := p) witness.tables).flatMap
        (fun decoded => msgSel decoded witness.data)) : Multiset (MemoryMsg (ZMod p))) =
      ((realDecodedInstructionRows witness.data witness.tables).map
        (fun decoded => Multiset.filter (fun m => Semantics.MemoryMsg.locOf m = loc)
          (↑(msgSel decoded witness.data) : Multiset (MemoryMsg (ZMod p))))).sum := by
    rw [filter_coe_flatMap,
      show realDecodedInstructionRows witness.data witness.tables =
        (decodedInstructionRows (p := p) witness.tables).filter
          (fun row => decide ((row.toChipRow witness.data).is_real = 1)) from rfl]
    exact sum_map_eq_sum_filter _ _ _ (fun decoded decodedMem hq => by
      rw [paddingEmpty decoded decodedMem (by simpa using hq)]; rfl)
  rw [hL, hR]

/-- **The active push bridge.** The active carrier's total per-location pushes equal the filter of all
decoded rows' produced Memory messages — the term appearing in B4's balance.  Padding rows drop out
(`paddingEmpty`). -/
lemma pushesAt_memoryFrontierRows (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (paddingEmpty : ∀ decoded ∈ decodedInstructionRows (p := p) witness.tables,
      (decoded.toChipRow witness.data).is_real ≠ 1 →
        decoded.producedMemoryMessages witness.data = [] ∧
          decoded.consumedMemoryMessages witness.data = [])
    (loc : MemLoc) :
    pushesAt (memoryFrontierRows witness) loc =
      Multiset.filter (fun m => Semantics.MemoryMsg.locOf m = loc)
        (↑((decodedInstructionRows (p := p) witness.tables).flatMap
          (fun decoded => decoded.producedMemoryMessages witness.data)) :
            Multiset (MemoryMsg (ZMod p))) :=
  frontierRows_agg_eq witness rowPushesAt DecodedInstructionRow.producedMemoryMessages
    (fun decoded loc => rowPushesAt_ordinaryRowFacts_coe decoded witness.data loc)
    (fun decoded decodedMem hne => (paddingEmpty decoded decodedMem hne).1) loc

/-- **The active pull bridge** (consumed analogue of `pushesAt_memoryFrontierRows`). -/
lemma pullsAt_memoryFrontierRows (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (paddingEmpty : ∀ decoded ∈ decodedInstructionRows (p := p) witness.tables,
      (decoded.toChipRow witness.data).is_real ≠ 1 →
        decoded.producedMemoryMessages witness.data = [] ∧
          decoded.consumedMemoryMessages witness.data = [])
    (loc : MemLoc) :
    pullsAt (memoryFrontierRows witness) loc =
      Multiset.filter (fun m => Semantics.MemoryMsg.locOf m = loc)
        (↑((decodedInstructionRows (p := p) witness.tables).flatMap
          (fun decoded => decoded.consumedMemoryMessages witness.data)) :
            Multiset (MemoryMsg (ZMod p))) :=
  frontierRows_agg_eq witness rowPullsAt DecodedInstructionRow.consumedMemoryMessages
    (fun decoded loc => rowPullsAt_ordinaryRowFacts_coe decoded witness.data loc)
    (fun decoded decodedMem hne => (paddingEmpty decoded decodedMem hne).2) loc

/-! ## The frontier balance -/

/-! ## The genesis `LiveOK` invariant -/

end SP1Clean.Soundness
