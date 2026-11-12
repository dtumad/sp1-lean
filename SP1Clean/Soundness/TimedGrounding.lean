import SP1Clean.Soundness.TouchChains

/-! # Timed grounding for the ordinary memory slice

This is the productionized ordinary-window grounding induction. Given a batch of row-fact records
(each carrying its `LocalStepFact` and a `FrameFact`), a true
boundary state push, per-key multiset balance of the state and memory records, and the in-circuit-style
per-row ordering/shape facts, **every pull's guarantee holds** — and in particular the final state
pull's `LocalStateTruth` and the memory finalize pulls' `LocalMemTruth`.

All semantic facts are relative to the selected shard initial state and public initial clock. Boot
reachability and zero-register initialization are intentionally outside this theorem; they are supplied
only when a shard-local execution is anchored in the fixed machine model.

Current scope, kept explicit rather than hidden behind a full-machine name:

- **Balance representation**: plain `Multiset` equalities over lists of messages (no
  `LookupAccessList`/`BalanceBridge` detour) — `genesis + pushes = final + pulls` per bus/key, where
  the per-key genesis/final records are `Option`s (`optMS` — lists of length ≤ 1). The
  field→ℤ→multiset translation from the real channel data is a separate seam
  (`Model/BalanceBridge.lean` is the existing adapter).
- **The full memory axis, straight-line, single row type**: the keys are `Semantics.MemLoc`
  (registers *and* RAM word addresses). The frontier is **partial** — `live : MemLoc → Option _` —
  because a total invariant over 2^64 RAM cells is not populatable; balance itself forces a `some`
  genesis at every key the minimal row touches (the chain's head pull, whose only admissible match
  is the frontier — every batch push is too late). **Intra-row same-key chains are admitted**
  (the landed SP-6 refinement, `Soundness/TouchChains.lean`): a row may touch one location several
  times (`add x1, x1, x2`; `bne x1, x1`) — its same-key touches form a slot-ordered chain whose
  links (each later pull re-claims the row's own previous push) are *derived* from balance, never
  certified by `TouchOK`.
- **Location-dependent effect offsets** (SP1's ordinary schedule, matching `microValue`'s effect
  convention): a register write lands at `t + 4`, a RAM write at `t + 1` (`writeOffset`); register
  reads observe pre-write content anywhere in `[t, t + 3]`, while RAM reads are pinned at `δ = 0`
  (`readWindow` — the RAM effect lands at `+1`, so only the window start observes pre-effect
  content).
- **The three layers collapse into one strong induction** on the remaining rows (`walk`): at each
  step the row with **minimal state-pull time** is popped; state balance + the `+8`/mod-8
  discipline force its state pull to equal the running head and give every remaining row the
  `t + 8` gap (layer A: `stateBalance_remaining_ge_eight`); per touched key, that gap forces the
  chain's head pull to equal the `live` frontier record, derives the intra-row links, and cancels
  the whole chain (layer B: `chainForcing_step_of_gap`); and its `LocalStepFact`/`FrameFact` fire
  to advance the head, the frontier (to each chain's **last** push), and the truth invariants
  (layer C: step facts fire in time order).
- **`FrameFact` is a required per-row record beyond `Truth.LocalStepFact`**, now over **all**
  locations: the step fact alone cannot give the engine value-persistence across a window for
  locations the row does not change — chips owe frames for RAM words as well as registers.
- The `microValue` **epoch lemmas** — the register trio (`regEpoch`, `microValue_reg`,
  `localValueAt_shift`) and the RAM trio (`ramEpoch`, `microValue_ram`, `localValueAt_shift_ram`) —
  are the semantic crux of "chain linearity ⇒ currency": the trajectory content is constant on
  each epoch (`[c0+8k+4, c0+8(k+1)+4)` for registers, `[c0+8k+1, c0+8(k+1)+1)` for RAM), so
  intra-window shifts are free and cross-window persistence reduces to the rows' frames. Mid-chain
  pull currency needs no shifting at all: nothing can follow a same-key write (the SP-6 production
  value layer, `chain_pull_values`), so every chain pull carries the frontier value inside the
  pre-effect read window.
- **The SP-6 fields are load-bearing**: `RowOK.align8` (mod-8 window alignment of every state pull
  to the public initial clock) feeds `stateBalance_remaining_ge_eight`'s `t + 8` gap — the one fact
  the link derivation consumes — and `LiveOK`'s frontier-time bound (`timeNat m ≤ t` per `some`
  record) is re-established from each chain's last-push bound (`≤ t + 4 < t + 8`). -/

namespace SP1Clean.Soundness.TimedGrounding

open Sail LeanRV64D LeanRV64D.Functions
open SP1Clean.Soundness.Target
open SP1Clean.Semantics
open SP1Clean.Channels (StateMsg MemoryMsg)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-! ## The register-epoch view of `microValue` -/

/-- One real Sail step determines `stepOnce`. -/
lemma stepOnce_of_sailStep {s s' : SailState} (h : SailStep s s') : stepOnce s = some s' := by
  obtain ⟨b, hrun⟩ := h
  change SP1Clean.Machine.stepOnce s = some s'
  unfold SP1Clean.Machine.stepOnce
  rw [hrun]

/-! ## The RAM-epoch view of `microValue` -/

/-! ## The per-row records

The schedule offsets (`writeOffset`/`readWindow`), `optMS`, the touch/chain structures
(`Touch`/`TouchOK`/`ChainOK`/`rowTouchesAt`/`rowPullsAt`/`rowPushesAt`), and the SP-6 balance
lemmas live in `Soundness/TouchChains.lean` (same namespace). -/

/-- **The carrier alignment relation** (Phase B1). The engine's `RowOK` pairs each pull positionally
with the same-location push at that push's micro-time (`t+3`/`t+2` for the register read-backs, `t`
for the write slot), so the walk must be fed an *aligned* carrier — but `ChipGroundingContracts`
proves `LocalStepFact`/`FrameFact` over the *ordinary* carrier (every pull read at the window start
`t`, in emitted order), and the row-`Spec` consumers read the ordinary carrier too. `AlignsWith
r_align r_ord` records that the two share their state edge and push list and that every ordinary pull
is matched by an aligned pull carrying the same message inside the pre-write register epoch
inside that location's pre-effect read window: `[t, t+4)` for registers and the singleton
`[t, t+1)` point for RAM. -/
structure AlignsWith (r_align r_ord : RowFacts p) : Prop where
  statePull : r_align.statePull = r_ord.statePull
  statePush : r_align.statePush = r_ord.statePush
  /-- The aligned push list is a *permutation* of the ordinary one (not a list equality): the aligned
  carrier reorders the pushes into per-key push-time order so `RowOK.chain_mono` holds at aliased keys
  (`add x3,x1,x1`), while the ordinary carrier keeps the emitted order. -/
  pushes : r_align.memPushes.Perm r_ord.memPushes
  /-- The aligned pull *messages* are a permutation of the ordinary ones — needed for the memory-bus
  balance's carrier-invariance (`match_` alone is one-directional and does not give it). -/
  pulls : (r_align.memPulls.map Prod.fst).Perm (r_ord.memPulls.map Prod.fst)
  ordTime : ∀ mp ∈ r_ord.memPulls, mp.2 = StateMsg.timeNat r_ord.statePull
  match_ : ∀ mp ∈ r_ord.memPulls, ∃ mp' ∈ r_align.memPulls, mp'.1 = mp.1 ∧
    StateMsg.timeNat r_align.statePull ≤ mp'.2 ∧
    mp'.2 ≤ StateMsg.timeNat r_align.statePull + readWindow (MemoryMsg.locOf mp.1)

/-! ## The value-level carrier exchange (W3)

The refresh-eliminated walk carrier replaces a pulled record by its value-equal pre-refresh
ancestor and re-limbs its state edge canonically, so message-identity transports (`AlignsWith`)
no longer apply.  `ValueAligned` is the weakened relation that still does: the state edge carries
the same ℕ time and 64-bit pc image, the pushes are the same records, and every ordinary pull is
matched by a carrier pull with the same location and value inside the location's pre-effect read
window.  The ordinary pulls' `ClkBound` is carried as an explicit field — derived once from the
memory balance — because the carrier's rewritten records cannot return it. -/

/-! ## State-edge re-spelling (W3)

The canonicalized State trail (`Soundness/StateCanon.lean`) walks the *re-limbed* endpoints
`canonState (decodedStateEdge …)`, because only there do the StateBump rows' re-limbing edges cancel
as self-loops.  The engine, however, is fed a carrier built from the physical row's own columns.
`stateRespell` is the one-field exchange between the two: it replaces a row's State pull/push
*messages* while keeping the whole memory side, and every fact the timed walk consumes transports
across it as soon as the two spellings agree on the ℕ time and the 64-bit pc image — which
`timeNat_canonState`/`pcBits_canonState` supply on goodness-filtered rows. -/

/-- Re-spell a row's State edge, keeping the fetch and the whole memory side. -/
def stateRespell (r : RowFacts p) (pull push : StateMsg (ZMod p)) : RowFacts p :=
  { r with statePull := pull, statePush := push }

/-! ## Per-key record lists -/

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
@[simp] theorem stateRespell_memPulls (r : RowFacts p) (pull push : StateMsg (ZMod p)) :
    (stateRespell r pull push).memPulls = r.memPulls := rfl

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
@[simp] theorem stateRespell_memPushes (r : RowFacts p) (pull push : StateMsg (ZMod p)) :
    (stateRespell r pull push).memPushes = r.memPushes := rfl

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
@[simp] theorem stateRespell_statePull (r : RowFacts p) (pull push : StateMsg (ZMod p)) :
    (stateRespell r pull push).statePull = pull := rfl

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
@[simp] theorem stateRespell_statePush (r : RowFacts p) (pull push : StateMsg (ZMod p)) :
    (stateRespell r pull push).statePush = push := rfl

/-- All pulled prior messages of a batch at location `loc` (as a multiset — order is irrelevant). -/
def pullsAt (rows : List (RowFacts p)) (loc : MemLoc) : Multiset (MemoryMsg (ZMod p)) :=
  (rows.map fun r => (↑(rowPullsAt r loc) : Multiset (MemoryMsg (ZMod p)))).sum

/-- All pushed messages of a batch at location `loc`. -/
def pushesAt (rows : List (RowFacts p)) (loc : MemLoc) : Multiset (MemoryMsg (ZMod p)) :=
  (rows.map fun r => (↑(rowPushesAt r loc) : Multiset (MemoryMsg (ZMod p)))).sum

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
/-- A batch's pushes split along a concatenation. This is what lets the walked carrier's Memory
balance be read off the instruction and syscall tables separately, once `pushesAt_perm` has put the
interleaving into two blocks. -/
@[simp] theorem pushesAt_append (l l' : List (RowFacts p)) (loc : MemLoc) :
    pushesAt (l ++ l') loc = pushesAt l loc + pushesAt l' loc := by
  rw [pushesAt, List.map_append, List.sum_append, ← pushesAt, ← pushesAt]

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
/-- The pulled twin of `pushesAt_append`. -/
@[simp] theorem pullsAt_append (l l' : List (RowFacts p)) (loc : MemLoc) :
    pullsAt (l ++ l') loc = pullsAt l loc + pullsAt l' loc := by
  rw [pullsAt, List.map_append, List.sum_append, ← pullsAt, ← pullsAt]

/-! ## List/multiset helpers -/

lemma exists_min_by {α : Type} (f : α → ℕ) :
    ∀ (l : List α), l ≠ [] → ∃ r ∈ l, ∀ r' ∈ l, f r ≤ f r'
  | [], h => absurd rfl h
  | [a], _ => ⟨a, List.mem_singleton_self a, by simp⟩
  | a :: b :: l, _ => by
    obtain ⟨r, hr, hmin⟩ := exists_min_by f (b :: l) (List.cons_ne_nil b l)
    by_cases hab : f a ≤ f r
    · refine ⟨a, List.mem_cons_self, fun r' hr' => ?_⟩
      rcases List.mem_cons.mp hr' with rfl | h
      · exact le_refl _
      · exact le_trans hab (hmin r' h)
    · refine ⟨r, List.mem_cons_of_mem a hr, fun r' hr' => ?_⟩
      rcases List.mem_cons.mp hr' with rfl | h
      · omega
      · exact hmin r' h

private lemma forall₂_exists_left {α β : Type} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ R l₁ l₂) : ∀ b ∈ l₂, ∃ a ∈ l₁, R a b := by
  induction h with
  | nil => intro b hb; cases hb
  | cons hR _ ih =>
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨_, List.mem_cons_self, hR⟩
    · obtain ⟨a, ha, hab⟩ := ih b hb
      exact ⟨a, List.mem_cons_of_mem _ ha, hab⟩

lemma mem_listSum_map {α β : Type} (f : α → Multiset β) :
    ∀ (l : List α) (b : β), b ∈ (l.map f).sum ↔ ∃ a ∈ l, b ∈ f a
  | [], b => by simp
  | a :: l, b => by
    simp only [List.map_cons, List.sum_cons, Multiset.mem_add, mem_listSum_map f l b,
      List.mem_cons]
    constructor
    · rintro (h | ⟨a', ha', hb⟩)
      · exact ⟨a, Or.inl rfl, h⟩
      · exact ⟨a', Or.inr ha', hb⟩
    · rintro ⟨a', rfl | ha', hb⟩
      · exact Or.inl hb
      · exact Or.inr ⟨a', ha', hb⟩

lemma listSum_map_pop {α β : Type} (f : α → Multiset β) (l1 l2 : List α) (r : α) :
    ((l1 ++ r :: l2).map f).sum = f r + ((l1 ++ l2).map f).sum := by
  simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons]
  rw [add_left_comm]

lemma coe_map_pop {α β : Type} (f : α → β) (l1 l2 : List α) (r : α) :
    (↑((l1 ++ r :: l2).map f) : Multiset β) = f r ::ₘ ↑((l1 ++ l2).map f) := by
  exact Multiset.coe_eq_coe.mpr (List.perm_middle.map f)

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
lemma pushesAt_pop (l1 l2 : List (RowFacts p)) (r : RowFacts p) (loc : MemLoc) :
    pushesAt (l1 ++ r :: l2) loc
      = (↑(rowPushesAt r loc) : Multiset (MemoryMsg (ZMod p))) + pushesAt (l1 ++ l2) loc := by
  simp only [pushesAt]; exact listSum_map_pop _ l1 l2 r

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
lemma pullsAt_pop (l1 l2 : List (RowFacts p)) (r : RowFacts p) (loc : MemLoc) :
    pullsAt (l1 ++ r :: l2) loc
      = (↑(rowPullsAt r loc) : Multiset (MemoryMsg (ZMod p))) + pullsAt (l1 ++ l2) loc := by
  simp only [pullsAt]; exact listSum_map_pop _ l1 l2 r

/-! ## The timeline-relative engine carriers

Timeline generalizations of the walk's carriers and epoch-shift lemmas (`microValueT`,
`Timeline`, and the `…T` truth predicates live in `Model/Semantics/`).  The ordinary
instantiation recovers every uniform carrier through the `…_ordinary` bridges, so everything
upstream of the walk keeps speaking the uniform vocabulary. -/

/-- The duration-generic core of `RowOK`: the exact `+8` window width is relaxed to a
lower-bound gap, so rows of any width `≥ 8` (ordinary `8`, syscall `264`) satisfy it.  Every
other field is verbatim `RowOK`'s. -/
structure RowOKCore (initialClock : ℕ) (r : RowFacts p) : Prop where
  timeGap : StateMsg.timeNat r.statePull + 8 ≤ StateMsg.timeNat r.statePush
  align8 : StateMsg.timeNat r.statePull % 8 = initialClock % 8
  touches : List.Forall₂ (TouchOK (StateMsg.timeNat r.statePull)) r.memPulls r.memPushes
  chain_mono : ∀ loc : MemLoc, List.IsChain
    (fun a b : Touch p => MemoryMsg.timeNat a.2 < MemoryMsg.timeNat b.2) (rowTouchesAt r loc)
  pushClkBound : ∀ m ∈ r.memPushes, SP1Clean.Channels.MemoryMsg.ClkBound m
  slotOfClkBound : ∀ pq ∈ r.memPulls.zip r.memPushes,
    SP1Clean.Channels.MemoryMsg.ClkBound (pq : Touch p).1.1 →
    MemoryMsg.timeNat (pq : Touch p).1.1 < MemoryMsg.timeNat pq.2

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
/-- `RowOKCore` transports across a time-preserving State re-spelling, for the same reason its
eight-tick sibling does: every field either ignores the State messages entirely or reads only
their ℕ time.  This is the form a 264-tick row needs, since it never satisfies `RowOK.time8`. -/
theorem rowOKCore_stateRespell {initialClock : ℕ} {r : RowFacts p} {pull push : StateMsg (ZMod p)}
    (hpull : StateMsg.timeNat pull = StateMsg.timeNat r.statePull)
    (hpush : StateMsg.timeNat push = StateMsg.timeNat r.statePush)
    (h : RowOKCore initialClock r) :
    RowOKCore initialClock (stateRespell r pull push) where
  timeGap := by
    show StateMsg.timeNat pull + 8 ≤ StateMsg.timeNat push
    rw [hpull, hpush]
    exact h.timeGap
  align8 := by
    show StateMsg.timeNat pull % 8 = initialClock % 8
    rw [hpull]
    exact h.align8
  touches := by
    show List.Forall₂ (TouchOK (StateMsg.timeNat pull)) r.memPulls r.memPushes
    rw [hpull]
    exact h.touches
  chain_mono := h.chain_mono
  pushClkBound := h.pushClkBound
  slotOfClkBound := h.slotOfClkBound

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
/-- `RowOK.chainOK`, on the duration-generic core (same proof — no field it reads changed). -/
lemma RowOKCore.chainOK {initialClock : ℕ} {r : RowFacts p} (hok : RowOKCore initialClock r)
    (loc : MemLoc)
    (hclk : ∀ pq ∈ rowTouchesAt r loc,
      SP1Clean.Channels.MemoryMsg.ClkBound (pq : Touch p).1.1) :
    ChainOK loc (StateMsg.timeNat r.statePull) (rowTouchesAt r loc) := by
  have hmem : ∀ pq ∈ rowTouchesAt r loc,
      TouchOK (StateMsg.timeNat r.statePull) pq.1 pq.2 ∧ MemoryMsg.locOf pq.2 = loc := by
    intro pq hpq
    obtain ⟨hz, hloc⟩ := mem_rowTouchesAt.mp hpq
    exact ⟨List.forall₂_zip hok.touches hz, hloc⟩
  refine
    { pull_loc := fun pq hpq => ?_
      push_loc := fun pq hpq => (hmem pq hpq).2
      slot := fun pq hpq =>
        hok.slotOfClkBound pq (mem_rowTouchesAt.mp hpq).1 (hclk pq hpq)
      read_lo := fun pq hpq => (hmem pq hpq).1.read_lo
      read_hi := fun pq hpq => ?_
      push_kind := fun pq hpq => ?_
      push_mono := hok.chain_mono loc }
  · rw [← (hmem pq hpq).1.loc_eq]; exact (hmem pq hpq).2
  · have h := (hmem pq hpq).1.read_hi
    rwa [(hmem pq hpq).1.loc_eq.symm.trans (hmem pq hpq).2] at h
  · rcases (hmem pq hpq).1.push_kind with h | h
    exacts [Or.inl h, Or.inr (by rwa [(hmem pq hpq).2] at h)]

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
/-- `push_time_ge`, on the duration-generic core. -/
lemma pushTimeGe_core {c0 : ℕ} {r : RowFacts p} (hok : RowOKCore c0 r)
    {q : MemoryMsg (ZMod p)} (hq : q ∈ r.memPushes) :
    StateMsg.timeNat r.statePull ≤ MemoryMsg.timeNat q := by
  obtain ⟨mp, -, hto⟩ := forall₂_exists_left hok.touches q hq
  exact hto.push_lo

/-! ## The timed grounding walk -/

end SP1Clean.Soundness.TimedGrounding
