import SP1Clean.Proofs.Completeness.ByteProviderTables
import ToClean.Air.PayloadReadCounts

/-! # Funding the original Byte providers from native Clean reader interactions -/

namespace SP1Clean.Soundness.ByteProviderDemand
open Circuit Air.Flat Air.Flat.WitnessGeneration LookupAccessList Channels
variable {p : ℕ} [Fact p.Prime] [Fact (2^25 < p)]
private local instance byteReaderBound : Fact (2^17 < p) := ⟨by have := Fact.out (p := 2^25 < p); omega⟩

/-- The normal native generator's demand tally on these evaluated reader interactions. -/
def tally (reads : List (Interaction (ZMod p))) : Tally (ZMod p) := Tally.empty.addInteractions reads

/-- Reconstruct the field message of a projected lookup key. -/
def fieldMessage (key : LookupKey) : Array (ZMod p) := (key.2.2.map Nat.cast).toArray

/-- Complete byte-channel key of an evaluated field message. -/
def messageKey (msg : Array (ZMod p)) : LookupKey := (.Byte,"SP1Byte",msg.toList.map ZMod.val)

omit [Fact (2^25 < p)] in
private theorem field_messageKey (msg : Array (ZMod p)) : fieldMessage (messageKey msg) = msg := by
  simp [fieldMessage,messageKey,List.map_map,Function.comp_def]

/-- Active message support in the generator's own physical demand order. -/
def requested (reads : List (Interaction (ZMod p))) : List LookupKey :=
  (tally reads).demands.map fun d => messageKey d.message

/-- Count reported by the original generator for a completely encoded byte-channel request. -/
def readerCount (reads : List (Interaction (ZMod p))) (key : LookupKey) : ℕ :=
  ((tally reads).net ("SP1Byte",fieldMessage (p := p) key)).natAbs

omit [Fact (2^25 < p)] in
private theorem net_at (reads : List (Interaction (ZMod p))) (ch : String) (msg : Array (ZMod p)) :
    (tally reads).net (ch,msg) = (reads.map fun i =>
      if (i.channel.name,i.msg) = (ch,msg) then Tally.signedCount i else 0).sum := by
  let applyOne := fun (t : Tally (ZMod p)) (i : Interaction (ZMod p)) => t.add i.channel.name i.msg (Tally.signedCount i)
  have accumulate (xs : List (Interaction (ZMod p))) (t : Tally (ZMod p)) :
      (xs.foldl applyOne t).net (ch,msg) = t.net (ch,msg) +
        (xs.map fun i => if (i.channel.name,i.msg) = (ch,msg) then Tally.signedCount i else 0).sum := by
    induction xs generalizing t with
    | nil => simp
    | cons i xs ih =>
      simp only [List.foldl_cons,List.map_cons,List.sum_cons,ih,applyOne,Tally.net_add]
      by_cases eq : (i.channel.name,i.msg) = (ch,msg)
      · simp [eq,add_assoc]
      · simp [eq,Ne.symm eq]
  have empty : (Tally.empty (F := ZMod p)).net (ch,msg) = 0 := by simp [Tally.net,Tally.empty]
  simpa only [tally,Tally.addInteractions,applyOne,empty,zero_add] using accumulate reads Tally.empty

omit [Fact (2^25 < p)] in
/-- A nonzero native demand originates at an actual nonzero interaction with exactly the same message. -/
theorem read_origin {reads : List (Interaction (ZMod p))} {d : Demand (ZMod p)} (active : d ∈ (tally reads).demands) :
    ∃ i ∈ reads, (i.channel.name,i.msg) = d.key ∧ i.mult ≠ 0 := by
  classical
  obtain ⟨net,nonzero⟩ := ((tally reads).mem_demands d).mp active
  by_contra absent
  have zero : (reads.map fun i => if (i.channel.name,i.msg) = d.key then Tally.signedCount i else 0).sum = 0 := by
    apply List.sum_eq_zero
    intro x used
    obtain ⟨i,seen,rfl⟩ := List.mem_map.mp used
    split
    · rename_i same
      have z : i.mult = 0 := by by_contra nonzero; exact absent ⟨i,seen,same,nonzero⟩
      cases dir : i.direction <;> simp [Tally.signedCount,dir,z]
    · rfl
  exact nonzero (net.symm.trans ((net_at reads d.channel d.message).trans zero))

/-- Typed local lookup guarantees are sufficient for the actual unit reads the original circuit
makes. The zero-weight physical sites can contain arbitrary messages. -/
theorem unit_guarantee_servable {i : Interaction (ZMod p)} (onByte : i.channel = byteChannel.toRaw)
    (pull : i.direction = .pull) (unit : i.mult = 1) (data : ProverData (ZMod p)) (honest : i.Guarantees data) :
    ByteServable (messageKey i.msg) := by
  rcases i with ⟨ch,dir,m,msg,arity⟩
  change ch = _ at onByte
  change dir = _ at pull
  change m = _ at unit
  subst ch dir m
  let r : ByteRow (ZMod p) := fromElements (⟨msg,arity⟩ : Vector _ (size ByteRow))
  have admitted : ByteRowSpec r := honest rfl rfl
  apply (byteRowSpec_iff_servable r).mp at admitted
  have eq : messageKey msg = byteLookupKey r := by
    change ((InteractionKind.Byte,"SP1Byte",msg.toList.map ZMod.val) : LookupKey) = _
    have cells : (toElements r).toArray = msg := congrArg Vector.toArray (ProvableType.toElements_fromElements _)
    rw [← cells]
    change (_,_,(toElements r).toList.map ZMod.val) = _
    rw [byteRow_toList]
    rfl
  exact eq ▸ admitted

/-- A generated reader's own requirements establish binary activity, so its own guarantees
admit the message whenever its physical multiplicity is nonzero. -/
theorem checked_reader {i : Interaction (ZMod p)} (onByte : i.channel = byteChannel.toRaw)
    (pull : i.direction = .pull) (data : ProverData (ZMod p)) (requirements : i.Requirements data)
    (honest : i.Guarantees data) (active : i.mult ≠ 0) : ByteServable (messageKey i.msg) := by
  apply unit_guarantee_servable onByte pull _ data honest
  rcases i with ⟨ch,dir,m,msg,arity⟩
  change ch = _ at onByte
  change dir = _ at pull
  subst ch dir
  exact (show m = 0 ∨ m = 1 from requirements).resolve_left active

omit [Fact (2^25 < p)] in
/-- All keys the native generator actually selects are valid if each original active reader
has its proper byte-channel guarantee. -/
theorem requested_servable (reads : List (Interaction (ZMod p)))
    (valid : ∀ i ∈ reads, i.mult ≠ 0 → ByteServable (messageKey i.msg)) :
    ∀ k ∈ requested reads, ByteServable k := by
  intro k used
  obtain ⟨d,active,rfl⟩ := List.mem_map.mp used
  obtain ⟨i,inside,same,nonzero⟩ := read_origin active
  have msg : i.msg = d.message := congrArg Prod.snd same
  rw [← msg]
  exact valid i inside nonzero


omit [Fact (2^25 < p)] in
/-- The original multiplicity tally at a message casts back to its literal signed field balance. -/
private theorem net_cast (reads : List (Interaction (ZMod p))) (msg : Array (ZMod p))
    (onByte : ∀ i ∈ reads, i.channel = byteChannel.toRaw) :
    (((tally reads).net ("SP1Byte",msg) : ℤ) : ZMod p) = balanceOf reads msg := by
  rw [net_at]
  induction reads with
  | nil => simp [balanceOf]
  | cons i tail ih =>
    have ch : i.channel.name = "SP1Byte" := congrArg RawChannel.name (onByte i List.mem_cons_self)
    have rest := ih (fun j hj => onByte j (List.mem_cons_of_mem _ hj))
    rw [List.map_cons,List.sum_cons,Int.cast_add,rest,balanceOf_cons,ch]
    simp only [Prod.mk.injEq,true_and]
    by_cases h : i.msg = msg
    · simp only [h,ite_true,add_left_inj]
      cases dir : i.direction <;> simp [Tally.signedCount,Interaction.signedMult,dir,FiniteField.val_F]
    · simp [h]

omit [Fact (2^25 < p)] in
/-- The original pull ledger is funded at its actual weights, including zero-weight rows.
Multiplicities accumulate in Clean's native integer tally before being cast into the field. -/
theorem readerCount_funds (reads : List (Interaction (ZMod p))) (msg : Array (ZMod p))
    (onByte : ∀ i ∈ reads, i.channel = byteChannel.toRaw)
    (pull : ∀ i ∈ reads, i.direction = .pull) :
    (readerCount reads (messageKey msg) : ZMod p) = -balanceOf reads msg := by
  rw [readerCount,field_messageKey]
  have nonpos : (tally reads).net ("SP1Byte",msg) ≤ 0 := by
    rw [net_at]
    have below (xs : List ℤ) (bounded : ∀ n ∈ xs, n ≤ 0) : xs.sum ≤ 0 := by
      induction xs with
      | nil => simp
      | cons x xs ih =>
        exact add_nonpos (bounded _ List.mem_cons_self) (ih (fun n hn => bounded n (List.mem_cons_of_mem _ hn)))
    apply below
    intro n used
    obtain ⟨i,inside,rfl⟩ := List.mem_map.mp used
    split
    · rw [Tally.signedCount,pull i inside]
      exact neg_nonpos.mpr (Int.natCast_nonneg _)
    · exact le_rfl
  rw [← Int.cast_natCast,Int.ofNat_natAbs_of_nonpos nonpos,Int.cast_neg,net_cast _ _ onByte]

omit [Fact (2^25 < p)] in
/-- If a reader message is absent from the native support, its actual source count is zero. -/
theorem count_zero_of_absent (reads : List (Interaction (ZMod p))) (msg : Array (ZMod p))
    (absent : messageKey msg ∉ requested reads) : readerCount reads (messageKey msg) = 0 := by
  rw [readerCount,field_messageKey]
  by_contra count
  let d : Demand (ZMod p) := ⟨"SP1Byte",msg,(tally reads).net ("SP1Byte",msg)⟩
  have nonzero : d.multiplicity ≠ 0 := by intro zero; exact count (by rw [show (tally reads).net ("SP1Byte",msg) = 0 from zero]; rfl)
  have active : d ∈ (tally reads).demands := ((tally reads).mem_demands d).mpr ⟨rfl,nonzero⟩
  exact absent (List.mem_map.mpr ⟨d,active,rfl⟩)

end SP1Clean.Soundness.ByteProviderDemand
