import SP1Clean.Proofs.Completeness.ByteReaderTally

/-! # Simultaneous signed balance of all native Byte demand providers -/

namespace SP1Clean.Soundness.ByteProviderDemand
open Circuit Air.Flat LookupAccessList Channels
variable {p : ℕ} [Fact p.Prime] [Fact (2^25 < p)]
private local instance providerBalanceWidth : Fact (2^24 < p) := ⟨by have := Fact.out (p := 2^25 < p); omega⟩

private theorem op_bound (op : ByteProviderId) : (operation op).idx < 6 := by cases op <;> decide

private theorem same_op {a b : ByteProviderId} (h : (operation a).idx = (operation b).idx) : a = b := by
  cases a <;> cases b <;> first | rfl | contradiction

/-- A complete message can be claimed by at most one of the original providers. -/
theorem selects_unique {k : LookupKey} {a b : Id} (ha : selects a k) (hb : selects b k) : a = b := by
  cases a with
  | inl op =>
    have code := cell_zero_of_selByte ha
    cases b with
    | inl other => exact congrArg Sum.inl (same_op (code.symm.trans (cell_zero_of_selByte hb)))
    | inr w =>
      have small := op_bound op
      change selRange w k = true at hb
      simp only [selRange,Bool.and_eq_true,decide_eq_true_eq] at hb
      omega
  | inr w =>
    change selRange w k = true at ha
    simp only [selRange,Bool.and_eq_true,decide_eq_true_eq] at ha
    cases b with
    | inl op =>
      have code := cell_zero_of_selByte hb
      have small := op_bound op
      omega
    | inr v =>
      change selRange v k = true at hb
      simp only [selRange,Bool.and_eq_true,decide_eq_true_eq] at hb
      exact congrArg Sum.inr (Fin.ext (ha.2.2.symm.trans hb.2.2))

/-- Every message supported by the release lands in a real opcode or valid physical width. -/
theorem selects_exists {k : LookupKey} (shape : IsByteKey k) (served : ByteServable k) : ∃ id, selects id k := by
  have choose (op : ByteProviderId) (code : cell k 0 = (operation op).idx) : selects (.inl op) k := by
    simp only [selects,selByte,shape,code,decide_true,Bool.and_self]
  have supported : cell k 0 ≤ 6 := by
    by_contra outside
    obtain ⟨n,above⟩ := Nat.exists_eq_add_of_le (by omega : 7 ≤ cell k 0)
    unfold ByteServable at served
    rw [above,Nat.add_comm] at served
    exact served
  generalize date : cell k 0 = n at supported
  interval_cases n
  · exact ⟨.inl .andByte,choose _ date⟩
  · exact ⟨.inl .orByte,choose _ date⟩
  · exact ⟨.inl .xorByte,choose _ date⟩
  · exact ⟨.inl .u8Range,choose _ date⟩
  · exact ⟨.inl .ltu,choose _ date⟩
  · exact ⟨.inl .msb,choose _ date⟩
  · simp only [ByteServable,date] at served
    let w : RangeChip.Width := ⟨cell k 2, Nat.lt_succ_of_le served.2.1⟩
    refine ⟨.inr w,?_⟩
    simp only [selects,selRange,shape,date,true_and,Bool.true_and,decide_eq_true_eq]
    rfl

private theorem all_nodup : all.Nodup := by decide

private theorem all_mem (id : Id) : id ∈ all := by
  cases id with
  | inl op => apply List.mem_append_left; exact List.mem_map_of_mem (ByteProviderId.mem_all op)
  | inr w => apply List.mem_append_right; exact List.mem_map_of_mem (List.mem_finRange w)

private theorem sum_unique {α : Type} [DecidableEq α] (xs : List α) (unique : xs.Nodup)
    (a : α) (weight : ℤ) : (xs.map (fun x => if x = a then weight else 0)).sum = if a ∈ xs then weight else 0 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨apart,distinct⟩ := List.nodup_cons.mp unique
    by_cases eq : x = a
    · subst x; simp [ih distinct,apart]
    · simp [ih distinct,eq,Ne.symm eq]

private theorem keyed_sum (xs : List LookupKey) (unique : xs.Nodup) (amount : LookupKey → ℤ) (k : LookupKey) :
    multiplicitySum (xs.map fun x => accessAt x (amount x)) k = if k ∈ xs then amount k else 0 := by
  trans (xs.map fun x => if x = k then amount k else 0).sum
  · induction xs with
    | nil => rfl
    | cons x xs ih =>
      rw [List.map_cons,multiplicitySum_cons,ih (List.nodup_cons.mp unique).2,List.map_cons,List.sum_cons]
      simp only [keyOf_accessAt,multOf_accessAt]
      split <;> simp_all
  · have total := sum_unique xs unique k (amount k)
    by_cases h : k ∈ xs <;> simpa only [h,ite_true,ite_false] using total

variable (support : List LookupKey) (count : LookupKey → ℕ) (valid : ∀ k ∈ support, ByteServable k)
    (data : ProverData (ZMod p))

private theorem pad_zero (id : Id) : multOf (access id (padding id)) = 0 := by
  rcases id with op | w
  · cases op <;> rfl
  · rfl

/-- At any individual message the physical ledger contains the funded amount exactly once
in the selected bucket. Padding contributes zero, regardless of its data. -/
theorem table_sum (id : Id) (k : LookupKey) :
    multiplicitySum (tableCleanAccesses (table support count valid data id)) k =
      if k ∈ keys support id then signedVal (count k : ZMod p) else 0 := by
  have distinct : (keys support id).Nodup := (List.nodup_dedup support).filter _
  rw [table_reader_counts,multiplicitySum_append,keyed_sum (keys support id) distinct (fun key => signedVal (count key : ZMod p)) k]
  suffices zero : ∀ n : ℕ, multiplicitySum (List.replicate n (access id (padding id))) k = 0 by simp [zero]
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ,multiplicitySum_cons,pad_zero,ite_self,ih,add_zero]

/-- Total signed provider balance at a physical lookup key, independently of the order in
which the original component registry enumerates its buckets. -/
theorem tables_sum (shape : ∀ k ∈ support, IsByteKey k) (k : LookupKey) :
    multiplicitySum (tablesCleanAccesses (tables support count valid data)) k =
      if k ∈ support then signedVal (count k : ZMod p) else 0 := by
  change multiplicitySum ((all.map (table support count valid data)).flatMap tableCleanAccesses) k = _
  rw [List.flatMap_map,multiplicitySum_flatMap]
  by_cases present : k ∈ support
  · obtain ⟨id,selected⟩ := selects_exists (shape k present) (valid k present)
    have point (i : Id) : multiplicitySum (tableCleanAccesses (table support count valid data i)) k =
        if i = id then signedVal (count k : ZMod p) else 0 := by
      rw [table_sum]
      congr 1
      apply propext
      rw [keys,List.mem_filter,List.mem_dedup]
      exact ⟨fun h => selects_unique h.2 selected,fun h => h ▸ ⟨present,selected⟩⟩
    simp only [point,sum_unique all all_nodup,all_mem,ite_true,present]
  · have none (i : Id) : k ∉ keys support i := by simp [keys,present]
    simp only [table_sum,none,ite_false,List.map_const',List.sum_replicate,
      nsmul_zero,present]

private theorem only_byte (id : Id) : Ledger.OnlyChannel (component (p := p) id) byteChannel.toRaw := by
  cases id with
  | inl op =>
    cases op
    · exact Ledger.onlyChannel_U8Range
    · exact Ledger.onlyChannel_MSB
    · exact Ledger.onlyChannel_AndByte
    · exact Ledger.onlyChannel_OrByte
    · exact Ledger.onlyChannel_XorByte
    · exact Ledger.onlyChannel_Ltu
  | inr w => exact Ledger.onlyChannel_Range w

private theorem table_only_byte (id : Id) :
    (table support count valid data id).interactionsWith byteChannel.toRaw =
      (table support count valid data id).interactions := by
  unfold Table.interactionsWith Table.interactions
  apply List.flatMap_congr
  intro row _
  unfold Operations.interactionValuesWith Operations.interactionValues
  exact congrArg (List.map _) (interactions_eq_interactionsWith_of_onlyChannel (component id) _ (only_byte id)).symm

/-- Whole evaluated Byte-channel supply, in original physical order. -/
noncomputable def supply : List (Interaction (ZMod p)) :=
  (tables support count valid data).flatMap (fun t => t.interactionsWith byteChannel.toRaw)

private theorem supply_accesses : (supply support count valid data).map Interaction.toAccess =
    tablesCleanAccesses (tables support count valid data) := by
  simp only [supply,tables,tablesCleanAccesses,List.flatMap_map,List.map_flatMap]
  apply List.flatMap_congr
  intro i _
  exact congrArg (List.map Interaction.toAccess) (table_only_byte support count valid data i)

private theorem supply_on_byte (i) (seen : i ∈ supply support count valid data) : i.channel = byteChannel.toRaw := by
  obtain ⟨t,_,paid⟩ := List.mem_flatMap.mp seen
  exact t.channel_eq_of_mem_interactionsWith paid

/-- Count all physical sites, including zero-padding, once for every installed provider. -/
theorem supply_height : (supply support count valid data).length =
    (all.map fun id => WitnessGeneration.demandHeight (keys support id).length).sum := by
  have lengths := congrArg List.length (supply_accesses support count valid data)
  simp only [List.length_map,tablesCleanAccesses,tables,List.length_flatMap,List.map_map] at lengths
  rw [lengths]
  apply congrArg List.sum
  apply List.map_congr_left
  intro id _
  change (tableCleanAccesses _).length = _
  rw [table_accesses,List.length_map,height]

/-- At every field message the 23 native weighted tables supply its funded amount. -/
theorem supply_balance (shape : ∀ k ∈ support, IsByteKey k) (msg : Array (ZMod p)) :
    balanceOf (supply support count valid data) msg =
      if messageKey msg ∈ support then (count (messageKey msg) : ZMod p) else 0 := by
  have bridge := intCast_multiplicitySum_message (supply support count valid data) byteChannel.toRaw
    (supply_on_byte support count valid data) msg
  change ((multiplicitySum ((supply support count valid data).map Interaction.toAccess) (messageKey msg) : ℤ) : ZMod p) = _ at bridge
  rw [supply_accesses,tables_sum support count valid data shape] at bridge
  by_cases member : messageKey msg ∈ support
  · simpa only [member,ite_true,intCast_signedVal] using bridge.symm
  · simpa only [member,ite_false,Int.cast_zero] using bridge.symm

omit [Fact (2^25 < p)] in
private theorem requested_shape {reads : List (Interaction (ZMod p))} (onByte : ∀ i ∈ reads, i.channel = byteChannel.toRaw) :
    ∀ k ∈ requested reads, IsByteKey k := by
  intro k used
  obtain ⟨d,active,rfl⟩ := List.mem_map.mp used
  obtain ⟨i,inside,same,_⟩ := read_origin active
  have msg : i.msg = d.message := congrArg Prod.snd same
  have size : i.msg.size = 4 := i.same_size.trans (congrArg RawChannel.arity (onByte i inside))
  simp [IsByteKey,messageKey,← msg,size]

/-- The generator's native reader tally suffices to build all physical providers simultaneously
and to balance their entire evaluated signed ledger against the original reads. The exact count
includes every disabled reader site and each independently padded demand bucket. -/
theorem funded_readers (reads : List (Interaction (ZMod p)))
    (onByte : ∀ i ∈ reads, i.channel = byteChannel.toRaw)
    (pull : ∀ i ∈ reads, i.direction = .pull)
    (serve : ∀ i ∈ reads, i.mult ≠ 0 → ByteServable (messageKey i.msg)) :
    let generated := supply (requested reads) (readerCount reads) (requested_servable reads serve) data
    LogUpBalanced (reads ++ generated) ∧
      (reads ++ generated).length = reads.length +
        (all.map fun id => WitnessGeneration.demandHeight (keys (requested reads) id).length).sum := by
  constructor
  · intro msg
    rw [balanceOf_append,supply_balance _ _ _ _ (requested_shape onByte)]
    by_cases present : messageKey msg ∈ requested reads
    · simp only [present,ite_true,readerCount_funds reads msg onByte pull,add_neg_cancel]
    · have zero := count_zero_of_absent reads msg present
      have source := readerCount_funds reads msg onByte pull
      rw [zero,Nat.cast_zero] at source
      simpa only [present,ite_false,add_zero] using neg_eq_zero.mp source.symm
  · exact (List.length_append ..).trans (congrArg (reads.length + ·) (supply_height ..))

end SP1Clean.Soundness.ByteProviderDemand
