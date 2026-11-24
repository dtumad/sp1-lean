import SP1Clean.Proofs.Completeness.CanonicalClosureWellFormed
import ToClean.Air.GuardedDemandTable

/-! # Exact agreement of the native byte guarantee with the installed Byte and Range tables -/

namespace SP1Clean.Soundness
open Circuit Air.Flat Channels LookupAccessList
variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
private local instance byteDemandLimbBound : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2^25 < p); omega⟩

/-- The four canonical field cells read by the native provider dispatcher. -/
def byteLookupKey (r : ByteRow (ZMod p)) : LookupKey :=
  (.Byte,"SP1Byte",[r.opcode.val,r.a.val,r.b.val,r.c.val])

omit [Fact (2 ^ 25 < p)] in
/-- The physical signed interaction has this key at every reader multiplicity. -/
theorem byte_pull_key (r : ByteRow (ZMod p)) (m : ZMod p) :
    keyOf (Interaction.toAccess (byteChannel.pulledIfValue m r)) = byteLookupKey r := by
  change (_,_,(toElements r).toList.map ZMod.val) = _
  rw [byteRow_toList]
  rfl

private theorem flag (a : ZMod p) (predicate : Prop) [Decidable predicate] :
    a.val = (if predicate then 1 else 0) ↔ (a = 0 ∨ a = 1) ∧ (a = 1 ↔ predicate) := by
  have hp : 2^25 < p := Fact.out
  by_cases h : predicate
  · rw [ite_eq_left h,ZMod.val_eq_one (by omega)]
    tauto
  · rw [ite_eq_right h,ZMod.val_eq_zero]
    constructor
    · intro zero
      have off : a ≠ 1 := by rw [zero]; exact zero_ne_one
      tauto
    · rintro ⟨either,iff⟩
      exact either.resolve_right (fun one => h (iff.mp one))

private theorem tagged (op : ByteOpcode) (a b c : ZMod p) :
    ByteServable (byteLookupKey ⟨op.idx,a,b,c⟩) ↔ op.constrain a b c := by
  have hp : 2^25 < p := Fact.out
  have small : op.idx < p := by cases op <;> simp only [ByteOpcode.idx] <;> omega
  have opcode : cell (byteLookupKey ⟨(op.idx : ZMod p),a,b,c⟩) 0 = op.idx := ZMod.val_natCast_of_lt small
  unfold ByteServable
  rw [opcode]
  have bitBound (h : a = 0 ∨ a = 1) : a.val < 256 := by
    rcases h with rfl | rfl <;> simp [ZMod.val_one]
  cases op
  all_goals simp only [ByteOpcode.idx,byteLookupKey,cell,List.getD,List.getElem?_cons_zero,List.getElem?_cons_succ,
    Option.getD_some,List.cons.injEq,true_and,and_true,ByteOpcode.constrain]
  all_goals try simp only [ZMod.val_natCast_of_lt (by omega : 0 < p),ZMod.val_natCast_of_lt (by omega : 1 < p),
    ZMod.val_natCast_of_lt (by omega : 2 < p),ZMod.val_natCast_of_lt (by omega : 3 < p),
    ZMod.val_natCast_of_lt (by omega : 4 < p),ZMod.val_natCast_of_lt (by omega : 5 < p),ZMod.val_natCast_of_lt (by omega : 6 < p),true_and]
  · constructor
    · rintro ⟨ha,hb,hc⟩
      exact ⟨⟨ha ▸ Nat.and_lt_two_pow (n := 8) _ hc,hb,hc⟩,ha⟩
    · exact fun h => ⟨h.2,h.1.2⟩
  · constructor
    · rintro ⟨ha,hb,hc⟩
      exact ⟨⟨ha ▸ Nat.or_lt_two_pow (n := 8) hb hc,hb,hc⟩,ha⟩
    · exact fun h => ⟨h.2,h.1.2⟩
  · constructor
    · rintro ⟨ha,hb,hc⟩
      exact ⟨⟨ha ▸ Nat.xor_lt_two_pow (n := 8) hb hc,hb,hc⟩,ha⟩
    · exact fun h => ⟨h.2,h.1.2⟩
  · simp
  · change (a.val = (if b.val < c.val then 1 else 0)) ∧ b.val < 256 ∧ c.val < 256 ↔ _
    rw [flag a (b.val < c.val)]
    exact ⟨fun ⟨⟨f,g⟩,b,c⟩ => ⟨⟨bitBound f,b,c⟩,f,g⟩,fun ⟨⟨_,b,c⟩,f,g⟩ => ⟨⟨f,g⟩,b,c⟩⟩
  · change ((a.val = (if 128 ≤ b.val then 1 else 0)) ∧ c.val = 0) ∧ b.val < 256 ↔ _
    rw [flag a (128 ≤ b.val),ZMod.val_eq_zero]
    exact ⟨fun ⟨⟨⟨f,g⟩,c⟩,b⟩ => ⟨⟨bitBound f,b⟩,f,g,c⟩,fun ⟨⟨_,b⟩,f,g,c⟩ => ⟨⟨⟨f,g⟩,c⟩,b⟩⟩
  · rw [ZMod.val_eq_zero]
    tauto

private theorem opcode_bound (k : LookupKey) (served : ByteServable k) : cell k 0 ≤ 6 := by
  by_contra outside
  obtain ⟨n,above⟩ := Nat.exists_eq_add_of_le (by omega : 7 ≤ cell k 0)
  unfold ByteServable at served
  rw [above,Nat.add_comm] at served
  exact served

/-- A typed byte-channel request is well formed exactly when the existing physical provider
dispatcher can serve its complete four-cell payload. -/
theorem byteRowSpec_iff_servable (r : ByteRow (ZMod p)) : ByteRowSpec r ↔ ByteServable (byteLookupKey r) := by
  constructor
  · rintro ⟨op,tag,valid⟩
    cases r with
    | mk code a b c =>
      change (op.idx : ZMod p) = code at tag
      cases tag
      exact (tagged op a b c).mpr valid
  · intro served
    let n := r.opcode.val
    have code : n ≤ 6 := opcode_bound (byteLookupKey r) served
    let op := ByteOpcode.ofNat n
    have index : op.idx = n := ByteOpcode.idx_ofNat code
    have tag : (op.idx : ZMod p) = r.opcode := by rw [index]; exact ZMod.natCast_zmod_val _
    refine ⟨op,tag,(tagged op r.a r.b r.c).mp ?_⟩
    simpa only [tag] using served


omit [Fact (2 ^ 25 < p)] in
private theorem pushed_access (r : ByteRow (ZMod p)) (m : ZMod p) :
    Interaction.toAccess (byteChannel.pushedIfValue m r) =
      accessAt (byteLookupKey r) (signedVal m) := by
  change (_,_,(toElements r).toList.map ZMod.val,_) = _
  rw [byteRow_toList]
  rfl

omit [Fact (2 ^ 25 < p)] in
/-- A singleton demand builds a constrained physical table at its registered provider, with
the requested positive field multiplicity in the original signed Clean ledger. -/
private theorem realize {Entry : Type} (c : Component (ZMod p)) (input : Entry → c.Input (ZMod p))
    (wellFormed : Entry → Prop) (access : Entry → LookupAccess) (multiplicity : Entry → ℕ)
    (e : Entry) (wf : wellFormed e) (data : ProverData (ZMod p))
    (demand : ∀ rows, c.FixedRowsMatch rows)
    (honest : ∀ data hint, c.circuit.ProverAssumptions (input e) data hint)
    (physical : ∀ data hint (bounded : [e].length ≤ UInt64.size)
      (consistent : data.tables c.circuit.name (size c.Input) = (([e].map input).map toElements).toArray)
      (_ : ∀ entry ∈ [e], wellFormed entry),
      tableCleanAccesses (Table.build c ([e].map input) data hint
        (by simpa only [List.length_map] using bounded) (demand _) consistent) =
          [e].map fun entry => actualProviderAccess (p := p) (access entry) (multiplicity entry)) :
    ∃ t : Table (ZMod p), t.component = c ∧ t.Constraints ∧ t.Guarantees ∧
      tableCleanAccesses t = [actualProviderAccess (p := p) (access e) (multiplicity e)] := by
  let inputs := [e].map input
  have bounded : inputs.length ≤ UInt64.size := by change 1 ≤ UInt64.size; decide
  let t := Table.ofInputs c inputs data bounded demand
  obtain ⟨constraints,guarantees⟩ := Table.ofInputs_valid c inputs data bounded demand (by
    intro i inside
    obtain rfl : i = input e := List.mem_singleton.mp inside
    exact honest _ _)
  exact ⟨t,rfl,constraints,guarantees,physical _ _ (by change 1 ≤ UInt64.size; decide) (c.inputData_consistent inputs data)
    (by simpa only [List.mem_singleton,forall_eq] using wf)⟩

/-- Every accepted typed request can be served by a registered Byte or Range table. The
generated table satisfies its own constraints and guarantees and has exactly the requested
physical signed interaction, including when the multiplicity is zero. -/
theorem byte_request_has_provider (r : ByteRow (ZMod p)) (m : ZMod p) (data : ProverData (ZMod p))
    (valid : ByteRowSpec r) :
    ∃ (id : ByteProviderId ⊕ RangeChip.Width) (t : Table (ZMod p)),
      t.component = providerTableFor (id.elim .byte .range) ∧ t.Constraints ∧ t.Guarantees ∧
        tableCleanAccesses t = [Interaction.toAccess (byteChannel.pushedIfValue m r)] := by
  let key := byteLookupKey r
  have served : ByteServable key := (byteRowSpec_iff_servable r).mp valid
  obtain ⟨op,tag,fields⟩ := valid
  have modulus : 2^25 < p := Fact.out
  have idx : op.idx < p := by cases op <;> simp only [ByteOpcode.idx] <;> omega
  have index : cell key 0 = op.idx := (congrArg ZMod.val tag).symm.trans (ZMod.val_natCast_of_lt idx)
  have shape : IsByteKey key = true := rfl
  have selected : selByte op.idx key = true := by simp only [selByte,shape,index,decide_true,Bool.and_self]
  let entry := byteEntryOfKey key m.val
  have operand (h : op.idx ≤ 5) : entry.WellFormed :=
    SupportedCoreTraceWitness.byteEntryOfKey_wellFormed h selected served
  have paid (a : LookupAccess) (round : a = accessAt key (m.val : ℤ)) :
      actualProviderAccess (p := p) a m.val = Interaction.toAccess (byteChannel.pushedIfValue m r) := by
    rw [round,pushed_access]
    simp only [actualProviderAccess,withFieldMultiplicity,ZMod.natCast_zmod_val]
    rfl
  cases op with
  | AND =>
    have wf := operand (by decide)
    obtain ⟨t,id,sat,guarantees,ledger⟩ := realize ByteChip.AndByte.component ByteChip.AndByte.ofEntry
      TraceGen.ByteEntry.WellFormed andAccess TraceGen.ByteEntry.multiplicity entry wf data
      (fun _ => trivial) (ByteChip.AndByte.proverAssumptions_of_entry wf) (and_traceTable_actualAccesses [entry])
    exact ⟨.inl .andByte,t,id,sat,guarantees,ledger.trans (congrArg List.singleton (paid _ (and_round _ _ selected served)))⟩
  | OR =>
    have wf := operand (by decide)
    obtain ⟨t,id,sat,guarantees,ledger⟩ := realize ByteChip.OrByte.component ByteChip.OrByte.ofEntry
      TraceGen.ByteEntry.WellFormed orAccess TraceGen.ByteEntry.multiplicity entry wf data
      (fun _ => trivial) (ByteChip.OrByte.proverAssumptions_of_entry wf) (or_traceTable_actualAccesses [entry])
    exact ⟨.inl .orByte,t,id,sat,guarantees,ledger.trans (congrArg List.singleton (paid _ (or_round _ _ selected served)))⟩
  | XOR =>
    have wf := operand (by decide)
    obtain ⟨t,id,sat,guarantees,ledger⟩ := realize ByteChip.XorByte.component ByteChip.XorByte.ofEntry
      TraceGen.ByteEntry.WellFormed xorAccess TraceGen.ByteEntry.multiplicity entry wf data
      (fun _ => trivial) (ByteChip.XorByte.proverAssumptions_of_entry wf) (xor_traceTable_actualAccesses [entry])
    exact ⟨.inl .xorByte,t,id,sat,guarantees,ledger.trans (congrArg List.singleton (paid _ (xor_round _ _ selected served)))⟩
  | U8Range =>
    have wf := operand (by decide)
    obtain ⟨t,id,sat,guarantees,ledger⟩ := realize ByteChip.U8Range.component ByteChip.U8Range.ofEntry
      TraceGen.ByteEntry.WellFormed u8RangeAccess TraceGen.ByteEntry.multiplicity entry wf data
      (fun _ => trivial) (ByteChip.U8Range.proverAssumptions_of_entry wf) (u8Range_traceTable_actualAccesses [entry])
    exact ⟨.inl .u8Range,t,id,sat,guarantees,ledger.trans (congrArg List.singleton (paid _ (u8Range_round _ _ selected served)))⟩
  | LTU =>
    have wf := operand (by decide)
    obtain ⟨t,id,sat,guarantees,ledger⟩ := realize ByteChip.Ltu.component ByteChip.Ltu.ofEntry
      TraceGen.ByteEntry.WellFormed ltuAccess TraceGen.ByteEntry.multiplicity entry wf data
      (fun _ => trivial) (ByteChip.Ltu.proverAssumptions_of_entry wf) (ltu_traceTable_actualAccesses [entry])
    exact ⟨.inl .ltu,t,id,sat,guarantees,ledger.trans (congrArg List.singleton (paid _ (ltu_round _ _ selected served)))⟩
  | MSB =>
    have wf := operand (by decide)
    obtain ⟨t,id,sat,guarantees,ledger⟩ := realize ByteChip.MSB.component ByteChip.MSB.ofEntry
      TraceGen.ByteEntry.WellFormed msbAccess TraceGen.ByteEntry.multiplicity entry wf data
      (fun _ => trivial) (ByteChip.MSB.proverAssumptions_of_entry wf) (msb_traceTable_actualAccesses [entry])
    exact ⟨.inl .msb,t,id,sat,guarantees,ledger.trans (congrArg List.singleton (paid _ (msb_round _ _ selected served)))⟩
  | Range =>
    let width : RangeChip.Width := ⟨r.b.val,Nat.lt_succ_of_le fields.2.1⟩
    have atWidth : selRange width key = true := by
      simp only [selRange,shape,index,ByteOpcode.idx,Bool.true_and,decide_eq_true_eq]
      exact ⟨trivial,rfl⟩
    let range := rangeEntryOfKey key m.val
    have wf : range.WellFormed width.val :=
      SupportedCoreTraceWitness.rangeEntryOfKey_wellFormed width atWidth served
    obtain ⟨t,id,sat,guarantees,ledger⟩ := realize (RangeChip.componentFor width) RangeChip.ofEntry
      (TraceGen.RangeEntry.WellFormed width.val) (rangeAccess width) TraceGen.RangeEntry.multiplicity
      range wf data (fun _ => trivial) (RangeChip.proverAssumptions_of_entry width wf)
      (range_traceTable_actualAccesses width [range])
    exact ⟨.inr width,t,id,sat,guarantees,ledger.trans (congrArg List.singleton (paid _ (range_round _ _ _ atWidth served)))⟩

end SP1Clean.Soundness
