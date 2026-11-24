import SP1Clean.Proofs.Completeness.ByteDemandMembership
import ToClean.Air.DemandPadding

/-! # Counting and padding the 23 original native Byte lookup providers

Clean groups demand by the complete signed interaction message. Each bucket has one active
row per distinct requested key. A byte pair or a Range operand identifies that key within the
bucket, giving a field-independent physical height bound.
-/

namespace SP1Clean.Soundness.ByteProviderDemand
open LookupAccessList Air.Flat.WitnessGeneration

/-- Six byte operations followed by the seventeen installed preprocessing widths. -/
abbrev Id := ByteProviderId ⊕ RangeChip.Width

/-- The original registered circuit for this part of the provider window. -/
def slot (id : Id) : ProviderTableId := id.elim .byte .range

/-- Order of the original tables inside the supervisor registry. -/
def all : List Id := ByteProviderId.all.map .inl ++ RangeChip.allWidths.map .inr

/-- Released opcode accepted by each of the six byte-specific demand generators. -/
def operation : ByteProviderId → ByteOpcode
  | .u8Range => .U8Range
  | .msb => .MSB
  | .andByte => .AND
  | .orByte => .OR
  | .xorByte => .XOR
  | .ltu => .LTU

/-- The existing complete-message selector used by the canonical provider closure. -/
def selects : Id → LookupKey → Bool
  | .inl op => selByte (operation op).idx
  | .inr width => selRange width

/-- One canonical occurrence per distinct message routed to this physical provider. -/
def keys (requests : List LookupKey) (id : Id) : List LookupKey := requests.dedup.filter (selects id)

/-- Aggregate or zero demand cast into this component's original typed row. -/
def entry : (id : Id) → LookupKey → ℕ → (slot id).Occurrence
  | .inl _ => byteEntryOfKey
  | .inr _ => rangeEntryOfKey

/-- Input that the original demand component obtains when it pads its physical trace. -/
def padding : (id : Id) → (slot id).Occurrence
  | .inl _ => ⟨0,0,0⟩
  | .inr _ => ⟨0,0⟩

/-- Physical occurrences include the zero-amount padding at the end of each bucket. -/
def entries (requests : List LookupKey) (count : LookupKey → ℕ) (id : Id) : List (slot id).Occurrence :=
  let active := keys requests id
  (active.map fun key => entry id key (count key)) ++
    List.replicate (demandPadding active.length) (padding id)

/-- Original access produced by one of the physical entries in this bucket. -/
def access : (id : Id) → (slot id).Occurrence → LookupAccess
  | .inl .u8Range => u8RangeAccess
  | .inl .msb => msbAccess
  | .inl .andByte => andAccess
  | .inl .orByte => orAccess
  | .inl .xorByte => xorAccess
  | .inl .ltu => ltuAccess
  | .inr w => rangeAccess w

/-- The original address and data for a requested message, with the supplied field count. -/
theorem round (id : Id) (k : LookupKey) (m : ℕ) (selected : selects id k) (valid : ByteServable k) :
    access id (entry id k m) = accessAt k m := by
  cases id with
  | inl op =>
    cases op
    · exact u8Range_round _ _ selected valid
    · exact msb_round _ _ selected valid
    · exact and_round _ _ selected valid
    · exact or_round _ _ selected valid
    · exact xor_round _ _ selected valid
    · exact ltu_round _ _ selected valid
  | inr w => exact range_round w _ _ selected valid

/-- Semantic byte membership establishes the original circuit's local operand bounds. -/
theorem entry_valid (id : Id) {k : LookupKey} (m : ℕ) (selected : selects id k) (valid : ByteServable k) :
    (slot id).Valid (entry id k m) := by
  cases id with
  | inl op =>
    exact SupportedCoreTraceWitness.byteEntryOfKey_wellFormed
      (show (operation op).idx ≤ 5 by cases op <;> decide) selected valid
  | inr w => exact SupportedCoreTraceWitness.rangeEntryOfKey_wellFormed w selected valid

/-- Every active and padded physical entry has valid operands at its own fixed width. -/
theorem entries_valid (requests : List LookupKey) (count : LookupKey → ℕ) (id : Id) (valid : ∀ k ∈ requests, ByteServable k) :
    ∀ e ∈ entries requests count id, (slot id).Valid e := by
  intro e used
  rcases List.mem_append.mp used with active | padded
  · obtain ⟨k,inside,rfl⟩ := List.mem_map.mp active
    obtain ⟨present,choice⟩ := List.mem_filter.mp inside
    exact entry_valid _ _ choice (valid k (List.mem_dedup.mp present))
  · obtain ⟨_,rfl⟩ := List.mem_replicate.mp padded
    cases id with
    | inl _ => exact ⟨by change 0 < 256; decide,by change 0 < 256; decide⟩
    | inr w => exact Nat.two_pow_pos w.val

/-- Exact physical height after grouping and independently rounding this bucket. -/
theorem height (requests : List LookupKey) (count : LookupKey → ℕ) (id : Id) :
    (entries requests count id).length = demandHeight (keys requests id).length := by
  simp only [entries,List.length_append,List.length_map,List.length_replicate,add_demandPadding]

/-- Two valid selected keys agree as soon as their original operand input agrees. -/
private theorem key_eq (id : Id) {x y : LookupKey} (xs : selects id x) (ys : selects id y)
    (xv : ByteServable x) (yv : ByteServable y) (h : entry id x 0 = entry id y 0) : x = y := by
  have same := congrArg (access id) h
  rw [round id x 0 xs xv,round id y 0 ys yv] at same
  exact congrArg keyOf same

/-- Within one bucket the two 8-bit operands or the single 16-bit Range operand encode the key. -/
private def operandCode : Id → LookupKey → ℕ
  | .inl _, k => 256 * cell k 2 + cell k 3
  | .inr _, k => cell k 1

private theorem code_bound (id : Id) {k : LookupKey} (selected : selects id k) (valid : ByteServable k) :
    operandCode id k < 65536 := by
  have well := entry_valid id 0 selected valid
  cases id with
  | inl op =>
    obtain ⟨b,c⟩ := well
    change cell k 2 < 256 at b
    change cell k 3 < 256 at c
    change 256 * cell k 2 + cell k 3 < 65536
    omega
  | inr w =>
    change cell k 1 < 2^w.val at well
    exact lt_of_lt_of_le well (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_of_lt_succ w.isLt))

private theorem code_injective (id : Id) {x y : LookupKey} (xs : selects id x) (ys : selects id y)
    (xv : ByteServable x) (yv : ByteServable y) (same : operandCode id x = operandCode id y) : x = y := by
  apply key_eq id xs ys xv yv
  cases id with
  | inl op =>
    have xc := (entry_valid (.inl op) 0 xs xv).2
    have yc := (entry_valid (.inl op) 0 ys yv).2
    change cell x 3 < 256 at xc
    change cell y 3 < 256 at yc
    change 256 * cell x 2 + cell x 3 = 256 * cell y 2 + cell y 3 at same
    have b : cell x 2 = cell y 2 := by omega
    have c : cell x 3 = cell y 3 := by omega
    simp only [entry,byteEntryOfKey,b,c]
    rfl
  | inr w => exact congrArg (fun a => TraceGen.RangeEntry.mk a 0) same

/-- Independently of the execution length, each physical provider contains at most 65536
distinct active keys. Repeated reads consume multiplicity, never a new bucket row. -/
theorem height_bound (requests : List LookupKey) (count : LookupKey → ℕ) (id : Id) (valid : ∀ k ∈ requests, ByteServable k) :
    (entries requests count id).length ≤ 65536 := by
  let ks := keys requests id
  have routed {k} (inside : k ∈ ks) : selects id k ∧ ByteServable k := by
    obtain ⟨present,selected⟩ := List.mem_filter.mp inside
    exact ⟨selected,valid k (List.mem_dedup.mp present)⟩
  let encode (k : {k // k ∈ ks}) : Fin 65536 := ⟨operandCode id k.val,code_bound id (routed k.property).1 (routed k.property).2⟩
  have injective : Function.Injective encode := by
    intro x y eq
    exact Subtype.ext (code_injective id (routed x.property).1 (routed y.property).1 (routed x.property).2 (routed y.property).2 (congrArg Fin.val eq))
  have distinct : ks.Nodup := (List.nodup_dedup requests).filter _
  have bound := (distinct.attach.map injective).length_le_card
  rw [height]
  apply demandHeight_le_pow (exponent := 16)
  change ks.length ≤ 65536
  simpa only [List.length_map,List.length_attach,Fintype.card_fin] using bound

end SP1Clean.Soundness.ByteProviderDemand
