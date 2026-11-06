import SP1Clean.Proofs.Completeness.Providers

/-! # Boolean occurrence ledgers and provider channel support

Clean represents direction separately from multiplicity. Execution rows contribute zero or one
occurrence; counted lookup providers use nonnegative field multiplicities. For boolean ledgers,
this module reuses Clean's multiset balance: a permutation of the active pushes and pulls proves
abstract balance. A concrete LogUp check additionally needs the physical interaction count bound.

The static provider profiles below identify every channel a built table can use. They let assembly
proofs eliminate unrelated channels without evaluating generated rows.
-/

namespace SP1Clean.Ledger

open Air.Flat (Component Table)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Active pushes, preserving repeated messages as separate physical occurrences. -/
abbrev pushedMessages (ins : List (Interaction (ZMod p))) : List (Array (ZMod p)) :=
  activeMessages ins .push

/-- Active pulls, using Clean's explicit direction instead of a negative field count. -/
abbrev pulledMessages (ins : List (Interaction (ZMod p))) : List (Array (ZMod p)) :=
  activeMessages ins .pull

/-- Every physical interaction is either disabled or contributes one occurrence. -/
def BooleanMults (ins : List (Interaction (ZMod p))) : Prop :=
  ∀ i ∈ ins, IsBool i.mult

omit [Fact (2 ^ 17 < p)] in
@[simp] lemma pushedMessages_nil : pushedMessages ([] : List (Interaction (ZMod p))) = [] := rfl

omit [Fact (2 ^ 17 < p)] in
@[simp] lemma pulledMessages_nil : pulledMessages ([] : List (Interaction (ZMod p))) = [] := rfl

omit [Fact (2 ^ 17 < p)] in
@[simp] lemma pushedMessages_append (as bs : List (Interaction (ZMod p))) :
    pushedMessages (as ++ bs) = pushedMessages as ++ pushedMessages bs := by
  simp [activeMessages, List.filter_append]

omit [Fact (2 ^ 17 < p)] in
@[simp] lemma pulledMessages_append (as bs : List (Interaction (ZMod p))) :
    pulledMessages (as ++ bs) = pulledMessages as ++ pulledMessages bs := by
  simp [activeMessages, List.filter_append]

omit [Fact (2 ^ 17 < p)] in
lemma pushedMessages_cons (i : Interaction (ZMod p)) (ins : List (Interaction (ZMod p))) :
    pushedMessages (i :: ins) =
      if i.direction = .push ∧ i.mult ≠ 0 then i.msg :: pushedMessages ins else pushedMessages ins := by
  simp [activeMessages, List.filter_cons, apply_ite]

omit [Fact (2 ^ 17 < p)] in
lemma pulledMessages_cons (i : Interaction (ZMod p)) (ins : List (Interaction (ZMod p))) :
    pulledMessages (i :: ins) =
      if i.direction = .pull ∧ i.mult ≠ 0 then i.msg :: pulledMessages ins else pulledMessages ins := by
  simp [activeMessages, List.filter_cons, apply_ite]

omit [Fact (2 ^ 17 < p)] in
/-- The canonical multiset check supplies abstract balance without a field-capacity premise. -/
theorem balancedInteractions_of_boolean_perm (ins : List (Interaction (ZMod p)))
    (boolean : BooleanMults ins) (permutation : (pushedMessages ins).Perm (pulledMessages ins)) :
    BalancedInteractions ins :=
  Balance.multiset.balancedInteractions_of_balanced ins (by trivial) ⟨boolean, permutation⟩

omit [Fact (2 ^ 17 < p)] in
@[simp] lemma booleanMults_append (as bs : List (Interaction (ZMod p))) :
    BooleanMults (as ++ bs) ↔ BooleanMults as ∧ BooleanMults bs := by
  simp only [BooleanMults, List.forall_mem_append]

omit [Fact (2 ^ 17 < p)] in
lemma booleanMults_flatMap {α : Type} (l : List α) (f : α → List (Interaction (ZMod p)))
    (h : ∀ a ∈ l, BooleanMults (f a)) : BooleanMults (l.flatMap f) := by
  intro i hi
  obtain ⟨a, ha, hia⟩ := List.mem_flatMap.mp hi
  exact h a ha i hia

omit [Fact (2 ^ 17 < p)] in
lemma pushedMessages_flatMap {α : Type} (l : List α) (f : α → List (Interaction (ZMod p))) :
    pushedMessages (l.flatMap f) = l.flatMap fun a => pushedMessages (f a) := by
  simp [activeMessages, List.filter_flatMap, List.map_flatMap]

omit [Fact (2 ^ 17 < p)] in
lemma pulledMessages_flatMap {α : Type} (l : List α) (f : α → List (Interaction (ZMod p))) :
    pulledMessages (l.flatMap f) = l.flatMap fun a => pulledMessages (f a) := by
  simp [activeMessages, List.filter_flatMap, List.map_flatMap]

/-! ## The per-table channel profile

Which of the four buses each provider/boundary component can contribute to at all. These are static
facts about the circuits — no row, no witness, no environment — and Clean's
`Table.interactionsWith_nil_of_channel_not_mem` turns each `∉` into a whole table's contribution
being literally `[]`.

The shape of the segment: **twenty-three byte-only providers** (the six opcode tables and all
seventeen range widths) plus the Program-ROM provider touch exactly one bus each; the two memory boundary tables
touch the Memory bus only; the two W3 system tables are the only provider-segment rows on more than
one bus (MemoryBump: Byte and Memory; StateBump: Byte and State); and the verifier row is on State
and Byte. -/

section Profile

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

open SP1Clean.Channels (stateChannel byteChannel programChannel memoryChannel)

/-- Every channel a component names is `ch0` — the shape the nil corollary below consumes. Stated
as a subset rather than a list equality so it is insensitive to the order and repetition the
elaborated `channelsWithGuarantees`/`channelsWithRequirements` lists happen to have. -/
def OnlyChannel (c : Component (ZMod p)) (ch0 : RawChannel (ZMod p)) : Prop :=
  ∀ channel ∈ c.circuit.channels, channel = ch0

theorem onlyChannel_U8Range :
    OnlyChannel (ByteChip.U8Range.component (p := p)) byteChannel.toRaw := by
  intro channel h
  have h' : channel ∈ (ByteChip.U8Range.circuit (p := p)).channels := h
  simp only [GeneralFormalCircuit.channels] at h'
  unfold ByteChip.U8Range.circuit at h'
  simpa [circuit_norm] using h'

theorem onlyChannel_MSB :
    OnlyChannel (ByteChip.MSB.component (p := p)) byteChannel.toRaw := by
  intro channel h
  have h' : channel ∈ (ByteChip.MSB.circuit (p := p)).channels := h
  simp only [GeneralFormalCircuit.channels] at h'
  unfold ByteChip.MSB.circuit at h'
  simpa [circuit_norm] using h'

theorem onlyChannel_AndByte :
    OnlyChannel (ByteChip.AndByte.component (p := p)) byteChannel.toRaw := by
  intro channel h
  have h' : channel ∈ (ByteChip.AndByte.circuit (p := p)).channels := h
  simp only [GeneralFormalCircuit.channels] at h'
  unfold ByteChip.AndByte.circuit at h'
  simpa [circuit_norm] using h'

theorem onlyChannel_OrByte :
    OnlyChannel (ByteChip.OrByte.component (p := p)) byteChannel.toRaw := by
  intro channel h
  have h' : channel ∈ (ByteChip.OrByte.circuit (p := p)).channels := h
  simp only [GeneralFormalCircuit.channels] at h'
  unfold ByteChip.OrByte.circuit at h'
  simpa [circuit_norm] using h'

theorem onlyChannel_XorByte :
    OnlyChannel (ByteChip.XorByte.component (p := p)) byteChannel.toRaw := by
  intro channel h
  have h' : channel ∈ (ByteChip.XorByte.circuit (p := p)).channels := h
  simp only [GeneralFormalCircuit.channels] at h'
  unfold ByteChip.XorByte.circuit at h'
  simpa [circuit_norm] using h'

theorem onlyChannel_Ltu :
    OnlyChannel (ByteChip.Ltu.component (p := p)) byteChannel.toRaw := by
  intro channel h
  have h' : channel ∈ (ByteChip.Ltu.circuit (p := p)).channels := h
  simp only [GeneralFormalCircuit.channels] at h'
  unfold ByteChip.Ltu.circuit at h'
  simpa [circuit_norm] using h'

theorem onlyChannel_Range (n : ℕ) (hn : 2 ^ n < p) :
    OnlyChannel (RangeChip.component (p := p) n hn) byteChannel.toRaw := by
  intro channel h
  have h' : channel ∈ (RangeChip.circuit n hn).channels := h
  simp only [GeneralFormalCircuit.channels] at h'
  unfold RangeChip.circuit at h'
  simpa [circuit_norm] using h'

theorem onlyChannel_ProgramProvider :
    OnlyChannel (ProgramProviderChip.component (p := p)) programChannel.toRaw := by
  intro channel h
  have h' : channel ∈ (ProgramProviderChip.circuit (p := p)).channels := h
  simp only [GeneralFormalCircuit.channels] at h'
  unfold ProgramProviderChip.circuit at h'
  simpa [circuit_norm] using h'

theorem onlyChannel_MemoryProvider :
    OnlyChannel (MemoryProviderChip.component (p := p)) memoryChannel.toRaw := by
  intro channel h
  have h' : channel ∈ (MemoryProviderChip.circuit (p := p)).channels := h
  simp only [GeneralFormalCircuit.channels] at h'
  unfold MemoryProviderChip.circuit at h'
  simpa [circuit_norm] using h'

set_option linter.unusedSectionVars false in
theorem onlyChannel_MemoryFinalize :
    OnlyChannel (MemoryFinalizeChip.component (p := p)) memoryChannel.toRaw := by
  intro channel h
  have h' : channel ∈ (MemoryFinalizeChip.circuit (p := p)).channels := h
  simp only [GeneralFormalCircuit.channels] at h'
  unfold MemoryFinalizeChip.circuit at h'
  simpa [circuit_norm] using h'

set_option linter.unusedSectionVars false in
/-- The corollary the assembly uses: a single-bus component's built table contributes literally
nothing to every other bus, so three of the four channel ledgers are discharged without touching a
row. -/
theorem builtTable_interactionsWith_eq_nil_of_ne (c : Component (ZMod p))
    (inputs : List (c.Input (ZMod p))) (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p))
    (bounded : inputs.length ≤ UInt64.size)
    (fixed : c.FixedRowsMatch (inputs.map (c.buildRow · data hint)))
    (consistent : data.tables c.circuit.name (size c.Input) = (inputs.map toElements).toArray)
    {channel ch0 : RawChannel (ZMod p)} (hsub : OnlyChannel c ch0) (hne : channel ≠ ch0) :
    (Table.build c inputs data hint bounded fixed consistent).interactionsWith channel = [] :=
  Table.interactionsWith_nil_of_channel_not_mem (by
    simp only [Table.build_component]
    exact fun hmem => hne (hsub channel hmem))

end Profile

end SP1Clean.Ledger
