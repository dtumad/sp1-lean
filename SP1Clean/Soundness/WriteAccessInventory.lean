import SP1Clean.Soundness.WriteOrdinarySources
import SP1Clean.Soundness.WriteHostSources
import SP1Clean.Soundness.WriteReadbackSources

/-! # All physical sources for counted WRITE versions

The source inventory consists of the 25 protected ordinary families, the released ECALL,
both HINT_READ word variants, register refreshes and the two ordered finalizers.
-/

namespace SP1Clean.WriteProbe.AccessInventory

open Circuit Air.Flat Soundness Channels

/-- A source is identified by its installed physical component, including distinct last-word rows. -/
inductive Source where
  | ordinary (id : InstructionChipId)
  | host (family : HostSources.Family)
  | refresh
  | finalizer (ram : Bool)
deriving DecidableEq

/-- Physical source families in registry order within each component group. -/
def sources : List Source := InstructionChipId.all.map .ordinary ++
  [.host .ecall, .host (.word false), .host (.word true), .refresh, .finalizer false, .finalizer true]

theorem sources_complete (id : Source) : id ∈ sources := by
  cases id with
  | ordinary instruction => exact List.mem_append_left _ (List.mem_map_of_mem (f := Source.ordinary) (InstructionChipId.mem_all instruction))
  | host family => cases family with
    | ecall => decide
    | word last => cases last <;> decide
  | refresh => decide
  | finalizer ram => cases ram <;> decide

theorem sources_nodup : sources.Nodup := by decide

theorem sources_length : sources.length = 31 := by decide

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

/-- Original component before publishing predecessor observations. -/
def original : Source → Component (ZMod p)
  | .ordinary id => ProtectedOrdinaryReceipt.component id
  | .host family => HostSources.original family
  | .refresh => { circuit := MemoryBumpChip.circuit, generation := MemoryBumpChip.generation, Assumptions := MemoryBumpChip.circuit.Assumptions }
  | .finalizer ram => originalFinal ram

/-- Attach the corresponding observation to the real rows of each installed family. -/
def publish (id : Source) (raw : Table (ZMod p)) (registered : raw.component = original id) : Table (ZMod p) :=
  match id with
  | .ordinary instruction => OrdinarySources.publish instruction raw registered
  | .host family => HostSources.publish family raw registered
  | .refresh => publishRefresh raw registered
  | .finalizer ram => publishFinal ram raw registered

/-- The positive source must occur in the original row with its gate, key, clock and word. -/
def Origin (raw : Source → Table (ZMod p)) (id : Source) (record : Readback (ZMod p)) : Prop :=
  match id with
  | .ordinary instruction => OrdinarySources.FromPull instruction (raw id) record
  | .host family => AccessSupply.FromPredecessor (raw id) (HostSources.upper family) record
  | .refresh => FromRefresh (raw id) record
  | .finalizer ram => FromFinal ram (raw id) record

/-- Each installed source authenticates its original physical predecessor. -/
theorem publish_authenticates (raw : Source → Table (ZMod p)) (registered : ∀ id, (raw id).component = original id) (id : Source) :
    (publish id (raw id) (registered id)).Authenticates readbackChannel (Origin raw id) := by
  cases id with
  | ordinary instruction => exact OrdinarySources.publish_authenticates instruction _ (registered (.ordinary instruction))
  | host family => exact HostSources.publish_authenticates family _ (registered (.host family))
  | refresh => exact refresh_authenticates _ (registered .refresh)
  | finalizer ram => exact final_authenticates ram _ (registered (.finalizer ram))

/-- Number of private source occurrences on a single physical row, including padding. -/
def perRow : Source → ℕ
  | .ordinary id => OrdinarySources.accessCount (p := p) id
  | .host .ecall => 3
  | .host (.word _) | .refresh | .finalizer _ => 1

theorem source_count (id : Source) (table : Table (ZMod p)) (registered : table.component = original id) :
    ((publish id table registered).interactionsWith readbackChannel.toRaw).length = table.length * perRow (p := p) id := by
  cases id with
  | ordinary instruction => exact OrdinarySources.publication_count instruction table registered
  | host family => cases family with
    | ecall => exact HostSources.publication_count .ecall table registered
    | word last => exact HostSources.publication_count (.word last) table registered
  | refresh =>
    simp only [publish, perRow, Nat.mul_one, Table.length]
    exact (congrArg List.length (publishRefresh_receipts table registered)).trans (List.length_map ..)
  | finalizer ram =>
    simp only [publish, perRow, Nat.mul_one, Table.length]
    exact (congrArg List.length (publishFinal_receipts ram table registered)).trans (List.length_map ..)

private theorem supply_count (supply : Table (ZMod p)) (installed : supply.component = ReadbackSupply.component) :
    (supply.interactionsWith readbackChannel.toRaw).length = supply.length := by
  simp only [Table.interactionsWith, installed, ReadbackSupply.receipt_values, List.length_flatMap, List.length_singleton, Table.length]
  simp

/-- All physically present private receipts and their supplier pulls, before using field balance. -/
noncomputable def ledger (raw : Source → Table (ZMod p)) (registered : ∀ id, (raw id).component = original id) (supply : Table (ZMod p)) :
    List (Interaction (ZMod p)) :=
  (supply :: sources.map (fun id => publish id (raw id) (registered id))).flatMap (·.interactionsWith readbackChannel.toRaw)

/-- Exact raw length against which LogUp applies its characteristic bound. -/
theorem ledger_length (raw : Source → Table (ZMod p)) (registered : ∀ id, (raw id).component = original id)
    (supply : Table (ZMod p)) (installed : supply.component = ReadbackSupply.component) :
    (ledger raw registered supply).length = supply.length + (sources.map (fun id => (raw id).length * perRow (p := p) id)).sum := by
  simp only [ledger, List.flatMap_cons, List.length_append, List.length_flatMap, List.map_map, Function.comp_def,
    source_count, supply_count supply installed]

/-- A counted version retains the complete physical source key, word and both time bounds. -/
def Meaning (raw : Source → Table (ZMod p)) (version : Version (ZMod p)) : Prop :=
  ∃ record, (∃ id, Origin raw id record) ∧ version.key = record.key ∧ version.value = record.value ∧
    Address.toNat version.lower = Semantics.clkNat record.previousHigh record.previousLow ∧
    Address.toNat version.upper = Semantics.clkNat record.currentHigh record.currentLow

/-- Raw receipt balance over the actual physical source group authenticates every positive
counted version. The conclusions give the exact original key, held word and both integer clocks. -/
theorem authenticates_versions (raw : Source → Table (ZMod p)) (registered : ∀ id, (raw id).component = original id)
    (supply : Table (ZMod p)) (installed : supply.component = ReadbackSupply.component) (checked : supply.Constraints)
    (balanced : BalancedInteractions (ledger raw registered supply)) :
    supply.Authenticates versionChannel (Meaning raw) := by
  refine ReadbackSupply.authenticates_versions _ supply installed checked _ ?_ balanced
  intro table member
  obtain ⟨id, _, rfl⟩ := List.mem_map.mp member
  exact (publish_authenticates raw registered id).mono (fun _ origin => ⟨id, origin⟩)

/-- Actual raw LogUp balance authenticates the source group at its exact occurrence count. -/
theorem authenticates_of_logUp (raw : Source → Table (ZMod p)) (registered : ∀ id, (raw id).component = original id)
    (supply : Table (ZMod p)) (installed : supply.component = ReadbackSupply.component) (checked : supply.Constraints)
    (fits : supply.length + (sources.map (fun id => (raw id).length * perRow (p := p) id)).sum < p)
    (balanced : LogUpBalanced (ledger raw registered supply)) : supply.Authenticates versionChannel (Meaning raw) := by
  apply authenticates_versions raw registered supply installed checked
  apply (Balance.logUp (F := ZMod p)).balancedInteractions_of_balanced _ _ balanced
  simpa only [Balance.logUp, ComputableRingChar.char_eq, ZMod.ringChar_zmod_n, decide_eq_true_eq, ledger_length raw registered supply installed] using fits

end SP1Clean.WriteProbe.AccessInventory
