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

private theorem authenticates (raw : Source → Table (ZMod p)) (registered : ∀ id, (raw id).component = original id) (id : Source) :
    (publish id (raw id) (registered id)).Authenticates readbackChannel (Origin raw id) := by
  cases id with
  | ordinary instruction => exact OrdinarySources.publish_authenticates instruction _ (registered (.ordinary instruction))
  | host family => exact HostSources.publish_authenticates family _ (registered (.host family))
  | refresh => exact refresh_authenticates _ (registered .refresh)
  | finalizer ram => exact final_authenticates ram _ (registered (.finalizer ram))

/-- Raw receipt balance over the actual physical source group authenticates every positive
counted version. The conclusions give the exact original key, held word and both integer clocks. -/
theorem authenticates_versions (raw : Source → Table (ZMod p)) (registered : ∀ id, (raw id).component = original id)
    (supply : Table (ZMod p)) (installed : supply.component = ReadbackSupply.component) (checked : supply.Constraints)
    (balanced : BalancedInteractions ((supply :: sources.map (fun id => publish id (raw id) (registered id))).flatMap
      (·.interactionsWith readbackChannel.toRaw))) :
    supply.Authenticates versionChannel (fun version => ∃ (record : Readback (ZMod p)),
      (∃ id, Origin raw id record) ∧ version.key = record.key ∧ version.value = record.value ∧
      Address.toNat version.lower = Semantics.clkNat record.previousHigh record.previousLow ∧
      Address.toNat version.upper = Semantics.clkNat record.currentHigh record.currentLow) := by
  refine ReadbackSupply.authenticates_versions _ supply installed checked _ ?_ balanced
  intro table member
  obtain ⟨id, _, rfl⟩ := List.mem_map.mp member
  exact (authenticates raw registered id).mono (fun _ origin => ⟨id, origin⟩)

end SP1Clean.WriteProbe.AccessInventory
