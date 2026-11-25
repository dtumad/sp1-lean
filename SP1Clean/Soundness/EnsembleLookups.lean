import SP1Clean.Soundness.SP1Ensemble
import ToClean.Air.LookupFree

/-! # Lookup freedom of the core instruction/provider inventory

The native instruction and provider components use polynomial constraints and channel
interactions only, so their physical constraints survive a change from witness-generation data
to the data derived from the committed tables (`LookupFree.constraintsHold_setData`). Channel
guarantees and semantic commitment bindings are separate obligations.
-/

namespace SP1Clean.Soundness

open Circuit Air.Flat

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

/-- Every native provider uses polynomial constraints and channel interactions only. -/
theorem providerTableFor_lookups_empty (id : ProviderTableId) :
    (providerTableFor (p := p) id).operations.lookups = [] := by
  cases id with
  | byte provider =>
    cases provider <;>
      simp [providerTableFor, Component.lookups_eq, Component.rowOperations,
        ByteChip.U8Range.circuit, ByteChip.MSB.circuit, ByteChip.AndByte.circuit,
        ByteChip.OrByte.circuit, ByteChip.XorByte.circuit, ByteChip.Ltu.circuit,
        ByteChip.U8Range.main, ByteChip.MSB.main, ByteChip.AndByte.main,
        ByteChip.OrByte.main, ByteChip.XorByte.main, ByteChip.Ltu.main,
        Gadgets.ToBits.rangeCheck, Gadgets.ToBits.toBits,
        Gadgets.BitwiseByte.circuit, circuit_norm]
  | range width =>
    simp [providerTableFor, Component.lookups_eq, Component.rowOperations,
      RangeChip.circuitFor, circuit_norm]
  | program =>
    simp [providerTableFor, Component.lookups_eq, Component.rowOperations,
      ProgramProviderChip.circuit, ProgramProviderChip.main,
      Gadgets.ToBits.rangeCheck, Gadgets.ToBits.toBits, circuit_norm]
  | memoryInit =>
    simp [providerTableFor, Component.lookups_eq, Component.rowOperations,
      MemoryProviderChip.circuit, MemoryProviderChip.main, WordRangeCheck.circuit, circuit_norm]
  | memoryFinalize =>
    simp [providerTableFor, Component.lookups_eq, Component.rowOperations,
      MemoryFinalizeChip.circuit, MemoryFinalizeChip.main, circuit_norm]
  | memoryBump => exact MemoryBumpChip.lookups_empty
  | stateBump => exact StateBumpChip.lookups_empty
  | halt => exact HaltChip.lookups_empty
  | syscallInstrs => exact SyscallInstrsChip.lookups_empty

/-- The core inventory: every instruction chip and every native provider is lookup-free. -/
theorem sp1Ensemble_lookupFree : LookupFree (sp1Ensemble (p := p)).tables :=
  LookupFree.append sp1Tables_lookups_empty
    (LookupFree.map fun id _ => providerTableFor_lookups_empty id)

end SP1Clean.Soundness
