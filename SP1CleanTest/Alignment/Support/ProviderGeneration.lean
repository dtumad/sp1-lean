import SP1Clean.Soundness.SP1Ensemble
import SP1CleanTest.Core.ComponentExport

/-! # Generation routes for the installed Byte and Range providers

Clean selects the provider by the complete Byte opcode and, for Range, its width. The typed
native inventory supplies component identities; physical table order is independent of opcode
order. This module only configures Clean's existing scheduler, using the installed circuits.
-/

namespace SP1CleanTest.Alignment.ProviderGeneration

open Air.Flat Circuit SP1Clean SP1Clean.Soundness
open SP1CleanTest.Core.ComponentExport (Fp)

private def message (index : ℕ) : Witgen.FExpr Fp := .expr (.var ⟨index⟩)

private def opcode : ByteProviderId → ℕ
  | .andByte => 0
  | .orByte => 1
  | .xorByte => 2
  | .u8Range => 3
  | .ltu => 4
  | .msb => 5

private def byteMode (provider : ByteProviderId) : WitnessGeneration.Mode Fp := .demand {
  channel := (Channels.byteChannel (p := SP1Prime)).toRaw
  direction := .pull
  aggregation := .byMessage
  predicate := .feq (message 0) (.const (opcode provider))
  predicate_valid := by cases provider <;> rfl
  input := ⟨match provider with
    | .msb => [.message 2, .multiplicity]
    | _ => [.message 2, .message 3, .multiplicity]⟩
}

private def rangeMode (width : Fin 17) : WitnessGeneration.Mode Fp := .demand {
  channel := (Channels.byteChannel (p := SP1Prime)).toRaw
  direction := .pull
  aggregation := .byMessage
  predicate := .and (.feq (message 0) (.const 6)) (.feq (message 2) (.const width.val))
  predicate_valid := by rfl
  input := ⟨[.message 1, .multiplicity]⟩
}

private def generation (id : ProviderTableId) (mode : WitnessGeneration.Mode Fp) :
    String × WitnessGeneration.Generation Fp :=
  let component := providerTableFor (p := SP1Prime) id
  (component.circuit.name, {
    mode
    padding := { input := Array.replicate component.rowOffset 0 }
  })

/-- Routing for all six installed Byte providers and the complete seventeen-width Range family. -/
def byteConfig : WitnessGeneration.Config Fp where
  components :=
    (ByteProviderId.all.map fun provider => generation (.byte provider) (byteMode provider)) ++
    ((List.finRange 17).map fun width => generation (.range width) (rangeMode width))
  fuel := 131074

end SP1CleanTest.Alignment.ProviderGeneration
