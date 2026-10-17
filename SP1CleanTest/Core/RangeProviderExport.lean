import SP1CleanTest.Core.ComponentExport
import SP1Clean.Proofs.Chips.ByteChip.RangeChip

/-! # Built-in export of the installed fixed-width Range family

These seventeen production providers prove membership through bit decomposition. Rust compares
their generated rows and messages with every row of SP1's verifier-fixed Range table and its AIR.
The physical layouts differ; the comparison leaves the external Byte bus open.
-/

namespace SP1CleanTest.Core.RangeProviderExport

open SP1Clean ComponentExport

/-- Every installed width, in the same increasing order as the native assembly. -/
def rustExports : List (String × Except String String) :=
  RangeChip.allWidths.map fun width =>
    (s!"range_{width.val}_provider.rs", exportRust (RangeChip.circuitFor width))

end SP1CleanTest.Core.RangeProviderExport
