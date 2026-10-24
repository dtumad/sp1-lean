module

public import SP1CleanTest.Core.ComponentExport
public import SP1Clean.Proofs.Chips.MemoryBumpChip.Formal
public import SP1Clean.Proofs.Chips.StateBumpChip.Formal

/-! # Built-in export of SP1's bump components

Both production circuits consume complete input rows and allocate no additional witness cells.
Rust supplies independently generated released-SP1 rows and compares constraints and the complete
open-bus ledger, including inactive rows. This is not a whole-execution generation claim.
-/

@[expose] public section

namespace SP1CleanTest.Core.SystemExport

open SP1Clean ComponentExport

/-- The two installed timestamp/state canonicalization components. -/
def rustExports : List (String × Except String String) := [
  ("memory_bump.rs", exportRust MemoryBumpChip.circuit),
  ("state_bump.rs", exportRust StateBumpChip.circuit)]

end SP1CleanTest.Core.SystemExport
