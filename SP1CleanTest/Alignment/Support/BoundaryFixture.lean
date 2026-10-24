module

public import SP1CleanTest.Alignment.Support.InstalledAssembly
public import SP1Clean.Model.Semantics.AccessSchedule

/-! # Shared finite memory-boundary inputs

The canonical frontier supplies last-access clocks. Source and target snapshots supply complete
values, and the production target constructors select the canonical change inventory. This helper
only constructs consumer inputs; Clean owns all witness generation and provider scheduling.
-/

@[expose] public section

namespace SP1CleanTest.Alignment.InstalledAssembly

open Circuit SP1Clean SP1Clean.Model.Core SP1Clean.Soundness SP1Clean.Semantics

/-- Close every touched register/RAM location, in address order, with target receipt checks. -/
def memorySeeds (context : Context) (frontier : AccessFrontier) (touched : List MemLoc) :
    Except String (List Seed) := do
  let registers := ((touched.filterMap fun loc => match loc with
    | .reg index => some index.toNat | .ram _ => none).mergeSort (· ≤ ·)).eraseDups
  let ram := ((touched.filterMap fun loc => match loc with
    | .ram cell => some cell.baseAddr.toNat | .reg _ => none).mergeSort (· ≤ ·)).eraseDups
  let mut consumers := registerSeeds context
    (registers.map fun index => (index, frontier (.reg (BitVec.ofNat 5 index))))
  let mut previous := (registers.getLast?).map (· + 1) |>.getD 0
  for address in ram do
    let record := memoryRecord address (frontier (.ram (BitVec.ofNat 61 (address / 8))))
      (context.target.memory.readWord address)
    let initial := OrderedSnapshotProvider.populate
      (Target.bitVecToWord (BitVec.ofNat 64 address)) previous address
    let final := OrderedMemoryProvider.populate record previous address
    let some check := FinalRamCheck.populate? context.source.sail.memorySnapshot context.target record
      | throw "RAM target constructor rejected its endpoint"
    consumers := consumers ++ [⟨1, (toElements initial).toList⟩, ⟨4, (toElements final).toList⟩,
      ⟨91, (toElements check).toList⟩]
    previous := address + 1
  let terminal := (toElements (OrderedBoundaryEnd.populate (Target.bitVecToWord (BitVec.ofNat 64 previous))
    (OrderedMemoryEnsemble.endKey (p := SP1Prime)))).toList
  return consumers ++ [⟨2, terminal⟩, ⟨5, terminal⟩]

end SP1CleanTest.Alignment.InstalledAssembly
