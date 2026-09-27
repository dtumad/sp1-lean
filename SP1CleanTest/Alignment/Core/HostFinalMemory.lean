import SP1CleanTest.Alignment.Support.HostFinalMemoryFixture

/-! # Complete physical host assembly with outgoing Memory checks

Reuse the existing active ADD fixture, its interpreter, and actual Byte/Range providers. The
host queue is empty and both commitment banks have physical terminals. The target consumers
validate every final record, including unchanged registers and code RAM. All registered channel
occurrences are retained; this fixture checks the assembled AIR, not the unclosed capstone.
-/

namespace SP1CleanTest.Alignment.Core.HostFinalMemory

open Circuit Air.Flat SP1Clean SP1Clean.Model.Core SP1Clean.Soundness

open Fixture

/-- The active ADD witness includes all target checks and actual lookup providers in one ledger. -/
theorem activeAcceptance : check target header rows = true := by native_decide

/-- No validator, unchanged final record or host terminal can disappear from the accepted witness. -/
theorem mutations :
    [check target header (rows.filter (fun row => row.1 != 88)),
     check target header (rows ++ [ramCheck 0]),
     check target header (rows.map fun row => if row.1 == 88 then ramCheck 1 else row),
     check target header (coreRows ++ terminals ++ [registerCheck 1 13 123 1, ramCheck 0]),
     check { target with registers := target.registers.set 31 1 } header rows,
     check { target with memory := target.memory.write 65544 1 } header rows,
     check target header (rows.filter (fun row => row.1 != 85))] = List.replicate 7 false := by
  native_decide

/-- An empty continuing segment needs no final inventory and still closes every physical channel. -/
theorem identityAcceptance : check source.sail.memorySnapshot identityHeader identityRows = true := by native_decide

end SP1CleanTest.Alignment.Core.HostFinalMemory
