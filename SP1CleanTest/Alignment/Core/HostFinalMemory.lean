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

/-- The shared nine-case battery accepts active ADD and empty identity, and rejects all seven
missing/duplicate validator, forged target, wrong-clock and missing-terminal cases. Keeping the
case definitions in the fixture also keeps large snapshot values out of theorem elaboration. -/
theorem regressions : results.all (fun (_, expected, actual) => expected == actual) = true := by
  native_decide

end SP1CleanTest.Alignment.Core.HostFinalMemory
