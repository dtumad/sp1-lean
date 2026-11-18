import SP1CleanTest.Alignment.Core.LocalCore

/-! # Compiled whole-assembly regression checks

Each check evaluates complete local assemblies over `ZMod SP1Prime`. As `native_decide` theorems they
ran in Lean's interpreter, which spent 173 of `LocalCore`'s 180 s on them; this driver runs the same
decisions as compiled code. It prints one line per check and exits with status 1 if any fails.
-/

/-- Run every suite, report each check with its time, and fail if any check fails. -/
def main : IO UInt32 := do
  let suites := [("LocalCore", SP1CleanTest.Core.LocalCore.checks)]
  let mut failed := 0
  for (suite, checks) in suites do
    for (name, run) in checks do
      let start ← IO.monoMsNow
      let passed := run ()
      let stop ← IO.monoMsNow
      IO.println s!"{if passed then "PASS" else "FAIL"} {suite}.{name} ({stop - start} ms)"
      unless passed do failed := failed + 1
  IO.println s!"{failed} failed"
  return if failed == 0 then 0 else 1
