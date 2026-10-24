module

public import Mathlib.Data.BitVec

/-! # Released SP1 exit acceptance

The default, non-experimental verifier policy accepts only exit zero, including when its
requested status is ANY. Raw HALT execution and the native AIR may still describe nonzero
exits. This policy is an additional release-facing condition, not a change to those semantics.
The independent Rust comparisons check it against the pinned executor's `StatusCode::ANY`.
-/

@[expose] public section

namespace SP1Clean.Semantics.ReleasePolicy

/-- The broadest accepted exit status in a default released SP1 verifier build. -/
def acceptsExit (exitCode : BitVec 32) : Bool := exitCode == 0

@[simp] theorem acceptsExit_iff (exitCode : BitVec 32) :
    acceptsExit exitCode = true ↔ exitCode = 0 := by
  simp [acceptsExit]

end SP1Clean.Semantics.ReleasePolicy
