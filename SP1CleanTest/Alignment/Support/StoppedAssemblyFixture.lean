import SP1CleanTest.Alignment.Support.BranchEnsembleFixture

/-! # Stopped-source instances of the complete installed assembly

The program and machine snapshot are shared with the compiler-derived branch fixture.
Optional terminal status and the two host banks remain independent instance fields. An empty
segment contributes zero to the numeric public Exit value even when its incoming host has a
nonzero stopped code. All physical components and boundary terminals remain installed.
-/

namespace SP1CleanTest.Alignment.StoppedAssembly

open SP1Clean SP1Clean.Model.Core SP1CleanTest.Alignment.InstalledAssembly

private def base : Context :=
  SP1Clean.Audit.BranchEnsemble.context SP1Clean.Audit.BranchEnsemble.target

/-- An already stopped host with exit code zero, retaining its empty queue and zero banks. -/
def zero : Context :=
  { base with
    source := { base.source with host.exitCode := some 0 }
    finalHost := { base.finalHost with exitCode := some 0 } }

/-- A wide stopped code and two nonzero banks prevent zero-valued endpoints hiding drift. -/
def wide : Context :=
  let host : HostState := { base.source.host with
    exitCode := some 65536
    committed := Vector.ofFn fun index : Fin 8 => BitVec.ofNat 32 (17 + index.val)
    deferred := Vector.ofFn fun index : Fin 8 => BitVec.ofNat 32 (33 + index.val) }
  { base with source := { base.source with host }, finalHost := host }

/-- No instruction retires, so every public clock/PC limb retains its incoming value. -/
def header : SP1PublicIO Fp := SP1Clean.Audit.BranchEnsemble.identityHeader

/-- A nonzero digest carrier, chosen to match the bank. The stopped assembly does not enforce
this equality: bank endpoints are fixed instance parameters, independent of this public field. -/
def wideHeader : SP1PublicIO Fp :=
  { header with committed_value_digest := Vector.ofFn fun index : Fin 32 =>
    if index.val % 4 == 0 then ((17 + index.val / 4 : ℕ) : Fp) else 0 }

/-- Changing a stopped code without execution violates the optional terminal boundary. -/
def changedCode : Context := { wide with finalHost.exitCode := some 0 }

/-- Removing the optional exit from a stopped host also violates the terminal boundary. -/
def restarted : Context := { wide with finalHost.exitCode := none }

/-- Advertising HALT-zero from a running source requires a real host-exit receipt. -/
def fabricatedHalt : Context := { base with finalHost.exitCode := some 0 }

end SP1CleanTest.Alignment.StoppedAssembly
