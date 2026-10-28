import SP1CleanTest.Alignment.Support.InstalledAssemblyLookups
import SP1Clean.Soundness.Shard.Trace

/-! # The exported assembly proves a Sail machine trace

The complete production assembly used for export comparisons is lookup-free, so the generic
committed-statement theorem applies to it with no remaining premise. Raw acceptance of a public
header yields a trace of the PolyFun SP1 machine from the complete source snapshot, ending with the
header's PC and clock and the context's outgoing registers and RAM.
-/

namespace SP1CleanTest.Alignment.InstalledAssembly

open Air.Flat SP1Clean SP1Clean.Model.Core SP1Clean.Soundness

/-- **The exported native assembly proves a Sail trace.** -/
theorem trace_of_statement (context : Context) (valid : context.image.Valid) {header : SP1PublicIO Fp}
    (accepted : (assembly context).Statement header) :
    Shard.SailTrace context.image valid context.source context.target context.finalHints context.finalHost
      header :=
  Shard.trace_of_committed_statement valid
    (fun component member => component_lookups context component (by
      rw [tables_eq]
      exact List.mem_append_left _ member))
    accepted

end SP1CleanTest.Alignment.InstalledAssembly
