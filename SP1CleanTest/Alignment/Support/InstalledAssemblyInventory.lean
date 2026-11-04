import SP1CleanTest.Alignment.Support.InstalledAssemblyChannels
import SP1CleanTest.Alignment.Support.InstalledAssemblyLookups

/-! # Authenticated checking for the complete installed assembly

The context changes instance data while this one checked inventory retains every physical
table, fixed lookup obligation and raw channel, including the public verifier.
-/

namespace SP1CleanTest.Alignment.InstalledAssembly

open Circuit Air.Flat

/-- No installed component requires a legacy finite lookup oracle. -/
theorem fixed_names (context : Context) : (fixed context).map (·.table.name) = [] := rfl

/-- Authenticate every physical table and the complete separate public verifier. -/
def description (context : Context) :
    EnsembleCheck (assembly context) where
  lookups := fixed context
  lookups_unique := by rw [fixed_names]; decide
  lookups_complete := lookups_complete context

end SP1CleanTest.Alignment.InstalledAssembly
