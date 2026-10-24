module

public import SP1CleanTest.Alignment.Support.InstalledAssemblyChannels
public import SP1CleanTest.Alignment.Support.InstalledAssemblyLookups

/-! # Authenticated checking for the complete installed assembly

The context changes instance data while this one checked inventory retains every physical
table, fixed lookup obligation and raw channel, including the public verifier.
-/

@[expose] public section

namespace SP1CleanTest.Alignment.InstalledAssembly

open Circuit Air.Flat

/-- No installed component requires a legacy finite lookup oracle. -/
theorem fixed_names (context : Context) : (fixed context).map (·.table.name) = [] := rfl

/-- Authenticate every physical table and the complete separate public verifier. -/
def description (context : Context) :
    EnsembleCheck ((assembly context).withChannels (channels context)) where
  lookups := fixed context
  lookups_unique := by rw [fixed_names]; decide
  lookups_complete := lookups_complete context
  channels_unique := channels_unique context
  channels_complete := channels_complete context
  verifier_channels_complete := verifier_channels_complete context

end SP1CleanTest.Alignment.InstalledAssembly
