import SP1CleanTest.Alignment.Audit.BranchCompilerRoundTrip

set_option pp.fullNames true

open SP1Clean.Audit.BranchCompilerRoundTrip

#check decode_branch
#check official_try_step
#check execution_step
#check projected
#check compiled_eq
#check compiled_routed
#check event_target
#check row_target
#check table_constraints
#check table_one_real_row
#check flat_check
#check joined

#print axioms decode_branch
#print axioms official_try_step
#print axioms execution_step
#print axioms table_constraints
#print axioms flat_check
#print axioms joined
