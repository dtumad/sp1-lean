//! Check released host AIR using released execution records.

use crate::export_support;
use sp1_core_executor::ExecutionRecord;

pub fn released_host_air(record: &ExecutionRecord) {
    use slop_air::Air;
    use slop_algebra::AbstractField;
    use slop_matrix::Matrix;
    use sp1_core_machine::{syscall::instructions::SyscallInstrsChip, SupervisorMode};
    use sp1_hypercube::air::MachineAir;
    use sp1_primitives::SP1Field as S;
    let chip = SyscallInstrsChip::<SupervisorMode>::default();
    let trace = chip.generate_trace(record, &mut ExecutionRecord::default());
    for row in trace.values.chunks(trace.width()) {
        let mut check = export_support::Sp1Evaluation {
            row: row.to_vec(),
            preprocessed: vec![],
            constraints: vec![],
            ledger: vec![],
            public: record.public_values.to_vec::<S>(),
        };
        chip.eval(&mut check);
        assert!(check.constraints.iter().all(|value| *value == S::zero()));
    }
}
