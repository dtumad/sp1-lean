//! Check released host AIR using released execution records.

use crate::export_support;
use p3_field::{PrimeCharacteristicRing, PrimeField64};
use p3_koala_bear::KoalaBear as F;
use sp1_core_executor::{events::MemoryRecordEnum, ExecutionRecord};

/// Compare a locally initialized segment against the released execution and row generator.
/// The Rust boot prelude sets the local source registers. Accesses before that cut have
/// previous timestamp zero in the segment, just like its fixed initial memory table.
pub fn check_host_instructions(
    record: &ExecutionRecord,
    (rust_start, local_start): (u64, u64),
    count: usize,
    native: &[Vec<F>],
) {
    use slop_air::Air;
    use slop_algebra::{AbstractField, PrimeField64 as _};
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

    let segment_clock = |timestamp| {
        if timestamp < rust_start {
            0
        } else {
            local_start + (timestamp - rust_start)
        }
    };
    let mut events = record.syscall_events[..count].to_vec();
    for (event, registers) in &mut events {
        event.clk = segment_clock(event.clk);
        for access in [&mut registers.a, &mut registers.b, &mut registers.c] {
            let (current, previous) = match access {
                MemoryRecordEnum::Read(r) => (&mut r.timestamp, &mut r.prev_timestamp),
                MemoryRecordEnum::Write(r) => (&mut r.timestamp, &mut r.prev_timestamp),
            };
            *current = segment_clock(*current);
            *previous = segment_clock(*previous);
        }
    }
    let segment = ExecutionRecord {
        syscall_events: events,
        ..Default::default()
    };
    let expected: slop_matrix::dense::RowMajorMatrix<S> =
        chip.generate_trace(&segment, &mut ExecutionRecord::default());
    assert_eq!(expected.width(), 65);
    let active: Vec<_> = native.iter().filter(|row| row[64] == F::ONE).collect();
    assert_eq!(active.len(), count);
    for (i, row) in active.into_iter().enumerate() {
        for (j, cell) in row[..65].iter().enumerate() {
            assert_eq!(
                cell.as_canonical_u64(),
                expected.values[i * 65 + j].as_canonical_u64(),
                "syscall instruction at position {i}, column {j}"
            );
        }
    }
}
