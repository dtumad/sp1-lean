extern crate alloc;

#[allow(dead_code)]
#[path = "support/assembly.rs"]
mod assembly;
#[allow(dead_code)]
#[path = "support/backend.rs"]
mod backend;
#[path = "support/fixture.rs"]
mod fixture;
use assembly::*;
use fixture::fixture;

#[allow(dead_code)]
#[path = "support/execution.rs"]
mod execution;
#[allow(dead_code)]
#[path = "support/export.rs"]
mod export_support;

use clean_backend::witness_generation::{generate, Program};
use clean_backend::GeneratedAirSpec;
use p3_field::PrimeCharacteristicRing;
use p3_koala_bear::KoalaBear as F;
use p3_matrix::Matrix;

fixture!(commit_complete_halt, "installed_commit_complete_halt");
fixture!(commit_partial_halt, "installed_commit_partial_halt");
fixture!(deferred_repeat, "installed_deferred_repeat");
fixture!(commit_repeat, "installed_commit_repeat");
#[test]
fn complete_commitment_rows_padding_and_public_mutations_match_native() {
    check_reference::<commit_repeat::Ensemble>(&commit_repeat::reference(), 9);
    check_reference::<deferred_repeat::Ensemble>(&deferred_repeat::reference(), 9);
    check_reference::<commit_partial_halt::Ensemble>(&commit_partial_halt::reference(), 9);
    check_reference::<commit_complete_halt::Ensemble>(&commit_complete_halt::reference(), 9);
}

fn commitment_execution<P: Program<F> + GeneratedAirSpec>(
    reference: &serde_json::Value,
    complete: bool,
    deferred: bool,
    stopped: bool,
) {
    use slop_air::Air;
    use slop_algebra::AbstractField;
    use slop_matrix::Matrix as _;
    use sp1_core_executor::{
        ExecutionRecord, Instruction, Opcode, Program as Sp1Program, SyscallCode,
    };
    use sp1_core_machine::{syscall::instructions::SyscallInstrsChip, SupervisorMode};
    use sp1_hypercube::air::MachineAir;
    use sp1_primitives::SP1Field as S;

    let case = &reference["cases"][0];
    let public = fields(&case["publicInput"]);
    let native = generate::<F, P>(&public, &fields(&case["privateInput"])).unwrap();
    let mut instructions = vec![];
    execution::load_constant(&mut instructions, 5, if deferred { 26 } else { 16 });
    execution::load_constant(&mut instructions, 10, if complete { 0 } else { 7 });
    execution::load_constant(&mut instructions, 11, 131075);
    // The prefix establishes the local source. The tested segment starts at the
    // same PC; clock comparison uses the measured prefix duration, not guessed timing.
    let base = 131072 - 4 * instructions.len() as u64;
    let addi = |rd, rs, imm| Instruction::new(Opcode::ADDI, rd, rs, imm, false, true);
    let ecall = || Instruction::new(Opcode::ECALL, 5, 10, 11, false, false);
    if complete {
        for bank in 0..2 {
            if bank == 1 {
                instructions.push(addi(5, 0, 26));
                instructions.push(addi(10, 0, 0));
            }
            for slot in 0..8 {
                instructions.push(ecall());
                if slot != 7 {
                    instructions.push(addi(10, 10, 1));
                }
            }
        }
    } else {
        instructions.extend([ecall(), ecall(), ecall()]);
    }
    // Continuing fixtures are proper local prefixes of this terminating Rust run.
    instructions.extend([addi(5, 0, 0), addi(10, 0, 0), ecall()]);
    let (executor, records) = execution::run(Sp1Program::new(instructions, base, base), &[]);
    assert_eq!(records.len(), 1);
    let record = &records[0];
    let count = if complete { 16 } else { 3 };
    assert_eq!(record.syscall_events.len(), count + 1);
    let first = record.syscall_events[0].0.clk;
    assert_eq!(record.syscall_events[0].0.pc, 131072);
    let (end_clock, end_pc) = if stopped {
        (
            record.public_values.last_timestamp,
            record.public_values.next_pc,
        )
    } else {
        let next_pc = record.syscall_events[count - 1].0.next_pc;
        let (next, _) = record
            .addi_events
            .iter()
            .find(|(event, _)| event.pc == next_pc)
            .expect("the continuing segment ends before the observed HALT setup");
        (next.clk, next.pc)
    };
    check_endpoints(&public, (9, 131072), (end_clock - first + 9, end_pc));
    for bank in 0..2 {
        for slot in 0..8 {
            let value = if bank == 0 {
                record.public_values.committed_value_digest[slot]
            } else {
                record.public_values.deferred_proofs_digest[slot]
            };
            let flag = if bank == 0 { public[56] } else { public[57] };
            assert_eq!(
                P::fixed_row::<F>(94, (8 * bank + slot) as u64),
                vec![
                    F::from_u64(bank as u64),
                    F::from_u64(slot as u64),
                    F::from_u64(u64::from(value & 65535)),
                    F::from_u64(u64::from(value >> 16)),
                    F::ZERO,
                    F::ZERO,
                    flag,
                    F::ONE,
                ]
            );
        }
    }
    let mut occurrences = [0usize; 16];
    for (event, _) in &record.syscall_events[..count] {
        let bank = usize::from(event.syscall_code == SyscallCode::COMMIT_DEFERRED_PROOFS);
        assert!(matches!(
            event.syscall_code,
            SyscallCode::COMMIT | SyscallCode::COMMIT_DEFERRED_PROOFS
        ));
        let slot = event.arg1 as usize;
        let table = 66 + 8 * bank + slot;
        let row = &native.tables[table][occurrences[8 * bank + slot]];
        occurrences[8 * bank + slot] += 1;
        assert_eq!(row[0], F::ZERO);
        assert_eq!(row[1], F::from_u64(event.clk - first + 9));
        assert_eq!(
            &row[2..6],
            &[
                F::from_u64(event.syscall_code as u64),
                F::ZERO,
                F::ZERO,
                F::ZERO
            ]
        );
        assert_eq!(
            &row[6..10],
            &[F::from_u64(event.arg1), F::ZERO, F::ZERO, F::ZERO]
        );
        assert_eq!(
            &row[10..14],
            &[
                F::from_u64(event.arg2 & 65535),
                F::from_u64(event.arg2 >> 16),
                F::ZERO,
                F::ZERO
            ]
        );
        assert_eq!(row[P::HINT_TABLES[table].width - 1], F::ONE);
    }
    for bank in 0..2 {
        let words = if bank == 0 {
            record.public_values.committed_value_digest
        } else {
            record.public_values.deferred_proofs_digest
        };
        let terminal = &native.tables[88 + bank][0];
        for (slot, value) in words.into_iter().enumerate() {
            assert_eq!(
                &terminal[2 + 4 * slot..6 + 4 * slot],
                &[
                    F::from_u64(u64::from(value & 65535)),
                    F::from_u64(u64::from(value >> 16)),
                    F::ZERO,
                    F::ZERO
                ]
            );
            if bank == 0 {
                let bytes = value.to_le_bytes().map(|byte| F::from_u64(u64::from(byte)));
                assert_eq!(&public[16 + 4 * slot..20 + 4 * slot], &bytes);
            } else {
                assert_eq!(public[48 + slot], F::from_u64(u64::from(value)));
            }
        }
    }
    assert_eq!(
        public[56],
        F::from_u64(u64::from(record.public_values.commit_syscall))
    );
    assert_eq!(
        public[57],
        F::from_u64(u64::from(record.public_values.commit_deferred_syscall))
    );
    assert_eq!(native.tables[64].len(), usize::from(stopped));
    assert_eq!(native.tables[57].len(), usize::from(!stopped));
    if stopped {
        assert_eq!(executor.registers()[5], 0);
    }
    // Check the released AIR on real released rows and its own shard public values.
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

#[test]
fn complete_commitment_programs_match_released_events_air_and_statement() {
    commitment_execution::<commit_repeat::Ensemble>(
        &commit_repeat::reference(),
        false,
        false,
        false,
    );
    commitment_execution::<deferred_repeat::Ensemble>(
        &deferred_repeat::reference(),
        false,
        true,
        false,
    );
    commitment_execution::<commit_partial_halt::Ensemble>(
        &commit_partial_halt::reference(),
        false,
        false,
        true,
    );
    commitment_execution::<commit_complete_halt::Ensemble>(
        &commit_complete_halt::reference(),
        true,
        false,
        true,
    );
}

fn commitment_proofs<P: Program<F> + GeneratedAirSpec>(
    reference: &serde_json::Value,
    repeated: Option<usize>,
) {
    let (traces, public) = prove_case::<P>(&reference["cases"][0]);
    for case in reference["cases"]
        .as_array()
        .unwrap()
        .iter()
        .skip(1)
        .take(5)
    {
        reject_traces::<P>(&fields(&case["publicInput"]), traces.clone());
    }
    for table in [88, 89, 94] {
        let mut missing = traces.clone();
        missing[table].values.clear();
        reject_traces::<P>(&public, missing);
    }
    // Only the sixteen counts are committed. Fixed payload and eligibility columns
    // come from the verifier's preprocessing, never from mutable witness columns.
    assert_eq!(traces[94].width(), 1);
    for slot in 0..16 {
        let mut changed = traces.clone();
        changed[94].values[slot] += F::ONE;
        reject_traces::<P>(&public, changed);
    }
    if let Some(table) = repeated {
        assert_eq!(traces[table].height(), 4);
        let activity = P::HINT_TABLES[table].width - 1;
        assert_eq!(
            traces[table].values[3 * traces[table].width() + activity],
            F::ZERO
        );
        for row in 0..3 {
            assert_eq!(
                traces[table].values[row * traces[table].width() + activity],
                F::ONE
            );
        }
        for enabled in [F::ONE, F::TWO, -F::ONE] {
            let mut changed = traces.clone();
            let column = 3 * changed[table].width() + activity;
            changed[table].values[column] = enabled;
            reject_traces::<P>(&public, changed);
        }
    }
}

#[test]
fn immutable_commitment_assemblies_prove_and_reject_forged_declarations() {
    commitment_proofs::<commit_repeat::Ensemble>(&commit_repeat::reference(), Some(73));
    commitment_proofs::<deferred_repeat::Ensemble>(&deferred_repeat::reference(), Some(81));
    commitment_proofs::<commit_partial_halt::Ensemble>(&commit_partial_halt::reference(), Some(73));
    commitment_proofs::<commit_complete_halt::Ensemble>(&commit_complete_halt::reference(), None);
}
