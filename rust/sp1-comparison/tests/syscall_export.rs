//! Released supervisor syscall AIR versus Clean's base, profile and installed host-call exports.
//! Public-value bindings use a checked semantic adapter; external buses remain open.

extern crate alloc;

#[path = "support/export.rs"]
mod export_support;

#[path = "support/execution.rs"]
mod execution;

use clean_backend::witness_generation::{generate, Program, WitnessGenerationError};
use clean_backend::GeneratedAirSpec;
use export_support::{Ledger, RowWitness, Sp1Evaluation};
use p3_field::{PrimeCharacteristicRing, PrimeField64};
use p3_koala_bear::KoalaBear as F;
use slop_air::Air;
use slop_algebra::{AbstractField, PrimeField64 as Sp1PrimeField64};
use slop_matrix::Matrix;
use sp1_core_executor::{
    events::{MemoryReadRecord, MemoryRecordEnum, MemoryWriteRecord, SyscallEvent},
    ExecutionRecord, RTypeRecord, SyscallCode, HALT_PC,
};
use sp1_core_machine::{
    air::MemoryAirBuilder,
    memory::RegisterAccessCols,
    syscall::instructions::{columns::SyscallInstrColumns, SyscallInstrsChip},
    SupervisorMode,
};
use sp1_hypercube::air::{MachineAir, PublicValues};
use sp1_primitives::SP1Field as S;
use std::borrow::{Borrow, BorrowMut};

macro_rules! generated_syscall {
    ($module:ident, $file:literal, $program:ident) => {
        #[allow(dead_code, unused_imports, unused_variables, unused_parens)]
        mod $module {
            include!(concat!(env!("CLEAN_ENSEMBLE_EXPORT_DIR"), "/", $file));
        }
        use $module::Ensemble as $program;
    };
}
generated_syscall!(base, "syscall_instruction.rs", Base);
generated_syscall!(profile, "core_syscall.rs", Core);
generated_syscall!(host, "host_call.rs", Host);

type Columns = SyscallInstrColumns<S, SupervisorMode>;
type Public = PublicValues<u32, u64, u64, u32>;

fn codes() -> [SyscallCode; 8] {
    [
        SyscallCode::HALT,
        SyscallCode::WRITE,
        SyscallCode::ENTER_UNCONSTRAINED,
        SyscallCode::COMMIT,
        SyscallCode::COMMIT_DEFERRED_PROOFS,
        SyscallCode::VERIFY_SP1_PROOF,
        SyscallCode::HINT_LEN,
        SyscallCode::HINT_READ,
    ]
}

fn read(value: u64, timestamp: u64, previous: u64) -> MemoryRecordEnum {
    MemoryRecordEnum::Read(MemoryReadRecord {
        value,
        timestamp,
        prev_timestamp: previous,
        prev_page_prot_record: None,
    })
}

fn event(
    code: SyscallCode,
    arg1: u64,
    arg2: u64,
    result: u64,
    clk: u64,
    pc: u64,
) -> (SyscallEvent, RTypeRecord) {
    let previous = clk - 1;
    (
        SyscallEvent {
            pc,
            next_pc: if code == SyscallCode::HALT {
                HALT_PC
            } else {
                pc + 4
            },
            clk,
            should_send: code.should_send() != 0,
            syscall_code: code,
            syscall_id: code.syscall_id(),
            arg1,
            arg2,
            exit_code: if code == SyscallCode::HALT {
                arg1 as u32
            } else {
                0
            },
            sig_return_pc_record: None,
            trap_result: None,
            trap_error: None,
        },
        RTypeRecord {
            op_a: 5,
            a: MemoryRecordEnum::Write(MemoryWriteRecord {
                value: result,
                prev_value: code as u64,
                timestamp: clk + 4,
                prev_timestamp: previous,
                prev_page_prot_record: None,
            }),
            op_b: 10,
            b: read(arg1, clk + 3, previous),
            op_c: 11,
            c: read(arg2, clk + 2, previous),
            is_untrusted: false,
        },
    )
}

fn public_for(event: &SyscallEvent) -> Public {
    let mut public = Public {
        committed_value_digest: core::array::from_fn(|i| 0x1234_5678 + i as u32),
        deferred_proofs_digest: core::array::from_fn(|i| 0x9876 + i as u32),
        commit_syscall: 1,
        commit_deferred_syscall: 1,
        exit_code: 19,
        ..Default::default()
    };
    match event.syscall_code {
        SyscallCode::HALT => public.exit_code = event.arg1 as u32,
        SyscallCode::COMMIT => {
            public.committed_value_digest[event.arg1 as usize] = event.arg2 as u32
        }
        SyscallCode::COMMIT_DEFERRED_PROOFS => {
            public.deferred_proofs_digest[event.arg1 as usize] = event.arg2 as u32
        }
        _ => {}
    }
    public
}

fn samples() -> Vec<(SyscallEvent, RTypeRecord)> {
    let mut cases = vec![];
    for clk in [1, (1 << 24) - 263, (1 << 24) + 1, (1 << 48) - 265] {
        for exit in [0, 65535, 65536, F::ORDER_U64 - 1] {
            cases.push(event(SyscallCode::HALT, exit, u64::MAX, 0, clk, 0x1_ffff));
        }
        for code in [
            SyscallCode::ENTER_UNCONSTRAINED,
            SyscallCode::WRITE,
            SyscallCode::VERIFY_SP1_PROOF,
            SyscallCode::HINT_LEN,
            SyscallCode::HINT_READ,
        ] {
            let result = match code {
                SyscallCode::ENTER_UNCONSTRAINED => 0,
                SyscallCode::HINT_LEN => u64::MAX,
                _ => code as u64,
            };
            cases.push(event(
                code,
                u64::MAX,
                u64::MAX - 1,
                result,
                clk,
                0xffff_ffff,
            ));
        }
    }
    for slot in 0..8 {
        for value in [0, 65536, u32::MAX as u64] {
            cases.push(event(
                SyscallCode::COMMIT,
                slot,
                value,
                SyscallCode::COMMIT as u64,
                1,
                65536,
            ));
        }
        for value in [0, 65536, F::ORDER_U64 - 1] {
            cases.push(event(
                SyscallCode::COMMIT_DEFERRED_PROOFS,
                slot,
                value,
                SyscallCode::COMMIT_DEFERRED_PROOFS as u64,
                1,
                65536,
            ));
        }
    }
    // The base circuit includes precompile dispatch; the installed profile must reject it.
    cases.push(event(
        SyscallCode::SHA_EXTEND,
        (1 << 48) - 1,
        (1 << 32) + 7,
        SyscallCode::SHA_EXTEND as u64,
        1,
        65536,
    ));
    cases
}

fn evaluation(row: &[S], public: &Public) -> Sp1Evaluation {
    Sp1Evaluation {
        row: row.to_vec(),
        preprocessed: vec![],
        constraints: vec![],
        ledger: vec![],
        public: public.to_vec(),
    }
}

fn native(row: &[S]) -> Vec<F> {
    row.iter()
        .map(|x| F::from_u64(x.as_canonical_u64()))
        .collect()
}

fn witness<P: Program<F>>(input: &[S]) -> Vec<F> {
    let witness = generate::<F, RowWitness<P>>(&[], &native(input)).unwrap();
    assert_eq!(witness.tables.len(), 1);
    assert_eq!(witness.tables[0].len(), 1);
    witness.tables[0][0].clone()
}

fn ledger<P: Program<F>>(row: &[F]) -> Ledger {
    P::interactions(0, row)
        .into_iter()
        .map(|entry| {
            (
                entry.channel.to_owned(),
                entry.multiplicity.as_canonical_u64(),
                entry
                    .message
                    .iter()
                    .map(PrimeField64::as_canonical_u64)
                    .collect(),
            )
        })
        .collect()
}

fn valid<P: Program<F> + GeneratedAirSpec>(row: &[F]) -> bool {
    let constraints = P::constraints::<F>(0, row);
    assert!(!constraints.is_empty());
    constraints.iter().all(|x| *x == F::ZERO)
}

fn reduce(word: &[S; 4]) -> S {
    word.iter().rev().fold(S::zero(), |acc, limb| {
        acc * S::from_canonical_u32(65536) + *limb
    })
}

/// Named native field families, independent of the released Rust public struct layout.
/// Retain every coefficient and all eight public/exit occurrences, including zero multiplicities.
fn public_ledger(cols: &Columns) -> Ledger {
    let commit = cols.is_commit.result;
    let deferred = cols.is_commit_deferred_proofs.result;
    let unit = core::array::from_fn(|index| S::from_bool(index == 0));
    let query = |base: u32, stride: u32, coefficients: &[S; 8], value: S| {
        let mut message = vec![S::from_canonical_u32(base), S::from_canonical_u32(stride)];
        message.extend(coefficients.iter().copied());
        message.push(value);
        message
    };
    let entry = |name: &str, mult: S, values: Vec<S>| {
        (
            name.to_owned(),
            mult.as_canonical_u64(),
            values
                .iter()
                .map(Sp1PrimeField64::as_canonical_u64)
                .collect(),
        )
    };
    let mut result = vec![
        entry("SP1Exit", cols.is_halt, vec![reduce(&cols.adapter.b().0)]),
        entry("SP1PublicValues", -commit, query(145, 0, &unit, S::one())),
        entry("SP1PublicValues", -deferred, query(147, 0, &unit, S::one())),
    ];
    for i in 0..4 {
        result.push(entry(
            "SP1PublicValues",
            -commit,
            query(
                32 + i as u32,
                4,
                &cols.index_bitmap,
                cols.expected_public_values_digest[i],
            ),
        ));
    }
    result.push(entry(
        "SP1PublicValues",
        -cols.is_real * deferred,
        query(72, 1, &cols.index_bitmap, reduce(&cols.adapter.c().0)),
    ));
    result
}

fn bindings_hold(entries: &Ledger, public: &Public) -> bool {
    entries.iter().all(|(channel, mult, message)| {
        if *mult == 0 {
            return true;
        }
        match channel.as_str() {
            "SP1Exit" => {
                assert_eq!(message.len(), 1);
                message[0] == public.exit_code as u64
            }
            "SP1PublicValues" => {
                assert_eq!(message.len(), 11);
                // Map the explicit family to named released fields, never to assumed offsets.
                let values: [S; 8] = match (message[0], message[1]) {
                    (base @ 32..=35, 4) => core::array::from_fn(|slot| {
                        S::from_canonical_u8(
                            public.committed_value_digest[slot].to_le_bytes()[(base - 32) as usize],
                        )
                    }),
                    (72, 1) => public.deferred_proofs_digest.map(S::from_canonical_u32),
                    (145, 0) => [S::from_canonical_u32(public.commit_syscall); 8],
                    (147, 0) => [S::from_canonical_u32(public.commit_deferred_syscall); 8],
                    _ => return false,
                };
                let expected = values
                    .iter()
                    .zip(&message[2..10])
                    .map(|(value, coefficient)| *value * S::from_canonical_u64(*coefficient))
                    .sum::<S>();
                expected.as_canonical_u64() == message[10]
            }
            _ => panic!("not a public binding: {channel}"),
        }
    })
}

fn normalize_supervisor_syscalls(entries: &mut Ledger) {
    for (channel, _, message) in entries {
        if channel == "SP1Syscall" {
            assert_eq!(
                message.len(),
                if cfg!(feature = "mprotect") { 10 } else { 9 }
            );
            if cfg!(feature = "mprotect") {
                assert_eq!(
                    message.remove(3),
                    0,
                    "supervisor trap code must be zero, even on padding"
                );
            }
        }
    }
}

fn compare(sp1: &[S], public: &Public, label: &str) -> bool {
    let cols: &Columns = sp1.borrow();
    let mut expected = evaluation(sp1, public);
    SyscallInstrsChip::<SupervisorMode>::default().eval(&mut expected);
    normalize_supervisor_syscalls(&mut expected.ledger);
    let binding = public_ledger(cols);
    expected.ledger.extend(binding.clone());
    let row = native(sp1);
    let mut actual = ledger::<Base>(&row);
    actual.sort();
    expected.ledger.sort();
    assert_eq!(
        actual, expected.ledger,
        "all physical interactions: {label}"
    );
    let accepted = valid::<Base>(&row) && bindings_hold(&binding, public);
    assert_eq!(
        accepted,
        expected.constraints.iter().all(|x| *x == S::zero()),
        "AIR and public binding satisfaction: {label}"
    );
    accepted
}

#[test]
fn supervisor_rows_public_bindings_and_every_column_match_released_sp1() {
    let cases = samples();
    assert_eq!(cases.len(), 85);
    let record = ExecutionRecord {
        syscall_events: cases.clone(),
        ..Default::default()
    };
    let trace = SyscallInstrsChip::<SupervisorMode>::default()
        .generate_trace(&record, &mut ExecutionRecord::default());
    assert_eq!(trace.width(), 65);
    assert_eq!(Base::WIDTHS, &[trace.width()]);
    assert_eq!(<Base as Program<F>>::PROVER_INPUTS, 65);
    assert_eq!(trace.height(), 96);
    let mut rejected = 0;
    for (index, row) in trace.values.chunks(trace.width()).enumerate() {
        let public = cases
            .get(index)
            .map_or_else(Public::default, |case| public_for(&case.0));
        assert_eq!(witness::<Base>(row), native(row));
        assert!(compare(row, &public, &format!("row {index}")));
        for col in 0..trace.width() {
            for delta in [1, 65536, F::ORDER_U64 - 1] {
                let mut changed = row.to_vec();
                changed[col] += S::from_canonical_u64(delta);
                rejected += usize::from(!compare(
                    &changed,
                    &public,
                    &format!("row {index}, column {col}, delta {delta}"),
                ));
            }
        }
    }
    assert!(rejected > 0);
}

#[test]
fn public_exit_flags_digest_bytes_and_deferred_slots_are_bound() {
    for case in samples() {
        let record = ExecutionRecord {
            syscall_events: vec![case],
            ..Default::default()
        };
        let trace = SyscallInstrsChip::<SupervisorMode>::default()
            .generate_trace(&record, &mut ExecutionRecord::default());
        let row = trace.row_slice(0);
        let public = public_for(&case.0);
        assert!(compare(&row, &public, "original public values"));
        match case.0.syscall_code {
            SyscallCode::HALT => {
                let mut changed = public;
                changed.exit_code = (changed.exit_code + 1) % F::ORDER_U64 as u32;
                assert!(!compare(&row, &changed, "wrong exit code"));
            }
            SyscallCode::COMMIT | SyscallCode::COMMIT_DEFERRED_PROOFS => {
                let deferred = case.0.syscall_code == SyscallCode::COMMIT_DEFERRED_PROOFS;
                let mut changed = public;
                if deferred {
                    changed.commit_deferred_syscall = 0;
                } else {
                    changed.commit_syscall = 0;
                }
                assert!(!compare(&row, &changed, "missing commit flag"));
                for slot in 0..8 {
                    for byte in 0..if deferred { 1 } else { 4 } {
                        let mut changed = public;
                        if deferred {
                            changed.deferred_proofs_digest[slot] ^= 1;
                        } else {
                            changed.committed_value_digest[slot] ^= 1 << (8 * byte);
                        }
                        assert_eq!(
                            compare(&row, &changed, "changed public digest"),
                            slot != case.0.arg1 as usize
                        );
                    }
                }
            }
            _ => {}
        }
    }
}

#[test]
fn inactive_commit_preserves_arbitrary_weighted_public_selection() {
    let public = Public {
        prev_committed_value_digest: [0x1234_5678; 8],
        committed_value_digest: core::array::from_fn(|slot| {
            u32::from_le_bytes([
                1 + slot as u8,
                17 + slot as u8,
                33 + slot as u8,
                65 + slot as u8,
            ])
        }),
        commit_syscall: 1,
        ..Default::default()
    };
    let minus_one = F::ORDER_U64 - 1;
    let mut bitmaps = vec![
        [0; 8],
        [1; 8],
        [1, 1, 0, 0, 0, 0, 0, 0],
        [2, 0, 0, 0, 0, 0, 0, 0],
        [minus_one, 0, 0, 0, 0, 0, 0, 0],
        [2, minus_one, 0, 0, 0, 0, 0, 0],
        [1, minus_one, 0, 0, 0, 0, 0, 0],
        [0, 3, 0, 5, 0, minus_one, 0, 7],
    ];
    bitmaps.extend((0..8).map(|slot| core::array::from_fn(|index| u64::from(index == slot))));
    assert_eq!(bitmaps.len(), 16);
    for bitmap in bitmaps {
        let mut row = vec![S::zero(); 65];
        let cols: &mut Columns = row.as_mut_slice().borrow_mut();
        cols.is_commit.result = S::one();
        cols.index_bitmap = bitmap.map(S::from_canonical_u64);
        cols.expected_public_values_digest = core::array::from_fn(|byte| {
            cols.index_bitmap
                .iter()
                .zip(public.committed_value_digest)
                .map(|(coefficient, word)| {
                    *coefficient * S::from_canonical_u8(word.to_le_bytes()[byte])
                })
                .sum::<S>()
        });
        assert_eq!(cols.is_real, S::zero());
        // These are open-bus row/public checks. Byte-provider acceptance remains separate;
        // arbitrary field weights can produce non-byte values, whose emitted range queries match.
        assert!(compare(&row, &public, "inactive weighted commit"));
        let mut previous = public;
        previous.prev_committed_value_digest = [0; 8];
        assert!(compare(&row, &previous, "previous digest is not selected"));
        let mut missing_flag = public;
        missing_flag.commit_syscall = 0;
        assert!(!compare(
            &row,
            &missing_flag,
            "inactive commit still requires its flag"
        ));
        for slot in 0..8 {
            for byte in 0..4 {
                let mut changed = public;
                changed.committed_value_digest[slot] ^= 1 << (8 * byte);
                assert_eq!(
                    compare(&row, &changed, "weighted public-cell mutation"),
                    bitmap[slot] == 0
                );
            }
        }
        for byte in 0..4 {
            for delta in [1, minus_one] {
                let mut changed = row.clone();
                let cols: &mut Columns = changed.as_mut_slice().borrow_mut();
                cols.expected_public_values_digest[byte] += S::from_canonical_u64(delta);
                assert!(!compare(&changed, &public, "wrong cached weighted result"));
            }
        }
    }
}

#[test]
fn installed_host_call_preserves_the_instruction_and_authenticates_write_length() {
    assert_eq!(Core::WIDTHS, &[71]);
    assert_eq!(<Core as Program<F>>::PROVER_INPUTS, 65);
    assert_eq!(Host::WIDTHS, &[85]);
    assert_eq!(<Host as Program<F>>::PROVER_INPUTS, 71);
    for case in samples() {
        let record = ExecutionRecord {
            syscall_events: vec![case],
            ..Default::default()
        };
        let trace = SyscallInstrsChip::<SupervisorMode>::default()
            .generate_trace(&record, &mut ExecutionRecord::default());
        let sp1 = trace.row_slice(0);
        let cols: &Columns = (*sp1).borrow();
        let core = witness::<Core>(&sp1);
        assert_eq!(&core[..65], native(&sp1));
        let in_profile = codes().contains(&case.0.syscall_code);
        assert_eq!(valid::<Core>(&core), in_profile);
        assert_eq!(ledger::<Core>(&core), ledger::<Base>(&native(&sp1)));
        for length in [0, 1, 65536, u64::MAX] {
            let mut input = sp1.to_vec();
            let mut extra = [S::zero(); 6];
            let access: &mut RegisterAccessCols<S> = extra.as_mut_slice().borrow_mut();
            access.populate(read(length, case.0.clk + 1, case.0.clk - 1), &mut vec![]);
            let access = *access;
            input.extend(extra);
            let host = witness::<Host>(&input);
            assert_eq!(&host[..71], native(&input));
            assert_eq!(&host[71..77], &core[65..]);
            assert_eq!(valid::<Host>(&host), in_profile);
            let flag = S::from_bool(case.0.syscall_code == SyscallCode::WRITE);
            let mut extra_air = evaluation(&sp1, &public_for(&case.0));
            extra_air.eval_register_access_read(
                cols.state.clk_high,
                S::from_canonical_u64(case.0.clk & 0xff_ffff) + S::one(),
                [S::from_canonical_u32(12), S::zero(), S::zero()],
                access,
                flag,
            );
            assert!(extra_air.constraints.iter().all(|x| *x == S::zero()));
            let mut expected = ledger::<Core>(&core);
            expected.extend(extra_air.ledger);
            let mut message = vec![
                cols.state.clk_high.as_canonical_u64(),
                case.0.clk & 0xff_ffff,
            ];
            for word in [
                cols.adapter.prev_a(),
                cols.adapter.b(),
                cols.adapter.c(),
                &cols.op_a_value,
            ] {
                message.extend(word.0.iter().map(Sp1PrimeField64::as_canonical_u64));
            }
            message.extend(
                access
                    .prev_value
                    .0
                    .iter()
                    .map(|x| (*x * flag).as_canonical_u64()),
            );
            expected.push(("sp1.native.host_call".to_owned(), 1, message));
            let mut actual = ledger::<Host>(&host);
            expected.sort();
            actual.sort();
            assert_eq!(
                actual, expected,
                "host handoff and all extra read occurrences"
            );
        }
    }
}

#[test]
fn full_register_aliases_are_rejected_by_the_composed_profile() {
    for code in codes() {
        for limb in 1..4 {
            let alias = code as u64 + (1 << (16 * limb));
            let result = match code {
                SyscallCode::ENTER_UNCONSTRAINED => 0,
                SyscallCode::HINT_LEN => 9,
                _ => alias,
            };
            let mut case = event(code, 0, 0, result, 1, 65536);
            match &mut case.1.a {
                MemoryRecordEnum::Write(write) => write.prev_value = alias,
                _ => unreachable!(),
            }
            let record = ExecutionRecord {
                syscall_events: vec![case],
                ..Default::default()
            };
            let trace = SyscallInstrsChip::<SupervisorMode>::default()
                .generate_trace(&record, &mut ExecutionRecord::default());
            let row = trace.row_slice(0);
            assert!(compare(&row, &public_for(&case.0), "upper-register alias"));
            assert!(!valid::<Core>(&witness::<Core>(&row)));
            let mut input = row.to_vec();
            input.extend([S::zero(); 6]);
            assert!(!valid::<Host>(&witness::<Host>(&input)));
        }
    }
}

#[test]
fn generated_padding_and_private_inputs_do_not_claim_closed_execution() {
    let zero = vec![S::zero(); 65];
    let core = witness::<Core>(&zero);
    let host = witness::<Host>(&vec![S::zero(); 71]);
    assert!(valid::<Core>(&core) && valid::<Host>(&host));
    assert!(ledger::<Core>(&core).iter().all(|entry| entry.1 == 0));
    assert!(ledger::<Host>(&host).iter().all(|entry| entry.1 == 0));
    assert_eq!(ledger::<Host>(&host).len(), ledger::<Core>(&core).len() + 5);
    for column in 65..71 {
        for delta in [1, 65536, F::ORDER_U64 - 1] {
            let mut changed = core.clone();
            changed[column] += F::from_u64(delta);
            assert!(!valid::<Core>(&changed));
            let mut changed = host.clone();
            changed[column + 6] += F::from_u64(delta);
            assert!(!valid::<Host>(&changed));
        }
    }
    let case = event(SyscallCode::HALT, 65536, 0, 0, 1, 65536);
    let record = ExecutionRecord {
        syscall_events: vec![case],
        ..Default::default()
    };
    let trace = SyscallInstrsChip::<SupervisorMode>::default()
        .generate_trace(&record, &mut ExecutionRecord::default());
    let input = native(&trace.row_slice(0));
    assert!(matches!(
        generate::<F, Base>(&[], &input),
        Err(WitnessGenerationError::Runtime(_))
    ));
    assert!(matches!(
        generate::<F, Core>(&[], &input),
        Err(WitnessGenerationError::Runtime(_))
    ));
    let mut host_input = input.clone();
    host_input.extend([F::ZERO; 6]);
    assert!(matches!(
        generate::<F, Host>(&[], &host_input),
        Err(WitnessGenerationError::Runtime(_))
    ));
    assert!(matches!(
        generate::<F, RowWitness<Host>>(&[], &input),
        Err(WitnessGenerationError::ProverInputWidth { .. })
    ));
}

#[test]
fn repeated_commits_use_the_released_shard_public_values() {
    // The executor permits overwrites, but the shard AIR compares both events against the final
    // bank. Do not confuse execution effects, per-row bindings and a valid whole-shard trace.
    for code in [SyscallCode::COMMIT, SyscallCode::COMMIT_DEFERRED_PROOFS] {
        for slot in 0..8 {
            for final_value in [65537, 131075] {
                let mut instructions = vec![];
                execution::syscall(&mut instructions, code, slot, 65537);
                execution::syscall(&mut instructions, code, slot, final_value);
                execution::syscall(&mut instructions, SyscallCode::HALT, 0, 0);
                let program = sp1_core_executor::Program::new(instructions, 65536, 65536);
                let (executor, records) = execution::run(program, &[]);
                assert_eq!(executor.exit_code(), 0);
                assert_eq!(records.len(), 1);
                let record = &records[0];
                assert_eq!(record.syscall_events.len(), 3);
                let public = &record.public_values;
                let bank = if code == SyscallCode::COMMIT {
                    &public.committed_value_digest
                } else {
                    &public.deferred_proofs_digest
                };
                for (index, value) in bank.iter().enumerate() {
                    assert_eq!(
                        *value,
                        if index == slot as usize {
                            final_value as u32
                        } else {
                            0
                        }
                    );
                }
                let trace = SyscallInstrsChip::<SupervisorMode>::default()
                    .generate_trace(record, &mut ExecutionRecord::default());
                for (index, row) in trace.values.chunks(trace.width()).enumerate() {
                    let accepted = compare(row, public, "released repeated-commit shard");
                    assert_eq!(accepted, index != 0 || final_value == 65537);
                }
            }
        }
    }
}
