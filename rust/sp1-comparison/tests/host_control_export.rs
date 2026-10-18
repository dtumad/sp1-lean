//! Native control/commit effects versus released execution, with independent Byte membership.
//! These components use per-call receipts; shard-public AIR equivalence is tested separately.

extern crate alloc;

#[path = "support/execution.rs"]
mod execution;
#[path = "support/export.rs"]
mod export_support;

use clean_backend::witness_generation::{generate, Program, WitnessGenerationError};
use clean_backend::GeneratedAirSpec;
use export_support::{Ledger, RowWitness, Sp1Evaluation};
use p3_field::{PrimeCharacteristicRing, PrimeField64};
use p3_koala_bear::KoalaBear as F;
use serde::Deserialize;
use slop_air::Air;
use slop_algebra::{AbstractField, PrimeField64 as Sp1PrimeField64};
use slop_matrix::Matrix;
use sp1_core_executor::{
    events::MemoryRecordEnum, Instruction, Opcode, Program as Sp1Program, SyscallCode,
};
use sp1_core_machine::{bytes::ByteChip, operations::LtOperationUnsigned, range::RangeChip};
use sp1_hypercube::air::{MachineAir, SP1_PROOF_NUM_PV_ELTS};
use sp1_primitives::SP1Field as S;
use std::{collections::HashSet, sync::OnceLock};

macro_rules! exported {
    ($module:ident, $file:literal) => {
        #[allow(dead_code, unused_imports, unused_variables, unused_parens)]
        mod $module {
            include!(concat!(env!("CLEAN_ENSEMBLE_EXPORT_DIR"), "/", $file));
        }
    };
}
exported!(halt, "host_halt.rs");
exported!(enter, "host_enter.rs");
exported!(commit_0, "host_commit_0.rs");
exported!(commit_1, "host_commit_1.rs");
exported!(commit_2, "host_commit_2.rs");
exported!(commit_3, "host_commit_3.rs");
exported!(commit_4, "host_commit_4.rs");
exported!(commit_5, "host_commit_5.rs");
exported!(commit_6, "host_commit_6.rs");
exported!(commit_7, "host_commit_7.rs");
exported!(deferred_0, "host_deferred_0.rs");
exported!(deferred_1, "host_deferred_1.rs");
exported!(deferred_2, "host_deferred_2.rs");
exported!(deferred_3, "host_deferred_3.rs");
exported!(deferred_4, "host_deferred_4.rs");
exported!(deferred_5, "host_deferred_5.rs");
exported!(deferred_6, "host_deferred_6.rs");
exported!(deferred_7, "host_deferred_7.rs");
exported!(commit_terminal, "host_commit_terminal.rs");
exported!(deferred_terminal, "host_deferred_terminal.rs");

struct Handler {
    input_width: usize,
    width: usize,
    row: fn(&[F]) -> Vec<F>,
    constraints_hold: fn(&[F]) -> bool,
    ledger: fn(&[F]) -> Ledger,
    rejects_open: fn(&[F]) -> bool,
}

fn handler<P: Program<F> + GeneratedAirSpec>() -> Handler {
    assert_eq!(<P as Program<F>>::COMPONENTS, 1);
    Handler {
        input_width: <P as Program<F>>::PROVER_INPUTS,
        width: P::WIDTHS[0],
        row: |input| {
            let witness = generate::<F, RowWitness<P>>(&[], input).unwrap();
            assert_eq!(witness.tables.len(), 1);
            assert_eq!(witness.tables[0].len(), 1);
            witness.tables[0][0].clone()
        },
        constraints_hold: |row| P::constraints::<F>(0, row).iter().all(|x| *x == F::ZERO),
        ledger: |row| {
            <P as Program<F>>::interactions(0, row)
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
        },
        rejects_open: |input| {
            matches!(
                generate::<F, P>(&[], input),
                Err(WitnessGenerationError::Runtime(_))
            )
        },
    }
}

fn handlers() -> Vec<Handler> {
    vec![
        handler::<halt::Ensemble>(),
        handler::<enter::Ensemble>(),
        handler::<commit_0::Ensemble>(),
        handler::<commit_1::Ensemble>(),
        handler::<commit_2::Ensemble>(),
        handler::<commit_3::Ensemble>(),
        handler::<commit_4::Ensemble>(),
        handler::<commit_5::Ensemble>(),
        handler::<commit_6::Ensemble>(),
        handler::<commit_7::Ensemble>(),
        handler::<deferred_0::Ensemble>(),
        handler::<deferred_1::Ensemble>(),
        handler::<deferred_2::Ensemble>(),
        handler::<deferred_3::Ensemble>(),
        handler::<deferred_4::Ensemble>(),
        handler::<deferred_5::Ensemble>(),
        handler::<deferred_6::Ensemble>(),
        handler::<deferred_7::Ensemble>(),
        handler::<commit_terminal::Ensemble>(),
        handler::<deferred_terminal::Ensemble>(),
    ]
}

fn source_membership<C: MachineAir<S, Program = Sp1Program> + Air<Sp1Evaluation>>(
    chip: C,
    width: usize,
) -> HashSet<Vec<u64>> {
    let fixed = chip
        .generate_preprocessed_trace(&Sp1Program::default())
        .unwrap();
    fixed
        .values
        .chunks(fixed.width())
        .flat_map(|row| {
            let mut evaluator = Sp1Evaluation {
                row: vec![S::one(); width],
                preprocessed: row.to_vec(),
                constraints: vec![],
                ledger: vec![],
                public: vec![S::zero(); SP1_PROOF_NUM_PV_ELTS],
            };
            chip.eval(&mut evaluator);
            assert!(evaluator.constraints.iter().all(|x| *x == S::zero()));
            evaluator
                .ledger
                .into_iter()
                .map(|(channel, mult, message)| {
                    assert_eq!(channel, "SP1Byte");
                    assert_eq!(mult, 1);
                    message
                })
        })
        .collect()
}

// This set is only a membership predicate. The actual ledger comparisons keep every occurrence
// and multiplicity; no physical inventory is reconstructed from the deduplicated set.
fn byte_membership() -> &'static HashSet<Vec<u64>> {
    static MEMBERS: OnceLock<HashSet<Vec<u64>>> = OnceLock::new();
    MEMBERS.get_or_init(|| {
        let mut members = source_membership(ByteChip::<S>::default(), 6);
        members.extend(source_membership(RangeChip::<S>::default(), 1));
        members
    })
}

impl Handler {
    fn valid(&self, row: &[F]) -> bool {
        assert_eq!(row.len(), self.width);
        (self.constraints_hold)(row)
            && (self.ledger)(row).iter().all(|(channel, mult, message)| {
                channel != "SP1Byte" || *mult == 0 || byte_membership().contains(message)
            })
    }
    fn build(&self, input: &[F]) -> Vec<F> {
        assert_eq!(input.len(), self.input_width);
        let row = (self.row)(input);
        assert_eq!(&row[..input.len()], input);
        row
    }
}

fn fields(values: &[u64]) -> Vec<F> {
    values.iter().map(|x| F::from_u64(*x)).collect()
}
fn values(fields: &[F]) -> Vec<u64> {
    fields.iter().map(PrimeField64::as_canonical_u64).collect()
}
fn word(value: u64) -> Vec<F> {
    fields(
        &(0..4)
            .map(|i| (value >> (16 * i)) & 65535)
            .collect::<Vec<_>>(),
    )
}
fn clock(value: u64) -> Vec<F> {
    fields(&[value >> 24, value & 0xff_ffff])
}
fn call(code: u64, arg1: u64, arg2: u64, result: u64, clk: u64) -> Vec<F> {
    let mut out = clock(clk);
    for value in [code, arg1, arg2, result, 0] {
        out.extend(word(value));
    }
    out
}
fn state(clk: u64, bank: &[u64; 8]) -> Vec<F> {
    let mut out = clock(clk);
    for value in bank {
        out.extend(word(*value));
    }
    out
}
fn comparison(value: u64, bound: u64) -> Vec<F> {
    let mut operation = LtOperationUnsigned::<S>::default();
    operation.populate_unsigned(&mut vec![], u64::from(value < bound), value, bound);
    let mut out = vec![operation.u16_compare_operation.bit];
    out.extend(operation.u16_flags);
    out.push(operation.not_eq_inv);
    out.extend(operation.comparison_limbs);
    out.iter()
        .map(|x| F::from_u64(x.as_canonical_u64()))
        .collect()
}
fn commit_input(deferred: bool, message: &[F], previous: &[F]) -> Vec<F> {
    let value = message[10..14].iter().enumerate().fold(0, |value, (i, x)| {
        value | (x.as_canonical_u64() << (16 * i))
    });
    let mut input = message.to_vec();
    input.extend(previous);
    input.extend(comparison(
        value,
        if deferred { F::ORDER_U64 } else { 1 << 32 },
    ));
    input.extend(
        message[10..14]
            .iter()
            .map(|x| F::from_u64(x.as_canonical_u64() % 256)),
    );
    input
}
fn nonbyte(ledger: Ledger) -> Ledger {
    ledger
        .into_iter()
        .filter(|entry| entry.0 != "SP1Byte")
        .collect()
}
fn entry(channel: &str, mult: F, payload: &[F]) -> (String, u64, Vec<u64>) {
    (channel.to_owned(), mult.as_canonical_u64(), values(payload))
}
fn same_ledger(mut actual: Ledger, mut expected: Ledger) {
    actual.sort();
    expected.sort();
    assert_eq!(actual, expected);
}

#[derive(Deserialize)]
struct Reference {
    name: String,
    input: Vec<u64>,
    row: Vec<u64>,
    ledger: Ledger,
}
fn references() -> Vec<Reference> {
    serde_json::from_str(include_str!(concat!(
        env!("CLEAN_ENSEMBLE_EXPORT_DIR"),
        "/host_control.reference.json"
    )))
    .unwrap()
}

#[test]
fn twenty_installed_components_match_lean_rows_and_complete_ledgers() {
    let references = references();
    assert_eq!(references.len(), 20);
    for (index, (handler, reference)) in handlers().iter().zip(references).enumerate() {
        let input = fields(&reference.input);
        let row = handler.build(&input);
        assert_eq!(values(&row), reference.row, "{}", reference.name);
        assert!(handler.valid(&row), "{}", reference.name);
        same_ledger((handler.ledger)(&row), reference.ledger);
        let expected = match index {
            0 => {
                let mut input = call(0, F::ORDER_U64 - 1, u64::MAX, 0, 265);
                input.extend(comparison(F::ORDER_U64 - 1, F::ORDER_U64));
                input
            }
            1 => call(3, u64::MAX, 0, 0, 265),
            2..=17 => {
                let deferred = index >= 10;
                let slot = (index - 2) % 8;
                let code = if deferred { 26 } else { 16 };
                commit_input(
                    deferred,
                    &call(code, slot as u64, 131075, code, 265),
                    &state(1, &core::array::from_fn(|i| 100 + i as u64)),
                )
            }
            _ => state(1, &core::array::from_fn(|i| 100 + i as u64)),
        };
        assert_eq!(
            input, expected,
            "released comparison columns and native field adapter"
        );
        assert!(
            (handler.rejects_open)(&input),
            "a row cannot close its own external buses"
        );
        let zero = handler.build(&vec![F::ZERO; handler.input_width]);
        assert_eq!(
            handler.valid(&zero),
            index >= 18,
            "terminal zero state is a real row, not inactive padding"
        );
        assert!((handler.ledger)(&zero).iter().any(|entry| entry.1 != 0));
    }
}

#[test]
fn all_commit_slots_preserve_released_executor_effects_and_literal_receipts() {
    let handlers = handlers();
    for deferred in [false, true] {
        let code = if deferred {
            SyscallCode::COMMIT_DEFERRED_PROOFS
        } else {
            SyscallCode::COMMIT
        };
        let channel = if deferred {
            "sp1.native.deferred_state"
        } else {
            "sp1.native.commit_state"
        };
        let bound = if deferred { F::ORDER_U64 } else { 1 << 32 };
        for slot in 0..8 {
            let handler = &handlers[2 + 8 * usize::from(deferred) + slot];
            for final_value in [0, 65537, bound - 1] {
                let mut instructions = vec![];
                execution::syscall(&mut instructions, code, slot as u64, 131075);
                execution::syscall(&mut instructions, code, slot as u64, final_value);
                execution::syscall(&mut instructions, SyscallCode::HALT, 0, 0);
                let (_, records) = execution::run(Sp1Program::new(instructions, 65536, 65536), &[]);
                assert_eq!(records.len(), 1);
                let record = &records[0];
                assert_eq!(record.syscall_events.len(), 3);
                let mut bank = [0u64; 8];
                let mut previous = state(0, &bank);
                for (event, access) in &record.syscall_events[..2] {
                    let result = match access.a {
                        MemoryRecordEnum::Write(write) => write.value,
                        _ => panic!("missing syscall result"),
                    };
                    let message = call(code as u64, event.arg1, event.arg2, result, event.clk);
                    let input = commit_input(deferred, &message, &previous);
                    let row = handler.build(&input);
                    assert!(handler.valid(&row));
                    bank[slot] = event.arg2;
                    let next = state(event.clk, &bank);
                    let mut expected = vec![
                        entry("sp1.native.host_call", -F::ONE, &message),
                        entry(channel, -F::ONE, &previous),
                        entry(channel, F::ONE, &next),
                    ];
                    expected.push(entry(
                        "SP1PublicValues",
                        F::ONE,
                        &fields(&[if deferred { 147 } else { 145 }, 1]),
                    ));
                    if deferred {
                        expected.push(entry(
                            "SP1PublicValues",
                            F::ONE,
                            &fields(&[72 + slot as u64, event.arg2]),
                        ));
                    } else {
                        for (byte, value) in (event.arg2 as u32).to_le_bytes().iter().enumerate() {
                            expected.push(entry(
                                "SP1PublicValues",
                                F::ONE,
                                &fields(&[32 + 4 * slot as u64 + byte as u64, u64::from(*value)]),
                            ));
                        }
                    }
                    same_ledger(nonbyte((handler.ledger)(&row)), expected);
                    let mut equal_clock = input.clone();
                    equal_clock[22..24].copy_from_slice(&message[..2]);
                    assert!(!handler.valid(&handler.build(&equal_clock)));
                    previous = next;
                }
                let public = if deferred {
                    record.public_values.deferred_proofs_digest
                } else {
                    record.public_values.committed_value_digest
                };
                assert_eq!(bank, public.map(u64::from));
                let terminal = &handlers[18 + usize::from(deferred)];
                let row = terminal.build(&previous);
                assert!(terminal.valid(&row));
                let mut final_state = fields(&[1 << 24, 0]);
                final_state.extend(bank.into_iter().flat_map(word));
                same_ledger(
                    nonbyte((terminal.ledger)(&row)),
                    vec![
                        entry(channel, -F::ONE, &previous),
                        entry(channel, F::ONE, &final_state),
                    ],
                );
            }
        }
    }
}

#[test]
fn halt_and_constrained_enter_match_released_execution() {
    let handlers = handlers();
    for exit in [0, 65535, 65536, F::ORDER_U64 - 1] {
        let mut instructions = vec![];
        execution::syscall(&mut instructions, SyscallCode::HALT, exit, u64::MAX);
        let (executor, records) = execution::run(Sp1Program::new(instructions, 65536, 65536), &[]);
        assert_eq!(u64::from(executor.exit_code()), exit);
        assert_eq!(records.len(), 1);
        let event = &records[0].syscall_events[0].0;
        let message = call(0, event.arg1, event.arg2, 0, event.clk);
        let mut input = message.clone();
        input.extend(comparison(exit, F::ORDER_U64));
        let row = handlers[0].build(&input);
        assert!(handlers[0].valid(&row));
        same_ledger(
            nonbyte((handlers[0].ledger)(&row)),
            vec![
                entry("sp1.native.host_call", -F::ONE, &message),
                entry("SP1HostExit", F::ONE, &word(exit)),
            ],
        );
    }
    let mut instructions = vec![];
    execution::syscall(
        &mut instructions,
        SyscallCode::ENTER_UNCONSTRAINED,
        u64::MAX,
        17,
    );
    // Minimal execution enters the unconstrained region; its writes roll back at EXIT. The
    // constrained trace takes the zero return and skips those instructions.
    instructions.push(Instruction::new(Opcode::BEQ, 5, 0, 16, false, true));
    execution::load_constant(&mut instructions, 9, 99);
    execution::load_constant(&mut instructions, 5, SyscallCode::EXIT_UNCONSTRAINED as u64);
    instructions.push(Instruction::new(Opcode::ECALL, 5, 10, 11, false, false));
    execution::syscall(&mut instructions, SyscallCode::HALT, 0, 0);
    let (executor, records) = execution::run(Sp1Program::new(instructions, 65536, 65536), &[]);
    assert_eq!(executor.registers()[9], 0);
    assert_eq!(records.len(), 1);
    assert_eq!(records[0].syscall_events.len(), 2);
    let (event, access) = records[0].syscall_events[0];
    let result = match access.a {
        MemoryRecordEnum::Write(write) => write.value,
        _ => panic!("missing ENTER result"),
    };
    assert_eq!(result, 0);
    let input = call(3, event.arg1, event.arg2, result, event.clk);
    let row = handlers[1].build(&input);
    assert!(handlers[1].valid(&row));
    same_ledger(
        (handlers[1].ledger)(&row),
        vec![entry("sp1.native.host_call", -F::ONE, &input)],
    );
}

#[test]
fn malformed_calls_bounds_and_terminal_clocks_are_rejected() {
    for (index, (handler, reference)) in handlers().iter().zip(references()).enumerate() {
        let input = fields(&reference.input);
        if index < 18 {
            for column in [2, 4, 14, 18] {
                let mut changed = input.clone();
                changed[column] += F::ONE;
                assert!(
                    !handler.valid(&handler.build(&changed)),
                    "handler {}, column {column}",
                    reference.name
                );
            }
        } else {
            for column in [0, 1] {
                let mut changed = input.clone();
                changed[column] = F::from_u64(1 << 24);
                assert!(!handler.valid(&handler.build(&changed)));
            }
        }
        if (2..18).contains(&index) {
            let deferred = index >= 10;
            let code = if deferred { 26 } else { 16 };
            let slot = (index - 2) % 8;
            for value in [if deferred { F::ORDER_U64 } else { 1 << 32 }, u64::MAX] {
                let input = commit_input(
                    deferred,
                    &call(code, slot as u64, value, code, 265),
                    &state(1, &[0; 8]),
                );
                assert!(!handler.valid(&handler.build(&input)));
            }
            let mut wrong_slot = input.clone();
            wrong_slot[6] += F::ONE;
            assert!(!handler.valid(&handler.build(&wrong_slot)));
        }
    }
}
