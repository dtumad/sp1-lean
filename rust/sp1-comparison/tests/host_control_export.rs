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
exported!(hint_length_empty, "host_hint_length_empty.rs");
exported!(hint_length, "host_hint_length.rs");
exported!(hint_read, "host_hint_read.rs");

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

// Independent encoding of one slot in the native weighted public-query schema.
fn public_query(base: u64, stride: u64, slot: usize, value: u64) -> Vec<F> {
    assert!(slot < 8);
    let mut result = fields(&[base, stride]);
    result.extend((0..8).map(|index| F::from_u64(u64::from(index == slot))));
    result.push(F::from_u64(value));
    result
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
                        &public_query(if deferred { 147 } else { 145 }, 0, 0, 1),
                    ));
                    if deferred {
                        expected.push(entry(
                            "SP1PublicValues",
                            F::ONE,
                            &public_query(72, 1, slot, event.arg2),
                        ));
                    } else {
                        for (byte, value) in (event.arg2 as u32).to_le_bytes().iter().enumerate() {
                            expected.push(entry(
                                "SP1PublicValues",
                                F::ONE,
                                &public_query(32 + byte as u64, 4, slot, u64::from(*value)),
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

const HINT_LENGTHS: [usize; 9] = [0, 1, 7, 8, 9, 16, 17, 65535, 65536];

fn hint_handlers() -> [Handler; 3] {
    [
        handler::<hint_length_empty::Ensemble>(),
        handler::<hint_length::Ensemble>(),
        handler::<hint_read::Ensemble>(),
    ]
}

fn address(value: u64) -> Vec<F> {
    word(value)[..3].to_vec()
}

fn hint_address(length: usize) -> u64 {
    if length % 2 == 0 {
        131072
    } else {
        131064
    }
}

fn hint_bytes(length: usize) -> Vec<u8> {
    (0..length).map(|index| (19 * index + 3) as u8).collect()
}

fn padded_words(bytes: &[u8]) -> Vec<u64> {
    let mut padded = bytes.to_vec();
    padded.resize(8 * (bytes.len() / 8 + 1), 0);
    padded
        .chunks_exact(8)
        .map(|chunk| u64::from_le_bytes(chunk.try_into().unwrap()))
        .collect()
}

fn queue_state(clk: u64, head: u64, allocated: u64) -> Vec<F> {
    [clock(clk), address(head), address(allocated)].concat()
}

fn node(pointer: u64, tail: u64, length: u64) -> Vec<F> {
    [address(pointer), address(tail), word(length)].concat()
}

fn length_input(message: &[F], previous: &[F], record: &[F]) -> Vec<F> {
    [message, previous, record].concat()
}

fn read_input(
    message: &[F],
    previous: &[F],
    record: &[F],
    start: u64,
    length: u64,
    last: u64,
) -> Vec<F> {
    let mut input = length_input(message, previous, record);
    input.extend(address(start));
    input.extend(
        word(start)[..3]
            .iter()
            .map(|x| F::from_u64(x.as_canonical_u64() / 8)),
    );
    input.extend(word(length));
    input.extend(
        word(length)[..3]
            .iter()
            .map(|x| F::from_u64(x.as_canonical_u64() / 8)),
    );
    input.extend(address(start + 8 * (length / 8)));
    input.extend(address(length / 8 + 1));
    input.extend(address(length / 8));
    input.extend(word(last));
    input
}

#[test]
fn hint_handlers_match_lean_constructor_rows_and_complete_ledgers() {
    let references: Vec<Reference> = serde_json::from_str(include_str!(concat!(
        env!("CLEAN_ENSEMBLE_EXPORT_DIR"),
        "/host_hints.reference.json"
    )))
    .unwrap();
    assert_eq!(references.len(), 1 + 2 * HINT_LENGTHS.len());
    let handlers = hint_handlers();
    for (index, reference) in references.into_iter().enumerate() {
        let (handler_index, input) = if index == 0 {
            (
                0,
                length_input(
                    &call(SyscallCode::HINT_LEN as u64, u64::MAX, 17, u64::MAX, 265),
                    &queue_state(1, 0, 0),
                    &vec![F::ZERO; 10],
                ),
            )
        } else {
            let length = HINT_LENGTHS[(index - 1) / 2];
            let previous = queue_state(1, 2, 2);
            let record = node(2, 1, length as u64);
            if index % 2 == 1 {
                (
                    1,
                    length_input(
                        &call(
                            SyscallCode::HINT_LEN as u64,
                            u64::MAX,
                            17,
                            length as u64,
                            265,
                        ),
                        &previous,
                        &record,
                    ),
                )
            } else {
                let start = hint_address(length);
                let words = padded_words(&hint_bytes(length));
                (
                    2,
                    read_input(
                        &call(
                            SyscallCode::HINT_READ as u64,
                            start,
                            length as u64,
                            SyscallCode::HINT_READ as u64,
                            265,
                        ),
                        &previous,
                        &record,
                        start,
                        length as u64,
                        *words.last().unwrap(),
                    ),
                )
            }
        };
        let handler = &handlers[handler_index];
        assert_eq!(values(&input), reference.input, "{}", reference.name);
        let row = handler.build(&input);
        assert!(handler.valid(&row));
        assert_eq!(values(&row), reference.row);
        same_ledger((handler.ledger)(&row), reference.ledger);
        assert!((handler.rejects_open)(&input));
        assert!(!handler.valid(&handler.build(&vec![F::ZERO; handler.input_width])));
    }
}

#[test]
fn hint_queue_effects_match_released_execution_and_final_padded_words() {
    let handlers = hint_handlers();
    for length in std::iter::once(None).chain(HINT_LENGTHS.map(Some)) {
        let hints = length
            .map(|length| vec![hint_bytes(length), vec![99]])
            .unwrap_or_default();
        let mut instructions = vec![];
        for _ in 0..2 {
            execution::syscall(&mut instructions, SyscallCode::HINT_LEN, u64::MAX, 17);
        }
        if let Some(length) = length {
            execution::syscall(
                &mut instructions,
                SyscallCode::HINT_READ,
                hint_address(length),
                length as u64,
            );
            execution::syscall(&mut instructions, SyscallCode::HINT_LEN, u64::MAX, 17);
            execution::syscall(&mut instructions, SyscallCode::HINT_READ, 262144, 1);
            execution::syscall(&mut instructions, SyscallCode::HINT_LEN, u64::MAX, 17);
        }
        execution::syscall(&mut instructions, SyscallCode::HALT, 0, 0);
        let mut program = Sp1Program::new(instructions, 65536, 65536);
        let starts = length
            .map(|length| vec![hint_address(length), 262144])
            .unwrap_or_default();
        for (bytes, start) in hints.iter().zip(&starts) {
            for index in 0..=padded_words(bytes).len() {
                std::sync::Arc::make_mut(&mut program.memory_image)
                    .insert(start + 8 * index as u64, u64::MAX);
            }
        }
        let (executor, records) = execution::run(program, &hints);
        assert_eq!(records.len(), 1);
        assert_eq!(
            records[0].syscall_events.len(),
            if length.is_some() { 7 } else { 3 }
        );
        let allocated = hints.len() as u64;
        let mut head = allocated;
        let mut previous = queue_state(0, head, allocated);
        let mut remaining = std::collections::VecDeque::from(hints.clone());
        for (event, access) in &records[0].syscall_events[..records[0].syscall_events.len() - 1] {
            let result = match access.a {
                MemoryRecordEnum::Write(write) => write.value,
                _ => panic!("missing hint syscall result"),
            };
            let message = call(
                event.syscall_code as u64,
                event.arg1,
                event.arg2,
                result,
                event.clk,
            );
            let record = remaining
                .front()
                .map(|bytes| node(head, head - 1, bytes.len() as u64))
                .unwrap_or_else(|| vec![F::ZERO; 10]);
            let mut expected = vec![
                entry("sp1.native.host_call", -F::ONE, &message),
                entry("sp1.native.hint_queue_state", -F::ONE, &previous),
            ];
            let (handler_index, input) = if event.syscall_code == SyscallCode::HINT_LEN {
                assert_eq!(
                    result,
                    remaining
                        .front()
                        .map(|bytes| bytes.len() as u64)
                        .unwrap_or(u64::MAX)
                );
                if head != 0 {
                    expected.push(entry("sp1.native.hint_node", -F::ONE, &record));
                }
                (
                    usize::from(head != 0),
                    length_input(&message, &previous, &record),
                )
            } else {
                assert_eq!(event.syscall_code, SyscallCode::HINT_READ);
                assert_eq!(result, SyscallCode::HINT_READ as u64);
                let bytes = remaining.pop_front().unwrap();
                assert_eq!(event.arg2, bytes.len() as u64);
                let words = padded_words(&bytes);
                for (index, word) in words.iter().enumerate() {
                    assert_eq!(
                        executor
                            .get_memory_value(event.arg1 + 8 * index as u64)
                            .value,
                        *word
                    );
                }
                assert_eq!(
                    executor
                        .get_memory_value(event.arg1 + 8 * words.len() as u64)
                        .value,
                    u64::MAX
                );
                let last_index = words.len() as u64 - 1;
                let last_address = event.arg1 + 8 * last_index;
                let last_value = executor.get_memory_value(last_address).value;
                let input = read_input(
                    &message, &previous, &record, event.arg1, event.arg2, last_value,
                );
                expected.push(entry("sp1.native.hint_node", -F::ONE, &record));
                expected.push(entry(
                    "sp1.native.hint_word",
                    -F::ONE,
                    &[
                        address(head),
                        address(last_index),
                        word(last_value),
                        vec![F::ONE],
                    ]
                    .concat(),
                ));
                expected.push(entry(
                    "sp1.native.hint_read_state",
                    F::ONE,
                    &[
                        clock(event.clk),
                        address(head),
                        address(0),
                        address(event.arg1),
                    ]
                    .concat(),
                ));
                expected.push(entry(
                    "sp1.native.hint_read_state",
                    -F::ONE,
                    &[
                        clock(event.clk),
                        address(head),
                        address(words.len() as u64),
                        address(last_address),
                    ]
                    .concat(),
                ));
                head -= 1;
                (2, input)
            };
            let next = queue_state(event.clk, head, allocated);
            expected.push(entry("sp1.native.hint_queue_state", F::ONE, &next));
            let handler = &handlers[handler_index];
            let row = handler.build(&input);
            assert!(handler.valid(&row));
            same_ledger(nonbyte((handler.ledger)(&row)), expected);
            previous = next;
        }
        assert!(remaining.is_empty());
        assert_eq!(head, 0);
    }
}

#[test]
fn malformed_hint_calls_clocks_and_spans_are_rejected() {
    let handlers = hint_handlers();
    let message = call(
        SyscallCode::HINT_READ as u64,
        131072,
        9,
        SyscallCode::HINT_READ as u64,
        265,
    );
    let previous = queue_state(1, 2, 2);
    let record = node(2, 1, 9);
    let input = read_input(&message, &previous, &record, 131072, 9, 155);
    let length = length_input(
        &call(SyscallCode::HINT_LEN as u64, u64::MAX, 17, 9, 265),
        &previous,
        &record,
    );
    let empty = length_input(
        &call(SyscallCode::HINT_LEN as u64, 0, 0, u64::MAX, 265),
        &queue_state(1, 0, 2),
        &vec![F::ZERO; 10],
    );
    for (handler, input) in handlers.iter().zip([empty, length, input.clone()]) {
        assert!(handler.valid(&handler.build(&input)));
        for column in [2, 4, 14, 18] {
            let mut changed = input.clone();
            changed[column] += F::ONE;
            assert!(!handler.valid(&handler.build(&changed)));
        }
        let mut equal_clock = input.clone();
        equal_clock[22..24].copy_from_slice(&input[..2]);
        assert!(!handler.valid(&handler.build(&equal_clock)));
        let mut wrong_head = input.clone();
        wrong_head[24] += F::ONE;
        assert!(!handler.valid(&handler.build(&wrong_head)));
    }
    for column in [6, 10, 40, 43, 46, 50, 53, 56, 59] {
        let mut changed = input.clone();
        changed[column] += F::ONE;
        assert!(
            !handlers[2].valid(&handlers[2].build(&changed)),
            "column {column}"
        );
    }
    for (start, length) in [
        (65528, 9),
        (131073, 9),
        ((1 << 48) - 8, 8),
        (131072, 1 << 48),
    ] {
        let message = call(
            SyscallCode::HINT_READ as u64,
            start,
            length,
            SyscallCode::HINT_READ as u64,
            265,
        );
        let changed = read_input(&message, &previous, &node(2, 1, length), start, length, 0);
        assert!(!handlers[2].valid(&handlers[2].build(&changed)));
    }
    // The handler requests an authenticated final word. Its local assertions alone do not bind
    // that word to source bytes; preserve this boundary instead of treating an open bus as proof.
    let mut changed = input.clone();
    changed[62] += F::ONE;
    assert_ne!(
        nonbyte((handlers[2].ledger)(&handlers[2].build(&changed))),
        nonbyte((handlers[2].ledger)(&handlers[2].build(&input)))
    );
    assert!((handlers[2].rejects_open)(&changed));
}
