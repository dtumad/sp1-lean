//! Native providers prove byte membership; SP1 authenticates a preprocessed table.
//! Compare messages with the actual released AIR without equating those physical layouts.

extern crate alloc;

#[path = "support/export.rs"]
mod export_support;

use clean_backend::witness_generation::{generate, Program, WitnessGenerationError};
use clean_backend::GeneratedAirSpec;
use export_support::{Ledger, RowWitness, Sp1Evaluation};
use p3_field::{PrimeCharacteristicRing, PrimeField64};
use p3_koala_bear::KoalaBear as F;
use slop_air::Air;
use slop_algebra::{AbstractField, PrimeField64 as Sp1PrimeField64};
use slop_matrix::Matrix;
use sp1_core_executor::{
    events::ByteLookupEvent, ByteOpcode, ExecutionRecord, Program as Sp1Program,
};
use sp1_core_machine::bytes::{ByteChip, NUM_BYTE_OPS};
use sp1_core_machine::range::RangeChip;
use sp1_hypercube::air::{MachineAir, SP1_PROOF_NUM_PV_ELTS};
use sp1_primitives::SP1Field;

macro_rules! generated_byte {
    ($module:ident, $file:literal, $program:ident) => {
        #[allow(dead_code, unused_imports, unused_variables, unused_parens)]
        mod $module {
            include!(concat!(env!("CLEAN_ENSEMBLE_EXPORT_DIR"), "/", $file));
        }
        use $module::Ensemble as $program;
    };
}
generated_byte!(and_byte, "and_byte_provider.rs", AndByteProvider);
generated_byte!(or_byte, "or_byte_provider.rs", OrByteProvider);
generated_byte!(xor_byte, "xor_byte_provider.rs", XorByteProvider);
generated_byte!(range_byte, "u8_range_byte_provider.rs", U8RangeByteProvider);
generated_byte!(ltu_byte, "ltu_byte_provider.rs", LtuByteProvider);
generated_byte!(msb_byte, "msb_byte_provider.rs", MsbByteProvider);
generated_byte!(range_0, "range_0_provider.rs", Range0Provider);
generated_byte!(range_1, "range_1_provider.rs", Range1Provider);
generated_byte!(range_2, "range_2_provider.rs", Range2Provider);
generated_byte!(range_3, "range_3_provider.rs", Range3Provider);
generated_byte!(range_4, "range_4_provider.rs", Range4Provider);
generated_byte!(range_5, "range_5_provider.rs", Range5Provider);
generated_byte!(range_6, "range_6_provider.rs", Range6Provider);
generated_byte!(range_7, "range_7_provider.rs", Range7Provider);
generated_byte!(range_8, "range_8_provider.rs", Range8Provider);
generated_byte!(range_9, "range_9_provider.rs", Range9Provider);
generated_byte!(range_10, "range_10_provider.rs", Range10Provider);
generated_byte!(range_11, "range_11_provider.rs", Range11Provider);
generated_byte!(range_12, "range_12_provider.rs", Range12Provider);
generated_byte!(range_13, "range_13_provider.rs", Range13Provider);
generated_byte!(range_14, "range_14_provider.rs", Range14Provider);
generated_byte!(range_15, "range_15_provider.rs", Range15Provider);
generated_byte!(range_16, "range_16_provider.rs", Range16Provider);

fn input<P: Program<F>>(b: u64, c: u64, multiplicity: u64) -> Vec<F> {
    match P::PROVER_INPUTS {
        2 => vec![F::from_u64(b), F::from_u64(multiplicity)],
        3 => vec![F::from_u64(b), F::from_u64(c), F::from_u64(multiplicity)],
        width => panic!("unexpected byte input width {width}"),
    }
}

fn valid<S: GeneratedAirSpec>(row: &[F]) -> bool {
    let constraints = S::constraints::<F>(0, row);
    assert!(!constraints.is_empty());
    constraints.iter().all(|value| *value == F::ZERO)
}

fn check<P: Program<F> + GeneratedAirSpec>(b: u64, c: u64, count: u64, mutate: bool) -> Ledger {
    assert_eq!(P::COMPONENTS, 1);
    assert_eq!(<P as Program<F>>::FIXED_WIDTHS, &[0]);
    let inputs = input::<P>(b, c, count);
    let witness = generate::<F, RowWitness<P>>(&[], &inputs).unwrap();
    assert_eq!(witness.tables.len(), 1);
    assert_eq!(witness.tables[0].len(), 1);
    let row = &witness.tables[0][0];
    assert_eq!(P::WIDTHS, &[row.len()]);
    assert_eq!(&row[..inputs.len()], inputs);
    assert!(valid::<P>(row));
    if mutate {
        for column in 0..row.len() {
            for delta in [1, 256, F::ORDER_U64 - 1] {
                let mut changed = row.clone();
                changed[column] += F::from_u64(delta);
                // Multiplicity is an unconstrained input; all other cells are uniquely determined.
                assert_eq!(
                    valid::<P>(&changed),
                    column == inputs.len() - 1,
                    "byte row ({b}, {c}, {count}), column {column}, delta {delta}"
                );
            }
        }
    }
    let ledger: Ledger = <P as Program<F>>::interactions(0, row)
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
        .collect();
    assert_eq!(ledger.len(), 1, "keep the zero-multiplicity occurrence");
    ledger
}

#[test]
fn all_byte_pairs_and_counts_match_released_preprocessing_and_air() {
    assert_eq!(F::ORDER_U64, <SP1Field as Sp1PrimeField64>::ORDER_U64);
    let chip = ByteChip::<SP1Field>::default();
    let trace = chip
        .generate_preprocessed_trace(&Sp1Program::default())
        .unwrap();
    assert_eq!((trace.height(), trace.width()), (65536, 7));
    assert_eq!(NUM_BYTE_OPS, 6);
    let providers: [fn(u64, u64, u64, bool) -> Ledger; 6] = [
        check::<AndByteProvider>,
        check::<OrByteProvider>,
        check::<XorByteProvider>,
        check::<U8RangeByteProvider>,
        check::<LtuByteProvider>,
        check::<MsbByteProvider>,
    ];
    let counts = [0, 1, 2, F::ORDER_U64 - 1];
    let edges = [0, 1, 127, 128, 254, 255];
    for (index, row) in trace.values.chunks(trace.width()).enumerate() {
        let b = row[0].as_canonical_u64();
        let c = row[1].as_canonical_u64();
        assert_eq!((b, c), ((index >> 8) as u64, (index & 255) as u64));
        for round in 0..counts.len() {
            let multiplicities: Vec<_> = (0..6).map(|op| counts[(round + op) % 4]).collect();
            let mut expected = Sp1Evaluation {
                row: multiplicities
                    .iter()
                    .copied()
                    .map(SP1Field::from_canonical_u64)
                    .collect(),
                preprocessed: row.to_vec(),
                constraints: vec![],
                ledger: vec![],
                public: vec![SP1Field::zero(); SP1_PROOF_NUM_PV_ELTS],
            };
            chip.eval(&mut expected);
            assert!(
                expected.constraints.is_empty(),
                "SP1 authenticates the fixed table"
            );
            assert_eq!(expected.ledger.len(), 6);
            let mut actual: Ledger = providers
                .iter()
                .enumerate()
                .flat_map(|(op, provider)| {
                    provider(
                        b,
                        c,
                        multiplicities[op],
                        edges.contains(&b) && edges.contains(&c),
                    )
                })
                .collect();
            assert_eq!(actual.len(), 6);
            // Preserve all occurrences, repeated MSB keys, zero counts and aggregate counts.
            actual.sort();
            expected.ledger.sort();
            assert_eq!(
                actual, expected.ledger,
                "byte pair ({b}, {c}), count round {round}"
            );
        }
    }
}

fn malformed<P: Program<F> + GeneratedAirSpec>(limit: u64) {
    for count in [0, 1, 2, F::ORDER_U64 - 1] {
        for operand in 0..P::PROVER_INPUTS - 1 {
            for value in [limit, limit + 1, 65536, F::ORDER_U64 - 1] {
                let mut inputs = input::<P>(0, 0, count);
                inputs[operand] = F::from_u64(value);
                let witness = generate::<F, RowWitness<P>>(&[], &inputs).unwrap();
                assert!(
                    !valid::<P>(&witness.tables[0][0]),
                    "out-of-range input must fail even at count zero"
                );
            }
        }
    }
    assert!(matches!(
        generate::<F, RowWitness<P>>(&[], &[]),
        Err(WitnessGenerationError::ProverInputWidth { .. })
    ));
}

#[test]
fn out_of_range_inputs_are_rejected_independently_of_multiplicity() {
    malformed::<AndByteProvider>(256);
    malformed::<OrByteProvider>(256);
    malformed::<XorByteProvider>(256);
    malformed::<U8RangeByteProvider>(256);
    malformed::<LtuByteProvider>(256);
    malformed::<MsbByteProvider>(256);
}

fn open_bus<P: Program<F> + GeneratedAirSpec>(b: u64, c: u64) {
    let padding = P::padding();
    assert_eq!(padding.len(), 1);
    assert_eq!(padding[0].input, input::<P>(0, 0, 0));
    let witness = generate::<F, P>(&[], &input::<P>(0, 0, 0)).unwrap();
    assert!(valid::<P>(&witness.tables[0][0]));
    for count in [1, 2, F::ORDER_U64 - 1] {
        assert!(
            matches!(
                generate::<F, P>(&[], &input::<P>(b, c, count)),
                Err(WitnessGenerationError::Runtime(_))
            ),
            "open byte bus must not balance"
        );
    }
}

#[test]
fn zero_padding_balances_but_unmatched_provider_rows_do_not() {
    open_bus::<AndByteProvider>(127, 255);
    open_bus::<OrByteProvider>(127, 255);
    open_bus::<XorByteProvider>(127, 255);
    open_bus::<U8RangeByteProvider>(127, 255);
    open_bus::<LtuByteProvider>(127, 255);
    open_bus::<MsbByteProvider>(127, 255);
}

struct RangeProvider {
    check: fn(u64, u64, u64, bool) -> Ledger,
    malformed: fn(u64),
    open_bus: fn(u64, u64),
}

const fn range_provider<P: Program<F> + GeneratedAirSpec>() -> RangeProvider {
    RangeProvider {
        check: check::<P>,
        malformed: malformed::<P>,
        open_bus: open_bus::<P>,
    }
}

const RANGE_PROVIDERS: [RangeProvider; 17] = [
    range_provider::<Range0Provider>(),
    range_provider::<Range1Provider>(),
    range_provider::<Range2Provider>(),
    range_provider::<Range3Provider>(),
    range_provider::<Range4Provider>(),
    range_provider::<Range5Provider>(),
    range_provider::<Range6Provider>(),
    range_provider::<Range7Provider>(),
    range_provider::<Range8Provider>(),
    range_provider::<Range9Provider>(),
    range_provider::<Range10Provider>(),
    range_provider::<Range11Provider>(),
    range_provider::<Range12Provider>(),
    range_provider::<Range13Provider>(),
    range_provider::<Range14Provider>(),
    range_provider::<Range15Provider>(),
    range_provider::<Range16Provider>(),
];

#[test]
fn every_range_width_value_and_count_matches_released_preprocessing_and_air() {
    assert_eq!(F::ORDER_U64, <SP1Field as Sp1PrimeField64>::ORDER_U64);
    let chip = RangeChip::<SP1Field>::default();
    let fixed = chip
        .generate_preprocessed_trace(&Sp1Program::default())
        .unwrap();
    assert_eq!((fixed.height(), fixed.width()), (131072, 2));
    let mut record = ExecutionRecord::default();
    for (index, row) in fixed.values.chunks(fixed.width()).enumerate() {
        let a = row[0].as_canonical_u64();
        let bits = row[1].as_canonical_u64();
        assert!(bits <= 16 && a < 1 << bits);
        if index == 0 {
            assert_eq!((a, bits), (0, 0));
        } else {
            assert_eq!(index as u64, (1 << bits) + a);
        }
        let edge = a == 0 || a == 1 || a == (1 << bits) - 1;
        for count in [0, 1, 2, F::ORDER_U64 - 1] {
            let mut expected = Sp1Evaluation {
                row: vec![SP1Field::from_canonical_u64(count)],
                preprocessed: row.to_vec(),
                constraints: vec![],
                ledger: vec![],
                public: vec![SP1Field::zero(); SP1_PROOF_NUM_PV_ELTS],
            };
            chip.eval(&mut expected);
            assert!(
                expected.constraints.is_empty(),
                "SP1 authenticates the fixed table"
            );
            assert_eq!(expected.ledger.len(), 1);
            assert_eq!(
                (RANGE_PROVIDERS[bits as usize].check)(a, 0, count, edge),
                expected.ledger,
                "Range row {index}, count {count}"
            );
        }
        if edge && index != 0 {
            record.byte_lookups.insert(
                ByteLookupEvent {
                    opcode: ByteOpcode::Range,
                    a: a as u16,
                    b: bits as u8,
                    c: 0,
                },
                1 + index % 3,
            );
        }
    }
    // Check the released count generator too, including the duplicate (0, 0) fixed row.
    // It routes that key to row 1, leaving row 0 unused; neither occurrence was deduplicated above.
    let counts = chip.generate_trace(&record, &mut ExecutionRecord::default());
    assert_eq!((counts.height(), counts.width()), (fixed.height(), 1));
    for (index, row) in fixed.values.chunks(fixed.width()).enumerate() {
        let event = ByteLookupEvent {
            opcode: ByteOpcode::Range,
            a: row[0].as_canonical_u64() as u16,
            b: row[1].as_canonical_u64() as u8,
            c: 0,
        };
        let expected = if index == 0 {
            0
        } else {
            *record.byte_lookups.get(&event).unwrap_or(&0)
        };
        assert_eq!(counts.values[index].as_canonical_u64(), expected as u64);
    }
}

#[test]
fn every_range_provider_rejects_overflow_even_at_zero_count() {
    for (bits, provider) in RANGE_PROVIDERS.iter().enumerate() {
        (provider.malformed)(1 << bits);
    }
}

#[test]
fn every_range_provider_accepts_zero_padding_and_rejects_unmatched_counts() {
    for provider in &RANGE_PROVIDERS {
        (provider.open_bus)(0, 0);
    }
}
