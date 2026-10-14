//! Compare the prototype with released preprocessing/AIR and the installed provider layout.

extern crate alloc;

#[path = "support/backend.rs"]
mod backend;
#[path = "support/export.rs"]
mod export_support;

use backend::{assert_backend_rejection, config, physical_reference};
use clean_backend::witness_generation::{generate, Program, WitnessGenerationError};
use clean_backend::{
    prove_ensemble, verify_ensemble, EnsembleShapeError, GeneratedAirSpec, GeneratedEnsemble,
};
use export_support::{NativeEvaluation, RowWitness, Sp1Evaluation};
use p3_field::{PrimeCharacteristicRing, PrimeField64};
use p3_koala_bear::KoalaBear as F;
use serde_json::{json, Value};
use slop_air::Air;
use slop_algebra::{AbstractField, PrimeField64 as Sp1PrimeField64};
use slop_matrix::Matrix;
use sp1_core_executor::Program as Sp1Program;
use sp1_core_machine::{bytes::ByteChip, range::RangeChip};
use sp1_hypercube::air::{MachineAir, SP1_PROOF_NUM_PV_ELTS};
use sp1_primitives::SP1Field;
use std::time::Instant;

macro_rules! generated {
    ($module:ident, $file:expr) => {
        #[allow(dead_code, unused_imports, unused_variables, unused_parens)]
        mod $module {
            include!(concat!(env!("CLEAN_ENSEMBLE_EXPORT_DIR"), "/", $file));
        }
    };
}
generated!(row, "unified_byte_row.rs");
generated!(empty, "unified_byte_0.rs");
generated!(single, "unified_byte_1.rs");
generated!(mixed, "unified_byte_7.rs");
generated!(repeated, "unified_byte_9.rs");
generated!(widths, "unified_byte_17.rs");
generated!(batch64, "unified_byte_64.rs");
generated!(batch65, "unified_byte_65.rs");
generated!(add, "add_instruction.rs");
generated!(beq, "branch_instruction.rs");
generated!(load, "load_byte_instruction.rs");

type Row = row::UnifiedByteRow;
type RowAir = row::UnifiedByteRowAirSpec;

fn reference() -> Value {
    serde_json::from_str(include_str!(concat!(
        env!("CLEAN_ENSEMBLE_EXPORT_DIR"),
        "/unified_byte.reference.json"
    )))
    .unwrap()
}

fn fields(value: &Value) -> Vec<F> {
    value
        .as_array()
        .unwrap()
        .iter()
        .map(|v| F::from_u64(v.as_u64().unwrap()))
        .collect()
}

fn valid<S: GeneratedAirSpec>(component: usize, row: &[F]) -> bool {
    S::constraints::<NativeEvaluation>(component, &[], row)
        .iter()
        .all(|v| *v == F::ZERO)
}

fn complete(input: &[u64; 5]) -> Vec<F> {
    generate::<F, RowWitness<Row>>(&[], &input.map(F::from_u64))
        .unwrap()
        .tables
        .pop()
        .unwrap()
        .pop()
        .unwrap()
}

fn compare_sp1(expected: &Sp1Evaluation) {
    assert!(
        expected.constraints.is_empty(),
        "SP1 authenticates the fixed rows"
    );
    for (channel, count, message) in &expected.ledger {
        assert_eq!(channel, "SP1Byte");
        assert_eq!(message.len(), 4);
        let input = [message[0], message[1], message[2], message[3], *count];
        let row = complete(&input);
        assert!(valid::<RowAir>(0, &row), "released member {input:?}");
        assert_eq!(row.len(), 68);
        let ledger = Row::interactions(0, &row);
        assert_eq!(ledger.len(), 1, "zero-count occurrences are retained");
        assert!(!ledger[0].assume_guarantees);
        assert_eq!(ledger[0].multiplicity.as_canonical_u64(), *count);
        assert_eq!(
            ledger[0]
                .message
                .iter()
                .map(PrimeField64::as_canonical_u64)
                .collect::<Vec<_>>(),
            *message
        );
    }
}

fn evaluation(preprocessed: &[SP1Field], counts: &[u64]) -> Sp1Evaluation {
    Sp1Evaluation {
        row: counts
            .iter()
            .copied()
            .map(SP1Field::from_canonical_u64)
            .collect(),
        preprocessed: preprocessed.to_vec(),
        constraints: vec![],
        ledger: vec![],
        public: vec![SP1Field::zero(); SP1_PROOF_NUM_PV_ELTS],
    }
}

#[test]
fn every_released_byte_pair_matches_at_all_count_classes() {
    assert_eq!(F::ORDER_U64, <SP1Field as Sp1PrimeField64>::ORDER_U64);
    let chip = ByteChip::<SP1Field>::default();
    let trace = chip
        .generate_preprocessed_trace(&Sp1Program::default())
        .unwrap();
    assert_eq!((trace.height(), trace.width()), (65536, 7));
    let counts = [0, 1, 2, F::ORDER_U64 - 1];
    for row in trace.values.chunks(trace.width()) {
        for round in 0..4 {
            let mut expected = evaluation(
                row,
                &(0..6)
                    .map(|op| counts[(round + op) % 4])
                    .collect::<Vec<_>>(),
            );
            chip.eval(&mut expected);
            assert_eq!(expected.ledger.len(), 6);
            compare_sp1(&expected);
        }
    }
}

#[test]
fn every_released_range_row_matches_including_duplicate_padding() {
    let chip = RangeChip::<SP1Field>::default();
    let trace = chip
        .generate_preprocessed_trace(&Sp1Program::default())
        .unwrap();
    assert_eq!((trace.height(), trace.width()), (131072, 2));
    let mut zero_width_rows = 0;
    for row in trace.values.chunks(trace.width()) {
        zero_width_rows += usize::from(row[1] == SP1Field::zero());
        for count in [0, 1, 2, F::ORDER_U64 - 1] {
            let mut expected = evaluation(row, &[count]);
            chip.eval(&mut expected);
            assert_eq!(expected.ledger.len(), 1);
            compare_sp1(&expected);
        }
    }
    assert_eq!(
        zero_width_rows, 2,
        "keep SP1's duplicate (0,0) preprocessing row"
    );
}

#[test]
fn malformed_rows_and_every_witness_column_are_rejected_even_at_zero_count() {
    let mut good = vec![
        [0, 128, 128, 255, 0],
        [1, 255, 128, 127, 0],
        [2, 255, 128, 127, 0],
        [3, 0, 255, 0, 0],
        [4, 1, 127, 128, 0],
        [5, 1, 128, 0, 0],
    ];
    for width in 0..=16 {
        for value in [0, (1 << width) - 1] {
            good.push([6, value, width, 0, 0]);
        }
    }
    for mut input in good {
        for count in [0, 1, 2, F::ORDER_U64 - 1] {
            input[4] = count;
            let row = complete(&input);
            assert!(valid::<RowAir>(0, &row));
            assert_eq!(
                RowAir::constraints::<NativeEvaluation>(0, &[], &row).len(),
                108
            );
            for column in 0..row.len() {
                for delta in [1, 256, F::ORDER_U64 - 1] {
                    let mut changed = row.clone();
                    changed[column] += F::from_u64(delta);
                    assert_eq!(
                        valid::<RowAir>(0, &changed),
                        column == 4,
                        "input {input:?}, column {column}, delta {delta}"
                    );
                }
            }
            for selectors in [[F::ZERO; 7], [F::ONE; 7], [F::from_u64(2); 7]] {
                let mut changed = row.clone();
                changed[5..12].copy_from_slice(&selectors);
                assert!(!valid::<RowAir>(0, &changed));
            }
        }
    }
    let bad = [
        [7, 0, 0, 0],
        [F::ORDER_U64 - 1, 0, 0, 0],
        [0, 0, 256, 0],
        [1, 0, 0, 256],
        [2, 1, 0, 0],
        [3, 1, 0, 0],
        [4, 2, 0, 1],
        [4, 0, 0, 1],
        [5, 0, 128, 0],
        [5, 0, 0, 1],
        [6, 0, 17, 0],
        [6, 1, 0, 0],
        [6, 65536, 16, 0],
        [6, 0, 16, 1],
        [6, 0, F::ORDER_U64 - 1, 0],
    ];
    for key in bad {
        for count in [0, 1, 2, F::ORDER_U64 - 1] {
            assert!(!valid::<RowAir>(
                0,
                &complete(&[key[0], key[1], key[2], key[3], count])
            ));
        }
    }
    assert!(matches!(
        generate::<F, RowWitness<Row>>(&[], &[]),
        Err(WitnessGenerationError::ProverInputWidth { .. })
    ));
}

fn check_closed<P: Program<F>, S: GeneratedAirSpec>(case: &Value) {
    let public = fields(&case["publicInput"]);
    let expected = case["accepted"].as_bool().unwrap();
    match generate::<F, P>(&public, &[]) {
        Err(_) => assert!(!expected),
        Ok(witness) => {
            let valid = witness
                .tables
                .iter()
                .enumerate()
                .all(|(i, rows)| rows.iter().all(|row| valid::<S>(i, row)));
            assert_eq!(valid, expected, "{}", case["name"]);
            assert_eq!(
                physical_reference::<P>(&public, &witness.tables),
                case["witness"]
            );
            if expected {
                let requests = public.chunks(4).collect::<Vec<_>>();
                for row in &witness.tables[0] {
                    let key = &row[..4];
                    let count = requests.iter().filter(|request| **request == key).count();
                    if row[4] != F::ZERO {
                        assert_eq!(row[4].as_canonical_u64(), count as u64);
                    } else {
                        assert!(row.iter().take(5).all(|v| *v == F::ZERO));
                    }
                }
                let statement = GeneratedEnsemble::<F, S>::new(&[witness.tables[0].len()]).unwrap();
                assert_eq!(
                    statement.interaction_count(),
                    (requests.len() + witness.tables[0].len()) as u128
                );
            }
        }
    }
}

#[test]
fn closed_rows_and_complete_ledgers_match_lean() {
    for case in reference()["cases"].as_array().unwrap() {
        match case["publicInput"].as_array().unwrap().len() / 4 {
            0 => check_closed::<empty::UnifiedByte, empty::UnifiedByteAirSpec>(case),
            1 => check_closed::<single::UnifiedByte, single::UnifiedByteAirSpec>(case),
            7 => check_closed::<mixed::UnifiedByte, mixed::UnifiedByteAirSpec>(case),
            9 => check_closed::<repeated::UnifiedByte, repeated::UnifiedByteAirSpec>(case),
            17 => check_closed::<widths::UnifiedByte, widths::UnifiedByteAirSpec>(case),
            64 => check_closed::<batch64::UnifiedByte, batch64::UnifiedByteAirSpec>(case),
            65 => check_closed::<batch65::UnifiedByte, batch65::UnifiedByteAirSpec>(case),
            size => panic!("unhandled request count {size}"),
        }
    }
}

#[test]
fn backend_binds_public_requests_counts_selectors_and_padding() {
    let reference = reference();
    let public = fields(&reference["cases"][1]["publicInput"]);
    let witness = mixed::generate(&public, &[]).unwrap();
    let statement = mixed::UnifiedByteStatement::<F>::new(&[8]).unwrap();
    assert_eq!(statement.interaction_count(), 15);
    let traces = witness.into_traces().unwrap();
    let config = config();
    let (proof, _) = prove_ensemble(&config, &statement, traces.clone(), &public).unwrap();
    verify_ensemble(&config, &statement, &proof, &public).unwrap();
    for column in [0, 1, 2, 3, 24, 25, 26, 27] {
        let mut wrong = public.clone();
        wrong[column] += F::ONE;
        assert!(verify_ensemble(&config, &statement, &proof, &wrong).is_err());
    }
    for cell in [4, 5, 11, 52, 67, 7 * 68 + 1, 7 * 68 + 4] {
        let mut wrong = traces.clone();
        wrong[0].values[cell] += F::ONE;
        assert_backend_rejection(|| {
            let (proof, _) = prove_ensemble(&config, &statement, wrong, &public).unwrap();
            verify_ensemble(&config, &statement, &proof, &public).is_err()
        });
    }
    assert!(matches!(
        mixed::UnifiedByteStatement::<F>::new(&[3]),
        Err(EnsembleShapeError::TraceHeight { .. })
    ));
    assert!(matches!(
        mixed::UnifiedByteStatement::<F>::new(&[1usize << 31]),
        Err(EnsembleShapeError::InteractionCountBound { .. })
    ));
    assert!(matches!(
        mixed::generate::<F>(&public[..public.len() - 1], &[]),
        Err(WitnessGenerationError::PublicInputWidth { .. })
    ));
    assert!(matches!(
        mixed::generate(&public, &[F::ZERO]),
        Err(WitnessGenerationError::ProverInputWidth { .. })
    ));
    assert!(
        generate::<F, Row>(&[], &[F::ZERO, F::ZERO, F::ZERO, F::ZERO, F::ONE]).is_err(),
        "open provider bus cannot balance"
    );
    let padded = empty::generate::<F>(&[], &[]).unwrap();
    let statement = empty::UnifiedByteStatement::<F>::new(&[1]).unwrap();
    assert_eq!(statement.interaction_count(), 1);
    let (proof, _) =
        prove_ensemble(&config, &statement, padded.into_traces().unwrap(), &[]).unwrap();
    verify_ensemble(&config, &statement, &proof, &[]).unwrap();
}

fn check_source<P: Program<F>, S: GeneratedAirSpec>(source: &Value, benchmark: &Value) {
    let input = fields(&source["input"]);
    let row = generate::<F, RowWitness<P>>(&[], &input)
        .unwrap()
        .tables
        .pop()
        .unwrap()
        .pop()
        .unwrap();
    assert!(valid::<S>(0, &row));
    assert_eq!(row, fields(&source["row"]));
    let ledger = P::interactions(0, &row);
    let actual: Vec<_> = ledger
        .iter()
        .map(|entry| {
            backend::interaction(
                entry.channel,
                entry.multiplicity.as_canonical_u64(),
                entry
                    .message
                    .iter()
                    .map(PrimeField64::as_canonical_u64)
                    .collect(),
                entry.assume_guarantees,
            )
        })
        .collect();
    assert_eq!(json!(actual), source["interactions"]);
    let requests: Vec<F> = ledger
        .into_iter()
        .filter(|entry| entry.channel == "SP1Byte" && entry.multiplicity != F::ZERO)
        .flat_map(|entry| {
            assert!(entry.assume_guarantees);
            assert_eq!(entry.multiplicity, -F::ONE);
            entry.message
        })
        .collect();
    assert_eq!(requests, fields(&benchmark["publicInput"]));
}

#[test]
fn real_instruction_workloads_match_the_exported_rust_rows() {
    let reference = reference();
    for source in reference["sources"].as_array().unwrap() {
        let benchmark = reference["benchmarks"]
            .as_array()
            .unwrap()
            .iter()
            .find(|b| b["name"] == source["name"])
            .unwrap();
        match source["name"].as_str().unwrap() {
            "add" => {
                check_source::<add::AddInstruction, add::AddInstructionAirSpec>(source, benchmark)
            }
            "beq" => check_source::<beq::BranchInstruction, beq::BranchInstructionAirSpec>(
                source, benchmark,
            ),
            "load-byte" => check_source::<
                load::LoadByteInstruction,
                load::LoadByteInstructionAirSpec,
            >(source, benchmark),
            name => panic!("unknown source {name}"),
        }
    }
}

fn measure<P: Program<F>, S: GeneratedAirSpec>(
    case: &Value,
    layout: &str,
    benchmark: bool,
) -> Value {
    let public = fields(&case["publicInput"]);
    let start = Instant::now();
    let witness = generate::<F, P>(&public, &[]).unwrap();
    let generation = start.elapsed();
    assert_eq!(
        physical_reference::<P>(&public, &witness.tables),
        case[layout]
    );
    assert!(witness
        .tables
        .iter()
        .enumerate()
        .all(|(i, rows)| rows.iter().all(|row| valid::<S>(i, row))));
    let heights = witness.tables.iter().map(Vec::len).collect::<Vec<_>>();
    let statement = GeneratedEnsemble::<F, S>::new(&heights).unwrap();
    let cells: usize = heights.iter().zip(S::WIDTHS).map(|(h, w)| h * w).sum();
    let mut result = json!({"name": case["name"], "layout": layout, "heights": heights,
        "widths": S::WIDTHS, "paddedCells": cells, "occurrences": statement.interaction_count(),
        "generationNs": generation.as_nanos() as u64});
    if benchmark {
        let config = config();
        let traces = witness.into_traces().unwrap();
        let start = Instant::now();
        let (proof, _) = prove_ensemble(&config, &statement, traces, &public).unwrap();
        result["proveNs"] = json!(start.elapsed().as_nanos() as u64);
        let start = Instant::now();
        verify_ensemble(&config, &statement, &proof, &public).unwrap();
        result["verifyNs"] = json!(start.elapsed().as_nanos() as u64);
    }
    result
}

macro_rules! comparison {
    ($module:ident, $name:literal) => {
        mod $module {
            generated!(baseline, concat!("byte_baseline_", $name, ".rs"));
            generated!(candidate, concat!("byte_candidate_", $name, ".rs"));
            pub fn run(case: &super::Value, layout: &str, benchmark: bool) -> super::Value {
                match layout {
                    "baseline" => super::measure::<
                        baseline::ByteBaseline,
                        baseline::ByteBaselineAirSpec,
                    >(case, layout, benchmark),
                    "candidate" => super::measure::<
                        candidate::UnifiedByte,
                        candidate::UnifiedByteAirSpec,
                    >(case, layout, benchmark),
                    _ => unreachable!(),
                }
            }
        }
    };
}
comparison!(bench_empty, "empty");
comparison!(bench_and, "and-only");
comparison!(bench_range, "range-heavy");
comparison!(bench_mixed, "mixed");
comparison!(bench_64, "distinct-64");
comparison!(bench_65, "distinct-65");
comparison!(bench_add, "add");
comparison!(bench_beq, "beq");
comparison!(bench_load, "load-byte");

#[test]
fn provider_layout_measurements() {
    let reference = reference();
    let selected = std::env::var("BYTE_BENCH_CASE").ok();
    let layout = std::env::var("BYTE_BENCH_LAYOUT").ok();
    for case in reference["benchmarks"].as_array().unwrap() {
        let name = case["name"].as_str().unwrap();
        if selected.as_deref().is_some_and(|selected| selected != name) {
            continue;
        }
        let run = match name {
            "empty" => bench_empty::run,
            "and-only" => bench_and::run,
            "range-heavy" => bench_range::run,
            "mixed" => bench_mixed::run,
            "distinct-64" => bench_64::run,
            "distinct-65" => bench_65::run,
            "add" => bench_add::run,
            "beq" => bench_beq::run,
            "load-byte" => bench_load::run,
            _ => panic!("unrecognized benchmark {name}"),
        };
        for kind in ["baseline", "candidate"] {
            if layout.as_deref().is_some_and(|layout| layout != kind) {
                continue;
            }
            // One warmup, followed by three sequential measured runs when requested.
            let benchmark = selected.is_some();
            let _ = run(case, kind, benchmark);
            for _ in 0..if benchmark { 3 } else { 1 } {
                println!("BYTE_MEASUREMENT {}", run(case, kind, benchmark));
            }
        }
    }
}
