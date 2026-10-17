//! Native immutable hint sources through Clean's emitter and scheduler.
//! This checks source-queue authentication, independently of SP1's complete HINT_READ execution.

extern crate alloc;

#[path = "support/backend.rs"]
mod backend;

use backend::{assert_backend_rejection, config, fixed_trace, physical_reference};
use clean_backend::{prove_ensemble, verify_ensemble, GeneratedAirSpec};
use p3_field::PrimeCharacteristicRing;
use p3_koala_bear::KoalaBear as F;
use p3_matrix::Matrix;
use serde_json::Value;

macro_rules! generated {
    ($module:ident, $file:expr) => {
        #[allow(dead_code, unused_imports, unused_variables, unused_parens)]
        mod $module {
            include!(concat!(env!("CLEAN_ENSEMBLE_EXPORT_DIR"), "/", $file));
        }
    };
}
generated!(nodes, "hint_nodes.rs");
generated!(words, "hint_words.rs");
generated!(nodes_empty, "hint_nodes_empty.rs");
generated!(words_empty, "hint_words_empty.rs");
generated!(nodes_unused, "hint_nodes_unused.rs");
generated!(words_unused, "hint_words_unused.rs");

// Independent literal input, not the generated fixed rows or Lean's reference inventory.
const HINTS: [&[u8]; 3] = [
    &[17, 34, 51, 68, 85, 102, 119, 136, 153, 170],
    &[1, 2, 3, 4, 5, 6, 7, 8],
    &[],
];

fn limbs(value: u64, width: usize) -> Vec<F> {
    (0..width)
        .map(|index| F::from_u64((value >> (16 * index)) & 0xffff))
        .collect()
}

fn records(words: bool) -> Vec<Vec<F>> {
    HINTS
        .into_iter()
        .rev()
        .enumerate()
        .flat_map(|(node, bytes)| {
            if !words {
                return vec![[
                    limbs(node as u64 + 1, 3),
                    limbs(node as u64, 3),
                    limbs(bytes.len() as u64, 4),
                ]
                .concat()];
            }
            // Every buffer includes a final padded word, including empty and aligned buffers.
            (0..=bytes.len() / 8)
                .map(|index| {
                    let mut padded = [0_u8; 8];
                    let remaining = &bytes[index * 8..];
                    let count = remaining.len().min(8);
                    padded[..count].copy_from_slice(&remaining[..count]);
                    [
                        limbs(node as u64 + 1, 3),
                        limbs(index as u64, 3),
                        limbs(u64::from_le_bytes(padded), 4),
                        vec![F::from_bool(index == bytes.len() / 8)],
                    ]
                    .concat()
                })
                .collect()
        })
        .collect()
}

fn reference() -> Value {
    serde_json::from_str(include_str!(concat!(
        env!("CLEAN_ENSEMBLE_EXPORT_DIR"),
        "/hint_sources.reference.json"
    )))
    .unwrap()
}

fn check_fixed<P: GeneratedAirSpec>(words: bool, empty: bool) {
    let width = if words { 11 } else { 10 };
    let source = if empty { vec![] } else { records(words) };
    let fixed = fixed_trace::<P>(0);
    assert_eq!(fixed.width(), width + 1);
    assert_eq!(fixed.height(), source.len().max(1).next_power_of_two());
    for (index, row) in fixed.values.chunks(width + 1).enumerate() {
        let expected = source
            .get(index)
            .map(|record| [record.clone(), vec![F::ONE]].concat())
            .unwrap_or(vec![F::ZERO; width + 1]);
        assert_eq!(row, expected, "physical row {index}");
    }
}

#[test]
fn fixed_rows_match_literal_bytes_tail_links_lengths_and_padding() {
    check_fixed::<nodes::Ensemble>(false, false);
    check_fixed::<words::Ensemble>(true, false);
    check_fixed::<nodes_empty::Ensemble>(false, true);
    check_fixed::<words_empty::Ensemble>(true, true);
    check_fixed::<nodes_unused::Ensemble>(false, false);
    check_fixed::<words_unused::Ensemble>(true, false);
}

macro_rules! compare_cases {
    ($module:ident, $words:expr, $empty:expr) => {
        for case in reference()[stringify!($module)].as_array().unwrap() {
            let public: Vec<F> = case["publicInput"]
                .as_array()
                .unwrap()
                .iter()
                .map(|cell| F::from_u64(cell.as_u64().unwrap()))
                .collect();
            let width = if $words { 11 } else { 10 };
            assert_eq!(public.len() % width, 0);
            let allowed = if $empty { vec![] } else { records($words) };
            let expected = public
                .chunks(width)
                .all(|request| allowed.iter().any(|record| record == request));
            assert_eq!(
                expected,
                case["accepted"].as_bool().unwrap(),
                "{}",
                case["name"]
            );
            let generated = $module::generate::<F>(&public, &[]);
            assert_eq!(
                generated.is_ok(),
                case.get("witness").is_some(),
                "{}",
                case["name"]
            );
            match generated {
                Err(_) => assert!(!expected),
                Ok(witness) => {
                    assert_eq!(
                        physical_reference::<$module::Ensemble>(&public, &witness.tables),
                        case["witness"],
                        "{}",
                        case["name"]
                    );
                    // Check both sides' outcomes, including padding requests that can generate
                    // a row but must fail eligibility constraints in the actual backend.
                    let traces = witness.into_traces().unwrap();
                    let heights: Vec<usize> = traces.iter().map(Matrix::height).collect();
                    let statement = $module::Statement::<F>::new(&heights).unwrap();
                    let config = config();
                    let check = || {
                        let (proof, _) =
                            prove_ensemble(&config, &statement, traces, &public).unwrap();
                        verify_ensemble(&config, &statement, &proof, &public).is_ok()
                    };
                    if expected {
                        assert!(check());
                    } else {
                        assert_backend_rejection(|| !check());
                    }
                }
            }
        }
    };
}

#[test]
fn generation_acceptance_and_complete_ledgers_match_lean_and_source_membership() {
    compare_cases!(nodes, false, false);
    compare_cases!(words, true, false);
    compare_cases!(nodes_empty, false, true);
    compare_cases!(words_empty, true, true);
}

#[test]
fn unused_inventories_keep_every_physical_zero_count() {
    compare_cases!(nodes_unused, false, false);
    compare_cases!(words_unused, true, false);
    for (tables, width, height) in [
        (nodes_unused::generate::<F>(&[], &[]).unwrap().tables, 12, 4),
        (words_unused::generate::<F>(&[], &[]).unwrap().tables, 13, 8),
    ] {
        assert_eq!(tables.len(), 1);
        assert_eq!(tables[0].len(), height);
        assert!(tables[0]
            .iter()
            .all(|row| row.len() == width && row[width - 1] == F::ZERO));
    }
}

macro_rules! backend_mutations {
    ($module:ident, $words:expr) => {{
        let allowed = records($words);
        let request = allowed.last().unwrap();
        let public = [request.clone(), request.clone()].concat();
        let witness = $module::generate::<F>(&public, &[]).unwrap();
        let width = request.len();
        let height = allowed.len().next_power_of_two();
        assert_eq!(witness.tables[0].len(), height);
        for (index, row) in witness.tables[0].iter().enumerate() {
            assert_eq!(
                row[width + 1],
                if index == allowed.len() - 1 {
                    F::TWO
                } else {
                    F::ZERO
                }
            );
        }
        let traces = witness.into_traces().unwrap();
        // All payload and eligibility cells are verifier-fixed, leaving only counts in the trace.
        assert_eq!($module::Ensemble::FIXED_WIDTHS, &[width + 1]);
        assert_eq!((traces[0].width(), traces[0].height()), (1, height));
        let statement = $module::Statement::<F>::new(&[height]).unwrap();
        assert!($module::Statement::<F>::new(&[height / 2]).is_err());
        assert!($module::Statement::<F>::new(&[height * 2]).is_err());
        let config = config();
        let (proof, _) = prove_ensemble(&config, &statement, traces.clone(), &public).unwrap();
        verify_ensemble(&config, &statement, &proof, &public).unwrap();
        for column in 0..width {
            let mut forged = public.clone();
            forged[column] += F::ONE;
            assert!($module::generate::<F>(&forged, &[]).is_err());
            assert!(verify_ensemble(&config, &statement, &proof, &forged).is_err());
        }
        // Every count matters, including unused real rows and every ineligible padding row.
        for row in 0..height {
            let mut forged = traces.clone();
            forged[0].values[row] += F::ONE;
            assert_backend_rejection(|| {
                let (proof, _) = prove_ensemble(&config, &statement, forged, &public).unwrap();
                verify_ensemble(&config, &statement, &proof, &public).is_err()
            });
        }
    }};
}

#[test]
fn node_backend_binds_all_public_fields_counts_and_fixed_height() {
    backend_mutations!(nodes, false);
}

#[test]
fn word_backend_binds_all_public_fields_counts_and_fixed_height() {
    backend_mutations!(words, true);
}
