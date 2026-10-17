extern crate alloc;

#[path = "support/backend.rs"]
mod backend;

// The generic printer emits helpers unused by some component shapes.
#[allow(dead_code, unused_imports, unused_variables, unused_parens)]
mod generated {
    include!(concat!(
        env!("CLEAN_ENSEMBLE_EXPORT_DIR"),
        "/installed_assembly.rs"
    ));
}

use clean_backend::witness_generation::Program;
use clean_backend::{prove_ensemble, verify_ensemble, EnsembleShapeError, GeneratedAirSpec};
use p3_field::PrimeCharacteristicRing;
use p3_koala_bear::KoalaBear as F;
use p3_matrix::Matrix;

fn reference() -> serde_json::Value {
    serde_json::from_str(include_str!(concat!(
        env!("CLEAN_ENSEMBLE_EXPORT_DIR"),
        "/installed_assembly.reference.json"
    )))
    .unwrap()
}

fn fields(value: &serde_json::Value) -> Vec<F> {
    value
        .as_array()
        .unwrap()
        .iter()
        .map(|cell| F::from_u64(cell.as_u64().unwrap()))
        .collect()
}

#[test]
fn complete_generated_witness_matches_native_rows_and_ledger() {
    let reference = reference();
    let inventory = reference["inventory"].as_array().unwrap();
    assert_eq!(inventory.len(), 94);
    assert_eq!(<generated::Ensemble as Program<F>>::COMPONENTS, 94);
    for (index, component) in inventory.iter().enumerate() {
        assert_eq!(
            component["name"],
            <generated::Ensemble as Program<F>>::COMPONENT_NAMES[index]
        );
        assert_eq!(
            component["width"],
            <generated::Ensemble as Program<F>>::ROW_WIDTHS[index]
        );
        assert_eq!(
            component["fixedWidth"],
            <generated::Ensemble as GeneratedAirSpec>::FIXED_WIDTHS[index]
        );
        assert_eq!(
            component["fixedHeight"],
            generated::Ensemble::FIXED_HEIGHTS[index]
        );
    }
    let cases = reference["cases"].as_array().unwrap();
    assert_eq!(cases.len(), 3);
    for case in cases {
        let public = fields(&case["publicInput"]);
        let private = fields(&case["privateInput"]);
        let result = generated::generate(&public, &private);
        if let Some(expected) = case.get("witness") {
            let witness = result.unwrap();
            assert_eq!(
                backend::physical_reference::<generated::Ensemble>(&public, &witness.tables),
                *expected
            );
            let constraints = witness.tables.iter().enumerate().all(|(component, rows)| {
                rows.iter().all(|row| {
                    generated::Ensemble::constraints(component, row)
                        .into_iter()
                        .all(|v| v == F::ZERO)
                })
            });
            assert_eq!(constraints, case["accepted"].as_bool().unwrap());
            if case["name"] == "active-branch" {
                assert_eq!(
                    witness.tables[18],
                    vec![fields(&reference["compilerBranchRow"])]
                );
                assert!(witness.tables.iter().filter(|rows| rows.is_empty()).count() > 50);
                let traces = witness.into_traces().unwrap();
                assert_eq!(traces.len(), 94);
                for (index, trace) in traces.iter().enumerate() {
                    assert_eq!(trace.width(), generated::Ensemble::WIDTHS[index]);
                    let fixed_height = generated::Ensemble::FIXED_HEIGHTS[index];
                    if fixed_height != 0 {
                        assert_eq!(trace.height(), fixed_height);
                        assert_eq!(
                            backend::fixed_trace::<generated::Ensemble>(index).height(),
                            fixed_height
                        );
                    }
                }
            }
        } else {
            assert!(!case["accepted"].as_bool().unwrap());
            assert!(
                result.is_err(),
                "mutation unexpectedly generated: {}",
                case["name"]
            );
        }
    }
}

#[test]
fn complete_assembly_proves_and_binds_public_endpoints() {
    let reference = reference();
    let case = &reference["cases"][0];
    let public = fields(&case["publicInput"]);
    let private = fields(&case["privateInput"]);
    let traces = generated::generate(&public, &private)
        .unwrap()
        .into_traces()
        .unwrap();
    let heights = traces.iter().map(Matrix::height).collect::<Vec<_>>();
    let statement = generated::Statement::<F>::new(&heights).unwrap();
    assert_eq!(statement.component_count(), 94);
    assert_eq!(
        statement.interaction_count() as usize,
        case["witness"]["interactions"].as_array().unwrap().len()
    );
    let config = backend::config();
    let (proof, _) = prove_ensemble(&config, &statement, traces, &public).unwrap();
    verify_ensemble(&config, &statement, &proof, &public).unwrap();
    let wrong_public = fields(&reference["cases"][1]["publicInput"]);
    assert!(verify_ensemble(&config, &statement, &proof, &wrong_public).is_err());

    let mut missing_branch = heights.clone();
    missing_branch[18] = 0;
    let wrong_statement = generated::Statement::<F>::new(&missing_branch).unwrap();
    assert!(verify_ensemble(&config, &wrong_statement, &proof, &public).is_err());
    let fixed = generated::Ensemble::FIXED_HEIGHTS
        .iter()
        .position(|height| *height > 0)
        .unwrap();
    let mut missing_fixed = heights;
    missing_fixed[fixed] = 0;
    assert!(matches!(generated::Statement::<F>::new(&missing_fixed),
        Err(EnsembleShapeError::FixedTraceHeight { component, actual: 0, .. }) if component == fixed));
}

#[test]
fn complete_assembly_rejects_a_changed_committed_branch_row() {
    let reference = reference();
    let case = &reference["cases"][0];
    let public = fields(&case["publicInput"]);
    let private = fields(&case["privateInput"]);
    let mut traces = generated::generate(&public, &private)
        .unwrap()
        .into_traces()
        .unwrap();
    let heights = traces.iter().map(Matrix::height).collect::<Vec<_>>();
    let statement = generated::Statement::<F>::new(&heights).unwrap();
    traces[18].values[0] += F::ONE;
    let config = backend::config();
    backend::assert_backend_rejection(|| {
        let (proof, _) = prove_ensemble(&config, &statement, traces, &public).unwrap();
        verify_ensemble(&config, &statement, &proof, &public).is_err()
    });
}
