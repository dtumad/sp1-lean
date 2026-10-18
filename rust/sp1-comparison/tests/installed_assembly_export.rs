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

#[allow(dead_code, unused_imports, unused_variables, unused_parens)]
mod empty {
    include!(concat!(
        env!("CLEAN_ENSEMBLE_EXPORT_DIR"),
        "/installed_empty.rs"
    ));
}

use clean_backend::witness_generation::{generate, Program};
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

fn empty_reference() -> serde_json::Value {
    serde_json::from_str(include_str!(concat!(
        env!("CLEAN_ENSEMBLE_EXPORT_DIR"),
        "/installed_empty.reference.json"
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

fn check_reference<P: Program<F> + GeneratedAirSpec>(reference: &serde_json::Value, cases: usize) {
    let inventory = reference["inventory"].as_array().unwrap();
    assert_eq!(inventory.len(), 94);
    assert_eq!(P::COMPONENTS, 94);
    for (index, component) in inventory.iter().enumerate() {
        assert_eq!(component["name"], P::COMPONENT_NAMES[index]);
        assert_eq!(component["width"], P::ROW_WIDTHS[index]);
        assert_eq!(
            component["fixedWidth"],
            <P as GeneratedAirSpec>::FIXED_WIDTHS[index]
        );
        assert_eq!(component["fixedHeight"], P::FIXED_HEIGHTS[index]);
    }
    let samples = reference["cases"].as_array().unwrap();
    assert_eq!(samples.len(), cases);
    for case in samples {
        let public = fields(&case["publicInput"]);
        let private = fields(&case["privateInput"]);
        let result = generate::<F, P>(&public, &private);
        if let Some(expected) = case.get("witness") {
            let witness = result.unwrap();
            assert_eq!(
                backend::physical_reference::<P>(&public, &witness.tables),
                *expected
            );
            let constraints = witness.tables.iter().enumerate().all(|(component, rows)| {
                rows.iter().all(|row| {
                    P::constraints(component, row)
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
            }
            if case["accepted"] == true {
                assert!(witness.tables.iter().filter(|rows| rows.is_empty()).count() > 50);
                let traces = witness.into_traces().unwrap();
                assert_eq!(traces.len(), 94);
                for (index, trace) in traces.iter().enumerate() {
                    assert_eq!(trace.width(), P::WIDTHS[index]);
                    let fixed_height = P::FIXED_HEIGHTS[index];
                    if fixed_height != 0 {
                        assert_eq!(trace.height(), fixed_height);
                        assert_eq!(backend::fixed_trace::<P>(index).height(), fixed_height);
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
fn complete_generated_witness_matches_native_rows_and_ledger() {
    check_reference::<generated::Ensemble>(&reference(), 3);
}

#[test]
fn empty_generated_witness_matches_native_boundaries_and_rejects_mutations() {
    let reference = empty_reference();
    check_reference::<empty::Ensemble>(&reference, 6);
    let case = &reference["cases"][0];
    let public = fields(&case["publicInput"]);
    // The source clock/PC are literal fixture inputs, independent of exported metadata.
    assert_eq!(public[0], F::ONE);
    assert_eq!(&public[4..7], &[F::ZERO, F::ONE, F::ZERO]);
    assert_eq!(&public[..7], &public[7..14]);
    let witness = empty::generate(&public, &fields(&case["privateInput"])).unwrap();
    // The instruction range is the canonical 25-chip inventory, following six memory
    // boundary components and the Program provider. No instruction row is invented.
    assert!(witness.tables[7..32].iter().all(Vec::is_empty));
    // Program and complete source/target register providers remain physically present,
    // with their fixed rows and zero multiplicities, despite no consumer demand.
    for index in [6, 59, 92] {
        assert_eq!(
            witness.tables[index].len(),
            empty::Ensemble::FIXED_HEIGHTS[index]
        );
        assert!(!witness.tables[index].is_empty());
        assert!(witness.tables[index]
            .iter()
            .all(|row| *row.last().unwrap() == F::ZERO));
    }
}

#[test]
fn empty_assembly_proves_and_requires_every_boundary_terminal() {
    let reference = empty_reference();
    let case = &reference["cases"][0];
    let public = fields(&case["publicInput"]);
    let private = fields(&case["privateInput"]);
    let traces = empty::generate(&public, &private)
        .unwrap()
        .into_traces()
        .unwrap();
    let heights = traces.iter().map(Matrix::height).collect::<Vec<_>>();
    let statement = empty::Statement::<F>::new(&heights).unwrap();
    let config = backend::config();
    let (proof, _) = prove_ensemble(&config, &statement, traces.clone(), &public).unwrap();
    verify_ensemble(&config, &statement, &proof, &public).unwrap();
    for case in reference["cases"]
        .as_array()
        .unwrap()
        .iter()
        .skip(1)
        .take(4)
    {
        assert!(
            verify_ensemble(&config, &statement, &proof, &fields(&case["publicInput"])).is_err()
        );
    }
    // Removing any one terminal must fail actual proving/verification with the new shape,
    // not merely fail to verify an old proof against a different statement.
    for name in [
        "sp1.native.SP1NativeMemoryInitOrder.terminal",
        "sp1.native.SP1NativeMemoryFinalOrder.terminal",
        "sp1.native.commit.terminal",
        "sp1.native.commit_deferred.terminal",
        "sp1.native.halt",
    ] {
        let index = <empty::Ensemble as Program<F>>::COMPONENT_NAMES
            .iter()
            .position(|actual| *actual == name)
            .unwrap();
        assert_eq!(heights[index], 1, "{name}");
        let mut missing = traces.clone();
        missing[index].values.clear();
        let mut missing_heights = heights.clone();
        missing_heights[index] = 0;
        let statement = empty::Statement::<F>::new(&missing_heights).unwrap();
        backend::assert_backend_rejection(|| {
            let (proof, _) = prove_ensemble(&config, &statement, missing, &public).unwrap();
            verify_ensemble(&config, &statement, &proof, &public).is_err()
        });
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
