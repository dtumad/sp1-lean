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

use clean_backend::witness_generation::Program;
use clean_backend::{EnsembleKey, EnsembleShapeError, GeneratedAirSpec};
use p3_field::PrimeCharacteristicRing;
use p3_koala_bear::KoalaBear as F;
use p3_matrix::Matrix;

fixture!(empty, installed_empty);
fixture!(generated, installed_assembly);
#[test]
fn complete_generated_witness_matches_native_rows_and_ledger() {
    check_reference::<generated::Ensemble>(&generated::reference(), 3);
}

#[test]
fn empty_generated_witness_matches_native_boundaries_and_rejects_mutations() {
    let reference = empty::reference();
    check_reference::<empty::Ensemble>(&reference, 6);
    let case = &reference["cases"][0];
    let public = fields(&case["publicInput"]);
    // The source clock/PC are literal fixture inputs, independent of exported metadata.
    assert_eq!(public[0], F::ONE);
    assert_eq!(&public[4..7], &[F::ZERO, F::ONE, F::ZERO]);
    assert_eq!(&public[..7], &public[7..14]);
    let witness = empty::generate(&public, &fields(&case["privateInput"]), 1).unwrap();
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
    let reference = empty::reference();
    let case = &reference["cases"][0];
    let public = fields(&case["publicInput"]);
    let private = fields(&case["privateInput"]);
    let traces = empty::generate(&public, &private, 1)
        .unwrap()
        .into_traces()
        .unwrap();
    let heights = traces.iter().map(Matrix::height).collect::<Vec<_>>();
    let statement = empty::Statement::<F>::new(&heights, 1).unwrap();
    let mut key = EnsembleKey::new(backend::config(), 1).unwrap();
    let proof = key.prove(&statement, traces.clone(), &public).unwrap();
    key.verify(&statement, &proof, &public).unwrap();
    // A single key must reindex its fixed commitments when a demand AIR enters and leaves
    // the batch. These are honest inactive ADD rows, with physical zero-count occurrences.
    let data = clean_backend::witness_generation::WitnessData::from_entries(vec![]);
    let padding = <empty::Ensemble as Program<F>>::complete_row(
        7,
        &vec![F::ZERO; empty::component_7::INPUT_WIDTH],
        &data,
        &data,
    )
    .unwrap();
    assert!(
        <empty::Ensemble as GeneratedAirSpec>::constraints(7, &padding)
            .iter()
            .all(|value| *value == F::ZERO)
    );
    assert!(<empty::Ensemble as Program<F>>::interactions(7, &padding)
        .iter()
        .all(|entry| entry.multiplicity == F::ZERO));
    for height in [2, 4, 0] {
        let mut varied = traces.clone();
        varied[7] = p3_matrix::dense::RowMajorMatrix::new(padding.repeat(height), padding.len());
        let heights = varied.iter().map(Matrix::height).collect::<Vec<_>>();
        let statement = empty::Statement::<F>::new(&heights, 1).unwrap();
        let proof = key.prove(&statement, varied, &public).unwrap();
        key.verify(&statement, &proof, &public).unwrap();
    }
    for case in reference["cases"]
        .as_array()
        .unwrap()
        .iter()
        .skip(1)
        .take(4)
    {
        assert!(key
            .verify(&statement, &proof, &fields(&case["publicInput"]))
            .is_err());
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
        let statement = empty::Statement::<F>::new(&missing_heights, 1).unwrap();
        backend::assert_backend_rejection(|| {
            let mut key = EnsembleKey::new(backend::config(), 1).unwrap();
            let proof = key.prove(&statement, missing, &public).unwrap();
            key.verify(&statement, &proof, &public).is_err()
        });
    }
}

#[test]
fn complete_assembly_proves_and_binds_public_endpoints() {
    let reference = generated::reference();
    let case = &reference["cases"][0];
    let public = fields(&case["publicInput"]);
    let private = fields(&case["privateInput"]);
    let traces = generated::generate(&public, &private, 1)
        .unwrap()
        .into_traces()
        .unwrap();
    let heights = traces.iter().map(Matrix::height).collect::<Vec<_>>();
    let statement = generated::Statement::<F>::new(&heights, 1).unwrap();
    assert_eq!(statement.component_count(), 95);
    assert_eq!(
        statement.interaction_counts().values().sum::<u128>() as usize,
        case["witness"]["interactions"].as_array().unwrap().len()
    );
    let mut key = EnsembleKey::new(backend::config(), 1).unwrap();
    let proof = key.prove(&statement, traces, &public).unwrap();
    key.verify(&statement, &proof, &public).unwrap();
    let wrong_public = fields(&reference["cases"][1]["publicInput"]);
    assert!(key.verify(&statement, &proof, &wrong_public).is_err());

    let mut missing_branch = heights.clone();
    missing_branch[18] = 0;
    let wrong_statement = generated::Statement::<F>::new(&missing_branch, 1).unwrap();
    assert!(key.verify(&wrong_statement, &proof, &public).is_err());
    let fixed = generated::Ensemble::FIXED_HEIGHTS
        .iter()
        .position(|height| *height > 0)
        .unwrap();
    let mut missing_fixed = heights;
    missing_fixed[fixed] = 0;
    assert!(matches!(generated::Statement::<F>::new(&missing_fixed, 1),
        Err(EnsembleShapeError::TraceHeight { component, height: 0 }) if component == fixed));
}

#[test]
fn complete_assembly_rejects_a_changed_committed_branch_row() {
    let reference = generated::reference();
    let case = &reference["cases"][0];
    let public = fields(&case["publicInput"]);
    let private = fields(&case["privateInput"]);
    let mut traces = generated::generate(&public, &private, 1)
        .unwrap()
        .into_traces()
        .unwrap();
    let heights = traces.iter().map(Matrix::height).collect::<Vec<_>>();
    let statement = generated::Statement::<F>::new(&heights, 1).unwrap();
    traces[18].values[0] += F::ONE;
    backend::assert_backend_rejection(|| {
        let mut key = EnsembleKey::new(backend::config(), 1).unwrap();
        let proof = key.prove(&statement, traces, &public).unwrap();
        key.verify(&statement, &proof, &public).is_err()
    });
}
