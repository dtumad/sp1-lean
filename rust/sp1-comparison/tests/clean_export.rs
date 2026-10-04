extern crate alloc;

// Clean's renderer emits reusable helpers that this small fixture does not all exercise.
#[allow(dead_code, unused_imports, unused_variables, unused_parens)]
mod generated {
    include!(concat!(
        env!("CLEAN_ENSEMBLE_EXPORT_DIR"),
        "/fixed_membership.rs"
    ));
}

use clean_backend::witness_generation::{Program, WitnessGenerationError};
use clean_backend::{
    prove_ensemble, verify_ensemble, EnsembleShapeError, GeneratedAirSpec, StarkConfig,
};
use p3_challenger::DuplexChallenger;
use p3_commit::ExtensionMmcs;
use p3_dft::Radix2DitParallel;
use p3_field::extension::BinomialExtensionField;
use p3_field::{Field, PrimeCharacteristicRing, PrimeField64};
use p3_fri::{create_test_fri_params, TwoAdicFriPcs};
use p3_koala_bear::{KoalaBear as F, Poseidon2KoalaBear};
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use p3_merkle_tree::MerkleTreeMmcs;
use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};
use rand::{rngs::SmallRng, SeedableRng};

type Perm = Poseidon2KoalaBear<16>;
type Hash = PaddingFreeSponge<Perm, 16, 8, 8>;
type Compress = TruncatedPermutation<Perm, 2, 8, 16>;
type Mmcs = MerkleTreeMmcs<<F as Field>::Packing, <F as Field>::Packing, Hash, Compress, 8>;
type Challenge = BinomialExtensionField<F, 4>;
type ChallengeMmcs = ExtensionMmcs<F, Challenge, Mmcs>;
type Challenger = DuplexChallenger<F, Perm, 16, 8>;
type Pcs = TwoAdicFriPcs<F, Radix2DitParallel<F>, Mmcs, ChallengeMmcs>;
type Config = StarkConfig<Pcs, Challenge, Challenger>;

fn config() -> Config {
    let mut rng = SmallRng::seed_from_u64(7);
    let permutation = Perm::new_from_rng_128(&mut rng);
    let mmcs = Mmcs::new(
        Hash::new(permutation.clone()),
        Compress::new(permutation.clone()),
    );
    let fri = create_test_fri_params(ChallengeMmcs::new(mmcs.clone()), 0);
    let pcs = Pcs::new(Radix2DitParallel::default(), mmcs, fri);
    Config::new(pcs, Challenger::new(permutation))
}

fn field(value: u64) -> F {
    F::from_u64(value)
}

#[test]
fn generated_witnesses_match_lean_and_independent_fixed_membership() {
    let reference: serde_json::Value = serde_json::from_str(include_str!(concat!(
        env!("CLEAN_ENSEMBLE_EXPORT_DIR"),
        "/fixed_membership.reference.json"
    )))
    .unwrap();
    assert_eq!(reference.as_array().unwrap().len(), 3);
    assert_eq!(F::ORDER_U64, 2_130_706_433);
    for (case, value) in reference.as_array().unwrap().iter().zip([7, 9, 8]) {
        assert_eq!(case["publicInput"], value);
        assert_eq!(case["accepted"], value != 8);
        let generated = generated::generate(&[field(value)], &[]);
        if value == 8 {
            assert!(generated.is_err(), "forged membership must fail");
            continue;
        }
        let witness = generated.unwrap();
        let tables = witness
            .tables
            .iter()
            .map(|table| {
                table
                    .iter()
                    .map(|row| row.iter().map(|x| x.as_canonical_u64()).collect::<Vec<_>>())
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        assert_eq!(serde_json::json!(tables), case["tables"]);
        assert_eq!(
            tables,
            vec![vec![
                vec![7, u64::from(value == 7), 49],
                vec![9, u64::from(value == 9), 81]
            ]]
        );
        assert_eq!(case["interactionCount"], 3);
        let statement = generated::FixedMembershipStatement::<F>::new(&[2]).unwrap();
        assert_eq!(
            statement.interaction_count(),
            3,
            "zero-count rows retain their occurrence"
        );
        let traces = witness.into_traces().unwrap();
        assert_eq!((traces[0].height(), traces[0].width()), (2, 2));
        let fixed = generated::FixedMembershipAirSpec::fixed_trace::<F>(0).unwrap();
        assert_eq!(fixed.values, vec![field(7), field(9)]);
    }
    assert!(matches!(
        generated::generate::<F>(&[], &[]),
        Err(WitnessGenerationError::PublicInputWidth { .. })
    ));
    assert!(matches!(
        generated::generate(&[field(7)], &[field(1)]),
        Err(WitnessGenerationError::ProverInputWidth { .. })
    ));
}

#[test]
fn generated_air_proves_and_binds_the_public_value() {
    let config = config();
    let statement = generated::FixedMembershipStatement::<F>::new(&[2]).unwrap();
    for value in [7, 9] {
        let public = [field(value)];
        let traces = generated::generate(&public, &[])
            .unwrap()
            .into_traces()
            .unwrap();
        let (proof, _) = prove_ensemble(&config, &statement, traces, &public).unwrap();
        verify_ensemble(&config, &statement, &proof, &public).unwrap();
        for wrong in [8, if value == 7 { 9 } else { 7 }] {
            assert!(verify_ensemble(&config, &statement, &proof, &[field(wrong)]).is_err());
        }
    }
}

#[test]
fn generated_air_rejects_wrong_shape_and_row_content() {
    let config = config();
    let statement = generated::FixedMembershipStatement::<F>::new(&[2]).unwrap();
    assert!(matches!(
        generated::FixedMembershipStatement::<F>::new(&[]),
        Err(EnsembleShapeError::ComponentCount { .. })
    ));
    assert!(matches!(
        generated::FixedMembershipStatement::<F>::new(&[2, 2]),
        Err(EnsembleShapeError::ComponentCount { .. })
    ));
    assert!(matches!(
        generated::FixedMembershipStatement::<F>::new(&[4]),
        Err(EnsembleShapeError::FixedTraceHeight { .. })
    ));
    let public = [field(7)];
    let traces = generated::generate(&public, &[])
        .unwrap()
        .into_traces()
        .unwrap();
    assert!(matches!(
        prove_ensemble(&config, &statement, vec![], &public),
        Err(EnsembleShapeError::TraceCount { .. })
    ));
    assert!(matches!(
        prove_ensemble(
            &config,
            &statement,
            vec![traces[0].clone(), traces[0].clone()],
            &public
        ),
        Err(EnsembleShapeError::TraceCount { .. })
    ));
    assert!(matches!(
        prove_ensemble(
            &config,
            &statement,
            vec![RowMajorMatrix::new(vec![field(1), field(0)], 1)],
            &public
        ),
        Err(EnsembleShapeError::TraceWidth { .. })
    ));

    // Release mode reaches verification for invalid witnesses; debug mode may reject them earlier.
    for (cell, value) in [(0, 0), (0, 2), (1, 64), (2, 1)] {
        let mut altered = traces.clone();
        altered[0].values[cell] = field(value);
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let (proof, _) = prove_ensemble(&config, &statement, altered, &public).unwrap();
            verify_ensemble(&config, &statement, &proof, &public).is_err()
        }));
        match result {
            Ok(rejected) => assert!(rejected, "invalid row cell {cell} was accepted"),
            Err(payload) => {
                let message = payload
                    .downcast_ref::<String>()
                    .map(String::as_str)
                    .or_else(|| payload.downcast_ref::<&str>().copied())
                    .unwrap_or("");
                if !cfg!(debug_assertions)
                    || !(message.contains("constraint") || message.contains("lookup"))
                {
                    std::panic::resume_unwind(payload);
                }
            }
        }
    }
    assert_eq!(
        <generated::FixedMembership as Program<F>>::COMPONENT_NAMES,
        &["allowed"]
    );
}
