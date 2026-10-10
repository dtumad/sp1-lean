extern crate alloc;

// Clean's renderer emits reusable helpers that this small fixture does not all exercise.
#[allow(dead_code, unused_imports, unused_variables, unused_parens)]
mod generated {
    include!(concat!(
        env!("CLEAN_ENSEMBLE_EXPORT_DIR"),
        "/fixed_membership.rs"
    ));
}

#[allow(dead_code, unused_imports, unused_variables, unused_parens)]
mod registers {
    include!(concat!(
        env!("CLEAN_ENSEMBLE_EXPORT_DIR"),
        "/snapshot_registers.rs"
    ));
}

#[allow(dead_code, unused_imports, unused_variables, unused_parens)]
mod empty_registers {
    include!(concat!(
        env!("CLEAN_ENSEMBLE_EXPORT_DIR"),
        "/snapshot_registers_empty.rs"
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

// This arbitrary local snapshot is not SP1's boot-only all-zero register table.
// Compute its values and Memory records independently of generated Lean metadata.
fn register(index: u64) -> Vec<u64> {
    assert!(index < 32);
    let value = index.wrapping_mul(0x0123_4567_89ab_cdef);
    let mut row = vec![index];
    row.extend((0..4).map(|limb| (value >> (16 * limb)) & 0xffff));
    row
}

fn memory(row: &[u64]) -> Vec<u64> {
    let mut message = vec![0, 0, row[0], 0, 0];
    message.extend_from_slice(&row[1..]);
    message
}

fn interaction(channel: &str, mult: u64, message: Vec<u64>, assumes: bool) -> serde_json::Value {
    serde_json::json!({
        "channel": channel, "message": message,
        "multiplicity": mult, "assumeGuarantees": assumes,
    })
}

fn physical_reference<P: Program<F>>(public: &[F], tables: &[Vec<Vec<F>>]) -> serde_json::Value {
    let interactions = P::verifier_interactions(public)
        .into_iter()
        .chain(tables.iter().enumerate().flat_map(|(component, rows)| {
            rows.iter()
                .flat_map(move |row| P::interactions(component, row))
        }))
        .map(|entry| {
            interaction(
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
        .collect::<Vec<_>>();
    let rows = tables
        .iter()
        .map(|table| {
            table
                .iter()
                .map(|row| {
                    row.iter()
                        .map(PrimeField64::as_canonical_u64)
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    serde_json::json!({"tables": rows, "interactions": interactions})
}

fn register_reference() -> serde_json::Value {
    serde_json::from_str(include_str!(concat!(
        env!("CLEAN_ENSEMBLE_EXPORT_DIR"),
        "/snapshot_registers.reference.json"
    )))
    .unwrap()
}

#[test]
fn snapshot_registers_match_source_values_and_complete_lean_ledger() {
    let reference = register_reference();
    let mut cases: Vec<_> = (0..32)
        .map(|index| {
            (
                format!("register-{index}"),
                [register(index), register(31)].concat(),
                true,
            )
        })
        .collect();
    cases.push((
        "repeated".to_owned(),
        [register(5), register(5)].concat(),
        true,
    ));
    for limb in 0..4 {
        let mut forged = register(5);
        forged[limb + 1] += 1;
        cases.push((
            format!("forged-limb-{limb}"),
            [forged, register(31)].concat(),
            false,
        ));
    }
    for index in [6, 32, 0] {
        let mut forged = register(5);
        forged[0] = index;
        cases.push((
            format!("forged-index-{index}"),
            [forged, register(31)].concat(),
            false,
        ));
    }
    assert_eq!(reference["cases"].as_array().unwrap().len(), cases.len());
    assert_eq!(cases.len(), 40);
    assert_eq!(
        <registers::SnapshotRegisters as Program<F>>::FIXED_WIDTHS,
        &[0, 5]
    );
    let fixed = registers::SnapshotRegistersAirSpec::fixed_trace::<F>(1).unwrap();
    assert_eq!((fixed.height(), fixed.width()), (32, 5));
    assert_eq!(
        fixed.values,
        (0..32).flat_map(register).map(field).collect::<Vec<_>>()
    );

    for (case, (name, public, accepted)) in reference["cases"].as_array().unwrap().iter().zip(cases)
    {
        assert_eq!(case["name"], name);
        assert_eq!(case["publicInput"], serde_json::json!(public));
        assert_eq!(case["accepted"], accepted);
        let public_fields: Vec<_> = public.iter().copied().map(field).collect();
        let result = registers::generate(&public_fields, &[]);
        assert_eq!(result.is_ok(), accepted, "{name}");
        if !accepted {
            continue;
        }
        let witness = result.unwrap();
        let actual =
            physical_reference::<registers::SnapshotRegisters>(&public_fields, &witness.tables);
        assert_eq!(actual, case["witness"], "{name}");
        let sparse: Vec<Vec<u64>> = public.chunks_exact(5).map(<[u64]>::to_vec).collect();
        let fixed_rows: Vec<Vec<u64>> = (0..32)
            .map(|index| {
                let mut row = register(index);
                row.push(sparse.iter().filter(|r| r[0] == index).count() as u64);
                row
            })
            .collect();
        assert_eq!(actual["tables"], serde_json::json!([sparse, fixed_rows]));
        let mut ledger: Vec<_> = sparse
            .iter()
            .map(|row| interaction("SP1Memory", F::ORDER_U64 - 1, memory(row), true))
            .collect();
        for row in &sparse {
            ledger.push(interaction(
                "sp1.native.source_registers",
                F::ORDER_U64 - 1,
                row.clone(),
                true,
            ));
            ledger.push(interaction("SP1Memory", 1, memory(row), false));
        }
        for row in fixed_rows {
            ledger.push(interaction(
                "sp1.native.source_registers",
                row[5],
                row[..5].to_vec(),
                false,
            ));
        }
        assert_eq!(actual["interactions"], serde_json::json!(ledger));
        assert_eq!(
            ledger.len(),
            38,
            "keep all repeated and zero-count occurrences"
        );
        let statement = registers::SnapshotRegistersStatement::<F>::new(&[2, 32]).unwrap();
        assert_eq!(statement.interaction_count(), 38);
        let traces = witness.into_traces().unwrap();
        assert_eq!((traces[0].height(), traces[0].width()), (2, 5));
        assert_eq!((traces[1].height(), traces[1].width()), (32, 1));
    }
}

#[test]
fn unused_snapshot_registers_keep_all_fixed_rows_and_zero_occurrences() {
    let witness = empty_registers::generate::<F>(&[], &[]).unwrap();
    let actual =
        physical_reference::<empty_registers::EmptySnapshotRegisters>(&[], &witness.tables);
    assert_eq!(actual, register_reference()["empty"]);
    let rows: Vec<_> = (0..32)
        .map(|index| {
            let mut row = register(index);
            row.push(0);
            row
        })
        .collect();
    let ledger: Vec<_> = (0..32)
        .map(|index| interaction("sp1.native.source_registers", 0, register(index), false))
        .collect();
    assert_eq!(
        actual,
        serde_json::json!({"tables": [rows], "interactions": ledger})
    );
    let statement = empty_registers::EmptySnapshotRegistersStatement::<F>::new(&[32]).unwrap();
    assert_eq!(statement.interaction_count(), 32);
    let config = config();
    let traces = witness.into_traces().unwrap();
    assert_eq!((traces[0].height(), traces[0].width()), (32, 1));
    let (proof, _) = prove_ensemble(&config, &statement, traces.clone(), &[]).unwrap();
    verify_ensemble(&config, &statement, &proof, &[]).unwrap();
    for index in [0, 5, 31] {
        let mut altered = traces.clone();
        altered[0].values[index] = field(1);
        let (proof, _) = prove_ensemble(&config, &statement, altered, &[]).unwrap();
        assert!(verify_ensemble(&config, &statement, &proof, &[]).is_err());
    }
}

#[test]
fn snapshot_register_proofs_bind_each_public_index_and_limb() {
    let config = config();
    let statement = registers::SnapshotRegistersStatement::<F>::new(&[2, 32]).unwrap();
    for indices in [[0, 31], [5, 5]] {
        let public: Vec<_> = indices.into_iter().flat_map(register).map(field).collect();
        let traces = registers::generate(&public, &[])
            .unwrap()
            .into_traces()
            .unwrap();
        let (proof, _) = prove_ensemble(&config, &statement, traces, &public).unwrap();
        verify_ensemble(&config, &statement, &proof, &public).unwrap();
        for cell in 0..public.len() {
            let mut changed = public.clone();
            changed[cell] += field(1);
            assert!(verify_ensemble(&config, &statement, &proof, &changed).is_err());
        }
    }
}

#[test]
fn snapshot_register_air_rejects_shapes_sparse_row_and_count_mutations() {
    for heights in [vec![], vec![32], vec![2, 32, 32], vec![2, 16], vec![2, 64]] {
        assert!(registers::SnapshotRegistersStatement::<F>::new(&heights).is_err());
    }
    assert!(matches!(
        registers::generate::<F>(&[], &[]),
        Err(WitnessGenerationError::PublicInputWidth { .. })
    ));
    let public: Vec<_> = [5, 31].into_iter().flat_map(register).map(field).collect();
    assert!(matches!(
        registers::generate(&public, &[field(1)]),
        Err(WitnessGenerationError::ProverInputWidth { .. })
    ));
    let traces = registers::generate(&public, &[])
        .unwrap()
        .into_traces()
        .unwrap();
    let config = config();
    let statement = registers::SnapshotRegistersStatement::<F>::new(&[2, 32]).unwrap();
    assert!(matches!(
        prove_ensemble(&config, &statement, vec![traces[0].clone()], &public),
        Err(EnsembleShapeError::TraceCount { .. })
    ));
    // Fixed values are verifier-owned and absent from committed traces. Mutate every
    // sparse index/limb and every count, including unused counts, in both directions.
    for (table, trace) in traces.iter().enumerate() {
        for cell in 0..trace.values.len() {
            for delta in [field(1), -field(1)] {
                let mut changed = traces.clone();
                changed[table].values[cell] += delta;
                let (proof, _) = prove_ensemble(&config, &statement, changed, &public).unwrap();
                assert!(
                    verify_ensemble(&config, &statement, &proof, &public).is_err(),
                    "accepted mutation of table {table}, cell {cell}"
                );
            }
        }
    }
}
