//! Native full-register syscall profile exported by Clean; SP1 supplies the code inventory.
//! This profile intentionally excludes other SP1 calls and rejects upper-register aliases.

extern crate alloc;

#[allow(dead_code, unused_imports, unused_variables, unused_parens)]
mod generated {
    include!(concat!(
        env!("CLEAN_ENSEMBLE_EXPORT_DIR"),
        "/syscall_code_guard.rs"
    ));
}

use clean_backend::witness_generation::{generate, Program};
use clean_backend::GeneratedAirSpec;
use generated::Ensemble as Profile;
use p3_field::{PrimeCharacteristicRing, PrimeField64};
use p3_koala_bear::KoalaBear as F;
use sp1_core_executor::SyscallCode;

fn codes() -> [u64; 8] {
    [
        SyscallCode::HALT as u64,
        SyscallCode::WRITE as u64,
        SyscallCode::ENTER_UNCONSTRAINED as u64,
        SyscallCode::COMMIT as u64,
        SyscallCode::COMMIT_DEFERRED_PROOFS as u64,
        SyscallCode::VERIFY_SP1_PROOF as u64,
        SyscallCode::HINT_LEN as u64,
        SyscallCode::HINT_READ as u64,
    ]
}

fn row(input: [u64; 5]) -> Vec<F> {
    let witness = generate::<F, Profile>(&[], &input.map(F::from_u64)).unwrap();
    assert_eq!(witness.tables.len(), 1);
    assert_eq!(witness.tables[0].len(), 1);
    witness.tables[0][0].clone()
}

fn valid(row: &[F]) -> bool {
    let constraints = Profile::constraints::<F>(0, row);
    assert_eq!(constraints.len(), 11);
    constraints.iter().all(|value| *value == F::ZERO)
}

#[test]
fn exported_profile_matches_released_codes_and_lean_rows() {
    let reference: serde_json::Value = serde_json::from_str(include_str!(concat!(
        env!("CLEAN_ENSEMBLE_EXPORT_DIR"),
        "/syscall_code_guard.reference.json"
    )))
    .unwrap();
    assert_eq!(reference["metrics"]["width"], 11);
    assert_eq!(reference["metrics"]["degreeBound"], 3);
    assert_eq!(reference["metrics"]["constraints"], 11);
    let cases = reference["cases"].as_array().unwrap();
    assert_eq!(cases.len(), 12);
    for (index, case) in cases.iter().enumerate() {
        let input: [u64; 5] = serde_json::from_value(case["input"].clone()).unwrap();
        let actual = row(input);
        let expected = input[4] == 0
            || (input[4] == 1
                && codes().contains(&input[0])
                && input[1..4].iter().all(|value| *value == 0));
        assert_eq!(case["accepted"], expected);
        assert_eq!(valid(&actual), expected);
        assert_eq!(
            serde_json::json!(actual
                .iter()
                .map(PrimeField64::as_canonical_u64)
                .collect::<Vec<_>>()),
            case["row"]
        );
        assert!(<Profile as Program<F>>::interactions(0, &actual).is_empty());
        if index < 8 {
            assert_eq!(input, [codes()[index], 0, 0, 0, 1]);
        }
    }
    // Exhaust the entire low-limb space against the independent released enum.
    for low in 0..=u16::MAX as u64 {
        assert_eq!(
            valid(&row([low, 0, 0, 0, 1])),
            codes().contains(&low),
            "code {low}"
        );
    }
}

#[test]
fn upper_aliases_nonboolean_activity_and_unselected_calls_are_rejected() {
    for code in codes() {
        for limb in 1..4 {
            for value in [1, 65535, 65536, F::ORDER_U64 - 1] {
                let mut input = [code, 0, 0, 0, 1];
                input[limb] = value;
                assert!(!valid(&row(input)), "alias {input:?}");
            }
        }
        for gate in [2, 3, F::ORDER_U64 - 1] {
            assert!(!valid(&row([code, 0, 0, 0, gate])));
        }
    }
    for low in [
        65536,
        F::ORDER_U64 - 1,
        SyscallCode::EXIT_UNCONSTRAINED as u64,
        SyscallCode::SHA_EXTEND as u64,
        SyscallCode::HINT_MPROTECT_FLUSH as u64,
    ] {
        assert!(!valid(&row([low, 0, 0, 0, 1])));
    }
    for input in [
        [65536, 91, 123, 90000, 0],
        [
            F::ORDER_U64 - 1,
            F::ORDER_U64 - 1,
            F::ORDER_U64 - 1,
            F::ORDER_U64 - 1,
            0,
        ],
    ] {
        assert!(valid(&row(input)));
    }
}

#[test]
fn every_shared_product_is_constrained_even_on_padding() {
    for code in codes().into_iter().chain([65536, F::ORDER_U64 - 1]) {
        for gate in [0, 1] {
            if gate == 1 && !codes().contains(&code) {
                continue;
            }
            let original = row([code, 0, 0, 0, gate]);
            assert_eq!(original.len(), 11);
            assert!(valid(&original));
            for column in 5..11 {
                for delta in [1, 256, F::ORDER_U64 - 1] {
                    let mut mutated = original.clone();
                    mutated[column] += F::from_u64(delta);
                    assert!(
                        !valid(&mutated),
                        "code {code}, gate {gate}, column {column}"
                    );
                }
            }
        }
    }
}
