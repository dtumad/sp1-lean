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

use clean_backend::witness_generation::{generate, Program, WitnessGenerationError};
use clean_backend::GeneratedAirSpec;
use p3_field::PrimeCharacteristicRing;
use p3_koala_bear::KoalaBear as F;
use p3_matrix::Matrix;

fixture!(fabricated_halt, "installed_fabricated_halt");
fixture!(changed_stopped, "installed_stopped_changed");
fixture!(stopped_wide, "installed_stopped_wide");
fixture!(stopped_zero, "installed_stopped_zero");
fixture!(empty, "installed_empty");
fixture!(generated, "installed_assembly");
fn stopped_receipt<P: GeneratedAirSpec>(public: &[F], word: &[F]) {
    let ledger = P::verifier_interactions(public);
    let receipts = ledger
        .iter()
        .filter(|entry| entry.channel == "SP1HostExit")
        .collect::<Vec<_>>();
    assert_eq!(receipts.len(), 1);
    assert_eq!(receipts[0].multiplicity, F::ZERO);
    assert_eq!(receipts[0].message.as_slice(), word);
}

#[test]
fn stopped_generated_witnesses_match_native_rows_and_full_verifiers() {
    let zero = stopped_zero::reference();
    let wide = stopped_wide::reference();
    check_reference::<stopped_zero::Ensemble>(&zero, 6);
    check_reference::<stopped_wide::Ensemble>(&wide, 6);
    let zero_public = fields(&zero["cases"][0]["publicInput"]);
    let wide_public = fields(&wide["cases"][0]["publicInput"]);
    // Literal independent encodings: optional exit status is not public exit_code.
    assert_eq!(zero_public[14], F::ZERO);
    assert_eq!(wide_public[14], F::ZERO);
    stopped_receipt::<stopped_zero::Ensemble>(&zero_public, &[F::ZERO; 4]);
    stopped_receipt::<stopped_wide::Ensemble>(&wide_public, &[F::ZERO, F::ONE, F::ZERO, F::ZERO]);
    for slot in 0..8 {
        assert_eq!(wide_public[16 + 4 * slot], F::from_u64(17 + slot as u64));
        assert!(wide_public[17 + 4 * slot..20 + 4 * slot]
            .iter()
            .all(|v| *v == F::ZERO));
    }
    assert_eq!(wide_public.len(), 58);
    for slot in 0..8 {
        assert_eq!(wide_public[48 + slot], F::from_u64(33 + slot as u64));
    }
    assert_eq!(&wide_public[56..58], &[F::ZERO, F::ZERO]);
    // Unused slots still belong to the immutable verifier-owned statement.
    let changed_digest = &wide["cases"][2];
    assert_eq!(changed_digest["name"], "changed-public-digest-byte");
    assert_eq!(changed_digest["accepted"], false);
    let mut expected_public = wide_public;
    expected_public[16] = F::from_u64(18);
    assert_eq!(fields(&changed_digest["publicInput"]), expected_public);
    assert_ne!(changed_digest["verifier"], wide["cases"][0]["verifier"]);
}

#[test]
fn invalid_optional_exit_instances_reject_generation_for_the_expected_reason() {
    let changed = changed_stopped::reference();
    let fabricated = fabricated_halt::reference();
    check_reference::<changed_stopped::Ensemble>(&changed, 2);
    check_reference::<fabricated_halt::Ensemble>(&fabricated, 1);
    for case in changed["cases"].as_array().unwrap() {
        let error = generate::<F, changed_stopped::Ensemble>(
            &fields(&case["publicInput"]),
            &fields(&case["privateInput"]),
        )
        .unwrap_err();
        assert!(
            matches!(&error, WitnessGenerationError::Runtime(message) if message.contains("host-boundary")),
            "{error}"
        );
    }
    let case = &fabricated["cases"][0];
    let public = fields(&case["publicInput"]);
    let error = generate::<F, fabricated_halt::Ensemble>(&public, &fields(&case["privateInput"]))
        .unwrap_err();
    assert!(
        matches!(&error, WitnessGenerationError::Runtime(message) if message.contains("SP1HostExit")),
        "{error}"
    );
    let ledger = <fabricated_halt::Ensemble as GeneratedAirSpec>::verifier_interactions(&public);
    let receipt = ledger
        .iter()
        .find(|entry| entry.channel == "SP1HostExit")
        .unwrap();
    assert_eq!(receipt.multiplicity, -F::ONE);
    assert_eq!(receipt.message, vec![F::ZERO; 4]);
}

fn prove_stopped_and_check_terminals<P: Program<F> + GeneratedAirSpec>(
    reference: &serde_json::Value,
) {
    let (traces, public) = prove_case::<P>(&reference["cases"][0]);
    assert!(traces[7..32].iter().all(|trace| trace.height() == 0));
    // Check the AIR/public relation with fresh proofs, beyond transcript binding of an old proof.
    for case in reference["cases"].as_array().unwrap().iter().skip(1) {
        let changed_public = fields(&case["publicInput"]);
        if changed_public != public {
            assert_eq!(case["accepted"], false);
            reject_traces::<P>(&changed_public, traces.clone());
        }
    }
    for name in [
        "sp1.native.SP1NativeMemoryInitOrder.terminal",
        "sp1.native.SP1NativeMemoryFinalOrder.terminal",
        "sp1.native.commit.terminal",
        "sp1.native.commit_deferred.terminal",
        "sp1.native.halt",
    ] {
        let index = P::COMPONENT_NAMES
            .iter()
            .position(|actual| *actual == name)
            .unwrap();
        assert_eq!(traces[index].height(), 1, "{name}");
        let mut missing = traces.clone();
        missing[index].values.clear();
        reject_traces::<P>(&public, missing);
    }
}

#[test]
fn stopped_assemblies_prove_and_require_every_terminal() {
    prove_stopped_and_check_terminals::<stopped_zero::Ensemble>(&stopped_zero::reference());
    prove_stopped_and_check_terminals::<stopped_wide::Ensemble>(&stopped_wide::reference());
}

#[test]
fn stopped_source_rejects_a_valid_active_branch_with_a_fresh_proof_attempt() {
    let reference = generated::reference();
    let (traces, public) = prove_case::<generated::Ensemble>(&reference["cases"][0]);
    assert_eq!(generated::Ensemble::WIDTHS, stopped_zero::Ensemble::WIDTHS);
    assert_eq!(
        generated::Ensemble::FIXED_HEIGHTS,
        stopped_zero::Ensemble::FIXED_HEIGHTS
    );
    for index in 0..95 {
        if generated::Ensemble::FIXED_HEIGHTS[index] != 0 {
            assert_eq!(
                backend::fixed_trace::<generated::Ensemble>(index).values,
                backend::fixed_trace::<stopped_zero::Ensemble>(index).values
            );
        }
    }
    reject_traces::<stopped_zero::Ensemble>(&public, traces);
}

#[test]
fn invalid_optional_exit_instances_reject_otherwise_valid_empty_traces() {
    let wide = stopped_wide::reference();
    let (traces, public) = prove_case::<stopped_wide::Ensemble>(&wide["cases"][0]);
    reject_traces::<changed_stopped::Ensemble>(&public, traces);
    let running = empty::reference();
    let (traces, public) = prove_case::<empty::Ensemble>(&running["cases"][0]);
    reject_traces::<fabricated_halt::Ensemble>(&public, traces);
}
