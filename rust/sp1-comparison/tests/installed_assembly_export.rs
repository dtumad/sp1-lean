extern crate alloc;

#[path = "support/backend.rs"]
mod backend;

#[allow(dead_code)]
#[path = "support/assembly.rs"]
mod assembly;
use assembly::*;

#[path = "support/execution.rs"]
mod execution;

#[allow(dead_code)]
#[path = "support/export.rs"]
mod export_support;

// Pair each built-in export with its native reference; generated helpers can be unused.
macro_rules! fixture {
    ($name:ident, $stem:literal) => {
        #[allow(dead_code, unused_imports, unused_variables, unused_parens)]
        mod $name {
            include!(concat!(
                env!("CLEAN_ENSEMBLE_EXPORT_DIR"),
                "/",
                $stem,
                ".rs"
            ));
            pub fn reference() -> serde_json::Value {
                serde_json::from_str(include_str!(concat!(
                    env!("CLEAN_ENSEMBLE_EXPORT_DIR"),
                    "/",
                    $stem,
                    ".reference.json"
                )))
                .unwrap()
            }
        }
    };
}
fixture!(generated, "installed_assembly");
fixture!(empty, "installed_empty");
fixture!(stopped_zero, "installed_stopped_zero");
fixture!(stopped_wide, "installed_stopped_wide");
fixture!(changed_stopped, "installed_stopped_changed");
fixture!(fabricated_halt, "installed_fabricated_halt");
fixture!(hint_read, "installed_hint_read");
fixture!(hint_word_padding, "installed_hint_word_padding");
fixture!(halt_zero, "installed_halt_zero");
fixture!(halt_wide, "installed_halt_wide");
fixture!(halt_max, "installed_halt_max");
fixture!(commit_repeat, "installed_commit_repeat");
fixture!(deferred_repeat, "installed_deferred_repeat");
fixture!(commit_partial_halt, "installed_commit_partial_halt");
fixture!(commit_complete_halt, "installed_commit_complete_halt");

use clean_backend::witness_generation::{generate, Program, WitnessGenerationError};
use clean_backend::{prove_ensemble, verify_ensemble, EnsembleShapeError, GeneratedAirSpec};
use p3_field::{PrimeCharacteristicRing, PrimeField64};
use p3_koala_bear::KoalaBear as F;
use p3_matrix::Matrix;

// Keep the physical count bound, including repeated and zero-multiplicity entries.
// Local assertions alone do not detect a missing consumer on a shared channel.

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
    let reference = empty::reference();
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
    let reference = generated::reference();
    let case = &reference["cases"][0];
    let public = fields(&case["publicInput"]);
    let private = fields(&case["privateInput"]);
    let traces = generated::generate(&public, &private)
        .unwrap()
        .into_traces()
        .unwrap();
    let heights = traces.iter().map(Matrix::height).collect::<Vec<_>>();
    let statement = generated::Statement::<F>::new(&heights).unwrap();
    assert_eq!(statement.component_count(), 95);
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
    let reference = generated::reference();
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

#[test]
fn complete_hint_read_matches_native_rows_and_rejects_malformed_consumers() {
    check_reference::<hint_read::Ensemble>(&hint_read::reference(), 7);
    check_reference::<hint_word_padding::Ensemble>(&hint_word_padding::reference(), 7);
}

#[test]
fn complete_hint_read_target_words_match_released_execution() {
    hint_target_words_match_released::<hint_read::Ensemble>(&hint_read::reference(), 16);
    hint_target_words_match_released::<hint_word_padding::Ensemble>(
        &hint_word_padding::reference(),
        24,
    );
}

fn hint_target_words_match_released<P: Program<F>>(reference: &serde_json::Value, length: u64) {
    use sp1_core_executor::{events::MemoryRecordEnum, Program as Sp1Program, SyscallCode};

    let case = &reference["cases"][0];
    let witness = generate::<F, P>(
        &fields(&case["publicInput"]),
        &fields(&case["privateInput"]),
    )
    .unwrap();
    let bytes = (0..length)
        .map(|index| (19 * index + 3) as u8)
        .collect::<Vec<_>>();
    let mut instructions = vec![];
    execution::syscall(&mut instructions, SyscallCode::HINT_READ, 65536, length);
    execution::syscall(&mut instructions, SyscallCode::HALT, 0, 0);
    let mut program = Sp1Program::new(instructions, 131072, 131072);
    let words = (length / 8 + 1) as usize;
    for index in 0..words as u64 + 1 {
        std::sync::Arc::make_mut(&mut program.memory_image).insert(65536 + 8 * index, u64::MAX);
    }
    let (executor, records) = execution::run(program, &[bytes]);
    assert_eq!(records.len(), 1);
    assert_eq!(records[0].syscall_events.len(), 2);
    let (event, access) = &records[0].syscall_events[0];
    assert_eq!(event.syscall_code, SyscallCode::HINT_READ);
    assert_eq!((event.arg1, event.arg2), (65536, length));
    let MemoryRecordEnum::Write(result) = access.a else {
        panic!("released HINT_READ must write its return register");
    };
    // These are native MemoryMsg columns, independent of generated layout metadata.
    let decode = |cells: &[F]| {
        cells.iter().enumerate().fold(0u64, |word, (index, cell)| {
            word | (cell.as_canonical_u64() << (16 * index))
        })
    };
    assert_eq!(witness.tables[90].len(), 4);
    for (row, (address, value)) in
        witness.tables[90][..3]
            .iter()
            .zip([(5, result.value), (10, 65536), (11, length)])
    {
        assert_eq!(decode(&row[2..5]), address);
        assert_eq!(decode(&row[5..9]), value);
        assert_eq!(row[10], F::ONE);
    }
    assert_eq!(witness.tables[91].len(), words.next_power_of_two());
    for (index, row) in witness.tables[91][..words].iter().enumerate() {
        let address = 65536 + 8 * index as u64;
        assert_eq!(decode(&row[2..5]), address);
        assert_eq!(decode(&row[5..9]), executor.get_memory_value(address).value);
        assert_eq!(&row[9..11], &[F::ONE, F::ONE]);
    }
    // Aligned HINT_READ writes a final zero word and leaves the next word alone.
    assert_eq!(executor.get_memory_value(65536 + length).value, 0);
    assert_eq!(executor.get_memory_value(65544 + length).value, u64::MAX);
}

#[test]
fn complete_hint_read_proves_with_arbitrary_disabled_cells_and_rejects_bad_activity() {
    check_hint_padding::<hint_read::Ensemble>(&hint_read::reference(), &[0, 1, 3, 4, 90, 91]);
    check_hint_padding::<hint_word_padding::Ensemble>(
        &hint_word_padding::reference(),
        &[0, 3, 84, 90],
    );
}

fn check_hint_padding<P: Program<F> + GeneratedAirSpec>(
    reference: &serde_json::Value,
    guarded: &[usize],
) {
    use p3_air::{Entry, SymbolicExpression, SymbolicVariable};

    let case = &reference["cases"][0];
    let public = fields(&case["publicInput"]);
    let witness = generate::<F, P>(&public, &fields(&case["privateInput"])).unwrap();
    let mut tables = witness.tables.clone();
    let activity = |component: usize| {
        let hint = &<P as Program<F>>::HINT_TABLES[component];
        assert_eq!(hint.key, <P as Program<F>>::COMPONENT_NAMES[component]);
        hint.width - 1
    };
    for &component in guarded {
        assert_eq!(P::HINT_TABLES[component].rows, 3);
        assert_eq!(tables[component].len(), 4);
        let enabled = activity(component);
        assert_eq!(tables[component][3][enabled], F::ZERO);
        tables[component][3].fill(F::from_u64(17));
        tables[component][3][enabled] = F::ZERO;
        assert!(P::constraints(component, &tables[component][3])
            .into_iter()
            .all(|value| value == F::ZERO));
        assert!(
            <P as Program<F>>::interactions(component, &tables[component][3])
                .into_iter()
                .all(|entry| entry.multiplicity == F::ZERO)
        );
    }
    let mut padded = witness.clone();
    padded.tables = tables;
    let traces = padded.into_traces().unwrap();
    let heights = traces.iter().map(Matrix::height).collect::<Vec<_>>();
    let statement = clean_backend::GeneratedEnsemble::<F, P>::new(&heights).unwrap();
    // Active host-call constraints have degree ten; their quotient needs a 16x LDE.
    // Read the actual emitted constraints so that this fixture detects degree drift.
    let mut max_degree = 0;
    for (component, rows) in witness.tables.iter().enumerate() {
        if rows.is_empty() {
            continue;
        }
        let row = (0..<P as Program<F>>::ROW_WIDTHS[component])
            .map(|index| {
                SymbolicExpression::<F>::from(SymbolicVariable::new(
                    Entry::Main { offset: 0 },
                    index,
                ))
            })
            .collect::<Vec<_>>();
        max_degree = max_degree.max(
            P::constraints(component, &row)
                .iter()
                .map(SymbolicExpression::degree_multiple)
                .max()
                .unwrap_or(0),
        );
    }
    assert_eq!(max_degree, 10);
    let config = backend::config_with_log_blowup(4);
    let (proof, _) = prove_ensemble(&config, &statement, traces.clone(), &public).unwrap();
    verify_ensemble(&config, &statement, &proof, &public).unwrap();
    let mut wrong_public = public.clone();
    wrong_public[7] += F::ONE;
    assert!(verify_ensemble(&config, &statement, &proof, &wrong_public).is_err());
    // Non-Boolean activity is constrained even when all child cells are padding.
    for &component in guarded {
        let mut row = witness.tables[component][3].clone();
        row[activity(component)] = F::from_u64(2);
        assert!(P::constraints(component, &row)
            .into_iter()
            .any(|value| value != F::ZERO));
    }
    // Both word variants must also be neutral on arbitrary inactive payloads.
    for component in [84, 85] {
        let enabled = P::HINT_TABLES[component].width - 1;
        let mut row = vec![F::from_u64(17); P::ROW_WIDTHS[component]];
        row[enabled] = F::ZERO;
        assert!(P::constraints(component, &row)
            .into_iter()
            .all(|value| value == F::ZERO));
        assert!(<P as Program<F>>::interactions(component, &row)
            .into_iter()
            .all(|entry| entry.multiplicity == F::ZERO));
        row[enabled] = F::from_u64(2);
        assert!(P::constraints(component, &row)
            .into_iter()
            .any(|value| value != F::ZERO));
    }
    // A real target checker or word cannot be erased, nor can padding consume a receipt.
    let mut activity_mutations = vec![
        (90, 0, F::ZERO),
        (90, 3, F::ONE),
        (91, 0, F::ZERO),
        (84, 0, F::ZERO),
        (85, 0, F::ZERO),
    ];
    if guarded.contains(&84) {
        activity_mutations.push((84, 3, F::ONE));
    }
    for (component, row, enabled) in activity_mutations {
        let mut changed = traces.clone();
        let column = row * changed[component].width() + activity(component);
        changed[component].values[column] = enabled;
        backend::assert_backend_rejection(|| {
            let (proof, _) = prove_ensemble(&config, &statement, changed, &public).unwrap();
            verify_ensemble(&config, &statement, &proof, &public).is_err()
        });
    }
}

#[test]
fn complete_halt_rows_and_public_mutations_match_native_checks() {
    check_reference::<halt_zero::Ensemble>(&halt_zero::reference(), 8);
    check_reference::<halt_wide::Ensemble>(&halt_wide::reference(), 8);
    check_reference::<halt_max::Ensemble>(&halt_max::reference(), 8);
}

fn halt_matches_released<P: Program<F>>(reference: &serde_json::Value, exit: u64) {
    use sp1_core_executor::{events::MemoryRecordEnum, Program as Sp1Program, SyscallCode};
    let case = &reference["cases"][0];
    let public = fields(&case["publicInput"]);
    let witness = generate::<F, P>(&public, &fields(&case["privateInput"])).unwrap();
    assert!(
        witness.tables[57].is_empty(),
        "active HALT must not also emit padding Exit"
    );
    assert_eq!(witness.tables[58].len(), 1);
    assert_eq!(witness.tables[64].len(), 1);
    let handler = &witness.tables[64][0];
    let mut instructions = vec![];
    execution::syscall(&mut instructions, SyscallCode::HALT, exit, 17);
    let (_, records) = execution::run(Sp1Program::new(instructions, 131072, 131072), &[]);
    assert_eq!(records.len(), 1);
    assert_eq!(records[0].syscall_events.len(), 1);
    let (event, access) = &records[0].syscall_events[0];
    assert_eq!(event.syscall_code, SyscallCode::HALT);
    assert_eq!((event.arg1, event.arg2), (exit, 17));
    let MemoryRecordEnum::Write(result) = access.a else {
        panic!("HALT must write x5");
    };
    assert_eq!(result.value, 0);
    assert_eq!(&handler[2..6], &[F::ZERO; 4]);
    assert_eq!(
        &handler[6..10],
        &[
            F::from_u64(exit & 65535),
            F::from_u64(exit >> 16),
            F::ZERO,
            F::ZERO
        ]
    );
    assert_eq!(
        &handler[10..14],
        &[F::from_u64(17), F::ZERO, F::ZERO, F::ZERO]
    );
    assert_eq!(&handler[14..22], &[F::ZERO; 8]);
    assert_eq!(
        public[14],
        F::from_u64(u64::from(records[0].public_values.exit_code))
    );
    assert_eq!(public[11], F::ONE);
    assert_eq!(&public[12..14], &[F::ZERO; 2]);
}

#[test]
fn complete_halt_effects_match_released_executor_and_public_values() {
    halt_matches_released::<halt_zero::Ensemble>(&halt_zero::reference(), 0);
    halt_matches_released::<halt_wide::Ensemble>(&halt_wide::reference(), 65536);
    halt_matches_released::<halt_max::Ensemble>(&halt_max::reference(), F::ORDER_U64 - 1);
}

fn halt_proofs<P: Program<F> + GeneratedAirSpec>(reference: &serde_json::Value) {
    let (traces, public) = prove_case::<P>(&reference["cases"][0]);
    assert_eq!(traces[57].height(), 0);
    assert_eq!(traces[64].height(), 1);
    for case in reference["cases"].as_array().unwrap().iter().skip(1) {
        reject_traces::<P>(&fields(&case["publicInput"]), traces.clone());
    }
    for index in [2, 5, 58, 64, 88, 89] {
        let mut missing = traces.clone();
        missing[index].values.clear();
        reject_traces::<P>(&public, missing);
    }
    let empty_reference = empty::reference();
    let (empty_traces, _) = prove_case::<empty::Ensemble>(&empty_reference["cases"][0]);
    let mut duplicated_exit = traces;
    duplicated_exit[57] = empty_traces[57].clone();
    reject_traces::<P>(&public, duplicated_exit);
}

#[test]
fn complete_halt_proves_and_rejects_missing_terminals_and_duplicate_exit() {
    halt_proofs::<halt_zero::Ensemble>(&halt_zero::reference());
    halt_proofs::<halt_wide::Ensemble>(&halt_wide::reference());
    halt_proofs::<halt_max::Ensemble>(&halt_max::reference());
}

#[test]
fn complete_commitment_rows_padding_and_public_mutations_match_native() {
    check_reference::<commit_repeat::Ensemble>(&commit_repeat::reference(), 9);
    check_reference::<deferred_repeat::Ensemble>(&deferred_repeat::reference(), 9);
    check_reference::<commit_partial_halt::Ensemble>(&commit_partial_halt::reference(), 9);
    check_reference::<commit_complete_halt::Ensemble>(&commit_complete_halt::reference(), 9);
}

fn commitment_execution<P: Program<F> + GeneratedAirSpec>(
    reference: &serde_json::Value,
    complete: bool,
    deferred: bool,
    stopped: bool,
) {
    use slop_air::Air;
    use slop_algebra::AbstractField;
    use slop_matrix::Matrix as _;
    use sp1_core_executor::{
        ExecutionRecord, Instruction, Opcode, Program as Sp1Program, SyscallCode,
    };
    use sp1_core_machine::{syscall::instructions::SyscallInstrsChip, SupervisorMode};
    use sp1_hypercube::air::MachineAir;
    use sp1_primitives::SP1Field as S;

    let case = &reference["cases"][0];
    let public = fields(&case["publicInput"]);
    let native = generate::<F, P>(&public, &fields(&case["privateInput"])).unwrap();
    let mut instructions = vec![];
    execution::load_constant(&mut instructions, 5, if deferred { 26 } else { 16 });
    execution::load_constant(&mut instructions, 10, if complete { 0 } else { 7 });
    execution::load_constant(&mut instructions, 11, 131075);
    // The prefix establishes the local source. The tested segment starts at the
    // same PC; clock comparison uses the measured prefix duration, not guessed timing.
    let base = 131072 - 4 * instructions.len() as u64;
    let addi = |rd, rs, imm| Instruction::new(Opcode::ADDI, rd, rs, imm, false, true);
    let ecall = || Instruction::new(Opcode::ECALL, 5, 10, 11, false, false);
    if complete {
        for bank in 0..2 {
            if bank == 1 {
                instructions.push(addi(5, 0, 26));
                instructions.push(addi(10, 0, 0));
            }
            for slot in 0..8 {
                instructions.push(ecall());
                if slot != 7 {
                    instructions.push(addi(10, 10, 1));
                }
            }
        }
    } else {
        instructions.extend([ecall(), ecall(), ecall()]);
    }
    // Continuing fixtures are proper local prefixes of this terminating Rust run.
    instructions.extend([addi(5, 0, 0), addi(10, 0, 0), ecall()]);
    let (executor, records) = execution::run(Sp1Program::new(instructions, base, base), &[]);
    assert_eq!(records.len(), 1);
    let record = &records[0];
    let count = if complete { 16 } else { 3 };
    assert_eq!(record.syscall_events.len(), count + 1);
    let first = record.syscall_events[0].0.clk;
    assert_eq!(record.syscall_events[0].0.pc, 131072);
    for bank in 0..2 {
        for slot in 0..8 {
            let value = if bank == 0 {
                record.public_values.committed_value_digest[slot]
            } else {
                record.public_values.deferred_proofs_digest[slot]
            };
            let flag = if bank == 0 { public[56] } else { public[57] };
            assert_eq!(
                P::fixed_row::<F>(94, (8 * bank + slot) as u64),
                vec![
                    F::from_u64(bank as u64),
                    F::from_u64(slot as u64),
                    F::from_u64(u64::from(value & 65535)),
                    F::from_u64(u64::from(value >> 16)),
                    F::ZERO,
                    F::ZERO,
                    flag,
                    F::ONE,
                ]
            );
        }
    }
    let mut occurrences = [0usize; 16];
    for (event, _) in &record.syscall_events[..count] {
        let bank = usize::from(event.syscall_code == SyscallCode::COMMIT_DEFERRED_PROOFS);
        assert!(matches!(
            event.syscall_code,
            SyscallCode::COMMIT | SyscallCode::COMMIT_DEFERRED_PROOFS
        ));
        let slot = event.arg1 as usize;
        let table = 66 + 8 * bank + slot;
        let row = &native.tables[table][occurrences[8 * bank + slot]];
        occurrences[8 * bank + slot] += 1;
        assert_eq!(row[0], F::ZERO);
        assert_eq!(row[1], F::from_u64(event.clk - first + 9));
        assert_eq!(
            &row[2..6],
            &[
                F::from_u64(event.syscall_code as u64),
                F::ZERO,
                F::ZERO,
                F::ZERO
            ]
        );
        assert_eq!(
            &row[6..10],
            &[F::from_u64(event.arg1), F::ZERO, F::ZERO, F::ZERO]
        );
        assert_eq!(
            &row[10..14],
            &[
                F::from_u64(event.arg2 & 65535),
                F::from_u64(event.arg2 >> 16),
                F::ZERO,
                F::ZERO
            ]
        );
        assert_eq!(row[P::HINT_TABLES[table].width - 1], F::ONE);
    }
    for bank in 0..2 {
        let words = if bank == 0 {
            record.public_values.committed_value_digest
        } else {
            record.public_values.deferred_proofs_digest
        };
        let terminal = &native.tables[88 + bank][0];
        for (slot, value) in words.into_iter().enumerate() {
            assert_eq!(
                &terminal[2 + 4 * slot..6 + 4 * slot],
                &[
                    F::from_u64(u64::from(value & 65535)),
                    F::from_u64(u64::from(value >> 16)),
                    F::ZERO,
                    F::ZERO
                ]
            );
            if bank == 0 {
                let bytes = value.to_le_bytes().map(|byte| F::from_u64(u64::from(byte)));
                assert_eq!(&public[16 + 4 * slot..20 + 4 * slot], &bytes);
            } else {
                assert_eq!(public[48 + slot], F::from_u64(u64::from(value)));
            }
        }
    }
    assert_eq!(
        public[56],
        F::from_u64(u64::from(record.public_values.commit_syscall))
    );
    assert_eq!(
        public[57],
        F::from_u64(u64::from(record.public_values.commit_deferred_syscall))
    );
    assert_eq!(native.tables[64].len(), usize::from(stopped));
    assert_eq!(native.tables[57].len(), usize::from(!stopped));
    if stopped {
        assert_eq!(executor.registers()[5], 0);
    }
    // Check the released AIR on real released rows and its own shard public values.
    let chip = SyscallInstrsChip::<SupervisorMode>::default();
    let trace = chip.generate_trace(record, &mut ExecutionRecord::default());
    for row in trace.values.chunks(trace.width()) {
        let mut check = export_support::Sp1Evaluation {
            row: row.to_vec(),
            preprocessed: vec![],
            constraints: vec![],
            ledger: vec![],
            public: record.public_values.to_vec::<S>(),
        };
        chip.eval(&mut check);
        assert!(check.constraints.iter().all(|value| *value == S::zero()));
    }
}

#[test]
fn complete_commitment_programs_match_released_events_air_and_statement() {
    commitment_execution::<commit_repeat::Ensemble>(
        &commit_repeat::reference(),
        false,
        false,
        false,
    );
    commitment_execution::<deferred_repeat::Ensemble>(
        &deferred_repeat::reference(),
        false,
        true,
        false,
    );
    commitment_execution::<commit_partial_halt::Ensemble>(
        &commit_partial_halt::reference(),
        false,
        false,
        true,
    );
    commitment_execution::<commit_complete_halt::Ensemble>(
        &commit_complete_halt::reference(),
        true,
        false,
        true,
    );
}

fn commitment_proofs<P: Program<F> + GeneratedAirSpec>(
    reference: &serde_json::Value,
    repeated: Option<usize>,
) {
    let (traces, public) = prove_case::<P>(&reference["cases"][0]);
    for case in reference["cases"]
        .as_array()
        .unwrap()
        .iter()
        .skip(1)
        .take(5)
    {
        reject_traces::<P>(&fields(&case["publicInput"]), traces.clone());
    }
    for table in [88, 89, 94] {
        let mut missing = traces.clone();
        missing[table].values.clear();
        reject_traces::<P>(&public, missing);
    }
    // Only the sixteen counts are committed. Fixed payload and eligibility columns
    // come from the verifier's preprocessing, never from mutable witness columns.
    assert_eq!(traces[94].width(), 1);
    for slot in 0..16 {
        let mut changed = traces.clone();
        changed[94].values[slot] += F::ONE;
        reject_traces::<P>(&public, changed);
    }
    if let Some(table) = repeated {
        assert_eq!(traces[table].height(), 4);
        let activity = P::HINT_TABLES[table].width - 1;
        assert_eq!(
            traces[table].values[3 * traces[table].width() + activity],
            F::ZERO
        );
        for row in 0..3 {
            assert_eq!(
                traces[table].values[row * traces[table].width() + activity],
                F::ONE
            );
        }
        for enabled in [F::ONE, F::TWO, -F::ONE] {
            let mut changed = traces.clone();
            let column = 3 * changed[table].width() + activity;
            changed[table].values[column] = enabled;
            reject_traces::<P>(&public, changed);
        }
    }
}

#[test]
fn immutable_commitment_assemblies_prove_and_reject_forged_declarations() {
    commitment_proofs::<commit_repeat::Ensemble>(&commit_repeat::reference(), Some(73));
    commitment_proofs::<deferred_repeat::Ensemble>(&deferred_repeat::reference(), Some(81));
    commitment_proofs::<commit_partial_halt::Ensemble>(&commit_partial_halt::reference(), Some(73));
    commitment_proofs::<commit_complete_halt::Ensemble>(&commit_complete_halt::reference(), None);
}
