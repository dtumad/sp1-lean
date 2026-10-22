extern crate alloc;

#[path = "support/backend.rs"]
mod backend;

#[path = "support/execution.rs"]
mod execution;

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

use clean_backend::witness_generation::{generate, Program, WitnessGenerationError};
use clean_backend::{prove_ensemble, verify_ensemble, EnsembleShapeError, GeneratedAirSpec};
use p3_field::{PrimeCharacteristicRing, PrimeField64};
use p3_koala_bear::KoalaBear as F;
use p3_matrix::Matrix;

fn fields(value: &serde_json::Value) -> Vec<F> {
    value
        .as_array()
        .unwrap()
        .iter()
        .map(|cell| F::from_u64(cell.as_u64().unwrap()))
        .collect()
}

// Keep the physical count bound, including repeated and zero-multiplicity entries.
// Local assertions alone do not detect a missing consumer on a shared channel.
fn physical_balance<P: Program<F>>(public: &[F], tables: &[Vec<Vec<F>>]) -> bool {
    use std::collections::BTreeMap;

    let mut channels = BTreeMap::<String, (usize, BTreeMap<Vec<u64>, F>)>::new();
    for entry in
        P::verifier_interactions(public)
            .into_iter()
            .chain(tables.iter().enumerate().flat_map(|(component, rows)| {
                rows.iter()
                    .flat_map(move |row| P::interactions(component, row))
            }))
    {
        let (count, messages) = channels.entry(entry.channel.to_owned()).or_default();
        *count += 1;
        let message = entry
            .message
            .iter()
            .map(PrimeField64::as_canonical_u64)
            .collect();
        *messages.entry(message).or_default() += entry.multiplicity;
    }
    channels.values().all(|(count, messages)| {
        (*count as u64) < F::ORDER_U64 && messages.values().all(|value| *value == F::ZERO)
    })
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
        assert_eq!(verifier_reference::<P>(&public), case["verifier"]);
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
            assert_eq!(
                constraints && physical_balance::<P>(&public, &witness.tables),
                case["accepted"].as_bool().unwrap(),
                "acceptance mismatch: {}",
                case["name"]
            );
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

fn verifier_reference<P: GeneratedAirSpec>(public: &[F]) -> serde_json::Value {
    serde_json::Value::Array(
        P::verifier_interactions(public)
            .into_iter()
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
            .collect(),
    )
}

fn prove_case<P: Program<F> + GeneratedAirSpec>(
    case: &serde_json::Value,
) -> (Vec<p3_matrix::dense::RowMajorMatrix<F>>, Vec<F>) {
    assert_eq!(case["accepted"], true);
    let public = fields(&case["publicInput"]);
    let traces = generate::<F, P>(&public, &fields(&case["privateInput"]))
        .unwrap()
        .into_traces()
        .unwrap();
    accept_traces::<P>(&public, traces.clone());
    (traces, public)
}

fn accept_traces<P: GeneratedAirSpec>(
    public: &[F],
    traces: Vec<p3_matrix::dense::RowMajorMatrix<F>>,
) {
    let heights = traces.iter().map(Matrix::height).collect::<Vec<_>>();
    let statement = clean_backend::GeneratedEnsemble::<F, P>::new(&heights).unwrap();
    let config = backend::config();
    let (proof, _) = prove_ensemble(&config, &statement, traces, public).unwrap();
    verify_ensemble(&config, &statement, &proof, public).unwrap();
}

fn reject_traces<P: GeneratedAirSpec>(
    public: &[F],
    traces: Vec<p3_matrix::dense::RowMajorMatrix<F>>,
) {
    let heights = traces.iter().map(Matrix::height).collect::<Vec<_>>();
    let statement = clean_backend::GeneratedEnsemble::<F, P>::new(&heights).unwrap();
    let config = backend::config();
    backend::assert_backend_rejection(|| {
        let (proof, _) = prove_ensemble(&config, &statement, traces, public).unwrap();
        verify_ensemble(&config, &statement, &proof, public).is_err()
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
    // This carrier is unused without COMMIT. The bank endpoints are instance constants;
    // acceptance here must not be reported as public digest-to-bank binding.
    let changed_digest = &wide["cases"][2];
    assert_eq!(changed_digest["name"], "unbound-public-digest-byte");
    assert_eq!(changed_digest["accepted"], true);
    let mut expected_public = wide_public;
    expected_public[16] = F::from_u64(18);
    assert_eq!(fields(&changed_digest["publicInput"]), expected_public);
    assert_eq!(changed_digest["verifier"], wide["cases"][0]["verifier"]);
    assert_eq!(changed_digest["witness"], wide["cases"][0]["witness"]);
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
            if case["accepted"] == true {
                assert_eq!(case["name"], "unbound-public-digest-byte");
                accept_traces::<P>(&changed_public, traces.clone());
            } else {
                reject_traces::<P>(&changed_public, traces.clone());
            }
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
    for index in 0..94 {
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
