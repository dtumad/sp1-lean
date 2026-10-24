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

#[allow(dead_code)]
#[path = "support/execution.rs"]
mod execution;

use clean_backend::witness_generation::{generate, Program};
use clean_backend::{prove_ensemble, verify_ensemble, GeneratedAirSpec};
use p3_field::{PrimeCharacteristicRing, PrimeField64};
use p3_koala_bear::KoalaBear as F;
use p3_matrix::Matrix;

fixture!(hint_word_padding, "installed_hint_word_padding");
fixture!(hint_read, "installed_hint_read");
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
