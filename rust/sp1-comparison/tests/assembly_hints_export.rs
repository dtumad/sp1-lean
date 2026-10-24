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
#[allow(dead_code)]
#[path = "support/export.rs"]
mod export_support;
use clean_backend::witness_generation::{generate, Program};
use p3_field::{PrimeCharacteristicRing, PrimeField64};
use p3_koala_bear::KoalaBear as F;
#[path = "support/host.rs"]
mod host;
use host::released_host_air;
use sp1_core_executor::{Instruction, Opcode, Program as Sp1Program, SyscallCode};

fixture!(hint_empty, "installed_hints_empty");
fixture!(hint_tail, "installed_hints_tail");
fixture!(hint_aligned, "installed_hints_aligned");

fn addi(rd: u8, rs: u64, immediate: u64) -> Instruction {
    Instruction::new(Opcode::ADDI, rd, rs, immediate, false, true)
}
fn ecall() -> Instruction {
    Instruction::new(Opcode::ECALL, 5, 10, 11, false, false)
}
fn decode(cells: &[F]) -> u64 {
    cells
        .iter()
        .enumerate()
        .map(|(i, v)| v.as_canonical_u64() << (16 * i))
        .sum()
}

fn hints<P: Program<F>>(reference: &serde_json::Value, length: u64) {
    let case = &reference["cases"][0];
    let public = fields(&case["publicInput"]);
    let witness = generate::<F, P>(&public, &fields(&case["privateInput"])).unwrap();
    let mut code = vec![];
    execution::load_constant(&mut code, 5, 240);
    execution::load_constant(&mut code, 10, 65536);
    execution::load_constant(&mut code, 11, 17);
    let base = 131072 - 4 * code.len() as u64;
    for read_length in [length, 8] {
        for _ in 0..2 {
            code.extend([addi(5, 0, 240), ecall()]);
        }
        code.extend([addi(5, 0, 241), addi(11, 0, read_length), ecall()]);
    }
    code.extend([
        addi(5, 0, 240),
        ecall(),
        addi(5, 0, 0),
        addi(10, 0, 0),
        ecall(),
    ]);
    let mut program = Sp1Program::new(code, base, base);
    for offset in [0, 8, 16, 24] {
        std::sync::Arc::make_mut(&mut program.memory_image).insert(65536 + offset, u64::MAX);
    }
    let bytes = |n| (0..n).map(|i| (19 * i + 3) as u8).collect::<Vec<_>>();
    let (executor, records) = execution::run(program, &[bytes(length), bytes(8)]);
    assert_eq!(records.len(), 1);
    let record = &records[0];
    assert_eq!(record.syscall_events.len(), 8);
    released_host_air(record);
    let first = record.syscall_events[0].0.clk - 8; // first instruction is ADDI x5, x0, 240
    assert_eq!(record.syscall_events[0].0.pc - 4, 131072);
    check_endpoints(
        &public,
        (9, 131072),
        (
            record.public_values.last_timestamp - first + 9,
            record.public_values.next_pc,
        ),
    );
    let expected_results = [length, length, 8, 8, u64::MAX];
    let mut observed = 0;
    for (event, access) in &record.syscall_events {
        if event.syscall_code == SyscallCode::HINT_LEN {
            assert_eq!(access.a.current_record().value, expected_results[observed]);
            let table = if observed == 4 { 83 } else { 82 };
            let row = &witness.tables[table][if observed == 4 { 0 } else { observed }];
            assert_eq!(row[1], F::from_u64(event.clk - first + 9));
            assert_eq!(decode(&row[14..18]), expected_results[observed]);
            observed += 1;
        }
    }
    assert_eq!(observed, 5);
    // Compare each transfer, so the overlapping second read cannot hide a bad first write.
    // An independent released prefix supplies the intermediate RAM state.
    let mut first_code = vec![];
    execution::syscall(&mut first_code, SyscallCode::HINT_READ, 65536, length);
    execution::syscall(&mut first_code, SyscallCode::HALT, 0, 0);
    let mut first_program = Sp1Program::new(first_code, 131072, 131072);
    for offset in [0, 8, 16, 24] {
        std::sync::Arc::make_mut(&mut first_program.memory_image).insert(65536 + offset, u64::MAX);
    }
    let (intermediate, _) = execution::run(first_program, &[bytes(length)]);
    let mut expected = vec![];
    for ((event, _), (size, state)) in record
        .syscall_events
        .iter()
        .filter(|(event, _)| event.syscall_code == SyscallCode::HINT_READ)
        .zip([(length, &intermediate), (8, &executor)])
    {
        for index in 0..=size / 8 {
            let address = 65536 + 8 * index;
            let value = state.get_memory_value(address).value;
            let clock = event.clk - first + 10;
            expected.push(vec![
                clock >> 24,
                clock & 0xffffff,
                address & 65535,
                (address >> 16) & 65535,
                address >> 32,
                value & 65535,
                (value >> 16) & 65535,
                (value >> 32) & 65535,
                value >> 48,
            ]);
        }
    }
    let mut actual = vec![];
    for table in [84, 85] {
        for row in &witness.tables[table] {
            actual.extend(
                P::interactions(table, row)
                    .into_iter()
                    .filter(|entry| entry.channel == "SP1Memory" && entry.multiplicity == F::ONE)
                    .map(|entry| {
                        entry
                            .message
                            .iter()
                            .map(PrimeField64::as_canonical_u64)
                            .collect::<Vec<_>>()
                    }),
            );
        }
    }
    actual.sort();
    expected.sort();
    assert_eq!(actual, expected);

    assert_eq!(witness.tables[63].len(), 2);
    assert_eq!(witness.tables[82].len(), 4);
    assert_eq!(witness.tables[83].len(), 1);
    assert!(witness.tables[57].is_empty());
    for row in &witness.tables[91] {
        if row[P::HINT_TABLES[91].width - 1] == F::ONE {
            assert_eq!(
                decode(&row[5..9]),
                executor.get_memory_value(decode(&row[2..5])).value
            );
        }
    }
    assert_eq!(executor.get_memory_value(65544).value, 0);
    assert_eq!(
        public[14],
        F::from_u64(u64::from(record.public_values.exit_code))
    );
}

#[test]
fn repeated_hint_observations_and_overlapping_reads_match_released_execution() {
    hints::<hint_empty::Ensemble>(&hint_empty::reference(), 0);
    hints::<hint_tail::Ensemble>(&hint_tail::reference(), 9);
    hints::<hint_aligned::Ensemble>(&hint_aligned::reference(), 16);
}

#[test]
fn references_preserve_every_native_row_and_occurrence() {
    check_reference::<hint_empty::Ensemble>(&hint_empty::reference(), 3);
    check_reference::<hint_tail::Ensemble>(&hint_tail::reference(), 3);
    check_reference::<hint_aligned::Ensemble>(&hint_aligned::reference(), 3);
}

#[test]
fn assemblies_prove_and_reject_missing_or_changed_obligations() {
    malformed::<hint_empty::Ensemble>(&hint_empty::reference(), &[58, 63, 82, 83, 85, 90, 91]);
    malformed::<hint_tail::Ensemble>(&hint_tail::reference(), &[58, 63, 82, 83, 84, 85, 90, 91]);
    malformed::<hint_aligned::Ensemble>(
        &hint_aligned::reference(),
        &[58, 63, 82, 83, 84, 85, 90, 91],
    );
}

#[test]
fn mixed_padding_retains_zero_occurrences_and_rejects_fake_activity() {
    type P = hint_aligned::Ensemble;
    let reference = hint_aligned::reference();
    let case = &reference["cases"][0];
    let public = fields(&case["publicInput"]);
    let witness = hint_aligned::generate(&public, &fields(&case["privateInput"])).unwrap();
    // Three nonfinal hint-word transfers require a fourth, disabled physical row.
    let table = 84;
    let enabled = <P as Program<F>>::HINT_TABLES[table].width - 1;
    assert_eq!(witness.tables[table].len(), 4);
    assert_eq!(witness.tables[table][3][enabled], F::ZERO);
    let mut padded = witness.clone();
    padded.tables[table][3].fill(F::from_u64(42));
    padded.tables[table][3][enabled] = F::ZERO;
    let occurrences = <P as Program<F>>::interactions(table, &padded.tables[table][3]);
    assert!(!occurrences.is_empty());
    assert!(occurrences
        .iter()
        .all(|entry| entry.multiplicity == F::ZERO));
    accept_traces::<P>(&public, padded.clone().into_traces().unwrap());
    for activity in [F::ONE, F::TWO, -F::ONE] {
        let mut changed = padded.clone();
        changed.tables[table][3][enabled] = activity;
        reject_traces::<P>(&public, changed.into_traces().unwrap());
    }
}
