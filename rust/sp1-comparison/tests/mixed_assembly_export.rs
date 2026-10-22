//! Finite assemblies compared with real released execution, including local cuts and padding.
extern crate alloc;

#[allow(dead_code)]
#[path = "support/assembly.rs"]
mod assembly;
#[allow(dead_code)]
#[path = "support/backend.rs"]
mod backend;
#[path = "support/execution.rs"]
mod execution;
#[allow(dead_code)]
#[path = "support/export.rs"]
mod export_support;

use assembly::*;
use clean_backend::witness_generation::{generate, Program};
use clean_backend::GeneratedAirSpec;
use p3_field::{PrimeCharacteristicRing, PrimeField64};
use p3_koala_bear::KoalaBear as F;
use p3_matrix::Matrix;
use sp1_core_executor::{
    events::MemoryRecordEnum, ExecutionRecord, ITypeRecord, Instruction, Opcode,
    Program as Sp1Program, SyscallCode,
};

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
fixture!(ordinary, "installed_ordinary");
fixture!(prefix, "installed_ordinary_prefix");
fixture!(suffix, "installed_ordinary_suffix");
fixture!(empty, "installed_ordinary_empty");
fixture!(hint_empty, "installed_hints_empty");
fixture!(hint_tail, "installed_hints_tail");
fixture!(hint_aligned, "installed_hints_aligned");
fixture!(enter, "installed_enter");

fn addi(rd: u8, rs: u64, immediate: u64) -> Instruction {
    Instruction::new(Opcode::ADDI, rd, rs, immediate, false, true)
}
fn ecall() -> Instruction {
    Instruction::new(Opcode::ECALL, 5, 10, 11, false, false)
}
fn branch(a: u8, b: u64, offset: u64) -> Instruction {
    Instruction::new(Opcode::BEQ, a, b, offset, false, true)
}
fn decode(cells: &[F]) -> u64 {
    cells
        .iter()
        .enumerate()
        .map(|(i, v)| v.as_canonical_u64() << (16 * i))
        .sum()
}

#[test]
fn mixed_references_preserve_every_native_row_and_occurrence() {
    check_reference::<ordinary::Ensemble>(&ordinary::reference(), 3);
    check_reference::<prefix::Ensemble>(&prefix::reference(), 3);
    check_reference::<suffix::Ensemble>(&suffix::reference(), 3);
    check_reference::<empty::Ensemble>(&empty::reference(), 3);
    check_reference::<hint_empty::Ensemble>(&hint_empty::reference(), 3);
    check_reference::<hint_tail::Ensemble>(&hint_tail::reference(), 3);
    check_reference::<hint_aligned::Ensemble>(&hint_aligned::reference(), 3);
    check_reference::<enter::Ensemble>(&enter::reference(), 3);
}

// A projection of actual released records, not another interpreter. Local cuts reset their
// authenticated source timestamps; every access after the cut retains the measured displacement.
struct Step {
    clock: u64,
    pc: u64,
    next_pc: u64,
    table: usize,
    accesses: Vec<(u64, MemoryRecordEnum)>,
}
fn accesses(record: &ITypeRecord) -> Vec<(u64, MemoryRecordEnum)> {
    vec![(record.op_a.into(), record.a), (record.op_b, record.b)]
}
fn ordinary_execution() -> Vec<Step> {
    let mut code = vec![];
    execution::load_constant(&mut code, 1, 65536);
    execution::load_constant(&mut code, 2, 3);
    let base = 131072 - 4 * code.len() as u64;
    let store = || Instruction::new(Opcode::SD, 2, 1, 0, false, true);
    let load = |rd| Instruction::new(Opcode::LD, rd, 1, 0, false, true);
    code.extend([
        addi(2, 2, 4),
        store(),
        load(2),
        addi(2, 2, 1),
        store(),
        load(3),
        branch(2, 3, 8),
        addi(2, 2, 99),
        addi(2, 2, 1),
        branch(2, 3, 8),
    ]);
    execution::syscall(&mut code, SyscallCode::HALT, 0, 0);
    let (executor, records) = execution::run(Sp1Program::new(code, base, base), &[]);
    assert_eq!((executor.registers()[2], executor.registers()[3]), (9, 8));
    assert_eq!(executor.get_memory_value(65536).value, 8);
    assert_eq!(records.len(), 1);
    let record = &records[0];
    let mut steps = vec![];
    for (event, access) in &record.addi_events {
        if (131072..131112).contains(&event.pc) {
            steps.push(Step {
                clock: event.clk,
                pc: event.pc,
                next_pc: event.pc + 4,
                table: 8,
                accesses: accesses(access),
            });
        }
    }
    for (events, table) in [
        (&record.memory_load_double_events, 23),
        (&record.memory_store_double_events, 28),
    ] {
        for (event, access) in events {
            let mut values = accesses(access);
            values.push((event.b.wrapping_add(event.c), event.mem_access));
            steps.push(Step {
                clock: event.clk,
                pc: event.pc,
                next_pc: event.pc + 4,
                table,
                accesses: values,
            });
        }
    }
    for (event, access) in &record.branch_events {
        steps.push(Step {
            clock: event.clk,
            pc: event.pc,
            next_pc: event.next_pc,
            table: 18,
            accesses: accesses(access),
        });
    }
    steps.sort_by_key(|step| step.clock);
    assert_eq!(steps.len(), 9);
    assert_eq!(steps[6].next_pc, 131104);
    assert_eq!(steps[8].next_pc, 131112);
    steps
}

fn check_cut<P: Program<F>>(
    reference: &serde_json::Value,
    steps: &[Step],
    start: usize,
    count: usize,
) {
    let case = &reference["cases"][0];
    let public = fields(&case["publicInput"]);
    let witness = generate::<F, P>(&public, &fields(&case["privateInput"])).unwrap();
    let initial_clock = 9 + 8 * start as u64;
    let initial_pc = steps.get(start).map_or(131112, |step| step.pc);
    let final_pc = if count == 0 {
        initial_pc
    } else {
        steps[start + count - 1].next_pc
    };
    assert_eq!(public[0], F::from_u64(initial_clock));
    assert_eq!(public[7], F::from_u64(initial_clock + 8 * count as u64));
    assert_eq!(decode(&public[4..7]), initial_pc);
    assert_eq!(decode(&public[11..14]), final_pc);
    let mut expected = vec![];
    if count > 0 {
        let first = steps[start].clock;
        let normalize = |clock| {
            if clock < first {
                0
            } else {
                clock - first + initial_clock
            }
        };
        for step in &steps[start..start + count] {
            for (address, access) in &step.accesses {
                for (record, multiplicity) in [
                    (access.previous_record(), F::ORDER_U64 - 1),
                    (access.current_record(), 1),
                ] {
                    let clock = normalize(record.timestamp);
                    expected.push((
                        multiplicity,
                        vec![
                            clock >> 24,
                            clock & 0xffffff,
                            address & 65535,
                            (address >> 16) & 65535,
                            address >> 32,
                            record.value & 65535,
                            (record.value >> 16) & 65535,
                            (record.value >> 32) & 65535,
                            record.value >> 48,
                        ],
                    ));
                }
            }
        }
    }
    let mut actual = vec![];
    for table in [8, 18, 23, 28] {
        let active = steps[start..start + count]
            .iter()
            .filter(|step| step.table == table)
            .count();
        assert_eq!(P::HINT_TABLES[table].rows, active);
        for row in &witness.tables[table] {
            for entry in P::interactions(table, row) {
                if entry.channel == "SP1Memory" && entry.multiplicity != F::ZERO {
                    actual.push((
                        entry.multiplicity.as_canonical_u64(),
                        entry
                            .message
                            .iter()
                            .map(PrimeField64::as_canonical_u64)
                            .collect(),
                    ));
                }
            }
        }
    }
    actual.sort();
    expected.sort();
    assert_eq!(
        actual, expected,
        "released memory access values and displaced timestamps"
    );
}

#[test]
fn arithmetic_ram_aliases_and_branch_cuts_match_released_execution() {
    let steps = ordinary_execution();
    check_cut::<ordinary::Ensemble>(&ordinary::reference(), &steps, 0, 9);
    check_cut::<prefix::Ensemble>(&prefix::reference(), &steps, 0, 2);
    check_cut::<suffix::Ensemble>(&suffix::reference(), &steps, 2, 7);
    check_cut::<empty::Ensemble>(&empty::reference(), &steps, 9, 0);
    let before = fields(&prefix::reference()["cases"][0]["publicInput"]);
    let after = fields(&suffix::reference()["cases"][0]["publicInput"]);
    assert_eq!(&before[7..14], &after[..7]);
}

fn released_host_air(record: &ExecutionRecord) {
    use slop_air::Air;
    use slop_algebra::AbstractField;
    use slop_matrix::Matrix;
    use sp1_core_machine::{syscall::instructions::SyscallInstrsChip, SupervisorMode};
    use sp1_hypercube::air::MachineAir;
    use sp1_primitives::SP1Field as S;
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
fn enter_uses_the_released_constrained_replay() {
    let reference = enter::reference();
    let case = &reference["cases"][0];
    let public = fields(&case["publicInput"]);
    let witness = enter::generate(&public, &fields(&case["privateInput"])).unwrap();
    let mut code = vec![];
    execution::load_constant(&mut code, 5, 3);
    execution::load_constant(&mut code, 11, 17);
    let base = 131072 - 4 * code.len() as u64;
    code.extend([ecall(), branch(5, 0, 12), addi(5, 0, 4), ecall(), ecall()]);
    let (executor, records) = execution::run(Sp1Program::new(code, base, base), &[]);
    assert_eq!(records.len(), 1);
    let record = &records[0];
    released_host_air(record);
    assert_eq!(record.syscall_events.len(), 2);
    assert_eq!(
        record.syscall_events[0].0.syscall_code,
        SyscallCode::ENTER_UNCONSTRAINED
    );
    assert_eq!(record.syscall_events[0].1.a.current_record().value, 0);
    assert_eq!(record.branch_events.len(), 1);
    assert_eq!(record.branch_events[0].0.next_pc, 131088);
    assert_eq!(executor.registers()[5], 0);
    assert_eq!(witness.tables[65].len(), 1);
    assert_eq!(decode(&witness.tables[65][0][14..18]), 0);
    assert_eq!(witness.tables[18].len(), 1);
    assert_eq!(witness.tables[64].len(), 1);
    assert!(witness.tables[57].is_empty());
    assert_eq!(public[7], F::from_u64(545));
}

fn malformed<P: Program<F> + GeneratedAirSpec>(reference: &serde_json::Value, consumers: &[usize]) {
    let (traces, public) = prove_case::<P>(&reference["cases"][0]);
    for column in [0, 7, 11, 14, 31, 56] {
        let mut changed = public.clone();
        changed[column] += F::ONE;
        reject_traces::<P>(&changed, traces.clone());
    }
    for table in consumers.iter().copied().chain([2, 5, 88, 89, 94]) {
        assert!(traces[table].height() > 0);
        let mut missing = traces.clone();
        missing[table].values.clear();
        reject_traces::<P>(&public, missing);
    }
    for table in [6, 59, 92, 94] {
        let mut wrong_count = traces.clone();
        wrong_count[table].values[0] += F::ONE;
        reject_traces::<P>(&public, wrong_count);
    }
    for &table in consumers {
        let mut changed = traces.clone();
        changed[table].values[0] += F::ONE;
        reject_traces::<P>(&public, changed);
    }
}

#[test]
fn mixed_assemblies_prove_and_reject_missing_or_changed_obligations() {
    malformed::<ordinary::Ensemble>(&ordinary::reference(), &[8, 18, 23, 28, 90, 91]);
    malformed::<prefix::Ensemble>(&prefix::reference(), &[8, 28, 90, 91]);
    malformed::<suffix::Ensemble>(&suffix::reference(), &[8, 18, 23, 28, 90, 91]);
    malformed::<empty::Ensemble>(&empty::reference(), &[57]);
    malformed::<hint_empty::Ensemble>(&hint_empty::reference(), &[58, 63, 82, 83, 85, 90, 91]);
    malformed::<hint_tail::Ensemble>(&hint_tail::reference(), &[58, 63, 82, 83, 84, 85, 90, 91]);
    malformed::<hint_aligned::Ensemble>(
        &hint_aligned::reference(),
        &[58, 63, 82, 83, 84, 85, 90, 91],
    );
    malformed::<enter::Ensemble>(&enter::reference(), &[18, 58, 64, 65, 90]);
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
