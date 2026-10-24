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
use sp1_core_executor::{
    events::MemoryRecordEnum, ITypeRecord, Instruction, Opcode, Program as Sp1Program, SyscallCode,
};

fixture!(ordinary, "installed_ordinary");
fixture!(prefix, "installed_ordinary_prefix");
fixture!(suffix, "installed_ordinary_suffix");
fixture!(empty, "installed_ordinary_empty");

fn addi(rd: u8, rs: u64, immediate: u64) -> Instruction {
    Instruction::new(Opcode::ADDI, rd, rs, immediate, false, true)
}
fn branch(a: u8, b: u64, offset: u64) -> Instruction {
    Instruction::new(Opcode::BEQ, a, b, offset, false, true)
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
    check_endpoints(
        &public,
        (initial_clock, initial_pc),
        (initial_clock + 8 * count as u64, final_pc),
    );
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

#[test]
fn references_preserve_every_native_row_and_occurrence() {
    check_reference::<ordinary::Ensemble>(&ordinary::reference(), 3);
    check_reference::<prefix::Ensemble>(&prefix::reference(), 3);
    check_reference::<suffix::Ensemble>(&suffix::reference(), 3);
    check_reference::<empty::Ensemble>(&empty::reference(), 3);
}

#[test]
fn assemblies_prove_and_reject_missing_or_changed_obligations() {
    malformed::<ordinary::Ensemble>(&ordinary::reference(), &[8, 18, 23, 28, 90, 91]);
    malformed::<prefix::Ensemble>(&prefix::reference(), &[8, 28, 90, 91]);
    malformed::<suffix::Ensemble>(&suffix::reference(), &[8, 18, 23, 28, 90, 91]);
    malformed::<empty::Ensemble>(&empty::reference(), &[57]);
}
