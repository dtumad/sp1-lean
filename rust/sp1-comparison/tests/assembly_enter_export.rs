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
use p3_field::{PrimeCharacteristicRing, PrimeField64};
use p3_koala_bear::KoalaBear as F;
use p3_matrix::Matrix;
#[path = "support/host.rs"]
mod host;
use clean_backend::witness_generation::Program;
use clean_backend::GeneratedAirSpec;
use host::check_host_instructions;
use sp1_core_executor::{Instruction, Opcode, Program as Sp1Program, SyscallCode};

fixture!(enter, installed_enter);
fixture!(enter_once, installed_enter_once);
fixture!(empty, installed_ordinary_empty);

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
fn enter_and_verify_share_the_receiver_on_released_constrained_replay() {
    let reference = enter::reference();
    let case = &reference["cases"][0];
    let public = fields(&case["publicInput"]);
    let witness = enter::generate(&public, &fields(&case["privateInput"]), 1).unwrap();
    let mut code = vec![];
    execution::load_constant(&mut code, 5, 3);
    execution::load_constant(&mut code, 11, u64::MAX);
    let base = 131072 - 4 * code.len() as u64;
    code.extend([
        ecall(),
        branch(5, 0, 12),
        addi(5, 0, 4),
        ecall(),
        addi(5, 0, 27),
        ecall(),
        ecall(),
        addi(5, 0, 0),
        ecall(),
    ]);
    let (executor, records) = execution::run(Sp1Program::new(code, base, base), &[]);
    assert_eq!(records.len(), 1);
    let record = &records[0];
    check_host_instructions(
        record,
        (record.syscall_events[0].0.clk, 9),
        record.syscall_events.len(),
        &witness.tables[58],
    );
    assert_eq!(record.syscall_events.len(), 4);
    assert_eq!(
        record.syscall_events[0].0.syscall_code,
        SyscallCode::ENTER_UNCONSTRAINED
    );
    assert_eq!(record.syscall_events[0].1.a.current_record().value, 0);
    assert_eq!(record.syscall_events[0].0.pc, 131072);
    let (verify, instruction) = &record.syscall_events[1];
    assert_eq!(verify.syscall_code, SyscallCode::VERIFY_SP1_PROOF);
    assert_eq!(verify.pc, 131092);
    assert_eq!(verify.arg2, u64::MAX);
    assert_eq!(instruction.a.current_record().value, 27);
    check_endpoints(
        &public,
        (9, 131072),
        (
            record.public_values.last_timestamp - record.syscall_events[0].0.clk + 9,
            record.public_values.next_pc,
        ),
    );
    assert_eq!(record.branch_events.len(), 1);
    assert_eq!(record.branch_events[0].0.next_pc, 131088);
    assert_eq!(executor.registers()[5], 0);
    assert_eq!(witness.tables[65].len(), 4);
    for (row, (call, accesses)) in witness.tables[65][..3].iter().zip(&record.syscall_events) {
        assert_eq!(row.len(), 19);
        assert_eq!(row[18], F::ONE);
        let clk = (row[0].as_canonical_u64() << 24) + row[1].as_canonical_u64();
        assert_eq!(clk, call.clk - record.syscall_events[0].0.clk + 9);
        assert_eq!(decode(&row[2..6]), call.syscall_code as u64);
        assert_eq!(decode(&row[6..10]), call.arg1);
        assert_eq!(decode(&row[10..14]), call.arg2);
        assert_eq!(decode(&row[14..18]), accesses.a.current_record().value);
    }
    assert_eq!(witness.tables[65][3][18], F::ZERO);
    let mut padding = vec![F::from_u64(17); 19];
    padding[18] = F::ZERO;
    assert!(enter::Ensemble::constraints(65, &padding)
        .iter()
        .all(|v| *v == F::ZERO));
    assert!(<enter::Ensemble as Program<F>>::interactions(65, &padding)
        .iter()
        .all(|site| site.multiplicity == F::ZERO));
    assert_eq!(
        decode(&witness.tables[65][0][2..6]),
        SyscallCode::ENTER_UNCONSTRAINED as u64
    );
    assert_eq!(decode(&witness.tables[65][0][14..18]), 0);
    assert_eq!(
        decode(&witness.tables[65][1][2..6]),
        verify.syscall_code as u64
    );
    assert_eq!(decode(&witness.tables[65][1][10..14]), verify.arg2);
    assert_eq!(
        decode(&witness.tables[65][1][14..18]),
        instruction.a.current_record().value
    );
    assert_eq!(witness.tables[18].len(), 1);
    assert_eq!(witness.tables[64].len(), 1);
    assert!(witness.tables[57].is_empty());
    assert_eq!(public[7], F::from_u64(1089));
}

#[test]
fn references_preserve_every_native_row_and_occurrence() {
    check_reference::<enter::Ensemble>(&enter::reference(), 3);
    check_reference::<enter_once::Ensemble>(&enter_once::reference(), 3);
    let single = enter_once::reference();
    let (trace, _) = prove_case::<enter_once::Ensemble>(&single["cases"][0]);
    assert_eq!(trace[65].height(), 1);
    assert_eq!(trace[65].values[18], F::ONE);
    let neither = empty::reference();
    let case = &neither["cases"][0];
    let generated = empty::generate(
        &fields(&case["publicInput"]),
        &fields(&case["privateInput"]),
        1,
    )
    .unwrap();
    assert!(generated.tables[64].is_empty());
    assert!(generated.tables[65].is_empty());
}

#[test]
fn assemblies_prove_and_reject_missing_or_changed_obligations() {
    let reference = enter::reference();
    malformed::<enter::Ensemble>(&reference, &[18, 58, 64, 65, 94]);
    let (traces, public) = prove_case::<enter::Ensemble>(&reference["cases"][0]);
    let width = traces[65].width();
    for (row, other_result) in [(0, 27), (1, 0), (2, 0)] {
        let mut changed = traces.clone();
        changed[65].values[row * width + 14] = F::from_u64(other_result);
        reject_traces::<enter::Ensemble>(&public, changed);
    }
    let mut invented = traces.clone();
    invented[65].values[3 * width + 18] = F::ONE;
    reject_traces::<enter::Ensemble>(&public, invented);
    let mut removed = traces;
    removed[65].values[2 * width + 18] = F::ZERO;
    reject_traces::<enter::Ensemble>(&public, removed);
}
