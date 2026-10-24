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
use clean_backend::GeneratedAirSpec;
use p3_field::{PrimeCharacteristicRing, PrimeField64};
use p3_koala_bear::KoalaBear as F;
use p3_matrix::Matrix;

fixture!(halt_max, "installed_halt_max");
fixture!(halt_wide, "installed_halt_wide");
fixture!(halt_zero, "installed_halt_zero");
fixture!(empty, "installed_empty");
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
    let base = 131072 - 4 * (instructions.len() as u64 - 1);
    let (_, records) = execution::run(Sp1Program::new(instructions, base, base), &[]);
    assert_eq!(records.len(), 1);
    assert_eq!(records[0].syscall_events.len(), 1);
    let (event, access) = &records[0].syscall_events[0];
    assert_eq!(event.syscall_code, SyscallCode::HALT);
    assert_eq!((event.arg1, event.arg2), (exit, 17));
    assert_eq!(event.pc, 131072);
    check_endpoints(
        &public,
        (9, event.pc),
        (
            records[0].public_values.last_timestamp - event.clk + 9,
            records[0].public_values.next_pc,
        ),
    );
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
