//! Compare Clean's fixed Program provider with released SP1 preprocessing, counts and AIR.

extern crate alloc;

#[path = "support/backend.rs"]
mod backend;
#[path = "support/export.rs"]
// The shared source evaluator also contains the open-bus adapter; this closed fixture needs only the evaluator.
#[allow(dead_code)]
mod export_support;

use backend::{assert_backend_rejection, config, fixed_trace, physical_reference};
use clean_backend::witness_generation::Program;
use clean_backend::{prove_ensemble, verify_ensemble, GeneratedAirSpec};
use export_support::Sp1Evaluation;
use p3_field::{PrimeCharacteristicRing, PrimeField64};
use p3_koala_bear::KoalaBear as F;
use p3_matrix::Matrix as CleanMatrix;
use serde_json::Value;
use slop_air::Air;
use slop_algebra::{AbstractField, PrimeField64 as Sp1PrimeField64};
use slop_matrix::Matrix;
use sp1_core_executor::{
    events::{AluEvent, MemoryReadRecord, MemoryRecordEnum},
    ExecutionRecord, ITypeRecord, Instruction, Opcode, Program as Sp1Program, RTypeRecord,
};
use sp1_core_machine::program::ProgramChip;
use sp1_hypercube::air::{MachineAir, SP1_PROOF_NUM_PV_ELTS};
use sp1_primitives::SP1Field;
use std::sync::Arc;

macro_rules! generated {
    ($module:ident, $file:expr) => {
        #[allow(dead_code, unused_imports, unused_variables, unused_parens)]
        mod $module {
            include!(concat!(env!("CLEAN_ENSEMBLE_EXPORT_DIR"), "/", $file));
        }
    };
}
generated!(active, "program_fixed.rs");
generated!(unused, "program_unused.rs");
generated!(empty, "program_empty.rs");

fn source_program() -> Sp1Program {
    let instructions = vec![
        Instruction::new(Opcode::ADDI, 1, 2, 7, false, true),
        Instruction::new(Opcode::ADD, 1, 2, 3, false, false),
        Instruction::new(Opcode::ECALL, 5, 10, 11, false, false),
    ];
    for (instruction, encoding) in instructions.iter().zip([0x00710093, 0x003100b3, 0x73]) {
        assert_eq!(instruction.encode(), encoding);
    }
    Sp1Program::new(instructions, 65536, 65536)
}

fn reference() -> Value {
    serde_json::from_str(include_str!(concat!(
        env!("CLEAN_ENSEMBLE_EXPORT_DIR"),
        "/program_fixed.reference.json"
    )))
    .unwrap()
}

fn requests() -> Vec<F> {
    let fixed = fixed_trace::<active::Ensemble>(0);
    [0, 0, 1]
        .into_iter()
        .flat_map(|row| fixed.values[row * 16..(row + 1) * 16].iter().copied())
        .collect()
}

#[test]
fn released_preprocessing_and_air_match_including_padding_and_zero_counts() {
    assert_eq!(F::ORDER_U64, <SP1Field as Sp1PrimeField64>::ORDER_U64);
    let source = ProgramChip::new()
        .generate_preprocessed_trace(&source_program())
        .unwrap();
    let native = fixed_trace::<active::Ensemble>(0);
    assert_eq!((source.height(), source.width()), (32, 16));
    assert_eq!((native.height(), native.width()), (32, 16));
    for (index, (expected, actual)) in source
        .values
        .chunks(16)
        .zip(native.values.chunks(16))
        .enumerate()
    {
        assert_eq!(
            expected
                .iter()
                .map(Sp1PrimeField64::as_canonical_u64)
                .collect::<Vec<_>>(),
            actual
                .iter()
                .map(PrimeField64::as_canonical_u64)
                .collect::<Vec<_>>(),
            "row {index}"
        );
        if index >= 3 {
            assert_eq!(
                actual,
                &native.values[..16],
                "padding repeats the first instruction"
            );
        }
        for count in [0, 1, 17, F::ORDER_U64 - 1] {
            let mut evaluation = Sp1Evaluation {
                row: vec![SP1Field::from_canonical_u64(count)],
                preprocessed: expected.to_vec(),
                constraints: vec![],
                ledger: vec![],
                public: vec![SP1Field::zero(); SP1_PROOF_NUM_PV_ELTS],
            };
            ProgramChip::new().eval(&mut evaluation);
            let mut row = actual.to_vec();
            row.push(F::from_u64(count));
            assert!(evaluation.constraints.is_empty());
            assert!(active::Ensemble::constraints::<F>(0, &row).is_empty());
            let ledger = <active::Ensemble as Program<F>>::interactions(0, &row);
            assert_eq!(ledger.len(), 1);
            assert_eq!(
                evaluation.ledger,
                vec![(
                    ledger[0].channel.to_owned(),
                    ledger[0].multiplicity.as_canonical_u64(),
                    ledger[0]
                        .message
                        .iter()
                        .map(PrimeField64::as_canonical_u64)
                        .collect()
                )]
            );
        }
    }
}

#[test]
fn upstream_scheduler_matches_source_counts_and_lean_physical_inventory() {
    let public = requests();
    let witness = active::generate::<F>(&public, &[]).unwrap();
    let reference = reference();
    assert_eq!(
        physical_reference::<active::Ensemble>(&public, &witness.tables),
        reference["active"]["witness"]
    );
    let mut source = ExecutionRecord {
        program: Arc::new(source_program()),
        ..Default::default()
    };
    // Only the PCs are read by ProgramChip; these records are a count fixture, not an execution proof.
    let read = MemoryRecordEnum::Read(MemoryReadRecord::default());
    for clock in [0, 1] {
        source.addi_events.push((
            AluEvent::new(clock, 65536, Opcode::ADDI, 0, 0, 7, false),
            ITypeRecord {
                op_a: 1,
                a: read,
                op_b: 2,
                b: read,
                op_c: 7,
                is_untrusted: false,
            },
        ));
    }
    source.add_events.push((
        AluEvent::new(2, 65540, Opcode::ADD, 0, 0, 0, false),
        RTypeRecord {
            op_a: 1,
            a: read,
            op_b: 2,
            b: read,
            op_c: 3,
            c: read,
            is_untrusted: false,
        },
    ));
    let counts: slop_matrix::dense::RowMajorMatrix<SP1Field> =
        ProgramChip::new().generate_trace(&source, &mut ExecutionRecord::default());
    assert_eq!((counts.height(), counts.width()), (32, 1));
    assert_eq!(
        counts
            .values
            .iter()
            .map(Sp1PrimeField64::as_canonical_u64)
            .collect::<Vec<_>>(),
        witness.tables[0]
            .iter()
            .map(|row| row[16].as_canonical_u64())
            .collect::<Vec<_>>()
    );
    assert_eq!(witness.tables[0][0][16], F::from_u64(2));
    assert_eq!(witness.tables[0][1][16], F::ONE);
    assert!(witness.tables[0][2..].iter().all(|row| row[16] == F::ZERO));
    let unused = unused::generate::<F>(&[], &[]).unwrap();
    assert_eq!(unused.tables[0].len(), 32);
    assert_eq!(
        physical_reference::<unused::Ensemble>(&[], &unused.tables),
        reference["unused"]["witness"]
    );
    let empty = empty::generate::<F>(&[], &[]).unwrap();
    assert_eq!(empty.tables, vec![vec![vec![F::ZERO; 17]]]);
    assert_eq!(
        physical_reference::<empty::Ensemble>(&[], &empty.tables),
        reference["empty"]["witness"]
    );
}

#[test]
fn backend_authenticates_rom_and_counts_without_forbidding_duplicate_padding() {
    let public = requests();
    let statement = active::Statement::<F>::new(&[32]).unwrap();
    let config = config();
    let traces = active::generate::<F>(&public, &[])
        .unwrap()
        .into_traces()
        .unwrap();
    assert_eq!((traces[0].height(), traces[0].width()), (32, 1));
    let (proof, _) = prove_ensemble(&config, &statement, traces.clone(), &public).unwrap();
    verify_ensemble(&config, &statement, &proof, &public).unwrap();
    for column in 0..16 {
        let mut forged = public.clone();
        forged[column] += F::ONE;
        assert!(
            active::generate(&forged, &[]).is_err(),
            "forged column {column}"
        );
        assert!(verify_ensemble(&config, &statement, &proof, &forged).is_err());
    }
    for row in [0, 1, 2, 31] {
        let mut forged = traces.clone();
        forged[0].values[row] += F::ONE;
        assert_backend_rejection(|| {
            let (proof, _) = prove_ensemble(&config, &statement, forged, &public).unwrap();
            verify_ensemble(&config, &statement, &proof, &public).is_err()
        });
    }
    // SP1 AIR permits moving count between physical copies of the same instruction.
    // Honest scheduling chooses the original row, but that is not an extra AIR restriction.
    let mut redistributed = traces;
    redistributed[0].values[31] = redistributed[0].values[0];
    redistributed[0].values[0] = F::ZERO;
    let (proof, _) = prove_ensemble(&config, &statement, redistributed, &public).unwrap();
    verify_ensemble(&config, &statement, &proof, &public).unwrap();
}

#[test]
fn empty_padding_cannot_supply_an_instruction() {
    let statement = empty::Statement::<F>::new(&[1]).unwrap();
    let config = config();
    let mut traces = empty::generate::<F>(&[], &[])
        .unwrap()
        .into_traces()
        .unwrap();
    let (proof, _) = prove_ensemble(&config, &statement, traces.clone(), &[]).unwrap();
    verify_ensemble(&config, &statement, &proof, &[]).unwrap();
    traces[0].values[0] = F::ONE;
    assert_backend_rejection(|| {
        let (proof, _) = prove_ensemble(&config, &statement, traces, &[]).unwrap();
        verify_ensemble(&config, &statement, &proof, &[]).is_err()
    });
}
