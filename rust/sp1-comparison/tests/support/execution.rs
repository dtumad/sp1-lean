//! Small decoded RISC-V programs executed and traced by the pinned SP1 implementation.

use sp1_core_executor::{
    ExecutionRecord, Instruction, MinimalExecutor, Opcode, Program, SP1CoreOpts, SupervisorMode,
    SyscallCode,
};
use sp1_core_machine::executor::trace_chunk;
use sp1_hypercube::air::PROOF_NONCE_NUM_WORDS;
use sp1_primitives::SP1Field;
use std::sync::Arc;

/// Use legal byte-sized immediates, so large arguments do not rely on the decoded format's
/// ability to hold constants that could not occur in an actual instruction.
pub fn load_constant(instructions: &mut Vec<Instruction>, register: u8, value: u64) {
    let bytes = value.to_be_bytes();
    let first = bytes.iter().position(|byte| *byte != 0).unwrap_or(7);
    instructions.push(Instruction::new(
        Opcode::ADDI,
        register,
        0,
        u64::from(bytes[first]),
        false,
        true,
    ));
    for byte in &bytes[first + 1..] {
        instructions.push(Instruction::new(
            Opcode::SLL,
            register,
            register.into(),
            8,
            false,
            true,
        ));
        instructions.push(Instruction::new(
            Opcode::ADDI,
            register,
            register.into(),
            u64::from(*byte),
            false,
            true,
        ));
    }
}

pub fn syscall(instructions: &mut Vec<Instruction>, code: SyscallCode, arg1: u64, arg2: u64) {
    load_constant(instructions, 5, code as u64);
    load_constant(instructions, 10, arg1);
    load_constant(instructions, 11, arg2);
    instructions.push(Instruction::new(Opcode::ECALL, 5, 10, 11, false, false));
}

/// Preserve the released shard builder's public values instead of manufacturing one set per row.
/// The iteration bound only guards these finite test programs against accidental loops.
pub fn run(
    program: Program,
    hints: &[Vec<u8>],
) -> (MinimalExecutor<SupervisorMode>, Vec<ExecutionRecord>) {
    let program = Arc::new(program);
    let mut executor = MinimalExecutor::<SupervisorMode>::new(program.clone(), false, Some(65536));
    for hint in hints {
        executor.with_input(hint);
    }
    let mut records = vec![];
    for _ in 0..8 {
        let Some(chunk) = executor.execute_chunk() else {
            assert!(executor.is_done());
            assert!(!records.is_empty());
            return (executor, records);
        };
        let record = ExecutionRecord {
            program: program.clone(),
            ..Default::default()
        };
        let (_, record, _) = trace_chunk::<SP1Field>(
            program.clone(),
            SP1CoreOpts::default(),
            chunk,
            [0; PROOF_NONCE_NUM_WORDS],
            record,
        )
        .expect("released SP1 tracing must succeed");
        records.push(record);
    }
    panic!("short conformance program did not terminate");
}
