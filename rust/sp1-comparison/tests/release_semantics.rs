//! Source-side regression cases for behavior reviewed during the release migration.
//! These call the released executor; they are not a proof of Lean/executor equivalence.

#[allow(dead_code)]
#[path = "support/execution.rs"]
mod execution;

use sp1_core_executor::{
    chunked_memory_init_events, Instruction, MinimalExecutor, Opcode, Program, SupervisorMode,
    SyscallCode,
};
use sp1_primitives::consts::STACK_TOP;
use std::sync::Arc;

/// A minimal ELF64 with one executable NOP and a separate partially initialized data segment.
fn elf_with_zero_fill(bytes: &[u8], memory_size: usize) -> Vec<u8> {
    let mut elf = vec![0u8; 180 + bytes.len()];
    elf[..7].copy_from_slice(b"\x7fELF\x02\x01\x01");
    elf[16..18].copy_from_slice(&2u16.to_le_bytes()); // ET_EXEC
    elf[18..20].copy_from_slice(&243u16.to_le_bytes()); // EM_RISCV
    elf[20..24].copy_from_slice(&1u32.to_le_bytes());
    elf[24..32].copy_from_slice(&STACK_TOP.to_le_bytes());
    elf[32..40].copy_from_slice(&64u64.to_le_bytes()); // program headers
    elf[52..54].copy_from_slice(&64u16.to_le_bytes());
    elf[54..56].copy_from_slice(&56u16.to_le_bytes());
    elf[56..58].copy_from_slice(&2u16.to_le_bytes());
    for (offset, flags, file_offset, address, file_size, mem_size) in [
        (64, 5u32, 176u64, STACK_TOP, 4u64, 4u64),
        (
            120,
            6,
            180,
            STACK_TOP + 4096,
            bytes.len() as u64,
            memory_size as u64,
        ),
    ] {
        elf[offset..offset + 4].copy_from_slice(&1u32.to_le_bytes()); // PT_LOAD
        elf[offset + 4..offset + 8].copy_from_slice(&flags.to_le_bytes());
        for (field, value) in [
            (8, file_offset),
            (16, address),
            (24, address),
            (32, file_size),
            (40, mem_size),
            (48, 4),
        ] {
            elf[offset + field..offset + field + 8].copy_from_slice(&value.to_le_bytes());
        }
    }
    elf[176..180].copy_from_slice(&0x0000_0013u32.to_le_bytes()); // ADDI x0,x0,0
    elf[180..].copy_from_slice(bytes);
    elf
}

#[test]
fn loader_preserves_file_bytes_when_zero_fill_shares_a_word() {
    for length in 1..=16 {
        let bytes: Vec<u8> = (1..=length as u8).collect();
        let program = Program::from(&elf_with_zero_fill(&bytes, 24)).unwrap();
        let mut expected = [0u8; 24];
        expected[..length].copy_from_slice(&bytes);
        for (index, word) in expected.chunks_exact(8).enumerate() {
            assert_eq!(
                program.memory_image[&(STACK_TOP + 4096 + 8 * index as u64)],
                u64::from_le_bytes(word.try_into().unwrap()),
                "file length {length}, word {index}"
            );
        }
    }
}

#[test]
fn initialization_events_do_not_add_an_empty_trailing_word() {
    // Unlike HINT_READ, this helper emits only occupied words. Preserve that distinction.
    for length in 0usize..=24 {
        let bytes: Vec<u8> = (1..=length as u8).collect();
        let events = chunked_memory_init_events(STACK_TOP, &bytes);
        assert_eq!(events.len(), length.div_ceil(8));
        for (index, event) in events.iter().enumerate() {
            let expected = bytes[index * 8..]
                .iter()
                .take(8)
                .enumerate()
                .fold(0u64, |word, (byte, value)| {
                    word | (u64::from(*value) << (8 * byte))
                });
            assert_eq!(event.addr, STACK_TOP + 8 * index as u64);
            assert_eq!(event.value, expected);
        }
    }
}

fn run(program: Program, hint: Option<&[u8]>) -> MinimalExecutor<SupervisorMode> {
    let mut executor = MinimalExecutor::<SupervisorMode>::new(Arc::new(program), false, Some(1024));
    if let Some(bytes) = hint {
        executor.with_input(bytes);
    }
    // Bounded even if a bad control-flow change stops reaching HALT.
    for _ in 0..4 {
        if executor.execute_chunk().is_none() {
            assert!(executor.is_done());
            assert_eq!(executor.exit_code(), 0);
            return executor;
        }
    }
    panic!("short regression program failed to halt");
}

#[test]
fn executor_sign_extends_auipc_and_jumps_at_wide_pc_bases() {
    // Linux x86 CI executes the JIT fixes; macOS exercises the portable implementation.
    for base in [STACK_TOP, 0x8000_0000] {
        let negative = 0xffff_ffff_8000_0000;
        let program = Program::new(
            vec![
                Instruction::new(Opcode::AUIPC, 6, negative, 0, true, true),
                Instruction::new(Opcode::AUIPC, 7, 0, 0, true, true),
                Instruction::new(Opcode::ADDI, 7, 7, 16, false, true),
                Instruction::new(Opcode::JALR, 0, 7, 0, false, true),
                Instruction::new(Opcode::ADDI, 6, 0, 123, false, true), // must be skipped
                Instruction::new(Opcode::ECALL, 5, 10, 11, false, false), // x5 = HALT
            ],
            base,
            base,
        );
        let executor = run(program, None);
        assert_eq!(executor.registers()[6], base.wrapping_add(negative));
        assert_eq!(executor.registers()[7], base + 20);
        assert_eq!(executor.registers()[0], 0);
    }
}

#[test]
fn hint_read_always_writes_its_final_padded_word() {
    let address = STACK_TOP + 4096;
    for length in [0usize, 1, 7, 8, 9, 16] {
        let bytes: Vec<u8> = (1..=length as u8).collect();
        let mut program = Program::new(
            vec![
                Instruction::new(Opcode::LUI, 10, address, 0, true, true),
                Instruction::new(Opcode::ADDI, 11, 0, length as u64, false, true),
                Instruction::new(
                    Opcode::ADDI,
                    5,
                    0,
                    SyscallCode::HINT_READ as u64,
                    false,
                    true,
                ),
                Instruction::new(Opcode::ECALL, 5, 10, 11, false, false),
                Instruction::new(Opcode::ADDI, 5, 0, 0, false, true),
                Instruction::new(Opcode::ADDI, 10, 0, 0, false, true), // HALT success
                Instruction::new(Opcode::ECALL, 5, 10, 11, false, false),
            ],
            STACK_TOP,
            STACK_TOP,
        );
        let word_count = length / 8 + 1;
        for index in 0..=word_count {
            Arc::make_mut(&mut program.memory_image).insert(address + 8 * index as u64, u64::MAX);
        }
        let executor = run(program, Some(&bytes));
        let mut expected = bytes.clone();
        expected.resize(word_count * 8, 0);
        for (index, word) in expected.chunks_exact(8).enumerate() {
            assert_eq!(
                executor.get_memory_value(address + 8 * index as u64).value,
                u64::from_le_bytes(word.try_into().unwrap()),
                "hint length {length}, word {index}"
            );
        }
        assert_eq!(
            executor
                .get_memory_value(address + 8 * word_count as u64)
                .value,
            u64::MAX
        );
    }
}

#[test]
fn remw_overflow_clears_a_nonzero_previous_remainder() {
    // Default Linux x86 runs the JIT; mprotect and macOS use released portable execution.
    let program = Program::new(
        vec![
            Instruction::new(Opcode::ADDI, 1, 0, 100, false, true),
            Instruction::new(Opcode::ADDI, 2, 0, 7, false, true),
            Instruction::new(Opcode::LUI, 3, 0xffff_ffff_8000_0000, 0, true, true),
            Instruction::new(Opcode::ADDI, 4, 0, u64::MAX, false, true),
            Instruction::new(Opcode::REMW, 6, 1, 2, false, false),
            Instruction::new(Opcode::REMW, 7, 3, 4, false, false),
            Instruction::new(Opcode::DIVW, 8, 3, 4, false, false),
            Instruction::new(Opcode::ECALL, 5, 10, 11, false, false),
        ],
        STACK_TOP,
        STACK_TOP,
    );
    let executor = run(program, None);
    assert_eq!(executor.registers()[6], 2);
    assert_eq!(executor.registers()[7], 0);
    assert_eq!(executor.registers()[8], 0xffff_ffff_8000_0000);
}

#[test]
fn verify_ignores_invalid_pointers_and_preserves_the_hint_queue() {
    let address = STACK_TOP + 4096;
    for (key, values) in [
        (0, 0),
        (u64::MAX, u64::MAX),
        (address, address),
        (address + 1, address + 32),
    ] {
        let mut code = vec![];
        execution::syscall(&mut code, SyscallCode::VERIFY_SP1_PROOF, key, values);
        code.push(Instruction::new(Opcode::ADDI, 6, 5, 0, false, true));
        execution::syscall(&mut code, SyscallCode::HINT_READ, address, 3);
        execution::syscall(&mut code, SyscallCode::HALT, 0, 0);
        let mut program = Program::new(code, STACK_TOP, STACK_TOP);
        Arc::make_mut(&mut program.memory_image).insert(address + 8, u64::MAX);
        // Trace the chunk too: VERIFY must ignore these pointers in constrained replay,
        // while preserving its ordinary return-register write.
        let (executor, records) = execution::run(program, &[vec![7, 8, 9]]);
        assert_eq!(executor.exit_code(), 0);
        assert_eq!(records.len(), 1);
        assert_eq!(records[0].syscall_events.len(), 3);
        let (event, access) = records[0].syscall_events[0];
        assert_eq!(event.syscall_code, SyscallCode::VERIFY_SP1_PROOF);
        assert_eq!((event.arg1, event.arg2), (key, values));
        match access.a {
            sp1_core_executor::events::MemoryRecordEnum::Write(write) => {
                assert_eq!(write.value, SyscallCode::VERIFY_SP1_PROOF as u64)
            }
            _ => panic!("VERIFY must retain its syscall result write"),
        }
        assert_eq!(
            executor.registers()[6],
            SyscallCode::VERIFY_SP1_PROOF as u64
        );
        assert_eq!(executor.get_memory_value(address).value, 0x090807);
        assert_eq!(executor.get_memory_value(address + 8).value, u64::MAX);
    }
}

#[test]
fn default_release_status_policy_rejects_every_sampled_nonzero_exit() {
    use sp1_core_executor::StatusCode;
    assert!(StatusCode::SUCCESS.is_accepted_code(0));
    assert!(StatusCode::ANY.is_accepted_code(0));
    for code in [1, 2, 3, 65536, u32::MAX] {
        assert!(!StatusCode::ANY.is_accepted_code(code));
        assert!(!StatusCode::SUCCESS.is_accepted_code(code));
    }
    assert!(!StatusCode::PANIC.is_accepted_code(1));
    assert!(!StatusCode::INVALID_HINT.is_accepted_code(3));
}
