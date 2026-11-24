//! Native immutable queue allocation, from supplied bytes through the real demand scheduler.
//! The arbitrary hook responses are host inputs. Released execution independently checks
//! the direct WRITE and the HINT_READ layout of every supplied buffer.

extern crate alloc;

#[path = "support/backend.rs"]
mod backend;
#[path = "support/execution.rs"]
mod execution;

use backend::{assert_backend_rejection, config, fixed_trace, physical_reference};
use clean_backend::{witness_generation::Program as WitnessProgram, EnsembleKey, GeneratedAirSpec};
use p3_field::{PrimeCharacteristicRing, PrimeField64};
use p3_koala_bear::KoalaBear as F;
use p3_matrix::Matrix;
use serde::Deserialize;
use sp1_core_executor::{Program, SyscallCode};
use std::sync::Arc;

#[allow(dead_code, unused_imports, unused_variables, unused_parens)]
mod generated {
    include!(concat!(
        env!("CLEAN_ENSEMBLE_EXPORT_DIR"),
        "/write_allocation.rs"
    ));
}

const DIRECT: &[u8] = &[16, 32, 48, 64, 80, 96, 112, 128, 144];
const RETURNED: [&[u8]; 3] = [&[], &[1, 2, 3, 4, 5, 6, 7, 8], &[254, 253, 252]];
const BLOCK: &str = "sp1.native.write_stream_blocks";
const WORD: &str = "sp1.native.hint_word";
const NODE: &str = "sp1.native.hint_node";
const CONTENTS: &str = "sp1.native.hint_allocation_contents";
const TICKET: &str = "sp1.native.write_queue_effect";

#[derive(Deserialize)]
struct Fixture {
    public: Vec<u64>,
    private: Vec<u64>,
    heights: Vec<usize>,
    witness: serde_json::Value,
}

fn fixture() -> (Vec<F>, Vec<F>, Vec<usize>, serde_json::Value) {
    let fixture: Fixture = serde_json::from_str(include_str!(concat!(
        env!("CLEAN_ENSEMBLE_EXPORT_DIR"),
        "/write_allocation.reference.json"
    )))
    .unwrap();
    (
        fixture.public.into_iter().map(F::from_u64).collect(),
        fixture.private.into_iter().map(F::from_u64).collect(),
        fixture.heights,
        fixture.witness,
    )
}

fn limbs(value: u64, n: usize) -> Vec<u64> {
    (0..n).map(|i| (value >> (16 * i)) & 65535).collect()
}

fn signed_rows(tables: &[Vec<Vec<F>>], table: usize, channel: &str) -> Vec<(u64, Vec<u64>)> {
    tables[table]
        .iter()
        .flat_map(|row| {
            <generated::Ensemble as WitnessProgram<F>>::interactions(table, row).into_iter()
        })
        .filter(|entry| entry.channel == channel)
        .map(|entry| {
            (
                entry.signed_multiplicity().as_canonical_u64(),
                entry
                    .message
                    .iter()
                    .map(PrimeField64::as_canonical_u64)
                    .collect(),
            )
        })
        .collect()
}

fn nonzero(mut rows: Vec<(u64, Vec<u64>)>) -> Vec<(u64, Vec<u64>)> {
    rows.retain(|(weight, _)| *weight != 0);
    rows.sort();
    rows
}

fn word_record(pointer: u64, index: usize, bytes: &[u8]) -> Vec<u64> {
    let rest = &bytes[8 * index..];
    let used = rest.len().min(8);
    let mut padded = [0u8; 8];
    padded[..used].copy_from_slice(&rest[..used]);
    [
        limbs(pointer, 3),
        limbs(index as u64, 3),
        limbs(u64::from_le_bytes(padded), 4),
        vec![u64::from(index == bytes.len() / 8)],
    ]
    .concat()
}

fn allocations() -> Vec<&'static [u8]> {
    std::iter::once(DIRECT)
        .chain(RETURNED.into_iter().rev())
        .collect()
}

#[test]
fn direct_and_hook_allocations_bind_every_record_and_keep_padding_occurrences() {
    let (public, private, heights, physical) = fixture();
    let w = generated::generate::<F>(&public, &private, 1).unwrap();
    assert_eq!(
        public
            .iter()
            .map(PrimeField64::as_canonical_u64)
            .collect::<Vec<_>>(),
        [0, 273, 4, 0, 0, 4, 0, 0]
    );
    assert_eq!(heights, [4, 4, 4, 8, 16, 4, 8]);
    assert_eq!(w.tables.iter().map(Vec::len).collect::<Vec<_>>(), heights);
    assert_eq!(
        physical_reference::<generated::Ensemble>(&public, &w.tables),
        physical
    );
    let minus = (-F::ONE).as_canonical_u64();
    let mut nodes = Vec::new();
    let mut words = Vec::new();
    let mut blocks = Vec::new();
    let mut contents = Vec::new();
    for (i, bytes) in allocations().iter().enumerate() {
        let pointer = i as u64 + 1;
        nodes.push((
            1,
            [
                limbs(pointer, 3),
                limbs(pointer - 1, 3),
                limbs(bytes.len() as u64, 4),
            ]
            .concat(),
        ));
        let hint = if i == 0 { 0 } else { 3 - i as u64 };
        contents.push((
            1,
            [
                vec![u64::from(i == 0)],
                limbs(pointer, 3),
                limbs(0, 3),
                limbs(hint, 3),
                limbs(bytes.len() as u64, 3),
            ]
            .concat(),
        ));
        for index in 0..=bytes.len() / 8 {
            words.push((1, word_record(pointer, index, bytes)));
            let part = &bytes[8 * index..];
            let used = part.len().min(8);
            if used > 0 {
                let mut lanes = vec![0; 8];
                for (slot, byte) in part.iter().take(8).enumerate() {
                    lanes[slot] = u64::from(*byte);
                }
                blocks.push((
                    if i == 0 { 1 } else { minus },
                    [
                        vec![if i == 0 { 14 } else { 4 }],
                        limbs(if i == 0 { pointer } else { 0 }, 3),
                        limbs(hint, 3),
                        limbs(index as u64, 3),
                        vec![used as u64],
                        lanes,
                    ]
                    .concat(),
                ));
            }
        }
    }
    assert_eq!(nonzero(signed_rows(&w.tables, 1, NODE)), nonzero(nodes));
    assert_eq!(
        nonzero(signed_rows(&w.tables, 1, CONTENTS)),
        nonzero(contents.clone())
    );
    for (weight, _) in &mut contents {
        *weight = minus;
    }
    assert_eq!(
        nonzero(signed_rows(&w.tables, 2, CONTENTS)),
        nonzero(contents)
    );
    assert_eq!(nonzero(signed_rows(&w.tables, 3, WORD)), nonzero(words));
    let physical = signed_rows(&w.tables, 3, BLOCK);
    assert_eq!(physical.len(), 2 * heights[3]);
    assert_eq!(nonzero(physical), nonzero(blocks.clone()));
    let fixed = fixed_trace::<generated::Ensemble>(5);
    for (_, block) in blocks.iter().filter(|(_, block)| block[0] == 4) {
        let expected: Vec<_> = block.iter().copied().chain([1]).map(F::from_u64).collect();
        assert!(fixed
            .values
            .chunks(fixed.width())
            .any(|row| row == expected));
    }
    let tickets: Vec<_> = [(257, 1, 1, 9, 0), (265, 0, 0, 1, 3), (273, 0, 1, 0, 0)]
        .into_iter()
        .map(|(clock, d, owner, n, replies)| {
            (
                minus,
                [
                    limbs(clock, 3),
                    vec![d],
                    limbs(owner, 3),
                    limbs(n, 3),
                    limbs(replies, 3),
                ]
                .concat(),
            )
        })
        .collect();
    assert_eq!(nonzero(signed_rows(&w.tables, 0, TICKET)), nonzero(tickets));
}

#[test]
fn released_direct_write_and_hint_read_reproduce_every_padded_word() {
    let (public, private, _, _) = fixture();
    let tables = generated::generate::<F>(&public, &private, 1)
        .unwrap()
        .tables;
    let published = nonzero(signed_rows(&tables, 3, WORD));
    let source = 262144u64;
    let mut instructions = Vec::new();
    execution::load_constant(&mut instructions, 12, DIRECT.len() as u64);
    execution::syscall(
        &mut instructions,
        SyscallCode::WRITE,
        (1u64 << 32) + 14,
        source,
    );
    // The released direct WRITE prepends its bytes to the preloaded opaque replies.
    let read_order: Vec<_> = std::iter::once((1u64, DIRECT))
        .chain(
            RETURNED
                .into_iter()
                .enumerate()
                .map(|(i, b)| (4 - i as u64, b)),
        )
        .collect();
    for (pointer, bytes) in &read_order {
        execution::syscall(
            &mut instructions,
            SyscallCode::HINT_READ,
            source + 64 * pointer,
            bytes.len() as u64,
        );
    }
    execution::syscall(&mut instructions, SyscallCode::HALT, 0, 0);
    let mut program = Program::new(instructions, 65536, 65536);
    for (i, chunk) in DIRECT.chunks(8).enumerate() {
        let mut lanes = [0u8; 8];
        lanes[..chunk.len()].copy_from_slice(chunk);
        Arc::make_mut(&mut program.memory_image)
            .insert(source + 8 * i as u64, u64::from_le_bytes(lanes));
    }
    let (executor, _) = execution::run(program, &RETURNED.map(<[u8]>::to_vec));
    let mut released = Vec::new();
    for (pointer, bytes) in read_order {
        for index in 0..=bytes.len() / 8 {
            let value = executor
                .get_memory_value(source + 64 * pointer + 8 * index as u64)
                .value;
            released.push((
                1,
                [
                    limbs(pointer, 3),
                    limbs(index as u64, 3),
                    limbs(value, 4),
                    vec![u64::from(index == bytes.len() / 8)],
                ]
                .concat(),
            ));
        }
    }
    assert_eq!(published, nonzero(released));
}

#[test]
fn backend_rejects_mutated_content_owner_tail_and_public_clock() {
    let (public, private, heights, _) = fixture();
    let w = generated::generate::<F>(&public, &private, 1).unwrap();
    let traces = w.into_traces().unwrap();
    let statement = generated::Statement::<F>::new(&heights, 1).unwrap();
    let mut key = EnsembleKey::new(config(), 1).unwrap();
    let proof = key.prove(&statement, traces.clone(), &public).unwrap();
    key.verify(&statement, &proof, &public).unwrap();
    // Locate genuine rows by their actual semantic payload, independently of scheduler order.
    let supplied = traces[3]
        .values
        .chunks(traces[3].width())
        .position(|row| row[1] == F::from_u64(2) && row[13] == F::ZERO)
        .unwrap();
    let direct = traces[3]
        .values
        .chunks(traces[3].width())
        .position(|row| row[0] == F::ONE && row[13] == F::ZERO)
        .unwrap();
    let aligned_tail = traces[3]
        .values
        .chunks(traces[3].width())
        .position(|row| row[1] == F::from_u64(3) && row[13] == F::ONE)
        .unwrap();
    for (table, row, col) in [
        (3, supplied, 28),
        (3, direct, 28),
        (3, supplied, 4),
        (3, aligned_tail, 36),
        (1, 0, 11),
        (0, 0, 0),
    ] {
        let mut corrupted = traces.clone();
        let width = corrupted[table].width();
        let input_width = [
            generated::component_0::INPUT_WIDTH,
            generated::component_1::INPUT_WIDTH,
            generated::component_2::INPUT_WIDTH,
            generated::component_3::INPUT_WIDTH,
        ][table];
        let first = row * width;
        let mut altered = corrupted[table].values[first..first + input_width].to_vec();
        altered[col] += F::ONE;
        let data = clean_backend::witness_generation::WitnessData::from_entries(vec![]);
        let full =
            <generated::Ensemble as WitnessProgram<F>>::complete_row(table, &altered, &data, &data)
                .unwrap();
        // Content and hook-owner substitutions are locally well-formed even after full
        // auxiliary regeneration. Their failure requires the joined channel statement.
        if table == 3 && row != aligned_tail {
            assert!(generated::Ensemble::constraints::<F>(table, &full)
                .into_iter()
                .all(|v| v == F::ZERO));
        }
        corrupted[table].values[first..first + width].copy_from_slice(&full);
        assert_backend_rejection(|| {
            let proof = key.prove(&statement, corrupted, &public).unwrap();
            key.verify(&statement, &proof, &public).is_err()
        });
    }
    let mut wrong = public;
    wrong[1] += F::ONE;
    assert!(key.verify(&statement, &proof, &wrong).is_err());
}
