//! Compare installed bump components with released SP1 trace generation and AIR.
//! All cells are inputs here: witness equality does not claim execution-to-row generation.

extern crate alloc;

#[path = "support/export.rs"]
mod export_support;
#[path = "support/rows.rs"]
mod row_support;

use p3_koala_bear::KoalaBear as NativeField;
use row_support::{check_all_rows, compare, padded_trace, reorder};
use slop_algebra::AbstractField;
use sp1_core_executor::{
    events::{MemoryReadRecord, MemoryRecordEnum, MemoryWriteRecord},
    ExecutionRecord,
};
use sp1_core_machine::{
    adapter::bump::{StateBumpChip, StateBumpCols},
    memory::{MemoryBumpChip, MemoryBumpCols},
};
use sp1_primitives::SP1Field;
use std::borrow::BorrowMut;

// Unused shared helpers are emitted by Clean for individual components as well as ensembles.
macro_rules! generated_system {
    ($module:ident, $file:literal, $program:ident) => {
        #[allow(dead_code, unused_imports, unused_variables, unused_parens)]
        mod $module {
            include!(concat!(env!("CLEAN_ENSEMBLE_EXPORT_DIR"), "/", $file));
        }
        use $module::Ensemble as $program;
    };
}
generated_system!(memory_bump, "memory_bump.rs", MemoryBump);
generated_system!(state_bump, "state_bump.rs", StateBump);

fn memory_row(row: &[SP1Field]) -> Vec<NativeField> {
    // Both carriers use the released MemoryAccessCols followed by timestamp limbs, address and gate.
    reorder::<MemoryBump>(row, 15, 0..row.len())
}

fn state_row(row: &[SP1Field]) -> Vec<NativeField> {
    reorder::<StateBump>(row, 14, 0..row.len())
}

#[test]
fn memory_refresh_and_bump_rows_match_released_sp1() {
    let mut record = ExecutionRecord::default();
    let cases = [
        (1, 9, true),
        ((1 << 24) - 9, (1 << 24) - 1, true),
        ((1 << 24) - 1, (1 << 24) + 1, true),
        ((1 << 48) - 9, (1 << 48) - 1, true),
        (1, (1 << 24) + 9, false),
        ((1 << 24) - 1, (1 << 24) + 264, false),
        ((1 << 32) - 1, (1 << 32) + 9, false),
        ((1 << 48) - (1 << 24) - 1, (1 << 48) - 1, false),
    ];
    for (index, (prev_timestamp, timestamp, is_refresh)) in cases.into_iter().enumerate() {
        for addr in [0, 1, 31] {
            let prev_value = 0xfedc_ba98_7654_3210 ^ (addr << 16) ^ index as u64;
            let event = if index % 2 == 0 {
                MemoryRecordEnum::Read(MemoryReadRecord {
                    value: prev_value,
                    prev_timestamp,
                    timestamp,
                    prev_page_prot_record: None,
                })
            } else {
                // A bump preserves the old value, even when the originating event is a write.
                MemoryRecordEnum::Write(MemoryWriteRecord {
                    value: !prev_value,
                    prev_value,
                    prev_timestamp,
                    timestamp,
                    prev_page_prot_record: None,
                })
            };
            record.bump_memory_events.push((event, addr, is_refresh));
        }
    }
    let chip = MemoryBumpChip::new();
    let trace = padded_trace(&chip, &record, record.bump_memory_events.len());
    check_all_rows::<MemoryBump>(&trace, memory_row, &chip);
}

#[test]
fn state_clock_and_pc_carries_match_released_sp1() {
    let record = ExecutionRecord {
        bump_state_events: vec![
            (1, 0, false, 0),
            (1, 8, false, 4),
            ((1 << 24) - 7, 8, false, 0x1234),
            ((1 << 24) - 263, 264, true, 1 << 16),
            ((1 << 32) - 7, 8, true, 1 << 32),
            ((1 << 48) - 15, 8, true, (1 << 48) - 4),
            ((1 << 40) + 1, 264, false, 0x1234_5678_9abc),
        ],
        ..Default::default()
    };
    let chip = StateBumpChip::new();
    let trace = padded_trace(&chip, &record, record.bump_state_events.len());
    check_all_rows::<StateBump>(&trace, state_row, &chip);
}

#[test]
fn memory_padding_leaves_timestamp_comparison_gated() {
    let mut row = vec![SP1Field::zero(); 15];
    let cols: &mut MemoryBumpCols<SP1Field> = row.as_mut_slice().borrow_mut();
    cols.access.access_timestamp.compare_low = SP1Field::from_canonical_u8(2);
    assert!(compare::<MemoryBump>(
        &row,
        &memory_row(&row),
        &MemoryBumpChip::new(),
        "inactive memory row permits a nonboolean comparison selector"
    ));
}

#[test]
fn state_padding_preserves_the_ungated_pc_carry_contract() {
    let chip = StateBumpChip::new();
    let mut row = vec![SP1Field::zero(); 14];
    let cols: &mut StateBumpCols<SP1Field> = row.as_mut_slice().borrow_mut();
    cols.pc[0] = SP1Field::one();
    assert!(!compare::<StateBump>(
        &row,
        &state_row(&row),
        &chip,
        "inactive state row still rejects a changed PC"
    ));
    let cols: &mut StateBumpCols<SP1Field> = row.as_mut_slice().borrow_mut();
    cols.pc[0] = SP1Field::from_canonical_u32(65536);
    cols.next_pc[1] = SP1Field::one();
    assert!(compare::<StateBump>(
        &row,
        &state_row(&row),
        &chip,
        "inactive state row accepts a value-preserving PC carry"
    ));
}
