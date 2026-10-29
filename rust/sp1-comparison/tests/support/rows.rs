//! Shared row comparisons against released SP1, preserving every physical interaction.

use super::export_support::{Ledger, RowWitness, Sp1Evaluation};
use clean_backend::witness_generation::{generate, Program, WitnessGenerationError};
use clean_backend::GeneratedAirSpec;
use p3_field::{PrimeCharacteristicRing, PrimeField64};
use p3_koala_bear::KoalaBear as NativeField;
use slop_air::Air;
use slop_algebra::{AbstractField, PrimeField64 as Sp1PrimeField64};
use slop_matrix::{dense::RowMajorMatrix, Matrix};
use sp1_core_executor::ExecutionRecord;
use sp1_hypercube::air::{MachineAir, SP1_PROOF_NUM_PV_ELTS};
use sp1_primitives::SP1Field;

pub fn compare<P: Program<NativeField> + GeneratedAirSpec>(
    sp1: &[SP1Field],
    row: &[NativeField],
    chip: &impl Air<Sp1Evaluation>,
    case: &str,
) -> bool {
    let mut expected = Sp1Evaluation {
        row: sp1.to_vec(),
        preprocessed: vec![],
        constraints: vec![],
        ledger: vec![],
        public: vec![SP1Field::zero(); SP1_PROOF_NUM_PV_ELTS],
    };
    chip.eval(&mut expected);
    let constraints = P::constraints::<NativeField>(0, row);
    assert!(!constraints.is_empty() && !expected.constraints.is_empty());
    let valid = constraints.iter().all(|value| *value == NativeField::ZERO);
    assert_eq!(
        valid,
        expected
            .constraints
            .iter()
            .all(|value| *value == SP1Field::zero()),
        "local constraint satisfaction differs: {case}"
    );
    let mut ledger: Ledger = <P as Program<NativeField>>::interactions(0, row)
        .into_iter()
        .map(|value| {
            (
                value.channel.to_owned(),
                value.multiplicity.as_canonical_u64(),
                value
                    .message
                    .iter()
                    .map(PrimeField64::as_canonical_u64)
                    .collect(),
            )
        })
        .collect();
    // Sorting preserves every occurrence; never filter zeros or combine repeated messages.
    ledger.sort();
    expected.ledger.sort();
    assert_eq!(
        ledger, expected.ledger,
        "complete component interaction multiset differs: {case}"
    );
    valid
}

pub fn check_trace<P: Program<NativeField> + GeneratedAirSpec>(
    trace: &RowMajorMatrix<SP1Field>,
    map_row: fn(&[SP1Field]) -> Vec<NativeField>,
    chip: &impl Air<Sp1Evaluation>,
) {
    assert_eq!(
        <NativeField as PrimeField64>::ORDER_U64,
        <SP1Field as Sp1PrimeField64>::ORDER_U64
    );
    assert_eq!(P::WIDTHS, &[trace.width()]);
    assert_eq!(<P as Program<NativeField>>::FIXED_WIDTHS, &[0]);
    for (index, sp1) in trace.values.chunks(trace.width()).enumerate() {
        let row = map_row(sp1);
        let input = &row[..P::PROVER_INPUTS];
        let witness = generate::<NativeField, RowWitness<P>>(&[], input).unwrap();
        assert_eq!(
            witness.tables,
            vec![vec![row.clone()]],
            "witness row {index}"
        );
        assert!(
            compare::<P>(sp1, &row, chip, &format!("SP1 row {index}")),
            "SP1 row {index} must satisfy both AIRs"
        );
    }
}

pub fn check_mutations<P: Program<NativeField> + GeneratedAirSpec>(
    trace: &RowMajorMatrix<SP1Field>,
    indices: &[usize],
    map_row: fn(&[SP1Field]) -> Vec<NativeField>,
    chip: &impl Air<Sp1Evaluation>,
) {
    let mut rejected = 0;
    for &index in indices {
        let original = trace.row_slice(index);
        for column in 0..trace.width() {
            for delta in [1, 65536, <SP1Field as Sp1PrimeField64>::ORDER_U64 - 1] {
                let mut row = original.to_vec();
                row[column] += SP1Field::from_canonical_u64(delta);
                rejected += usize::from(!compare::<P>(
                    &row,
                    &map_row(&row),
                    chip,
                    &format!("SP1 row {index}, column {column}, delta {delta}"),
                ));
            }
        }
    }
    assert!(
        rejected > 0,
        "the mutation battery must exercise rejected constraints"
    );
}

pub fn check_open_buses<P: Program<NativeField>>(row: &[NativeField]) {
    let input = &row[..P::PROVER_INPUTS];
    let error = generate::<NativeField, P>(&[], input).unwrap_err();
    assert!(matches!(error, WitnessGenerationError::Runtime(_)));
    assert!(matches!(
        generate::<NativeField, RowWitness<P>>(&[], &input[..input.len() - 1]),
        Err(WitnessGenerationError::ProverInputWidth { .. })
    ));
}

/// Every adapter is an independently checked permutation of the released SP1 layout.
pub fn reorder<P: Program<NativeField> + GeneratedAirSpec>(
    sp1: &[SP1Field],
    input_width: usize,
    indices: impl IntoIterator<Item = usize>,
) -> Vec<NativeField> {
    assert_eq!(P::WIDTHS, &[sp1.len()]);
    assert_eq!(P::PROVER_INPUTS, input_width);
    let indices: Vec<_> = indices.into_iter().collect();
    let mut sorted = indices.clone();
    sorted.sort_unstable();
    assert_eq!(sorted, (0..sp1.len()).collect::<Vec<_>>());
    indices
        .into_iter()
        .map(|i| NativeField::from_u64(sp1[i].as_canonical_u64()))
        .collect()
}

pub fn padded_trace<C>(
    chip: &C,
    record: &ExecutionRecord,
    active: usize,
) -> RowMajorMatrix<SP1Field>
where
    C: MachineAir<SP1Field, Record = ExecutionRecord, Program = sp1_core_executor::Program>,
{
    let trace = chip.generate_trace(record, &mut ExecutionRecord::default());
    assert_eq!(trace.width(), chip.width());
    assert_eq!(trace.height(), active.div_ceil(32) * 32);
    assert!(
        active > 0 && trace.height() > active,
        "exercise active and padding rows"
    );
    trace
}

/// New families mutate every column of every event and padding row.
pub fn check_all_rows<P: Program<NativeField> + GeneratedAirSpec>(
    trace: &RowMajorMatrix<SP1Field>,
    map_row: fn(&[SP1Field]) -> Vec<NativeField>,
    chip: &impl Air<Sp1Evaluation>,
) {
    check_trace::<P>(trace, map_row, chip);
    check_mutations::<P>(
        trace,
        &(0..trace.height()).collect::<Vec<_>>(),
        map_row,
        chip,
    );
    check_open_buses::<P>(&map_row(&trace.row_slice(0)));
}
