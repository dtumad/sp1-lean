//! Compare Clean's generated instruction code directly with the released SP1 Rust AIR.
//! These are component tests: global provider balance and lowering correctness are separate claims.

extern crate alloc;

use clean_backend::witness_generation::{
    generate, Interaction, Mode, Padding, Program, WitnessData, WitnessGenerationError,
};
use clean_backend::GeneratedAirSpec;
use p3_field::{PrimeCharacteristicRing, PrimeField64};
use p3_koala_bear::KoalaBear as NativeField;
use slop_air::{Air, AirBuilder, AirBuilderWithPublicValues, BaseAir};
use slop_algebra::{AbstractField, PrimeField64 as Sp1PrimeField64};
use slop_matrix::{dense::RowMajorMatrix, Matrix};
use sp1_core_executor::{
    events::{AluEvent, MemInstrEvent, MemoryReadRecord, MemoryRecordEnum, MemoryWriteRecord},
    get_quotient_and_remainder, ExecutionRecord, ITypeRecord, Opcode, RTypeRecord,
};
use sp1_core_machine::{
    air::TrivialOperationBuilder,
    alu::{
        add_sub::add::AddChip,
        divrem::{DivRemChip, DivRemCols},
        mul::{MulChip, MulCols},
    },
    memory::load::load_byte::{LoadByteChip, LoadByteColumns},
    SupervisorMode,
};
use sp1_hypercube::{
    air::{AirInteraction, InteractionScope, MachineAir, MessageBuilder, SP1_PROOF_NUM_PV_ELTS},
    InteractionKind,
};
use sp1_primitives::SP1Field;
use std::marker::PhantomData;
use std::mem::offset_of;

// Clean emits a shared helper set; this instruction does not need every helper.
#[allow(dead_code, unused_imports, unused_variables, unused_parens)]
mod generated_add {
    include!(concat!(
        env!("CLEAN_ENSEMBLE_EXPORT_DIR"),
        "/add_instruction.rs"
    ));
}
use generated_add::{AddInstruction, AddInstructionAirSpec};

// The same upstream helper set is emitted for each standalone component.
#[allow(dead_code, unused_imports, unused_variables, unused_parens)]
mod generated_load_byte {
    include!(concat!(
        env!("CLEAN_ENSEMBLE_EXPORT_DIR"),
        "/load_byte_instruction.rs"
    ));
}
use generated_load_byte::{LoadByteInstruction, LoadByteInstructionAirSpec};

#[allow(dead_code, unused_imports, unused_variables, unused_parens)]
mod generated_div_rem {
    include!(concat!(
        env!("CLEAN_ENSEMBLE_EXPORT_DIR"),
        "/div_rem_instruction.rs"
    ));
}
use generated_div_rem::{DivRemInstruction, DivRemInstructionAirSpec};

#[allow(dead_code, unused_imports, unused_variables, unused_parens)]
mod generated_mul {
    include!(concat!(
        env!("CLEAN_ENSEMBLE_EXPORT_DIR"),
        "/mul_instruction.rs"
    ));
}
use generated_mul::{MulInstruction, MulInstructionAirSpec};

type Ledger = Vec<(String, u64, Vec<u64>)>;

/// SP1 supplies the actual expressions; this builder records their field evaluations.
struct Sp1Evaluation {
    row: Vec<SP1Field>,
    constraints: Vec<SP1Field>,
    ledger: Ledger,
    public: Vec<SP1Field>,
}

impl AirBuilder for Sp1Evaluation {
    type F = SP1Field;
    type Expr = SP1Field;
    type Var = SP1Field;
    type M = RowMajorMatrix<SP1Field>;
    fn main(&self) -> Self::M {
        RowMajorMatrix::new(self.row.clone(), self.row.len())
    }
    fn is_first_row(&self) -> Self::Expr {
        SP1Field::one()
    }
    fn is_last_row(&self) -> Self::Expr {
        SP1Field::one()
    }
    fn is_transition_window(&self, _: usize) -> Self::Expr {
        panic!("instruction-local comparison must not read adjacent rows")
    }
    fn assert_zero<I: Into<Self::Expr>>(&mut self, value: I) {
        self.constraints.push(value.into());
    }
}
impl AirBuilderWithPublicValues for Sp1Evaluation {
    type PublicVar = SP1Field;
    fn public_values(&self) -> &[SP1Field] {
        &self.public
    }
}
impl TrivialOperationBuilder for Sp1Evaluation {}

impl Sp1Evaluation {
    fn interaction(
        &mut self,
        interaction: AirInteraction<SP1Field>,
        scope: InteractionScope,
        receiving: bool,
    ) {
        assert_eq!(scope, InteractionScope::Local);
        // Clean's State direction agrees with SP1. Byte, Memory and Program orient
        // guarantees from providers to consumers, reversing SP1's send/receive signs.
        let (channel, reverse) = match interaction.kind {
            InteractionKind::State => ("SP1State", false),
            InteractionKind::Byte => ("SP1Byte", true),
            InteractionKind::Memory => ("SP1Memory", true),
            InteractionKind::Program => ("SP1Program", true),
            other => panic!("unmapped SP1 instruction interaction: {other:?}"),
        };
        let mult = if receiving ^ reverse {
            -interaction.multiplicity
        } else {
            interaction.multiplicity
        };
        self.ledger.push((
            channel.to_owned(),
            mult.as_canonical_u64(),
            interaction
                .values
                .iter()
                .map(Sp1PrimeField64::as_canonical_u64)
                .collect(),
        ));
    }
}
impl MessageBuilder<AirInteraction<SP1Field>> for Sp1Evaluation {
    fn send(&mut self, value: AirInteraction<SP1Field>, scope: InteractionScope) {
        self.interaction(value, scope, false);
    }
    fn receive(&mut self, value: AirInteraction<SP1Field>, scope: InteractionScope) {
        self.interaction(value, scope, true);
    }
}

/// The generated constraint function takes row values directly; no expression interpreter.
struct NativeEvaluation;
impl p3_air::AirBuilder for NativeEvaluation {
    type F = NativeField;
    type Expr = NativeField;
    type Var = NativeField;
    type M = p3_matrix::dense::RowMajorMatrix<NativeField>;
    fn main(&self) -> Self::M {
        unreachable!("generated constraints take an explicit row")
    }
    fn is_first_row(&self) -> Self::Expr {
        unreachable!("flat AIR has no row selectors")
    }
    fn is_last_row(&self) -> Self::Expr {
        unreachable!("flat AIR has no row selectors")
    }
    fn is_transition_window(&self, _: usize) -> Self::Expr {
        unreachable!("flat AIR has no adjacent-row constraints")
    }
    fn assert_zero<I: Into<Self::Expr>>(&mut self, _: I) {
        unreachable!("generated constraints return their values")
    }
}
impl p3_air::AirBuilderWithPublicValues for NativeEvaluation {
    type PublicVar = NativeField;
    fn public_values(&self) -> &[NativeField] {
        &[]
    }
}

/// Use Clean's runtime to construct one row, without satisfying its external buses.
/// Only this test adapter suppresses scheduling interactions. The generated interactions
/// are checked separately against SP1, including repeated and zero-multiplicity entries.
/// The unadapted generated program must still reject an active row with no providers.
struct RowWitness<P>(PhantomData<P>);
impl<P: Program<NativeField>> Program<NativeField> for RowWitness<P> {
    const FUEL: usize = <P as Program<NativeField>>::FUEL;
    const COMPONENTS: usize = <P as Program<NativeField>>::COMPONENTS;
    const PUBLIC_INPUTS: usize = <P as Program<NativeField>>::PUBLIC_INPUTS;
    const PROVER_INPUTS: usize = <P as Program<NativeField>>::PROVER_INPUTS;
    const FIXED_WIDTHS: &'static [usize] = <P as Program<NativeField>>::FIXED_WIDTHS;
    const COMPONENT_NAMES: &'static [&'static str] = <P as Program<NativeField>>::COMPONENT_NAMES;
    fn modes() -> Vec<Mode<NativeField>> {
        P::modes()
    }
    fn padding() -> Vec<Padding<NativeField>> {
        P::padding()
    }
    fn initial_rows(
        component: usize,
        input: &[NativeField],
    ) -> Result<Vec<Vec<NativeField>>, String> {
        P::initial_rows(component, input)
    }
    fn complete_row(
        component: usize,
        input: &[NativeField],
        data: &WitnessData<NativeField>,
    ) -> Result<Vec<NativeField>, String> {
        P::complete_row(component, input, data)
    }
    fn interactions(_: usize, _: &[NativeField]) -> Vec<Interaction<NativeField>> {
        vec![]
    }
    fn verifier_interactions(_: &[NativeField]) -> Vec<Interaction<NativeField>> {
        vec![]
    }
}

fn r_type_event(index: usize, opcode: Opcode, a: u64, b: u64, c: u64) -> (AluEvent, RTypeRecord) {
    let clk = 9 + 8 * index as u64;
    let read = |value, offset| {
        MemoryRecordEnum::Read(MemoryReadRecord {
            value,
            timestamp: clk + offset,
            prev_timestamp: clk - 8,
            prev_page_prot_record: None,
        })
    };
    (
        AluEvent::new(clk, 4096 + 4 * index as u64, opcode, a, b, c, false),
        RTypeRecord {
            op_a: 5,
            op_b: 6,
            op_c: 7,
            is_untrusted: false,
            a: MemoryRecordEnum::Write(MemoryWriteRecord {
                prev_timestamp: clk - 8,
                prev_page_prot_record: None,
                prev_value: 0,
                timestamp: clk + 4,
                value: a,
            }),
            b: read(b, 3),
            c: read(c, 2),
        },
    )
}

fn add_trace() -> RowMajorMatrix<SP1Field> {
    let values = [
        0,
        1,
        65535,
        65536,
        u32::MAX as u64,
        1 << 32,
        (1 << 63) - 1,
        1 << 63,
        u64::MAX,
    ];
    let mut record = ExecutionRecord::default();
    for b in values {
        for c in values {
            record.add_events.push(r_type_event(
                record.add_events.len(),
                Opcode::ADD,
                b.wrapping_add(c),
                b,
                c,
            ));
        }
    }
    let chip = AddChip::<SupervisorMode>::default();
    let trace = chip.generate_trace(&record, &mut ExecutionRecord::default());
    assert_eq!(
        trace.width(),
        <AddChip<SupervisorMode> as BaseAir<SP1Field>>::width(&chip)
    );
    assert_eq!(trace.height(), 96); // 81 independent events and 15 SP1-generated padding rows.
    trace
}

fn add_row(sp1: &[SP1Field]) -> Vec<NativeField> {
    // SP1: state, adapter, result limbs, is_real. Clean: is_real, state, adapter, result limbs.
    assert_eq!(sp1.len(), AddInstructionAirSpec::WIDTHS[0]);
    std::iter::once(sp1.last().unwrap())
        .chain(&sp1[..sp1.len() - 1])
        .map(|value| NativeField::from_u64(value.as_canonical_u64()))
        .collect()
}

fn compare<P: Program<NativeField>, S: GeneratedAirSpec>(
    sp1: &[SP1Field],
    row: &[NativeField],
    chip: &impl Air<Sp1Evaluation>,
    case: &str,
) -> bool {
    let mut expected = Sp1Evaluation {
        row: sp1.to_vec(),
        constraints: vec![],
        ledger: vec![],
        public: vec![SP1Field::zero(); SP1_PROOF_NUM_PV_ELTS],
    };
    chip.eval(&mut expected);
    let constraints = S::constraints::<NativeEvaluation>(0, &[], row);
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
    let mut ledger: Ledger = P::interactions(0, row)
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
        "complete instruction interaction multiset differs: {case}"
    );
    valid
}

fn check_trace<P: Program<NativeField>, S: GeneratedAirSpec>(
    trace: &RowMajorMatrix<SP1Field>,
    map_row: fn(&[SP1Field]) -> Vec<NativeField>,
    chip: &impl Air<Sp1Evaluation>,
) {
    assert_eq!(
        <NativeField as PrimeField64>::ORDER_U64,
        <SP1Field as Sp1PrimeField64>::ORDER_U64
    );
    assert_eq!(S::WIDTHS, &[trace.width()]);
    assert_eq!(S::FIXED_WIDTHS, &[0]);
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
            compare::<P, S>(sp1, &row, chip, &format!("SP1 row {index}")),
            "SP1 row {index} must satisfy both AIRs"
        );
    }
}

fn check_mutations<P: Program<NativeField>, S: GeneratedAirSpec>(
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
                rejected += usize::from(!compare::<P, S>(
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

#[test]
fn generated_add_witness_and_air_match_released_sp1() {
    check_trace::<AddInstruction, AddInstructionAirSpec>(
        &add_trace(),
        add_row,
        &AddChip::<SupervisorMode>::default(),
    );
}

#[test]
fn all_add_columns_preserve_constraints_and_interactions_under_mutation() {
    // Carries, wraparound and inactive padding: 396 mutations.
    check_mutations::<AddInstruction, AddInstructionAirSpec>(
        &add_trace(),
        &[0, 40, 80, 81],
        add_row,
        &AddChip::<SupervisorMode>::default(),
    );
}

fn check_open_buses<P: Program<NativeField>>(row: &[NativeField]) {
    let input = &row[..P::PROVER_INPUTS];
    let error = generate::<NativeField, P>(&[], input).unwrap_err();
    assert!(matches!(error, WitnessGenerationError::Runtime(_)));
    assert!(matches!(
        generate::<NativeField, RowWitness<P>>(&[], &input[..input.len() - 1]),
        Err(WitnessGenerationError::ProverInputWidth { .. })
    ));
}

#[test]
fn instruction_fixtures_do_not_claim_provider_balance() {
    check_open_buses::<AddInstruction>(&add_row(&add_trace().row_slice(0)));
    check_open_buses::<LoadByteInstruction>(&load_byte_row(&load_byte_trace().row_slice(0)));
    check_open_buses::<DivRemInstruction>(&div_rem_row(&div_rem_trace().row_slice(0)));
    check_open_buses::<MulInstruction>(&mul_row(&mul_trace().row_slice(0)));
}

fn load_byte_event(
    index: usize,
    opcode: Opcode,
    base: u64,
    offset: u64,
    word: u64,
    negative_immediate: bool,
    previous_window: bool,
) -> (MemInstrEvent, ITypeRecord) {
    let clk = if previous_window {
        (1 << 24) + 9
    } else {
        9 + 8 * index as u64
    };
    let c = if negative_immediate {
        offset.wrapping_sub(8)
    } else {
        offset + 8
    };
    let b = (base + offset).wrapping_sub(c);
    let byte = word.to_le_bytes()[offset as usize];
    let a = if opcode == Opcode::LB {
        byte as i8 as i64 as u64
    } else {
        byte as u64
    };
    let read = |value, timestamp, prev_timestamp| {
        MemoryRecordEnum::Read(MemoryReadRecord {
            value,
            timestamp,
            prev_timestamp,
            prev_page_prot_record: None,
        })
    };
    (
        MemInstrEvent {
            clk,
            pc: 4096 + 4 * index as u64,
            opcode,
            a,
            b,
            c,
            op_a_0: false,
            mem_access: read(word, clk + 1, if previous_window { 5 } else { clk - 8 }),
        },
        ITypeRecord {
            op_a: 5,
            op_b: 6,
            op_c: c,
            is_untrusted: false,
            a: MemoryRecordEnum::Write(MemoryWriteRecord {
                prev_timestamp: clk - 8,
                prev_page_prot_record: None,
                prev_value: word.rotate_left(13),
                timestamp: clk + 4,
                value: a,
            }),
            b: read(b, clk + 3, clk - 8),
        },
    )
}

fn load_byte_trace() -> RowMajorMatrix<SP1Field> {
    let mut record = ExecutionRecord::default();
    for opcode in [Opcode::LB, Opcode::LBU] {
        for base in [1 << 16, (1 << 48) - 8] {
            for word in [0, u64::MAX, 0x807f_ff00_0180_fe7f, 0x0102_0304_0506_0708] {
                for negative_immediate in [false, true] {
                    for offset in 0..8 {
                        let index = record.memory_load_byte_events.len();
                        record.memory_load_byte_events.push(load_byte_event(
                            index,
                            opcode,
                            base,
                            offset,
                            word,
                            negative_immediate,
                            false,
                        ));
                    }
                }
            }
        }
    }
    // Exercise MemoryAccess's timestamp-high branch independently of register accesses.
    for opcode in [Opcode::LB, Opcode::LBU] {
        let index = record.memory_load_byte_events.len();
        record.memory_load_byte_events.push(load_byte_event(
            index,
            opcode,
            1 << 32,
            7,
            0x80ff_7f00_1234_5678,
            true,
            true,
        ));
    }
    assert_eq!(record.memory_load_byte_events.len(), 258);
    let chip = LoadByteChip::<SupervisorMode>::default();
    let trace = chip.generate_trace(&record, &mut ExecutionRecord::default());
    assert_eq!(
        trace.width(),
        <LoadByteChip<SupervisorMode> as BaseAir<SP1Field>>::width(&chip)
    );
    assert_eq!(trace.height(), 288); // 258 events and 30 SP1-generated padding rows.
    trace
}

fn load_byte_row(sp1: &[SP1Field]) -> Vec<NativeField> {
    type Columns = LoadByteColumns<u8, SupervisorMode>;
    let address = offset_of!(Columns, address_operation);
    let memory = offset_of!(Columns, memory_access);
    let selectors = offset_of!(Columns, is_lb);
    assert_eq!(sp1.len(), LoadByteInstructionAirSpec::WIDTHS[0]);
    assert_eq!(selectors + 2, sp1.len());
    assert_eq!(memory - address, 4);
    // Clean places selectors first and the four witnessed address cells last.
    sp1[selectors..]
        .iter()
        .chain(&sp1[..address])
        .chain(&sp1[memory..selectors])
        .chain(&sp1[address..memory])
        .map(|value| NativeField::from_u64(value.as_canonical_u64()))
        .collect()
}

#[test]
fn generated_load_byte_witness_and_air_match_released_sp1() {
    check_trace::<LoadByteInstruction, LoadByteInstructionAirSpec>(
        &load_byte_trace(),
        load_byte_row,
        &LoadByteChip::<SupervisorMode>::default(),
    );
}

#[test]
fn all_load_byte_columns_preserve_constraints_and_interactions_under_mutation() {
    // Both selectors, both address bounds, cross-window memory reads and padding.
    check_mutations::<LoadByteInstruction, LoadByteInstructionAirSpec>(
        &load_byte_trace(),
        &[0, 64, 128, 192, 256, 257, 258],
        load_byte_row,
        &LoadByteChip::<SupervisorMode>::default(),
    );
}

fn div_rem_trace() -> RowMajorMatrix<SP1Field> {
    let values = [
        0,
        1,
        7,
        65535,
        65536,
        (1 << 31) - 1,
        1 << 31,
        u32::MAX as u64,
        1 << 32,
        1 << 63,
        u64::MAX,
    ];
    let mut record = ExecutionRecord::default();
    for opcode in [
        Opcode::DIV,
        Opcode::DIVU,
        Opcode::REM,
        Opcode::REMU,
        Opcode::DIVW,
        Opcode::REMW,
        Opcode::DIVUW,
        Opcode::REMUW,
    ] {
        for b in values {
            for c in values {
                let (quotient, remainder) = get_quotient_and_remainder(b, c, opcode);
                let a = match opcode {
                    Opcode::DIV | Opcode::DIVU | Opcode::DIVW | Opcode::DIVUW => quotient,
                    _ => remainder,
                };
                record.divrem_events.push(r_type_event(
                    record.divrem_events.len(),
                    opcode,
                    a,
                    b,
                    c,
                ));
            }
        }
    }
    assert_eq!(record.divrem_events.len(), 968);
    let chip = DivRemChip::<SupervisorMode>::default();
    let trace = chip.generate_trace(&record, &mut ExecutionRecord::default());
    assert_eq!(
        trace.width(),
        <DivRemChip<SupervisorMode> as BaseAir<SP1Field>>::width(&chip)
    );
    assert_eq!(trace.height(), 992); // Includes 24 SP1-generated "0 divided by 1" padding rows.
    trace
}

fn div_rem_row(sp1: &[SP1Field]) -> Vec<NativeField> {
    type Columns = DivRemCols<u8, SupervisorMode>;
    let mut indices = Vec::new();
    macro_rules! block {
        ($field:tt, $width:expr) => {{
            let start = offset_of!(Columns, $field);
            indices.extend(start..start + $width);
        }};
    }
    macro_rules! scalar {
        ($($field:ident),+ $(,)?) => { $(block!($field, 1);)+ };
    }
    // Native inputs: activity, reader columns and seven selectors; DIVU starts the witnesses.
    scalar!(is_real);
    indices.extend(0..offset_of!(Columns, a));
    scalar!(is_div, is_rem, is_remu, is_divw, is_remw, is_divuw, is_remuw, is_divu);
    block!(quotient_comp, 4);
    block!(a, 4);
    block!(b, 4);
    block!(c, 4);
    block!(c_times_quotient_lower, 45);
    block!(c_times_quotient_upper, 45);
    scalar!(
        is_overflow,
        b_neg,
        b_neg_not_overflow,
        b_not_neg_not_overflow,
        is_real_not_word,
        rem_neg,
        c_neg
    );
    block!(c_times_quotient, 8);
    block!(carry, 8);
    block!(is_overflow_b, 11);
    block!(is_overflow_c, 11);
    block!(is_c_0, 11);
    block!(abs_c, 4);
    block!(abs_remainder, 4);
    block!(remainder_comp, 4);
    block!(max_abs_c_or_1, 4);
    block!(c_neg_operation, 4);
    block!(rem_neg_operation, 4);
    scalar!(
        abs_c_alu_event,
        abs_rem_alu_event,
        remainder_check_multiplicity
    );
    // The native less-than witness writes comparison limbs before flags, inverse and bit.
    let comparison = offset_of!(Columns, remainder_lt_operation.comparison_limbs);
    let flags = offset_of!(Columns, remainder_lt_operation.u16_flags);
    indices.extend(comparison..comparison + 2);
    indices.extend(flags..flags + 4);
    indices.push(offset_of!(Columns, remainder_lt_operation.not_eq_inv));
    indices.push(offset_of!(
        Columns,
        remainder_lt_operation.u16_compare_operation.bit
    ));
    block!(remainder, 4);
    block!(quotient, 4);
    scalar!(b_msb, c_msb, rem_msb, quot_msb);
    assert_eq!(sp1.len(), DivRemInstructionAirSpec::WIDTHS[0]);
    assert_eq!(
        <DivRemInstruction as Program<NativeField>>::PROVER_INPUTS,
        36
    );
    // Check this independent source-side map is a complete permutation, even on malformed rows.
    let mut sorted = indices.clone();
    sorted.sort_unstable();
    assert_eq!(sorted, (0..sp1.len()).collect::<Vec<_>>());
    indices
        .into_iter()
        .map(|index| NativeField::from_u64(sp1[index].as_canonical_u64()))
        .collect()
}

#[test]
fn generated_div_rem_witness_and_air_match_released_sp1() {
    check_trace::<DivRemInstruction, DivRemInstructionAirSpec>(
        &div_rem_trace(),
        div_rem_row,
        &DivRemChip::<SupervisorMode>::default(),
    );
}

#[test]
fn all_div_rem_columns_preserve_constraints_and_interactions_under_mutation() {
    // Zero division, signed overflow at both widths, negative operands, and nonzero padding.
    let indices: Vec<usize> = (0..8)
        .flat_map(|opcode| [0, 76, 109, 120].map(|row| opcode * 121 + row))
        .chain([968])
        .collect();
    check_mutations::<DivRemInstruction, DivRemInstructionAirSpec>(
        &div_rem_trace(),
        &indices,
        div_rem_row,
        &DivRemChip::<SupervisorMode>::default(),
    );
}

fn mul_trace() -> RowMajorMatrix<SP1Field> {
    let values: [u64; 11] = [
        0,
        1,
        7,
        65535,
        65536,
        (1 << 31) - 1,
        1 << 31,
        u32::MAX as u64,
        1 << 32,
        1 << 63,
        u64::MAX,
    ];
    let mut record = ExecutionRecord::default();
    for opcode in [
        Opcode::MUL,
        Opcode::MULH,
        Opcode::MULHU,
        Opcode::MULHSU,
        Opcode::MULW,
    ] {
        for b in values {
            for c in values {
                let a = match opcode {
                    Opcode::MUL => b.wrapping_mul(c),
                    Opcode::MULH => (((b as i64 as i128) * (c as i64 as i128)) >> 64) as u64,
                    Opcode::MULHU => (((b as u128) * (c as u128)) >> 64) as u64,
                    Opcode::MULHSU => (((b as i64 as i128) * (c as i128)) >> 64) as u64,
                    Opcode::MULW => (b as i32).wrapping_mul(c as i32) as i64 as u64,
                    _ => unreachable!(),
                };
                record
                    .mul_events
                    .push(r_type_event(record.mul_events.len(), opcode, a, b, c));
            }
        }
    }
    assert_eq!(record.mul_events.len(), 605);
    let chip = MulChip::<SupervisorMode>::default();
    let trace = chip.generate_trace(&record, &mut ExecutionRecord::default());
    assert_eq!(
        trace.width(),
        <MulChip<SupervisorMode> as BaseAir<SP1Field>>::width(&chip)
    );
    assert_eq!(trace.height(), 608); // Includes three all-zero SP1 padding rows.
    trace
}

fn mul_row(sp1: &[SP1Field]) -> Vec<NativeField> {
    type Columns = MulCols<u8, SupervisorMode>;
    // Native inputs: reader columns and selectors. Witnesses: multiplication block and result.
    // Offsets come from the independently pinned Rust struct, never the generated row inventory.
    let mut indices: Vec<usize> = (0..offset_of!(Columns, a)).collect();
    indices.extend([
        offset_of!(Columns, is_mul),
        offset_of!(Columns, is_mulh),
        offset_of!(Columns, is_mulhu),
        offset_of!(Columns, is_mulhsu),
        offset_of!(Columns, is_mulw),
    ]);
    let operation = offset_of!(Columns, mul_operation);
    indices.extend(operation..operation + 45);
    let result = offset_of!(Columns, a);
    indices.extend(result..result + 4);
    assert_eq!(sp1.len(), MulInstructionAirSpec::WIDTHS[0]);
    assert_eq!(<MulInstruction as Program<NativeField>>::PROVER_INPUTS, 33);
    let mut sorted = indices.clone();
    sorted.sort_unstable();
    assert_eq!(sorted, (0..sp1.len()).collect::<Vec<_>>());
    indices
        .into_iter()
        .map(|index| NativeField::from_u64(sp1[index].as_canonical_u64()))
        .collect()
}

#[test]
fn generated_mul_witness_and_air_match_released_sp1() {
    check_trace::<MulInstruction, MulInstructionAirSpec>(
        &mul_trace(),
        mul_row,
        &MulChip::<SupervisorMode>::default(),
    );
}

#[test]
fn all_mul_columns_preserve_constraints_and_interactions_under_mutation() {
    // Zero, word-sign boundary, signed high product, maximal limbs, and inactive padding.
    let indices: Vec<usize> = (0..5)
        .flat_map(|opcode| [0, 76, 109, 120].map(|row| opcode * 121 + row))
        .chain([605])
        .collect();
    check_mutations::<MulInstruction, MulInstructionAirSpec>(
        &mul_trace(),
        &indices,
        mul_row,
        &MulChip::<SupervisorMode>::default(),
    );
}
