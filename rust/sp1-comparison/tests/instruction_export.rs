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
    ExecutionRecord, ITypeRecord, Opcode, RTypeRecord,
};
use sp1_core_machine::{
    air::TrivialOperationBuilder,
    alu::add_sub::add::AddChip,
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
            let i = record.add_events.len() as u64;
            let clk = 9 + 8 * i;
            let a = b.wrapping_add(c);
            let read = |value, offset| {
                MemoryRecordEnum::Read(MemoryReadRecord {
                    value,
                    timestamp: clk + offset,
                    prev_timestamp: clk - 8,
                    prev_page_prot_record: None,
                })
            };
            record.add_events.push((
                AluEvent::new(clk, 4096 + 4 * i, Opcode::ADD, a, b, c, false),
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
        "local constraint satisfaction differs"
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
        "complete instruction interaction multiset differs"
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
            compare::<P, S>(sp1, &row, chip),
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
                rejected += usize::from(!compare::<P, S>(&row, &map_row(&row), chip));
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
