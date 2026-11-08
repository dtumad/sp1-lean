//! Concrete field evaluation and one-row Clean runtime support for export comparisons.

use clean_backend::witness_generation::{Direction, Program, WitnessData};
use p3_field::PrimeField64;
use p3_koala_bear::KoalaBear as NativeField;
use slop_air::{AirBuilder, AirBuilderWithPublicValues};
use slop_algebra::{AbstractField, PrimeField64 as Sp1PrimeField64};
use slop_matrix::dense::RowMajorMatrix;
use sp1_core_machine::air::TrivialOperationBuilder;
use sp1_hypercube::{
    air::{AirInteraction, InteractionScope, MessageBuilder},
    InteractionKind,
};
use sp1_primitives::SP1Field;
use std::collections::BTreeMap;

pub type Ledger = Vec<(String, u64, Vec<u64>)>;

/// SP1 supplies the actual expressions; this builder records their field evaluations.
pub struct Sp1Evaluation {
    pub row: Vec<SP1Field>,
    pub preprocessed: Vec<SP1Field>,
    pub constraints: Vec<SP1Field>,
    pub ledger: Ledger,
    pub public: Vec<SP1Field>,
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
impl slop_air::PairBuilder for Sp1Evaluation {
    fn preprocessed(&self) -> Self::M {
        RowMajorMatrix::new(self.preprocessed.clone(), self.preprocessed.len())
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
            InteractionKind::Syscall => ("SP1Syscall", false),
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

/// Complete an isolated component row through the generated upstream witness function.
/// This checks the row program; full ensemble tests separately exercise channel scheduling.
pub fn complete_row<P: Program<NativeField>>(
    input: &[NativeField],
) -> Result<Vec<NativeField>, String> {
    assert_eq!(P::COMPONENTS, 1);
    if input.len() != P::PROVER_INPUTS {
        return Err(format!(
            "row input has width {}, expected {}",
            input.len(),
            P::PROVER_INPUTS
        ));
    }
    let data = WitnessData::from_entries(vec![]);
    let hint = WitnessData::from_entries(vec![("input", vec![input.to_vec()])]);
    P::complete_row(0, input, &data, &hint)
}

/// Determine whether a component row leaves an unmatched external demand. Count over integers,
/// retaining direction separately from the natural field count. Physical comparisons above and
/// in the callers still compare every occurrence, including repeated keys and zero counts.
pub fn has_open_bus<P: Program<NativeField>>(input: &[NativeField]) -> bool {
    let row = complete_row::<P>(input).unwrap();
    let mut counts = BTreeMap::new();
    for entry in P::interactions(0, &row) {
        let key = (
            entry.channel,
            entry
                .message
                .iter()
                .map(PrimeField64::as_canonical_u64)
                .collect::<Vec<_>>(),
        );
        let count = i128::from(entry.multiplicity.as_canonical_u64());
        *counts.entry(key).or_insert(0) += match entry.direction {
            Direction::Push => count,
            Direction::Pull => -count,
        };
    }
    counts.values().any(|count| *count != 0)
}
