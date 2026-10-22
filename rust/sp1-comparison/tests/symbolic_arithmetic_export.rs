//! Exact ADD, ADDI, ADDW, SUB and SUBW conformance by bounded-degree polynomial interpolation.
//!
//! Uses the emitted AIR and released SP1 evaluators, with degree bounds from their
//! upstream symbolic expressions. No expression interpreter or Rust-to-Lean oracle.
//! For n variables and total degree d < characteristic, the integer simplex
//! {a : sum(a) <= d} determines every polynomial: the binomial-polynomial basis
//! gives a triangular evaluation matrix with nonzero diagonal on this set.
//! We compare polynomial systems up to nonzero scaling and duplicate/zero
//! equations, after BOTH systems independently force op_a_0 = 0. This establishes
//! equality of their row-acceptance predicates under the explicit permutation.
//! The supervisor profile fixes is_untrusted_programs_enabled = 0; all other
//! public inputs must be absent from the symbolic expressions. With mprotect,
//! the released supervisor AIR itself rejects mode flag one, even on padding.
//! Affine interaction occurrences are compared on zero and every unit vector,
//! before sorting, so duplicates and zero multiplicities remain present.
//! This trusts the Rust checker, upstream degree arithmetic and adapters; it is
//! not a kernel-checked lowering proof or a witness/whole-execution theorem.

extern crate alloc;

use clean_backend::GeneratedAirSpec;
use p3_air::{Entry as NativeEntry, SymbolicExpression as NativeExpression, SymbolicVariable};
use p3_field::{PrimeCharacteristicRing, PrimeField64};
use p3_koala_bear::KoalaBear as F;
use slop_air::{Air, AirBuilder, AirBuilderWithPublicValues, BaseAir, PairBuilder};
use slop_algebra::{AbstractField, Field, PrimeField64 as Sp1PrimeField64};
use slop_matrix::dense::RowMajorMatrix;
use slop_uni_stark::{
    get_symbolic_constraints, Entry, SymbolicAirBuilder, SymbolicExpression,
    SymbolicVariable as Sp1Variable,
};
use sp1_core_machine::{
    adapter::register::{alu_type::ALUTypeReader, i_type::ITypeReader, r_type::RTypeReader},
    air::TrivialOperationBuilder,
    alu::add_sub::{
        add::{AddChip, AddCols},
        addi::{AddiChip, AddiCols},
        addw::{AddwChip, AddwCols},
        sub::{SubChip, SubCols},
        subw::{SubwChip, SubwCols},
    },
    SupervisorMode,
};
use sp1_hypercube::{
    air::{AirInteraction, InteractionScope, MessageBuilder, PublicValues, SP1_PROOF_NUM_PV_ELTS},
    InteractionBuilder, InteractionKind,
};
use sp1_primitives::SP1Field as S;
use std::collections::BTreeSet;

macro_rules! fixture {
    ($module:ident, $file:literal) => {
        #[allow(dead_code, unused_imports, unused_variables, unused_parens)]
        mod $module {
            include!(concat!(env!("CLEAN_ENSEMBLE_EXPORT_DIR"), "/", $file));
        }
    };
}
fixture!(add, "add_instruction.rs");
fixture!(addi, "addi_instruction.rs");
fixture!(addw, "addw_instruction.rs");
fixture!(sub, "sub_instruction.rs");
fixture!(subw, "subw_instruction.rs");
#[allow(dead_code)]
#[path = "support/export.rs"]
mod support;

fn mode_flag() -> usize {
    std::mem::offset_of!(PublicValues<[u8; 4], [u8; 3], [u8; 4], u8>, is_untrusted_programs_enabled)
}

fn local(expression: &SymbolicExpression<S>, width: usize, profile: bool) {
    use SymbolicExpression::*;
    match expression {
        Variable(v) => {
            if v.entry == Entry::Public {
                assert!(
                    profile && cfg!(feature = "mprotect") && v.index == mode_flag(),
                    "public input outside the supervisor profile"
                );
            } else {
                assert_eq!(v.entry, Entry::Main { offset: 0 });
                assert!(v.index < width);
            }
        }
        Constant(_) => (),
        Add { x, y, .. } | Sub { x, y, .. } | Mul { x, y, .. } => {
            local(x, width, profile);
            local(y, width, profile);
        }
        Neg { x, .. } => local(x, width, profile),
        _ => panic!("row selector outside the interpolation domain"),
    }
}

// Keep SP1's affine interaction collector, but expose symbolic public variables:
// its ordinary public vector contains zeros and could otherwise hide dependencies.
struct CheckedInteractions {
    inner: InteractionBuilder<S>,
    width: usize,
    public: Vec<Sp1Variable<S>>,
}

impl AirBuilder for CheckedInteractions {
    type F = S;
    type Expr = SymbolicExpression<S>;
    type Var = Sp1Variable<S>;
    type M = RowMajorMatrix<Self::Var>;
    fn main(&self) -> Self::M {
        self.inner.main()
    }
    fn is_first_row(&self) -> Self::Expr {
        self.inner.is_first_row()
    }
    fn is_last_row(&self) -> Self::Expr {
        self.inner.is_last_row()
    }
    fn is_transition_window(&self, size: usize) -> Self::Expr {
        self.inner.is_transition_window(size)
    }
    fn assert_zero<I: Into<Self::Expr>>(&mut self, value: I) {
        self.inner.assert_zero(value);
    }
}
impl PairBuilder for CheckedInteractions {
    fn preprocessed(&self) -> Self::M {
        self.inner.preprocessed()
    }
}
impl AirBuilderWithPublicValues for CheckedInteractions {
    type PublicVar = Sp1Variable<S>;
    fn public_values(&self) -> &[Self::PublicVar] {
        &self.public
    }
}
impl TrivialOperationBuilder for CheckedInteractions {}
impl CheckedInteractions {
    fn new(width: usize) -> Self {
        Self {
            inner: InteractionBuilder::<S>::new(0, width),
            width,
            public: (0..SP1_PROOF_NUM_PV_ELTS)
                .map(|index| Sp1Variable::new(Entry::Public, index))
                .collect(),
        }
    }

    fn check(&self, message: &AirInteraction<SymbolicExpression<S>>) {
        local(&message.multiplicity, self.width, false);
        for value in &message.values {
            local(value, self.width, false);
        }
    }
}
impl MessageBuilder<AirInteraction<SymbolicExpression<S>>> for CheckedInteractions {
    fn send(&mut self, message: AirInteraction<SymbolicExpression<S>>, scope: InteractionScope) {
        self.check(&message);
        self.inner.send(message, scope);
    }
    fn receive(&mut self, message: AirInteraction<SymbolicExpression<S>>, scope: InteractionScope) {
        self.check(&message);
        self.inner.receive(message, scope);
    }
}

#[derive(Clone, Copy, Debug)]
enum Mutation {
    None,
    DropZero,
    ActiveOnly,
    FlipMultiplicity,
    DegreeFour,
}

fn native_constraints<P: GeneratedAirSpec, E: PrimeCharacteristicRing + Clone>(
    row: &[E],
    mutation: Mutation,
    zero_constraints: &[usize],
) -> Vec<E> {
    let mut values = P::constraints(0, row);
    match mutation {
        // Remove every independently identified affine zero-column assertion.
        // Discovery uses the real evaluator on a determining affine basis.
        Mutation::DropZero => {
            values = values
                .into_iter()
                .enumerate()
                .filter_map(|(index, value)| (!zero_constraints.contains(&index)).then_some(value))
                .collect();
        }
        Mutation::ActiveOnly => values.push(row[0].clone() - E::ONE),
        Mutation::DegreeFour => values.push(row[0].clone().exp_u64(4)),
        _ => (),
    }
    values
}

fn native_interactions<P: GeneratedAirSpec, E: PrimeCharacteristicRing + Clone>(
    row: &[E],
    mutation: Mutation,
) -> Vec<clean_backend::witness_generation::Interaction<E>> {
    let mut values = P::interactions(0, row);
    if matches!(mutation, Mutation::FlipMultiplicity) {
        values[0].multiplicity = -values[0].multiplicity.clone();
    }
    values
}

fn sp1_evaluate<C: Air<support::Sp1Evaluation>>(
    chip: &C,
    row: &[u64],
    mode: u64,
) -> support::Sp1Evaluation {
    let mut public = vec![S::zero(); SP1_PROOF_NUM_PV_ELTS];
    public[mode_flag()] = S::from_canonical_u64(mode);
    let mut sp1 = support::Sp1Evaluation {
        row: row.iter().copied().map(S::from_canonical_u64).collect(),
        preprocessed: vec![],
        constraints: vec![],
        ledger: vec![],
        public,
    };
    chip.eval(&mut sp1);
    sp1
}

fn evaluate<P: GeneratedAirSpec, C: Air<support::Sp1Evaluation>>(
    chip: &C,
    row: &[u64],
    mutation: Mutation,
    zero_constraints: &[usize],
) -> (Vec<S>, Vec<S>, support::Ledger, support::Ledger) {
    let sp1 = sp1_evaluate(chip, row, 0);
    let native = std::iter::once(*row.last().unwrap())
        .chain(row[..row.len() - 1].iter().copied())
        .map(F::from_u64)
        .collect::<Vec<_>>();
    let constraints = native_constraints::<P, _>(&native, mutation, zero_constraints)
        .into_iter()
        .map(|v| S::from_canonical_u64(v.as_canonical_u64()))
        .collect();
    let ledger = native_interactions::<P, _>(&native, mutation)
        .into_iter()
        .map(|v| {
            (
                v.channel.to_owned(),
                v.multiplicity.as_canonical_u64(),
                v.message
                    .iter()
                    .map(PrimeField64::as_canonical_u64)
                    .collect(),
            )
        })
        .collect();
    (sp1.constraints, constraints, sp1.ledger, ledger)
}

// All nonnegative integer multi-indices of total weight <= degree, excluding a
// column separately proved zero by an affine constraint in BOTH systems.
fn grid(
    row: &mut [u64],
    index: usize,
    remaining: usize,
    zero: usize,
    visit: &mut impl FnMut(&[u64]),
) {
    if index == row.len() {
        visit(row);
        return;
    }
    for value in 0..=if index == zero { 0 } else { remaining } {
        row[index] = value as u64;
        grid(row, index + 1, remaining - value, zero, visit);
    }
}

fn normalized(values: &[Vec<S>]) -> BTreeSet<Vec<u64>> {
    values
        .iter()
        .filter_map(|v| {
            v.iter().find(|x| **x != S::zero()).map(|first| {
                let scale = first.inverse();
                v.iter().map(|x| (*x * scale).as_canonical_u64()).collect()
            })
        })
        .collect()
}

fn compare<P, C>(chip: C, zero_column: usize, input_width: usize, mutation: Mutation)
where
    P: GeneratedAirSpec + clean_backend::witness_generation::Program<F>,
    C: Air<support::Sp1Evaluation> + Air<SymbolicAirBuilder<S>> + Air<CheckedInteractions>,
{
    let width = <C as BaseAir<S>>::width(&chip);
    assert!(zero_column < width - 1);
    assert_eq!(P::PROVER_INPUTS, input_width);
    // Independent SP1 offsets above define the map. Verify it is a permutation.
    let mut permutation = std::iter::once(width - 1)
        .chain(0..width - 1)
        .collect::<Vec<_>>();
    permutation.sort_unstable();
    assert_eq!(permutation, (0..width).collect::<Vec<_>>());
    assert_eq!(P::WIDTHS, &[width]);
    assert_eq!(
        <P as GeneratedAirSpec>::FIELD_ORDER,
        <F as PrimeField64>::ORDER_U64
    );
    assert_eq!(<P as GeneratedAirSpec>::FIXED_WIDTHS, &[0]);
    assert_eq!(P::PUBLIC_VALUES, 0);
    assert_eq!(P::VERIFIER_INTERACTIONS, 0);
    assert_eq!(
        <F as PrimeField64>::ORDER_U64,
        <S as Sp1PrimeField64>::ORDER_U64
    );
    let sp1 = get_symbolic_constraints::<S, _>(&chip, 0, SP1_PROOF_NUM_PV_ELTS);
    for expr in &sp1 {
        local(expr, width, true);
    }
    // The feature adds a supervisor-mode assertion, not user-mode conformance.
    assert_eq!(
        sp1_evaluate(&chip, &vec![0; width], 1)
            .constraints
            .iter()
            .all(|v| *v == S::zero()),
        !cfg!(feature = "mprotect")
    );
    let row = (0..width)
        .map(|index| {
            NativeExpression::<F>::from(SymbolicVariable::new(
                NativeEntry::Main { offset: 0 },
                index,
            ))
        })
        .collect::<Vec<_>>();
    let original = P::constraints(0, &row);
    let basis = (0..=width)
        .map(|point| {
            let mut values = vec![F::ZERO; width];
            if point > 0 {
                values[point - 1] = F::ONE;
            }
            P::constraints(0, &values)
        })
        .collect::<Vec<_>>();
    let zero_constraints = original
        .iter()
        .enumerate()
        .filter_map(|(index, expr)| {
            (expr.degree_multiple() <= 1
                && basis.iter().enumerate().all(|(point, values)| {
                    values[index]
                        == if point == zero_column + 2 {
                            F::ONE
                        } else {
                            F::ZERO
                        }
                }))
            .then_some(index)
        })
        .collect::<Vec<_>>();
    assert!(
        !zero_constraints.is_empty(),
        "unmodified native AIR must force its mapped zero column"
    );
    let native = native_constraints::<P, _>(&row, mutation, &zero_constraints);
    let degree = sp1
        .iter()
        .map(SymbolicExpression::degree_multiple)
        .chain(native.iter().map(NativeExpression::degree_multiple))
        .max()
        .unwrap();
    assert!(degree < <S as Sp1PrimeField64>::ORDER_U64 as usize);
    assert!(
        degree <= 3,
        "arithmetic grid budget; never silently truncate degree"
    );
    for interaction in native_interactions::<P, _>(&row, mutation) {
        assert!(interaction.multiplicity.degree_multiple() <= 1);
        assert!(interaction.message.iter().all(|v| v.degree_multiple() <= 1));
    }
    // Upstream collector rejects non-affine messages/multiplicities.
    let mut interactions = CheckedInteractions::new(width);
    chip.eval(&mut interactions);
    let (sends, receives) = interactions.inner.interactions();
    let mut left = vec![Vec::new(); sp1.len()];
    let mut right = vec![Vec::new(); native.len()];
    let mut ledger_left: Vec<(String, Vec<Vec<u64>>)> = vec![];
    let mut ledger_right: Vec<(String, Vec<Vec<u64>>)> = vec![];
    let mut expected_zero = vec![];
    for point in 0..=width {
        let mut values = vec![0u64; width];
        if point > 0 {
            values[point - 1] = 1;
        }
        expected_zero.push(S::from_canonical_u64(values[zero_column]));
        let (a, b, la, lb) = evaluate::<P, _>(&chip, &values, mutation, &zero_constraints);
        assert_eq!(a.len(), left.len());
        assert_eq!(b.len(), right.len());
        for (target, value) in left.iter_mut().zip(a) {
            target.push(value);
        }
        for (target, value) in right.iter_mut().zip(b) {
            target.push(value);
        }
        for (target, ledger) in [(&mut ledger_left, la), (&mut ledger_right, lb)] {
            if point == 0 {
                *target = ledger.iter().map(|v| (v.0.clone(), vec![])).collect();
            }
            assert_eq!(target.len(), ledger.len());
            for ((name, samples), (channel, mult, message)) in target.iter_mut().zip(ledger) {
                assert_eq!(name, &channel);
                if let Some(previous) = samples.first() {
                    assert_eq!(previous.len(), message.len() + 1);
                }
                samples.push(std::iter::once(mult).chain(message).collect());
            }
        }
    }
    assert_eq!(sends.len() + receives.len(), ledger_left.len());
    assert!(sp1
        .iter()
        .zip(&left)
        .any(|(expr, v)| expr.degree_multiple() <= 1 && *v == expected_zero));
    assert!(
        native
            .iter()
            .zip(&right)
            .any(|(expr, v)| expr.degree_multiple() <= 1 && *v == expected_zero),
        "native system must independently enforce op_a_0 = 0"
    );
    ledger_left.sort();
    ledger_right.sort();
    assert!(
        ledger_left == ledger_right,
        "complete affine interaction multisets"
    );
    for values in left.iter_mut().chain(right.iter_mut()) {
        values.clear();
    }
    let mut points = 0usize;
    grid(&mut vec![0; width], 0, degree, zero_column, &mut |values| {
        let (a, b, _, _) = evaluate::<P, _>(&chip, values, mutation, &zero_constraints);
        assert_eq!(a.len(), left.len());
        assert_eq!(b.len(), right.len());
        for (target, value) in left.iter_mut().zip(a) {
            target.push(value);
        }
        for (target, value) in right.iter_mut().zip(b) {
            target.push(value);
        }
        points += 1;
    });
    // In the binomial-polynomial basis, evaluation at these multi-indices is
    // triangular with nonzero diagonal when characteristic > degree. Thus these
    // points determine every polynomial of total degree <= degree exactly.
    let variables = width - 1;
    let expected_points = (1..=degree).fold(1usize, |n, k| n * (variables + k) / k);
    assert_eq!(points, expected_points);
    let lhs = normalized(&left);
    let rhs = normalized(&right);
    println!("width={width}, degree={degree}, zero_column={zero_column}, points={points}, sp1_constraints={}, native_constraints={}, sp1_distinct={}, native_distinct={}, interactions={}",
        sp1.len(), native.len(), lhs.len(), rhs.len(), ledger_left.len());
    assert!(
        lhs == rhs,
        "constraint polynomial systems after independently forced zero column"
    );
}

// These offsets come from the pinned release's concrete layouts, never generated metadata.
fn compare_arithmetic(family: usize, mutation: Mutation) {
    macro_rules! family {
        ($module:ident, $chip:ident, $cols:ident, $reader:ident, $operation:ident) => {{
            type Columns = $cols<u8, SupervisorMode>;
            let real = std::mem::offset_of!(Columns, is_real);
            assert_eq!(real + 1, std::mem::size_of::<Columns>());
            let zero =
                std::mem::offset_of!(Columns, adapter) + std::mem::offset_of!($reader<u8>, op_a_0);
            println!("{}: {mutation:?}", stringify!($module));
            compare::<$module::Ensemble, _>(
                $chip::<SupervisorMode>::default(),
                zero,
                std::mem::offset_of!(Columns, $operation) + 1,
                mutation,
            );
        }};
    }
    match family {
        0 => family!(add, AddChip, AddCols, RTypeReader, add_operation),
        1 => family!(addi, AddiChip, AddiCols, ITypeReader, add_operation),
        2 => family!(addw, AddwChip, AddwCols, ALUTypeReader, addw_operation),
        3 => family!(sub, SubChip, SubCols, RTypeReader, sub_operation),
        4 => family!(subw, SubwChip, SubwCols, RTypeReader, subw_operation),
        _ => unreachable!(),
    }
}

#[test]
fn arithmetic_constraints_and_interactions_agree_for_all_rows() {
    for family in 0..5 {
        compare_arithmetic(family, Mutation::None);
    }
}

#[test]
fn interpolation_guard_rejects_constraint_bus_and_domain_changes() {
    for family in 0..5 {
        for (mutation, expected) in [
            (
                Mutation::DropZero,
                "native system must independently enforce op_a_0 = 0",
            ),
            (Mutation::ActiveOnly, "constraint polynomial systems"),
            (
                Mutation::FlipMultiplicity,
                "complete affine interaction multisets",
            ),
            (Mutation::DegreeFour, "arithmetic grid budget"),
        ] {
            let error = std::panic::catch_unwind(|| compare_arithmetic(family, mutation))
                .expect_err("adversarial AIR change must be detected");
            let message = error
                .downcast_ref::<String>()
                .map(String::as_str)
                .or_else(|| error.downcast_ref::<&str>().copied())
                .unwrap_or("");
            assert!(
                message.contains(expected),
                "{mutation:?}: unexpected failure: {message}"
            );
        }
    }
    // The stock interaction collector supplies zero public values. A symbolic
    // public dependency must be rejected before that can hide it from the check.
    let error = std::panic::catch_unwind(|| {
        let mut builder = CheckedInteractions::new(33);
        builder.send(
            AirInteraction::new(
                vec![Sp1Variable::new(Entry::Public, mode_flag()).into()],
                SymbolicExpression::one(),
                InteractionKind::Byte,
            ),
            InteractionScope::Local,
        );
    })
    .expect_err("symbolic public dependency must not be erased");
    let message = error
        .downcast_ref::<String>()
        .map(String::as_str)
        .or_else(|| error.downcast_ref::<&str>().copied())
        .unwrap_or("");
    assert!(
        message.contains("public input outside the supervisor profile"),
        "{message}"
    );
}
