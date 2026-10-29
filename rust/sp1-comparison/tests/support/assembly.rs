//! Shared full-assembly reference and backend checks. Empty and zero rows stay physical.

use crate::backend;
use clean_backend::witness_generation::{generate, Program};
use clean_backend::{prove_ensemble, verify_ensemble, EnsembleShapeError, GeneratedAirSpec};
use p3_field::{PrimeCharacteristicRing, PrimeField64};
use p3_koala_bear::KoalaBear as F;
use p3_matrix::Matrix;

pub fn fields(value: &serde_json::Value) -> Vec<F> {
    value
        .as_array()
        .unwrap()
        .iter()
        .map(|cell| F::from_u64(cell.as_u64().unwrap()))
        .collect()
}

/// Encode independently observed clocks/PCs in the native header's exact limb order.
pub fn check_endpoints(public: &[F], initial: (u64, u64), final_state: (u64, u64)) {
    let encode = |(clock, pc): (u64, u64)| {
        [
            clock & 65535,
            (clock >> 16) & 255,
            (clock >> 24) & 255,
            clock >> 32,
            pc & 65535,
            (pc >> 16) & 65535,
            pc >> 32,
        ]
        .map(F::from_u64)
    };
    assert_eq!(&public[..7], &encode(initial));
    assert_eq!(&public[7..14], &encode(final_state));
}

pub fn physical_balance<P: Program<F>>(public: &[F], tables: &[Vec<Vec<F>>]) -> bool {
    use std::collections::BTreeMap;

    let mut channels = BTreeMap::<String, (usize, BTreeMap<Vec<u64>, F>)>::new();
    for entry in
        P::verifier_interactions(public)
            .into_iter()
            .chain(tables.iter().enumerate().flat_map(|(component, rows)| {
                rows.iter()
                    .flat_map(move |row| P::interactions(component, row))
            }))
    {
        let (count, messages) = channels.entry(entry.channel.to_owned()).or_default();
        *count += 1;
        let message = entry
            .message
            .iter()
            .map(PrimeField64::as_canonical_u64)
            .collect();
        *messages.entry(message).or_default() += entry.multiplicity;
    }
    channels.values().all(|(count, messages)| {
        (*count as u64) < F::ORDER_U64 && messages.values().all(|value| *value == F::ZERO)
    })
}

pub fn check_reference<P: Program<F> + GeneratedAirSpec>(
    reference: &serde_json::Value,
    cases: usize,
) {
    let inventory = reference["inventory"].as_array().unwrap();
    assert_eq!(inventory.len(), 95);
    assert_eq!(P::COMPONENTS, 95);
    for (index, component) in inventory.iter().enumerate() {
        assert_eq!(component["name"], P::COMPONENT_NAMES[index]);
        assert_eq!(component["width"], P::ROW_WIDTHS[index]);
        assert_eq!(
            component["fixedWidth"],
            <P as GeneratedAirSpec>::FIXED_WIDTHS[index]
        );
        assert_eq!(component["fixedHeight"], P::FIXED_HEIGHTS[index]);
    }
    let samples = reference["cases"].as_array().unwrap();
    assert_eq!(samples.len(), cases);
    for case in samples {
        let public = fields(&case["publicInput"]);
        assert_eq!(verifier_reference::<P>(&public), case["verifier"]);
        let private = fields(&case["privateInput"]);
        let result = generate::<F, P>(&public, &private);
        if let Some(expected) = case.get("witness") {
            let witness = result.unwrap();
            assert_eq!(
                backend::physical_reference::<P>(&public, &witness.tables),
                *expected
            );
            let constraints = witness.tables.iter().enumerate().all(|(component, rows)| {
                rows.iter().all(|row| {
                    P::constraints(component, row)
                        .into_iter()
                        .all(|v| v == F::ZERO)
                })
            });
            assert_eq!(
                constraints && physical_balance::<P>(&public, &witness.tables),
                case["accepted"].as_bool().unwrap(),
                "acceptance mismatch: {}",
                case["name"]
            );
            if case["name"] == "active-branch" {
                assert_eq!(
                    witness.tables[18],
                    vec![fields(&reference["compilerBranchRow"])]
                );
            }
            if case["accepted"] == true {
                let traces = witness.into_traces().unwrap();
                assert_eq!(traces.len(), 95);
                for (index, trace) in traces.iter().enumerate() {
                    assert_eq!(trace.width(), P::WIDTHS[index]);
                    let fixed_height = P::FIXED_HEIGHTS[index];
                    if fixed_height != 0 {
                        assert_eq!(trace.height(), fixed_height);
                        assert_eq!(backend::fixed_trace::<P>(index).height(), fixed_height);
                    }
                }
            }
        } else {
            assert!(!case["accepted"].as_bool().unwrap());
            assert!(
                result.is_err(),
                "mutation unexpectedly generated: {}",
                case["name"]
            );
        }
    }
}

pub fn verifier_reference<P: GeneratedAirSpec>(public: &[F]) -> serde_json::Value {
    serde_json::Value::Array(
        P::verifier_interactions(public)
            .into_iter()
            .map(|entry| {
                backend::interaction(
                    entry.channel,
                    entry.multiplicity.as_canonical_u64(),
                    entry
                        .message
                        .iter()
                        .map(PrimeField64::as_canonical_u64)
                        .collect(),
                    entry.assume_guarantees,
                )
            })
            .collect(),
    )
}

pub fn prove_case<P: Program<F> + GeneratedAirSpec>(
    case: &serde_json::Value,
) -> (Vec<p3_matrix::dense::RowMajorMatrix<F>>, Vec<F>) {
    assert_eq!(case["accepted"], true);
    let public = fields(&case["publicInput"]);
    let traces = generate::<F, P>(&public, &fields(&case["privateInput"]))
        .unwrap()
        .into_traces()
        .unwrap();
    accept_traces::<P>(&public, traces.clone());
    (traces, public)
}

pub fn accept_traces<P: GeneratedAirSpec>(
    public: &[F],
    traces: Vec<p3_matrix::dense::RowMajorMatrix<F>>,
) {
    let heights = traces.iter().map(Matrix::height).collect::<Vec<_>>();
    let statement = clean_backend::GeneratedEnsemble::<F, P>::new(&heights).unwrap();
    let config = backend::config_with_log_blowup(4);
    let (proof, _) = prove_ensemble(&config, &statement, traces, public).unwrap();
    verify_ensemble(&config, &statement, &proof, public).unwrap();
}

pub fn reject_traces<P: GeneratedAirSpec>(
    public: &[F],
    traces: Vec<p3_matrix::dense::RowMajorMatrix<F>>,
) {
    let heights = traces.iter().map(Matrix::height).collect::<Vec<_>>();
    let statement = match clean_backend::GeneratedEnsemble::<F, P>::new(&heights) {
        Ok(statement) => statement,
        Err(EnsembleShapeError::FixedTraceHeight {
            expected,
            actual: 0,
            ..
        }) if expected > 0 => return,
        Err(error) => panic!("unexpected malformed-shape result: {error:?}"),
    };
    let config = backend::config_with_log_blowup(4);
    backend::assert_backend_rejection(|| {
        let (proof, _) = prove_ensemble(&config, &statement, traces, public).unwrap();
        verify_ensemble(&config, &statement, &proof, public).is_err()
    });
}

pub fn malformed<P: Program<F> + GeneratedAirSpec>(
    reference: &serde_json::Value,
    consumers: &[usize],
) {
    eprintln!("assembly {}", std::any::type_name::<P>());
    let (traces, public) = prove_case::<P>(&reference["cases"][0]);
    for column in [0, 7, 11, 14, 31, 56] {
        eprintln!("changed public column {column}");
        let mut changed = public.clone();
        changed[column] += F::ONE;
        reject_traces::<P>(&changed, traces.clone());
    }
    for table in consumers.iter().copied().chain([2, 5, 88, 89, 94]) {
        eprintln!("missing table {table}");
        assert!(traces[table].height() > 0);
        let mut missing = traces.clone();
        missing[table].values.clear();
        reject_traces::<P>(&public, missing);
    }
    for table in [6, 59, 92, 94] {
        eprintln!("changed provider count {table}");
        let mut wrong_count = traces.clone();
        wrong_count[table].values[0] += F::ONE;
        reject_traces::<P>(&public, wrong_count);
    }
    for &table in consumers {
        let column = if table == 57 {
            // HaltPaddingChip fixes is_real (the last input) to zero. Its first
            // clock cell is deliberately free, so changing it must remain valid.
            assert_eq!(P::HINT_TABLES[table].width, 25);
            assert_eq!(traces[table].values[24], F::ZERO);
            eprintln!("allowed unused clock change in padding Exit");
            let mut padding = traces.clone();
            padding[table].values[0] += F::ONE;
            accept_traces::<P>(&public, padding);
            24
        } else {
            0
        };
        eprintln!("changed column {column} of table {table}");
        let mut changed = traces.clone();
        changed[table].values[column] += F::ONE;
        reject_traces::<P>(&public, changed);
    }
}
