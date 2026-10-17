//! Native ROM exclusion through Clean's emitted AIR, distinct from SP1 runtime mprotect.

extern crate alloc;

#[path = "support/backend.rs"]
mod backend;

use backend::{assert_backend_rejection, config, fixed_trace, physical_reference};
use clean_backend::{prove_ensemble, verify_ensemble, GeneratedAirSpec};
use p3_field::{PrimeCharacteristicRing, PrimeField64};
use p3_koala_bear::KoalaBear as F;
use p3_matrix::Matrix;
use serde_json::Value;
use std::collections::BTreeSet;

#[allow(dead_code, unused_imports, unused_variables, unused_parens)]
mod rom {
    include!(concat!(
        env!("CLEAN_ENSEMBLE_EXPORT_DIR"),
        "/write_permission.rs"
    ));
}
#[allow(dead_code, unused_imports, unused_variables, unused_parens)]
mod empty {
    include!(concat!(
        env!("CLEAN_ENSEMBLE_EXPORT_DIR"),
        "/write_permission_empty.rs"
    ));
}

const LIMIT: u64 = 1 << 48;
// Independent input: instruction PCs, not Lean's generated interval inventory.
const ROM: [u64; 4] = [131072, 65536, 65536, 0x2_0004_0004];

fn code_bytes() -> BTreeSet<u64> {
    ROM.into_iter().flat_map(|pc| pc..pc + 4).collect()
}

fn limbs(address: u64) -> Vec<F> {
    (0..3)
        .map(|limb| F::from_u64((address >> (16 * limb)) & 0xffff))
        .collect()
}

fn inputs(first: u64, second: u64) -> Vec<F> {
    [limbs(first), limbs(second)].concat()
}

fn reference() -> Value {
    serde_json::from_str(include_str!(concat!(
        env!("CLEAN_ENSEMBLE_EXPORT_DIR"),
        "/write_permission.reference.json"
    )))
    .unwrap()
}

fn permitted(public: &[F], empty: bool) -> bool {
    let code = code_bytes();
    public.chunks_exact(3).all(|limbs| {
        let canonical = limbs.iter().all(|limb| limb.as_canonical_u64() < 65536);
        let address = limbs
            .iter()
            .enumerate()
            .map(|(i, limb)| limb.as_canonical_u64() << (16 * i))
            .sum::<u64>();
        canonical && address < LIMIT && (empty || !code.contains(&address))
    })
}

#[test]
fn fixed_intervals_are_the_complement_of_literal_rom_bytes() {
    let mut intervals = Vec::new();
    let mut lower = 0;
    for protected in code_bytes() {
        if lower < protected {
            intervals.push([limbs(lower), limbs(protected - 1), vec![F::ONE]].concat());
        }
        lower = protected + 1;
    }
    if lower < LIMIT {
        intervals.push([limbs(lower), limbs(LIMIT - 1), vec![F::ONE]].concat());
    }
    let fixed = fixed_trace::<rom::Ensemble>(1);
    assert_eq!(fixed.width(), 7);
    assert_eq!(fixed.height(), intervals.len().next_power_of_two());
    for (index, row) in fixed.values.chunks(7).enumerate() {
        assert_eq!(
            row,
            intervals.get(index).cloned().unwrap_or(vec![F::ZERO; 7])
        );
    }
    let fixed = fixed_trace::<empty::Ensemble>(1);
    assert_eq!(
        fixed.values,
        [limbs(0), limbs(LIMIT - 1), vec![F::ONE]].concat()
    );
}

#[test]
fn generated_rows_and_complete_ledgers_match_lean_and_native_policy() {
    for empty_rom in [false, true] {
        let reference = reference();
        for case in reference[if empty_rom { "empty" } else { "rom" }]
            .as_array()
            .unwrap()
        {
            let public: Vec<F> = case["publicInput"]
                .as_array()
                .unwrap()
                .iter()
                .map(|value| F::from_u64(value.as_u64().unwrap()))
                .collect();
            let expected = permitted(&public, empty_rom);
            assert_eq!(
                expected,
                case["accepted"].as_bool().unwrap(),
                "{}",
                case["name"]
            );
            let generated = if empty_rom {
                empty::generate::<F>(&public, &[])
            } else {
                rom::generate::<F>(&public, &[])
            };
            assert_eq!(
                generated.is_ok(),
                case.get("witness").is_some(),
                "generation outcome: {}",
                case["name"]
            );
            match generated {
                Err(_) => assert!(!expected, "{}", case["name"]),
                Ok(witness) => {
                    let actual = if empty_rom {
                        physical_reference::<empty::Ensemble>(&public, &witness.tables)
                    } else {
                        physical_reference::<rom::Ensemble>(&public, &witness.tables)
                    };
                    assert_eq!(actual, case["witness"], "{}", case["name"]);
                    // Witness generation does not replace AIR acceptance: malformed limbs can
                    // generate rows, and their local range assertions must still reject them.
                    let config = config();
                    let traces = witness.into_traces().unwrap();
                    let heights: Vec<usize> = traces.iter().map(Matrix::height).collect();
                    if empty_rom {
                        let statement = empty::Statement::<F>::new(&heights).unwrap();
                        let check = || {
                            let (proof, _) =
                                prove_ensemble(&config, &statement, traces, &public).unwrap();
                            verify_ensemble(&config, &statement, &proof, &public).is_ok()
                        };
                        if expected {
                            assert!(check());
                        } else {
                            assert_backend_rejection(|| !check());
                        }
                    } else {
                        let statement = rom::Statement::<F>::new(&heights).unwrap();
                        let check = || {
                            let (proof, _) =
                                prove_ensemble(&config, &statement, traces, &public).unwrap();
                            verify_ensemble(&config, &statement, &proof, &public).is_ok()
                        };
                        if expected {
                            assert!(check());
                        } else {
                            assert_backend_rejection(|| !check());
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn backend_rejects_forged_intervals_counts_public_inputs_and_witness_cells() {
    let public = inputs(65540, 65540);
    let witness = rom::generate::<F>(&public, &[]).unwrap();
    assert_eq!(witness.tables.len(), 2);
    assert_eq!(witness.tables[0].len(), 2);
    assert_eq!(
        witness.tables[1]
            .iter()
            .map(|row| row[7].as_canonical_u64())
            .sum::<u64>(),
        2
    );
    assert!(witness.tables[1].iter().any(|row| row[7] == F::ZERO));
    let traces = witness.into_traces().unwrap();
    let heights: Vec<usize> = traces.iter().map(Matrix::height).collect();
    let statement = rom::Statement::<F>::new(&heights).unwrap();
    let config = config();
    let (proof, _) = prove_ensemble(&config, &statement, traces.clone(), &public).unwrap();
    verify_ensemble(&config, &statement, &proof, &public).unwrap();
    for column in 0..6 {
        let mut forged = public.clone();
        forged[column] += F::ONE;
        assert!(verify_ensemble(&config, &statement, &proof, &forged).is_err());
    }
    // Address, all endpoint limbs, and one auxiliary witness are mutable trace cells.
    for column in 0..10 {
        let mut forged = traces.clone();
        forged[0].values[column] += F::ONE;
        assert_backend_rejection(|| {
            let (proof, _) = prove_ensemble(&config, &statement, forged, &public).unwrap();
            verify_ensemble(&config, &statement, &proof, &public).is_err()
        });
    }
    for row in 0..traces[1].height() {
        let mut forged = traces.clone();
        forged[1].values[row] += F::ONE;
        assert_backend_rejection(|| {
            let (proof, _) = prove_ensemble(&config, &statement, forged, &public).unwrap();
            verify_ensemble(&config, &statement, &proof, &public).is_err()
        });
    }
    assert_eq!(rom::Ensemble::FIXED_WIDTHS, &[0, 7]);
    assert!(rom::Statement::<F>::new(&[2, heights[1] * 2]).is_err());
}
