//! Shared backend configuration and literal witness comparisons for export fixtures.

use clean_backend::{witness_generation::Program, StarkConfig};
use p3_challenger::DuplexChallenger;
use p3_commit::ExtensionMmcs;
use p3_dft::Radix2DitParallel;
use p3_field::{extension::BinomialExtensionField, Field, PrimeField64};
use p3_fri::{create_test_fri_params, TwoAdicFriPcs};
use p3_koala_bear::{KoalaBear as F, Poseidon2KoalaBear};
use p3_merkle_tree::MerkleTreeMmcs;
use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};
use rand::{rngs::SmallRng, SeedableRng};

type Perm = Poseidon2KoalaBear<16>;
type Hash = PaddingFreeSponge<Perm, 16, 8, 8>;
type Compress = TruncatedPermutation<Perm, 2, 8, 16>;
type Mmcs = MerkleTreeMmcs<<F as Field>::Packing, <F as Field>::Packing, Hash, Compress, 8>;
type Challenge = BinomialExtensionField<F, 4>;
type ChallengeMmcs = ExtensionMmcs<F, Challenge, Mmcs>;
type Challenger = DuplexChallenger<F, Perm, 16, 8>;
type Pcs = TwoAdicFriPcs<F, Radix2DitParallel<F>, Mmcs, ChallengeMmcs>;
pub type Config = StarkConfig<Pcs, Challenge, Challenger>;

pub fn config() -> Config {
    let mut rng = SmallRng::seed_from_u64(7);
    let permutation = Perm::new_from_rng_128(&mut rng);
    let mmcs = Mmcs::new(
        Hash::new(permutation.clone()),
        Compress::new(permutation.clone()),
    );
    let fri = create_test_fri_params(ChallengeMmcs::new(mmcs.clone()), 0);
    let pcs = Pcs::new(Radix2DitParallel::default(), mmcs, fri);
    Config::new(pcs, Challenger::new(permutation))
}

// Release mode verifies a rejected proof; debug mode can reject invalid constraints earlier.
// Propagate unrelated panics instead of treating an arbitrary crash as rejection.
pub fn assert_backend_rejection(check: impl FnOnce() -> bool) {
    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(check)) {
        Ok(rejected) => assert!(rejected, "invalid witness was accepted"),
        Err(payload) => {
            let message = payload
                .downcast_ref::<String>()
                .map(String::as_str)
                .or_else(|| payload.downcast_ref::<&str>().copied())
                .unwrap_or("");
            if !cfg!(debug_assertions)
                || !(message.contains("constraint") || message.contains("lookup"))
            {
                std::panic::resume_unwind(payload);
            }
        }
    }
}

pub fn interaction(
    channel: &str,
    mult: u64,
    message: Vec<u64>,
    assumes: bool,
) -> serde_json::Value {
    serde_json::json!({
        "channel": channel, "message": message,
        "multiplicity": mult, "assumeGuarantees": assumes,
    })
}

pub fn physical_reference<P: Program<F>>(
    public: &[F],
    tables: &[Vec<Vec<F>>],
) -> serde_json::Value {
    let interactions = P::verifier_interactions(public)
        .into_iter()
        .chain(tables.iter().enumerate().flat_map(|(component, rows)| {
            rows.iter()
                .flat_map(move |row| P::interactions(component, row))
        }))
        .map(|entry| {
            interaction(
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
        .collect::<Vec<_>>();
    let rows = tables
        .iter()
        .map(|table| {
            table
                .iter()
                .map(|row| {
                    row.iter()
                        .map(PrimeField64::as_canonical_u64)
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    serde_json::json!({"tables": rows, "interactions": interactions})
}
