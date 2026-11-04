//! Pair a built-in export with its native reference.

macro_rules! fixture {
    ($name:ident, $stem:ident) => {
        #[allow(dead_code, unused_imports, unused_variables, unused_parens)]
        mod $name {
            pub use sp1_clean_comparison::generated::$stem::*;
            pub fn reference() -> serde_json::Value {
                serde_json::from_str(include_str!(concat!(
                    env!("CLEAN_ENSEMBLE_EXPORT_DIR"),
                    "/",
                    stringify!($stem),
                    ".reference.json"
                )))
                .unwrap()
            }
        }
    };
}

pub(crate) use fixture;
