//! Pair a built-in export with its native reference.

macro_rules! fixture {
    ($name:ident, $stem:literal) => {
        #[allow(dead_code, unused_imports, unused_variables, unused_parens)]
        mod $name {
            include!(concat!(
                env!("CLEAN_ENSEMBLE_EXPORT_DIR"),
                "/",
                $stem,
                ".rs"
            ));
            pub fn reference() -> serde_json::Value {
                serde_json::from_str(include_str!(concat!(
                    env!("CLEAN_ENSEMBLE_EXPORT_DIR"),
                    "/",
                    $stem,
                    ".reference.json"
                )))
                .unwrap()
            }
        }
    };
}

pub(crate) use fixture;
