//! Shared generated assembly fixtures, compiled as a library for the comparison binaries.

#[cfg(feature = "assembly-export")]
extern crate alloc;

#[cfg(feature = "assembly-export")]
pub mod generated {
    include!(concat!(
        env!("CLEAN_ENSEMBLE_EXPORT_DIR"),
        "/shared_assemblies.rs"
    ));
}
