# Rust comparison

[sp1-comparison](sp1-comparison/README.md) tests Clean's generated Rust AIR and witnesses
against the released SP1 revision in [provenance](../scripts/provenance.json).

Run `python3 scripts/check_ensemble_export.py` from the repository root. It builds the export
fixtures, generates twice, checks artifact identity and runs both locked Rust configurations.
Generated Rust, references and logs stay under `.lake/ensemble-export/`.

These are executable comparisons, not formal lowering or cryptographic soundness proofs.
The former JSON interpreter, reverse extractor and committed SP1 dumps are retired.
