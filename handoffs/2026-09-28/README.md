# September 28 talk: evidence handoff

This draft PR is a delivery channel for the presentation agent. It contains the already validated evidence, with no new circuit implementation or slide/source-pin edits. It is intended for review and transfer rather than merging this archival snapshot into the maintained codebase.

**Start with [the evidence index](evidence/README.md).** Read the files directly on GitHub or [download the complete evidence archive](evidence.tar.gz). The archive is an unchanged copy of the locally delivered bundle.

| Talk material | Evidence page | Code PR |
|---|---|---|
| Actual ADD witness and seven rejected mutations; complete counter compiler and acceptance equivalence | [Examples](evidence/examples/README.md) | [#100](https://github.com/dtumad/sp1-lean/pull/100) |
| Three gadgets through BN254 WASM/full R1CS, including a rejected result and a valid inverse-of-zero mutation | [Backend](evidence/backend/README.md) | [#104](https://github.com/dtumad/sp1-lean/pull/104) |
| Full official Sail branch step joined to real event compilation and the generated local circuit row | [Branch](evidence/branch/README.md) | [#106](https://github.com/dtumad/sp1-lean/pull/106) |

Each page includes reproducible commands, actual outputs, exact revisions, dependency pins, cache conditions, validation provenance, remaining boundaries and speaker wording. Counter and branch theorem statements/axioms are included literally; executable tests are distinguished from universal production proofs.

The evidence directory and archive retain their original status snapshots. Since that capture, #103 has merged into main. The [publication-time #106 snapshot](publication-ci.json) records guards/core build/handoff passing and full alignment CI still running at the last check. Refresh the live PR before changing the talk's claims. Successful local validation is already recorded, including the final commit's identical source-tree relationship to the complete validation run.

Archive SHA-256:

```text
eff37fb6b3fca6857145960a08c04874063e8d2c4177fc89180e7ea0b1bb09f7  evidence.tar.gz
```

After extracting, run `shasum -a 256 -c SHA256SUMS` inside `presentation-evidence/`. The same per-file manifest is available in [the browsable directory](evidence/SHA256SUMS).

For the presentation refresh:

- Use the captured counter's `2→5` output, rather than labeling the schematic `3→5` as that output.
- Report five accepted and 21 rejected backend mutations; inverse seven is deliberately valid.
- Keep the joined branch claim at local chip acceptance; full assembled balance and general compiler completeness remain separate.
- Update the talk's pin, excerpts and wording coherently, then rebuild the deck. This PR does not change the talk repository.
