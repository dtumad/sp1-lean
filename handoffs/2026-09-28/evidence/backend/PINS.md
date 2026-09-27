Exact local revision: `698bec03cf75327921a694c55a219d340a77ea47`, branch `codex/backend-gadget-conformance`, [PR #104](https://github.com/dtumad/sp1-lean/pull/104).

All 14 installed dependency checkouts matched their resolved pins and had no tracked edits before reproduction. The existing shell checker repeats those checks before building. Floating-looking `inputRev` strings on inherited packages are resolved by the committed manifest to the immutable revisions below; this run did not update them.

| Dependency | Resolved and observed revision | Repository |
|---|---|---|
| PolyFun | `997828ce4c04ccdc01f5f199069e26a6195ef6e7` | https://github.com/Verified-zkEVM/PolyFun |
| Sail | `bde9ecc665b663bbdb29afb11fb6634870fdc7df` | https://github.com/dtumad/lean-sail |
| Clean | `fba2a29f5e36420d797c1de118ac9f11f23b819e` | https://github.com/Verified-zkEVM/clean |
| mathlib | `0df444a360eaa60ab8c11dca51a86af692955474` | https://github.com/leanprover-community/mathlib4 |
| cslib | `98e395a701f2027a413ad24729e1a11a6c772eb4` | https://github.com/leanprover/cslib |
| CompPoly | `a09455a22fea4623a2a1c5b363cf6efc61486a83` | https://github.com/Verified-zkEVM/CompPoly.git |
| plausible | `b7eb3304aeae834b12dda98993a37f6a41f6f0bb` | https://github.com/leanprover-community/plausible |
| LeanSearchClient | `5f4d51b81cbd3f6b32b156bfad9056621a040404` | https://github.com/leanprover-community/LeanSearchClient |
| importGraph | `16f02aa7642864af59f1ff0e384a015994db9118` | https://github.com/leanprover-community/import-graph |
| proofwidgets | `4be2e3d5087eeb272cf5a8853b8f9dd025ef5957` | https://github.com/leanprover-community/ProofWidgets4 |
| aesop | `3448c0bcc5ce01b2d1546e483ec3620e32df3d0e` | https://github.com/leanprover-community/aesop |
| Qq | `92c15be17b7caf78c2ad767ec40f89052d908d81` | https://github.com/leanprover-community/quote4 |
| batteries | `4488d40d070b9700d4d5a6aa342f0d40c31b2a2d` | https://github.com/leanprover-community/batteries |
| Cli | `6130a47896ce867c6a4a55373441e59e565bad0f` | https://github.com/leanprover/lean4-cli |

Toolchain: `leanprover/lean4:v4.33.1`; local Lean commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, arm64-apple-darwin24.6.0, Release. Lake `5.0.0-src+819816b`.

Checker pins: Node `22.16.0`, snarkjs `0.7.6` (the local package, lock, artifact manifest and installed version agree). The entire npm transitive graph, resolved package URLs and integrity hashes are in [package-lock.json](pins/package-lock.json). Observed local npm `11.5.2`, Python `3.9.6`, git `2.54.0`, macOS `26.4.1` build `25E253`. npm/Python/git/macOS are recorded environment versions, not additional repository pins. No `circom` executable is used.

Exact source copies: [lakefile](pins/lakefile.toml), [Lake manifest](pins/lake-manifest.json), [Lean toolchain](pins/lean-toolchain), [npm package](pins/package.json), [npm lock](pins/package-lock.json). The backend's Clean provenance is `fba2a29f5e36420d797c1de118ac9f11f23b819e`; CompPoly supplies the existing BN254 scalar-field prime certificate. Sail is a repository dependency but the native backend exporter uses a Sail-free import closure.

The field is BN254 scalar field, characteristic `21888242871839275222246405745257275088548364400416034343698204186575808495617`. SP1 v6.4.0 uses KoalaBear, characteristic `2130706433`, as recorded in the copied [SP1Field.lean](source/SP1Field.lean). This campaign does not export the SP1 field.

[Before metadata](pins/environment-before.json) records cache presence, tool output, resolved/observed dependency commits, and clean status; [after metadata](pins/environment-after.json) confirms the same head and clean status. Empty `statusPorcelain` means `git status --porcelain=v1` returned no entries; ignored build/package data are intentionally absent from that status. The native executable was already present and its SHA-256 remained `900030b4017d72e7b39bb4c9ec3a9566a6d5ca4b7fb4cd25bad0c4fb13511b5e`.
