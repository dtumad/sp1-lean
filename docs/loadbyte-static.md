# LoadByte with a fixed byte table

`LoadByteStaticChip` is a separately named native alternative. It uses exactly the existing
LoadByte assumptions, semantic specification, event inputs and generated witness cells. The
original circuit, registry entry and whole-chip Rust-faithfulness proof remain unchanged.

The alternative replaces the selected-limb U8Range pair request with two lookups in Clean's
existing 256-row `Gadgets.ByteTable`. Each lookup checks `isReal * byte`, so inactive rows keep
their original byte-witness freedom. The production soundness/completeness proofs and the
fixed-table realization justify the replacement. Fixed-table rows never come from prover data.

Run from a prepared pinned checkout:

```sh
scripts/check_loadbyte_static.sh
```

Install Git, Python 3 and elan, then explicitly install the toolchain named in `lean-toolchain`
and prepare pinned dependencies with `lake exe cache get` if needed. Do not run bare `lake update`.
The runner validates every dependency revision and rejects tracked dependency edits. It neither
installs tools nor downloads caches. Build before using a standalone `lake env lean` inspection;
that command does not rebuild dependencies.

The executable driver checks 64 cases: LB and LBU, all eight byte offsets, and byte values 0, 127,
128 and 255. Positive rows use `MemoryEvent.toLoadByteInputs`. Additional cases reject a wrong
low byte, contradictory selectors and an active out-of-range byte; accept an inactive row with
low byte and selected byte 300; and retain reader demand whose U8Range key equals the removed
selected-limb request. `native_decide` occurs only in the test library.

The comparison uses 64 active consumer rows and one inactive row on both sides. The old assembly
has one dedicated selected-pair provider row per consumer, including the inactive consumer.
The new assembly removes those dedicated providers. Both sides retain identical residual
provider tables, generated from the actual remaining reader requests. Duplicate keys are kept
as separate occurrences. Raw interaction counts include zero multiplicities.

For this exact workload, the measured counts are:

| Metric | Original | Alternative |
| --- | ---: | ---: |
| Consumer input / witness cells | 2,795 / 260 | 2,795 / 260 |
| Consumer assertions | 2,080 | 2,080 |
| Consumer raw interactions | 1,495 | 1,430 |
| Dedicated / shared residual provider rows | 65 / 800 | 0 / 800 |
| Assembly physical rows | 930 | 865 |
| Assembly input / witness cells | 4,846 / 13,748 | 4,651 / 12,708 |
| Assembly total cells | 18,594 | 17,359 |
| Assembly assertions | 16,786 | 15,616 |
| Assembly raw interactions | 2,360 | 2,230 |
| Assembly raw Byte interactions | 1,775 | 1,645 |
| Assembly zero-multiplicity Byte occurrences | 47 | 45 |
| Fixed lookup occurrences | 0 | 130 |
| Maximum assertion degree bound | 3 | 3 |
| Maximum lookup-entry degree bound | 0 (none) | 2 |

The alternative's fixed table has 256 rows. Both aggregate Byte ledgers balance, and all
69 regression expectations pass. These figures measure the dedicated-provider fixture;
they are not timing measurements or a count of the canonical SP1 provider inventory.

The executable tests close the Byte ledger and check every local assertion and fixed lookup in
these tables. State, Memory and Program interactions remain visible consumer demand. This is
not an all-channel execution witness. The production assembly transport theorem treats arbitrary
shared residual tables separately; its stated premises and conclusions are included in the
literal declaration report. There is no claim here about a canonical aggregated inventory,
whole-core speedup, or R1CS cost.

Reports are written under `.lake/build/loadbyte-static/`:

- `results.json`: actual input/witness cell, assertion, fixed-lookup, interaction and provider-row counts;
  degree bounds computed from actual expression syntax; and every regression outcome.
- `axioms.log`: literal Lean signatures and axiom dependencies of the production theorems.
- `commands.log`: executed commands, exit codes, stdout, stderr and elapsed times.
- `provenance.json`: exact source revision, dirty status, toolchain, all dependency pins,
  preexisting cache conditions and available CI environment identifiers.

The reported degree is a syntactic polynomial upper bound, without cancellation or backend
lowering. Timings use whatever prepared artifacts are recorded in provenance; they are not
cold-build benchmarks. Local runs have empty CI identifiers. A recorded CI invocation describes
that execution and does not attest to later revisions or unrelated jobs.
On a pull request, `GITHUB_SHA` records the integration checkout and `SP1_LOADBYTE_PR_HEAD`
records the PR head separately.

Speaker paragraph: We can change how this native chip checks a byte while preserving its
semantic contract and every witness cell. The new fixed lookups remove one selected request
and its dedicated provider contribution per physical row, while retaining reader requests with
the same key. The report measures that precise assembly change and tests both active loads and
inactive witness freedom. It is a proved local alternative, separate from the unchanged
Rust-faithful chip and the larger SP1 capstone.
