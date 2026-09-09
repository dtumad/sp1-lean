# Axiom and trust ledger

Checked against the consolidated stack on 2026-09-08. Each raw file retains the source revision
at which its unchanged declaration inventory was recorded:
[`axiom-census.txt`](axiom-census.txt) (the main library, including `ToClean`, 937 declarations) and
[`axiom-census-test.txt`](axiom-census-test.txt) (the `SP1CleanTest` anchors, 77 declarations).
`scripts/run_audit.sh` reproduces both and rejects dependency drift. The main and test split lets
CI elaborate each probe against the library built by that job.

## Result

- 1014 released declarations are probed.
- No source proof deferrals or project `axiom` declarations occur in the main library.
- No probed declaration carries `sorryAx`.
- Kernel bypasses and `native_decide` are absent from the main library.
- Compiler-trusted executable witnesses and regressions are isolated in `SP1CleanTest/`.

There is no direct-admission allowlist and no transitive `sorryAx` carrier allowlist. Both are empty.
The census is an explicit released-declaration inventory, not a claim that every declaration in the
repository has been independently reviewed. Adding a new public claim requires adding its probe.

An unexplained change to an axiom set requires review. A changed generated bit-vector proof-constant
index can be harmless, but must still be inspected before updating the raw snapshots. Historical
inventory growth and retired proof names can be recovered from git history.

## Dependency classes

The census reports several classes that should not be conflated:

| Class | Scope |
|---|---|
| `propext`, `Classical.choice`, `Quot.sound` | ordinary Lean/mathlib logical baseline |
| generated `bv_decide` proof constants | selected arithmetic and bit-vector helper proofs |
| generated Sail platform hooks | the official interpreter's external platform operations |
| generated `native_decide` constants | executable conformance tests only |
| `sorryAx` | forbidden; absent |

Most chip-local semantic and whole-chip faithfulness proofs use only the ordinary logical baseline.
Mul and several Sail bridges additionally retain generated bit-vector decision proofs. Execution
theorems stated against the complete Sail interpreter inherit its platform-hook surface, including
hooks not reached by the supported ordinary RV64IM paths.

`supported_core_native_sound` is proof-complete and `sorryAx`-free. Its census is not limited to the
three logical axioms because its target and its 25 Sail bridges retain the generated Sail and
bit-vector dependencies. The conditional exact-upstream
`sp1_air_refinement_of_obligations`/`sp1_air_sound_of_obligations` declarations inherit the same target
surface.

## Coverage of the probe generator

The generator scans:

- every chip's soundness, completeness, bundled circuit, and Sail bridge;
- Branch's split core proofs and DivRem's split completeness driver;
- every whole-chip faithfulness theorem, including the nested DivRem exact module;
- the proof-bearing 25-chip faithfulness index;
- witness and full-trace conformance anchors;
- the active official-Sail-step, deterministic-compiler-event, and bounded native non-vacuity join;
- the native grounding and soundness capstones;
- the generic ensemble correctness/export interfaces, fixed program provider, and finite
  program-image and host-memory frame proofs;
- the common shard evaluator, paired exact relation, natural-ledger bridge, and native
  correctness/language-equality surface;
- exact Core profile and manifest guards;
- the conditional exact-AIR refinement boundary;
- COMMIT-wrapper strengthening theorems; and
- registry, routing, balance, decode, and execution support theorems.

An incorrect fully qualified name causes probe elaboration to fail. The generator also compares
its new inventory with both committed probe files before writing either: losing a recorded name
fails even if a sibling still matches the same regular-expression target. This closes the partial
alternation failure that previously let a renamed `_core` theorem disappear from the census.

`python3 scripts/gen_axiom_probe.py --check` checks exact source/probe agreement without writing and
runs in CI. Intentional removals or renames require regenerating with `--allow-removals` and reviewing
the probe diff; that flag does not permit a configured target to match nothing. The audit-tool
regressions cover partial matches, both library inventories, intentional renames, and read-only
checking. This is protection against accidental coverage loss, not against a reviewer approving a
reduced inventory.

## Reproduce

```bash
lake build SP1Clean
lake test
python3 scripts/gen_axiom_probe.py --check
scripts/run_audit.sh
```

Use the raw census for declaration-level review. The summary above is intended to explain classes, not
replace that evidence.
