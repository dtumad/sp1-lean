# Architecture

The library separates execution meaning from circuit implementations, machine assembly and
backend integration. Specifications should be readable without unfolding witness generation,
and a chip should be understandable with its local correctness proofs.

## Current ownership

| Area | Current source | Responsibility |
|---|---|---|
| Semantics | `SP1Clean/Math/`, `SP1Clean/Model/` | Arithmetic, official Sail adapters, complete execution, snapshots, host effects and resources |
| Contracts | `SP1Clean/FormalModel/` | Semantic Specs and checked relation/capstone targets |
| Circuits | `SP1Clean/Circuits/Types/`, `SP1Clean/Native/`, `SP1Clean/Proofs/Chips/`, `SP1Clean/Proofs/Operations/` | Native columns/readers/gadgets/chips, witnesses and local soundness/completeness |
| Machine | `SP1Clean/Soundness/`, `SP1Clean/Proofs/Completeness/`, `SP1Clean/Alignment/` | Registration, assembly, grounding, Sail bridges and physical compiler |
| Legacy Rust alignment | `SP1Clean/Extracted/`, `SP1Clean/Faithful/`, `SP1Clean/Composition/` | Generated pinned oracles and exact-to-native comparison evidence |
| Upstream additions | `ToClean/`, `ToPolyFun/`, `ToMathlib/` | Reusable missing APIs in upstream namespaces, independent of SP1 |
| Tests | `SP1CleanTest/` | Executable examples, non-vacuity, adversarial witnesses and native computation |

The current import rules are encoded in [layering.txt](../scripts/layering.txt);
[the layering guide](layering.md) describes their mechanical enforcement.
The core index is [SP1Clean/Core.lean](../SP1Clean/Core.lean); the full index is
[SP1Clean.lean](../SP1Clean.lean). Tests never feed production imports.

## Consolidation direction

[#16](https://github.com/dtumad/sp1-lean/issues/16) moves ownership into purpose-oriented
**Semantics / Circuits / Machine / Export** areas, guided by Clean's Specs, Types, Gadgets,
Air and Backends organization. This is an in-progress migration, not a description of a completed
directory move.

Contracts stay below implementations. Feature directories colocate definitions, witness generation
and local proofs; machine-specific grounding stays in Machine. Lean module visibility supplies
public entry points and private implementation details, with exposed definitions only where
consumers need reduction. [#33](https://github.com/dtumad/sp1-lean/issues/33) owns that migration,
including generated Sail prerequisites.

Complete API migrations replace old objects and all in-repository consumers. There is no external
compatibility requirement. Prefer one transition/trace, one interpretation/Realizes boundary,
one complete finite state with projections, and one typed physical inventory. Retain distinctions
that express different meanings: finite versus realized state, event versus physical row, semantic
limit versus witness capacity, and raw ledger versus a derived accounting view.

## Proof boundaries

A semantic `Spec` describes the intended relation; it does not repeat assertions. A bundled
Clean circuit is the compositional proof boundary. Parents invoke child `circuit` interfaces
rather than inline the implementation or reconstruct its soundness proof.

Channels carry actual field tuples and multiplicities. Global execution truth is derived from
raw constraints, complete balance, authenticated boundaries and ranked chronology; it is not
smuggled into a channel payload. Keep occurrence lists through transformations: equal keys do
not identify occurrences, and disabled interactions still affect characteristic bounds.

SP1 grounding needs an exhaustive ordered execution path. Clean verifier guarantees alone do
not supply it, so adopting VmTables is justified only when it removes the existing obligation.
Generalize authentication, ordering or resource arguments when a real consumer demonstrates
the abstraction.

Native readers and operations own their shared column types under `Circuits/Types`. These modules
and the word foundation use Lean module mode. The import gate rejects any transitive dependency
from native circuits back into `Extracted`. Legacy Rust oracles reuse the native types only after
the generator checks their field layouts against independent Rust reflection output; the
assertion and interaction definitions remain generated migration evidence.

## Upstream and generated boundaries

To* means “To Upstream”: additions belong in the namespace they would have upstream and state
the missing capability in their module documentation. ToMathlib imports Mathlib; ToPolyFun imports
PolyFun; ToClean imports Clean and may use those two. None imports SP1Clean.

Prefer additions over dependency forks. A fork is reserved for a required modification of a
canonical declaration that cannot be expressed at an extension layer. Its patch and exit remain
explicit. Built-in Clean export is the integration owner; thin SP1 adapters should not become
another emitter, expression IR, interpreter or scheduler.

Generated Sail output is owned by its pinned generator/runtime pair. Legacy Rust oracles are owned
by their generator until migration. See [provenance](../scripts/provenance.json),
[export](export.md) and [assurance](assurance.md) for the distinct trust boundaries.
