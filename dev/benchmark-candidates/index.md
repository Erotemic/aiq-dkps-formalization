# Benchmark candidate index

Use this before restating theorems, slimming conformances, choosing leaves, or
matching a comparator export. Benchmark candidates are distilled invariant traps
from real mistakes in this repo. This file routes by failure class; it is not a
replacement for grep (see [`../SEARCH.md`](../SEARCH.md)).

## Comparator / export invariants

| Failure class | Read |
|---|---|
| A Mathlib-only conformance drops an unused `variable`; semantically-identical statement, but the export's universe signature shifts → `statement do not match` | [`lean-questions.md`](lean-questions.md) Q1 |
| Conformance omits an *accumulated section instance* the solution's signature carries (instance telescope mismatch) | [`lean-questions.md`](lean-questions.md) Q2 |
| General: a conformance must mirror the source's *exact* binder telescope (type vars + instances) because the exporter doesn't alpha-normalize | [`lean-questions.md`](lean-questions.md) Q1, Q2 |

## Proof / kernel / hygiene invariants

| Failure class | Read |
|---|---|
| Using a `grep sorry` (matching comment prose) as the trust boundary for sorry-freeness instead of `#print axioms` | [`lean-questions.md`](lean-questions.md) Q3 |

## How to extend

Add a row here when you add a question. Prefer routing by the **invariant** (what
a model fails at), with the surface API as a secondary cue. Spin a question into
its own `topic-YYYY-MM-DD.md` file when it gets long or focused, and link it from
the relevant row.
