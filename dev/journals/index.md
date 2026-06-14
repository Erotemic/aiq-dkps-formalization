# Journal index

Use this index when debugging a confusing symptom. Search `dev/journals/` when
in doubt; this file is a routing aid, not a complete replacement for grep (see
[`../SEARCH.md`](../SEARCH.md)).

## Comparator / export

| Symptom | Read |
|---|---|
| Comparator prints `Challenge and solution theorem statement do not match` even though the module builds, `#print axioms` is clean, and `pp.all #check` looks identical | [`comparator-statement-export-matching-2026-06-14.md`](comparator-statement-export-matching-2026-06-14.md) |
| `#print <name>` shows different `.{u_1,u_2,u_3}` vs `.{u_1,u_2,u_4}` universe signatures for "the same" theorem | [`comparator-statement-export-matching-2026-06-14.md`](comparator-statement-export-matching-2026-06-14.md) |
| Restated conformance: `failed to synthesize instance` although the source compiles | [`comparator-statement-export-matching-2026-06-14.md`](comparator-statement-export-matching-2026-06-14.md) |
| Leaderboard: `Unknown constant ForMathlib.X` — the declaration lives in a different ForMathlib module than expected | [`comparator-statement-export-matching-2026-06-14.md`](comparator-statement-export-matching-2026-06-14.md) |

## Provenance / verification process

| Symptom | Read |
|---|---|
| A `grep sorry` reports sorries in libraries that are actually clean (matched docstring prose like "no `sorry` remains") | [`comparator-statement-export-matching-2026-06-14.md`](comparator-statement-export-matching-2026-06-14.md) (and benchmark Q3) |

## Consuming reviewer feedback / instructions

| Symptom | Read |
|---|---|
| Over-built a framework / ran a too-broad sweep / mis-scoped after reading reviewer feedback that was an **LLM rephrasing** with invented meta-structure | [`lessons_learned.md`](lessons_learned.md) (2026-06-14, "Over-relying on a ChatGPT rephrasing") |

## How to extend

Add a row when you write a postmortem. Phrase the **Symptom** column the way
you'd search for it from *inside* the bug — the literal error text or the
confusing behavior — not the post-diagnosis vocabulary.
