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

## Lean: turning a theorem into a `def` + API / apply-lemma debugging

| Symptom | Read |
|---|---|
| `unknown identifier 'h'` in a helper whose statement doesn't use `h`; `simp` "unsolved goals" you can't see; structural `simp` lemma won't fire (a compute lemma rewrote the pattern); `rw [someDef]` errors; mismatched `mkQ x` vs `Quotient.mk x` | [`lessons_learned.md`](lessons_learned.md) (2026-06-14, "Debugging the apply-lemma when ∃→def") + [`../mathlib-proof-polishing.md`](../mathlib-proof-polishing.md) §Structural polish |
| Should I keep the `exists_…` wrapper next to the new `def`? Is this corollary worth keeping / "pending"? `variable (φ ψ)` parse error or `theDef h` fails after making params explicit; is "Procrustes"/field-term prose OK; which file should a `def` live in | [`lessons_learned.md`](lessons_learned.md) (2026-06-14, "Maintainer follow-up on the `def`") + [`../mathlib-proof-polishing.md`](../mathlib-proof-polishing.md) §"Maintainer follow-up" |
| How do I run the `mathlib-quality` skill (`/cleanup`, golfing rules) without stripping our AI-authorship provenance? What's the carve-out for staging vs the fork? `lemma` vs `theorem` — is there a rule? | [`../mathlib-quality-adapter.md`](../mathlib-quality-adapter.md) |
| Reviewer collapsed my `simpa only [long @[simp] list] using fact.symm` to `simp [fact]`; when do I pin an explicit `simp only` vs use bare `simp`; should a terminal simp keep the explicit list / the `.symm`? | [`lessons_learned.md`](lessons_learned.md) (2026-06-14, "Terminal `simp`: collapse, don't pin") + [`../mathlib-proof-polishing.md`](../mathlib-proof-polishing.md) §"The second pass" |
| Should I make this a `def` or keep the `∃` theorem? How do I tell if the object is unique/canonical? Is `#print axioms` the right test? | [`../mathlib-proof-polishing.md`](../mathlib-proof-polishing.md) §"Structural polish" point 0 (canonicity test: choice-free *term*, not the axiom closure) |

## Consuming reviewer feedback / instructions

| Symptom | Read |
|---|---|
| Over-built a framework / ran a too-broad sweep / mis-scoped after reading reviewer feedback that was an **LLM rephrasing** with invented meta-structure | [`lessons_learned.md`](lessons_learned.md) (2026-06-14, "Over-relying on a ChatGPT rephrasing") |

## How to extend

Add a row when you write a postmortem. Phrase the **Symptom** column the way
you'd search for it from *inside* the bug — the literal error text or the
confusing behavior — not the post-diagnosis vocabulary.
