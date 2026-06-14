# Lean / Mathlib / comparator benchmark questions

Distilled invariant traps from real mistakes in this repo. Each entry is
self-contained. See [`README.md`](README.md) for the workflow and prompt levels,
[`index.md`](index.md) to route by failure class.

---

## Q1 — A "cleaned-up" Mathlib-only conformance drops an unused `variable`, and the comparator rejects a semantically-identical statement

Date: 2026-06-14 · Tags: `comparator-statement-match`, `universe-parameters`,
`lean4export`, `conformance-mirrors-source`, `mathlib-only-restatement`

**Level A — pre-error operation.**

You maintain a comparator "challenge" package. For each upstreamable theorem
there is a `Conformance.lean` that **imports only Mathlib** and restates the
theorem as `sorry` (the spec), and a `Leaderboard.lean` that imports the project
and supplies the real proof. The comparator exports both with `lean4export` and
checks the solution proves the conformance's statement with permitted axioms.

The source theorem lives in a file whose section reads:

```lean
-- ForMathlib/Analysis/InnerProductSpace/GramMatrix.lean
variable {𝕜 E F ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
-- … (other theorems that DO use F) …
variable [FiniteDimensional 𝕜 E]

theorem gram_eq_gram_iff_exists_linearIsometryEquiv_map_eq {φ ψ : ι → E} :
    gram 𝕜 φ = gram 𝕜 ψ ↔ ∃ W : E ≃ₗᵢ[𝕜] E, ∀ i, W (φ i) = ψ i := …
```

Your task: write the Mathlib-only conformance that exposes **only** this one
theorem as a `sorry` stub. The natural, tidy thing to write is:

```lean
variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

namespace Matrix
theorem gram_eq_gram_iff_exists_linearIsometryEquiv_map_eq {φ ψ : ι → E} :
    gram 𝕜 φ = gram 𝕜 ψ ↔ ∃ W : E ≃ₗᵢ[𝕜] E, ∀ i, W (φ i) = ψ i := by sorry
end Matrix
```

It builds green. `#print axioms` on the real theorem is clean. `set_option
pp.all true in #check @…` prints a type that looks **identical** to the
solution's. But the comparator fails:

```
uncaught exception: Challenge and solution theorem statement do not match:
'ForMathlib.Matrix.gram_eq_gram_iff_exists_linearIsometryEquiv_map_eq'
```

Why does it fail, and what is the minimal fix?

### Expected answer

The theorem doesn't use `F`, so you dropped it from the `variable` line — the
"obvious cleanup." But Lean assigns **universe parameters positionally by the
order variables are declared**, and the source's unused `F : Type*` sits between
`E` and `ι`, consuming a universe slot:

```
source (solution):  …map_eq.{u_1, u_2, u_4}   -- 𝕜=u_1, E=u_2, F=u_3 (unused, but reserved), ι=u_4
your conformance:    …map_eq.{u_1, u_2, u_3}   -- 𝕜=u_1, E=u_2, ι=u_3
```

The *types* are alpha-equivalent (three universe params, same body), but the
comparator's `lean4export` comparison is **name-sensitive on universe
parameters** — it does not alpha-normalize `{u_1,u_2,u_3}` against
`{u_1,u_2,u_4}`. So it reports "statement do not match" even though the
proposition is identical and `pp.all` `#check` looked the same (the `#check`
output shows `Type u_3` vs `Type u_4` in the body — easy to skim past;
`#print name` shows the leading `.{…}` signature explicitly).

**Minimal fix:** reproduce the source's *exact* `variable` context, including the
unused `F` and its instances, so the universe numbering matches:

```lean
variable {𝕜 E F ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 E]
```

**The invariant:** *a Mathlib-only conformance must mirror the source's variable
context exactly — including unused type variables and accumulated section
instances — because the exporter compares universe signatures and the full
instance telescope without alpha-normalizing. "Tidying away" anything the source
declares can shift the export even when the proposition is unchanged.*

**Validation:**

```lean
#print ForMathlib.Matrix.gram_eq_gram_iff_exists_linearIsometryEquiv_map_eq
-- compare the leading `.{…}` against the solution module's print
```
then the ground truth:
```bash
bash scripts/run_challenge_comparator.sh --config comparator/candidate-01-gram-rigidity.json
```

### Why this matters as a benchmark

- **It rewards distrusting `lake build`.** Build-green + axiom-clean + a
  pp.all type that *looks* identical all say "ship it." The failure is one rung
  below, in the export. A model that only checks compilation never sees it.
- **Counterintuitive direction.** Every instinct says "drop the unused
  variable." Here the unused variable is *load-bearing* for the export. The
  model must know universe params are positional over *declared* (not *used*)
  type variables, and that the exporter is name-sensitive.
- **Checkable:** `#print` shows the `.{…}` signature; the comparator is the
  ground truth; the fix is one line.

---

## Q2 — Same trap, instance flavour: the conformance omits an *accumulated section instance* the solution carries

Date: 2026-06-14 · Tags: `comparator-statement-match`, `instance-arg-order`,
`conformance-mirrors-source`

**Level B — error repair.**

A conformance restates a topology lemma; the source is:

```lean
-- ForMathlib/Topology/Berge.lean
variable {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]
-- … earlier in the section, before this theorem, the file adds:
--     variable [FirstCountableTopology X]   (used by the proof)
theorem continuous_iInf_of_isCompact [FirstCountableTopology P]
    {K : Set X} (hK : IsCompact K) (hKne : K.Nonempty)
    {g : P → X → ℝ} (hg : Continuous (Function.uncurry g)) :
    Continuous (fun p => ⨅ x : ↥K, g p ↑x) := …
```

The conformance copied only `variable {P X} [TopologicalSpace P] [TopologicalSpace X]`
and the theorem's own `[FirstCountableTopology P]`. It builds; the comparator
fails `statement do not match`. A `pp.all` `#check @…` diff shows the solution's
type has an **extra** `[@FirstCountableTopology X inst_1]` between
`[TopologicalSpace X]` and `[FirstCountableTopology P]` that the conformance
lacks. Fix it.

### Expected answer

In the source, `[FirstCountableTopology X]` is an *accumulated section variable*
added before this theorem; the proof uses it, so Lean includes it in the
signature — positioned by declaration order, i.e. **before** the theorem's own
`[FirstCountableTopology P]`. The conformance, with a `sorry` proof, will *not*
auto-include a section instance the statement doesn't mention, so you must add it
**explicitly, in the right order**:

```lean
theorem continuous_iInf_of_isCompact [FirstCountableTopology X] [FirstCountableTopology P]
    {K : Set X} … := by sorry
```

**Invariant:** the export carries the *entire instance telescope in declaration
order*. A conformance must reproduce every instance the solution's signature
contains, including ones that entered via accumulated `variable` lines, and in
the same order — a `sorry` proof won't pull them in for you.

**Validation:** `set_option pp.all true in #check @ForMathlib.continuous_iInf_of_isCompact`
in each module; diff the instance telescope. Then the comparator config.

### Why this matters

Sibling of Q1 (universe slot → instance slot). Together they teach the general
rule — *mirror the source's binder telescope exactly* — from two different
directions, so a model that only learned the universe case still gets caught.

---

## Q3 — "The papers have sorries!" — a `grep sorry` that matched docstring prose

Date: 2026-06-14 · Tags: `comment-grep-false-positive`, `sorry-hygiene`,
`print-axioms`

**Level C — distilled micro-question.**

You need to confirm four Lean libraries are sorry-free. You run:

```bash
grep -rn "sorry" Acharyya2024 Acharyya2025 DkpsQuench Helm2025 --include=*.lean \
  | grep -vE "/-|--.*sorry"
```

and report "Acharyya2024: 5 sorries, Acharyya2025: 1 sorry." Both numbers are
**wrong** (the libraries are clean). What did the grep catch, and what is the
correct check?

### Expected answer

The matches are **docstring/comment prose**, not `sorry` terms — lines like
`` Status: COMPLETE — no `sorry` remains `` and `` No `axiom`, no `sorry`. ``.
The `-vE "/-|--.*sorry"` filter only drops lines that *contain* a comment
opener; it does **not** drop the *body* lines of a multi-line `/- … -/` block,
so prose mentioning the word "sorry" sails through.

Correct checks, in order of trustworthiness:

1. **Ask the kernel, not grep:** `#print axioms <capstone>` — a real `sorry`
   anywhere in the proof tree surfaces as `sorryAx`. Clean output is
   `[propext, Classical.choice, Quot.sound]`.
2. If you must grep, **strip comments first** (remove `/- … -/` blocks and `--`
   lines), *then* match `\bsorry\b` on the remaining code.

**Invariant:** *never let a textual grep over source be the trust boundary for a
semantic property the toolchain can decide.* `sorry`-freeness is a
`#print axioms` question; lemma existence is a `#check` question; statement match
is a comparator question. Greps over comments produce both false positives (here)
and false negatives.

### Why this matters

A wrong "the papers are broken" report can trigger pointless recovery work
(reverting, hunting git history) over a non-existent problem. The trap is using
the cheap, lossy tool for a question the precise tool answers crisply — and the
domain *has* the precise tool one keystroke away.
