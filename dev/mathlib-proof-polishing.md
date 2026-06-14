# Mathlib proof-polishing: "folding" proofs

Distilled from reviewer feedback (`@wwylele`, PR #40567, `GramMatrix.lean`,
2026-06-14) on the Gram-rigidity proof. These are durable techniques to apply
when polishing any proof for upstream (ForMathlib candidates first; the DKPS
paper proofs later). Read this before a polishing pass.

> **Tooling.** For the mechanical golf/style rules (extracted from thousands of
> merged Mathlib PRs) we use the vendored `mathlib-quality` skill. See
> [`mathlib-quality-adapter.md`](mathlib-quality-adapter.md) for *how to run it
> in this repo* — the key house-rule being that staging files **keep their
> AI-authorship provenance header** (the no-provenance/copyright-header swap is
> fork/PR-time only). This file remains the home for the *judgment* lessons
> (∃→def, fold-vs-don't, terminology, placement) that the mechanical rules don't
> cover.

> ⚠️ **Provenance — read this first.** The reviewer's *actual* message was the
> worked before→after **examples** plus one line: *"This is to show you how you
> can 'fold' proofs. This might not be the final optimal proof yet. You should
> try doing another pass after this one."* That's it — concrete diffs and "do
> another pass; there are more like these in the PR."
>
> The version first handed to the agent was a **ChatGPT rephrasing** that wrapped
> those diffs in invented meta-structure ("what the reviewer is *really* asking
> for", a 9-step argument breakdown, a long appendix). Treating that scaffolding
> as the reviewer's intent caused two real mistakes (see
> [`journals/lessons_learned.md`](journals/lessons_learned.md), 2026-06-14):
> over-generalizing into a repo-wide mechanical sweep, and mis-scoping away from
> the actual ask (fold *this PR's* remaining proofs).
>
> **So: the before→after examples below are the signal. The prose around them is
> derived/secondary.** When reviewer feedback has been rephrased by another LLM,
> anchor on the demonstrated diffs, not on any narrated "intent."

> The goal is **not** to golf the proof short. It is to make the proof *express
> the mathematical argument* clearly while delegating routine Lean bookkeeping
> (coercions, subtype membership, quotient/range maps) to the simplifier.

The Gram proof's math is: build `Tφ, Tψ` (linear-combination maps) → they
preserve inner products (Grams agree) → norms agree → `ker Tφ ≤ ker Tψ` →
descend `Tψ` through the quotient → identify on ranges → upgrade to a
`LinearIsometryEquiv` → transport ranges to spans → generators map right. The
*code* should read like that, with one named local fact per step.

---

## The core idiom: rewrite-friendly local lemmas

Prefer a **parameterized `have`** whose *type* is a rewrite rule shaped to match
what appears later:

```lean
have key (c c' : ι →₀ 𝕜) : ⟪Tφ c, Tφ c'⟫_𝕜 = ⟪Tψ c, Tψ c'⟫_𝕜 := by
  simp [hTφ, hTψ, inner_linearCombination_linearCombination, h]
```

not the `∀`-quantified `have key : ∀ c c', … := by intro c c'; …` form.

**Why:** `simp` does **not** look at a local lemma's proof — it uses its *type*
as a rewrite rule. `key` becomes `⟪Tφ ?c, Tφ ?c'⟫ ↦ ⟪Tψ ?c, Tψ ?c'⟫`, so a later
`simp [key]` matches subterms and instantiates `?c, ?c'`. Shape the **LHS** to
match the complicated expression you'll hit downstream. (`hf_apply (c) :
f ⟨Tφ c, _⟩ = Tψ c` is the same trick: it gives `simp` the rule
`f ⟨Tφ ?c, _⟩ ↦ Tψ ?c`.)

---

## The moves, with before → after

**1. `simp` over manual congruence under sums.** If the proof is "rewrite a
pointwise equality everywhere under a sum/product," let `simp` do it:

```lean
-- before
refine Finsupp.sum_congr fun i _ => Finsupp.sum_congr fun j _ => ?_; rw [h i j]
-- after
simp [hTφ, hTψ, inner_linearCombination_linearCombination, h]
```

**2. `simpa [defs] using fact` when the goal is "an existing theorem in
disguise"** (after unfolding a local def). More robust than `rw [def]; exact
fact` — absorbs coercions, defeq, harmless normalization:

```lean
-- before
rw [hTφ]; exact Finsupp.range_linearCombination 𝕜
-- after
simpa [hTφ] using Finsupp.range_linearCombination 𝕜
```

**3. Common normal form for hypothesis and goal.** Rewrite both into the same
language, then it's a one-liner. Ask: *"what normal form makes `hc` apply
directly to the goal?"*

```lean
-- before: ker proof via intermediate `Tφ c = 0`, `‖Tψ c‖ = 0`, mem_ker juggling
-- after
intro c hc
rw [LinearMap.mem_ker, ← norm_eq_zero] at ⊢ hc   -- both sides become norm = 0
rw [norm_eq, hc]
```

**4. Let `simp` handle standard Mathlib constructions** before reaching for
`change` / `show` / subtype extensionality / repeated `rw`. These usually have
simp lemmas already: `LinearMap.comp_apply`, `LinearMap.codRestrict_apply`,
`Submodule.mkQ_apply`, `Submodule.liftQ_apply`, `quotKerEquivRange`,
subtype coercions, span/range transport, span membership,
`LinearIsometryEquiv.ofEq` / `ofSurjective`.

```lean
-- before: change … ; rw [hf', LinearMap.codRestrict_apply, hf_apply c]; exact hc
-- after
simpa [hLr, hf', hf_apply] using hc
-- before: change … ; rw [hf', LinearMap.codRestrict_apply]; exact hfφ
-- after
simp [hLr, hf', hfφ]
```

**5. Membership via the named lemma**, folded through the local def:

```lean
-- before
rw [hrangeφ]; exact Submodule.subset_span ⟨i, rfl⟩
-- after
simpa [hrangeφ] using Submodule.mem_span_of_mem (Set.mem_range_self i)
```

**6. Drop unnecessary tactics.** `classical` was not needed here. After folding,
re-check for now-dead `classical`, `show`, `change`, explicit coercion handling,
and unused `have`s/hypotheses.

---

## Guardrails (do not over-rotate)

- **Don't copy a suggested fold blindly — Lean must accept it.** If `simp [...]`
  fails, *inspect which local def/lemma is missing from the simp set*; don't
  revert to the long proof. If `rw [key]` doesn't instantiate in a goal, try the
  explicit `rw [key c c]`, or `simp [key]`.
- **Readability beats brevity.** Keep the meaningful named locals (`key`,
  `norm_eq`, `hker`, `hf_apply`, …); later steps use those facts instead of
  reopening definitions. If a `simp` proof turns opaque/fragile, a slightly
  longer proof is fine — but still isolate the math fact, then simplify the
  transport.
- **Verify after every fold.** Recompile; a fold that "looks right" can fail to
  instantiate. (And per `dev/journals/`, build-green is not the only check —
  for a comparator-bound statement, the export still has to match.)

## The second pass

The reviewer's first pass "may not be optimal." After it compiles:
1. repeated local rewrites → promote to a local lemma;
2. `rw …; exact …` → `simpa … using …`;
3. remove leftover `show` / `change` / coercion handling;
4. **simp set, by position:**
   - **Non-terminal** simp (a later `rw`/`refine`/`simp` consumes its output) →
     `simp?` / `squeeze_simp` to pin a stable, explicit `simp only [...]` (don't
     ship a fragile bare `simp` whose normal form a downstream tactic depends on).
   - **Terminal** simp (it closes the goal) → the opposite: **collapse** to
     `simp [math_fact]`. Drop any reconstructed `@[simp]` bookkeeping lemmas (the
     default set already has them) *and* a trailing `.symm` (simp orients
     equalities). I.e. `simp only [@[simp] list]; exact fact.symm` ⇒
     `simp [fact]` — **not** `simpa only [list] using fact.symm` (that keeps the
     redundant list; @wwylele on PR #40567 cut it to `simp [fact]`). This is
     vendored golfing rule **1.15** ("terminal `simp only` → `simp`"); apply it.
5. remove now-unused lemmas/assumptions;
6. re-check `classical` and other dead tactics.

## Structural polish: turning an `∃` theorem into a `def` + API

A different *kind* of polish from folding. When a reviewer asks *"is the object
this `∃` produces unique? if so, make it a `def` and provide API"* (verbatim
@wwylele on PR #40567), they want the **construction exposed**, not just its
existence. The Mathlib idiom:

0. **First ask: is the object morally *canonical*, not just existent?** A `def` is
   warranted when the object is unique/canonical. @wwylele's operational test
   (PR #40567): **look for `Classical.choice` / `Classical.choose` / `choose` /
   `Classical.arbitrary` in the definition's *term*.** If the construction makes no
   arbitrary choice — it's an explicit formula/composition — the object is
   canonical and a `def` is right. If you'd build it by `Classical.choose`-ing the
   witness out of the `∃` proof, it is *not* canonical (the choice is arbitrary):
   prefer to keep the `∃` theorem. **Caveat:** the axiom *closure* (`#print axioms`)
   is the *wrong* test — almost everything in Mathlib transitively depends on
   `Classical.choice`; what matters is whether the *term you wrote* chooses. Mathlib
   does occasionally `def` a non-canonical object for convenience
   (`stdOrthonormalBasis`, which depends on a basis choice), but that's the
   less-common exception and such defs do carry a choice.

   *Our case:* `linearIsometryEquivSpanOfInnerEq` is choice-free (a composition of
   `ofEq` / `quotKerEquivRange` / `quotEquivOfEq` / `isometryOfInner`) — canonical,
   which is exactly why the `def` was the right call. The `LinearMap.eqOn_span`
   uniqueness argument below is the *proof* of canonicity; the choice-free term is
   the *quick check* for it.

1. **Find the canonical analog and copy its API shape.** For "an isometry equiv
   from a generator correspondence" that's **`Orthonormal.equiv`**
   (`Mathlib/Analysis/InnerProductSpace/Orthonormal.lean`): a `def` built via an
   `isometryOf…` constructor, an **`@[simp]` apply lemma** (the computation rule
   on generators), a `coe`/`_toLinearEquiv` rfl-lemma, and **no separate
   uniqueness theorem** — uniqueness is the *justification* for the def
   (recovered via `ext` / `LinearMap.eqOn_span`), not a lemma you state. **Do not
   keep an `exists_…` existence wrapper alongside the `def`.** *(An earlier draft
   of this doc said to keep it as a one-line corollary "so downstream callers are
   untouched"; @wwylele's follow-up review deleted it — see "Maintainer follow-up"
   below. The `def` + its `@[simp]` apply lemma fully subsume `∃ L, ∀ i, L (φ i) =
   ψ i`; a caller who wants the existence form writes `⟨theDef …, theDef_apply …⟩`
   inline. `Orthonormal.equiv` ships no such wrapper either.)* *Read the
   surrounding code to find this; don't invent names.*

2. **`…OfInner` / `…OfBijective` separate "it's a (bi)linear map" from "it's an
   isometry."** `LinearEquiv.isometryOfInner (e) (h : ∀ x y, ⟪e x, e y⟫ = ⟪x, y⟫)`
   upgrades a `≃ₗ` to a `≃ₗᵢ` from inner-preservation alone — so you build a clean
   underlying `≃ₗ`, prove *one* inner-preservation fact, and the
   norm-preservation/surjectivity scaffolding the existence proof carried just
   drops out. Here the clean `≃ₗ` was a composition of standard equivs
   (`quotKerEquivRange⁻¹ ≪≫ quotEquivOfEq ker_eq ≪≫ quotKerEquivRange`);
   transport between defeq-but-not-syntactic carriers (`range T` vs
   `span (range ·)`) via `LinearEquiv.ofEq` / `LinearIsometryEquiv.ofEq`.

### Gotchas proving the `@[simp]` apply lemma (these were the actual time-sinks)
- **`include h`.** A `variable (h : P)` is auto-included only where the
  *statement* mentions it. Helper lemmas/defs whose statement doesn't use `h`
  (but whose proof does) need an explicit `include h`, else "unknown identifier
  `h`".
- **Debug a stuck `simp`/apply lemma with `extract_goal`.** `sorry` the
  obligation so the file compiles, reproduce the goal in a scratch, and
  `extract_goal` to see the *actual* residual — don't guess. (Twice the residual
  was already trivial `⟪…⟫ = ⟪…⟫`; the bug was a *different* declaration.)
- **simp ordering / premature rewriting.** A "compute" lemma can fire too early
  and destroy the pattern a "structural" lemma needs: `Finsupp.linearCombination_single`
  rewrote the carrier `Tφ (single i 1) → φ i`, so `quotKerEquivRange_symm_apply_image`
  (which matches `⟨f x, _⟩`) stopped applying. Fix: do the structural `simp only`
  **without** the compute lemma, then apply it in a *second* `simp`.
- **Bridge mismatched canonical forms.** `quotKerEquivRange_symm_apply_image`
  produces `(ker f).mkQ x` but `quotEquivOfEq_mk` matches `Submodule.Quotient.mk x`
  → add `Submodule.mkQ_apply` to bridge.
- **`rw [defName]` does not unfold a def** — use `simp only [defName]` (delta).
- **Don't guess lemma names** — grep Mathlib (`coe_isometryOfInner`,
  `coe_ofEq_apply`); a made-up `symm_trans_apply` aborted the whole `simp`.
- **Carrier-rewrite for subtype-valued apply lemmas.** Rewrite the input
  `⟨φ i, _⟩` to `⟨Tφ (single i 1), _⟩` (`Subtype.ext (by simp)`) so the quotient
  lemmas fire; compute the chain; simplify `linearCombination (single i 1)` to
  `ψ i` last.

The payoff: the def is shorter than the existence proof *and* more useful (it's
the named object + a `@[simp]` computation rule), and `#print axioms` stays clean.

### Maintainer follow-up (the second review pass on the `def`)

After the `def` landed, @wwylele's next pass (PR #40567, 2026-06-14) trimmed it
further. The durable lessons — most of which *correct or sharpen* the advice
above:

- **A `def` + apply lemma makes the `exists_…` wrapper dead weight — delete it.**
  This reverses the "keep it as a corollary" instinct (step 1). Once the named
  object exists, `∃ L, ∀ i, L (φ i) = ψ i` is recovered inline; a standing
  wrapper is API bloat a reviewer will cut.
- **Distinguish a genuine theorem from a *forgetful derivation* before keeping a
  corollary.** Two corollaries that looked like "more API" were just
  `(theEquiv).toLinearIsometry` (forgets surjectivity) and
  `(span ψ).subtypeₗᵢ.comp (theEquiv).toLinearIsometry` (post-compose the
  inclusion into the ambient space). Neither is new math — both are one-liners a
  caller writes at the use site, and the downstream proof that *used* them now
  just inlines the same expressions. Test: *"is this a new fact, or a trivial
  cast/restatement of the strongest object?"* If the latter, drop it — and it is
  **not** "pending-candidate" material either (a named wrapper for a one-liner
  won't survive upstream review).
- **Expose only the strongest object + its computation rule; let callers cast
  down.** The keepers were the equiv `def`, its `@[simp]` apply lemma, the
  finite-dim ambient equivalence, and the `gram`-iff. Everything between them and
  the `def` was inlined.
- **Don't name-drop a field's signature problem in prose unless the statement *is*
  that problem.** "Procrustes" was questioned: this file is the *exact /
  zero-residual* case (equal Grams ⇒ an exact isometry), not the orthogonal
  Procrustes *optimization* (least-squares `min ‖ΩA−B‖`, SVD solution, generic
  nonzero residual). Fix: drop the editorial term from the docstring; keep the
  citation, qualified as "the exact, zero-residual case." Reference ≠ claim the
  result solves the named problem.
- **"Where should this live?" is an import-cost question, not a thematic one.**
  Asked whether the `def` belongs in `InnerProductSpace/LinearMap.lean`: it needs
  `Finsupp.linearCombination` + `LinearAlgebra.Isomorphisms` (`quotKerEquivRange`),
  which that file doesn't import, so the move isn't free. Answer placement with
  the dependency delta, then thematic fit.
- **`variable (φ ψ)` to make def params explicit: place it *before* the docstring**
  (between docstring and `def` is a parse error), and remember **section
  variables only auto-fill *implicit* references** — once `φ ψ` are explicit you
  must pass them at every `@`-site inside the section (`theDef φ ψ h`, not
  `theDef h`).

## Where does a declaration go? (place by dependencies, not theme or first use)

We got placement **wrong repeatedly** — `inner_linearCombination_linearCombination`
went `GramMatrix.lean` → `Orthonormal.lean` → `Basic.lean` (three homes) before
@wwylele's "this doesn't involve `Orthonormal`, move it earlier" landed it
correctly. Distilled rule, applied in order:

1. **Dependency floor.** List the declarations the *statement and proof* actually
   use; the home is at/after the latest of them. (`inner_linearComb…` uses
   `Finsupp.sum_inner` + `inner_smul_left` → both in `InnerProductSpace/Basic.lean`,
   so Basic is the floor.)
2. **Concept test (wwylele's).** *"Does this declaration involve the file's central
   concept?"* A `Foo.lean` file is a promise that its public contents are about
   `Foo`. If the statement/proof never mentions `Orthonormal`, it does **not**
   belong in `Orthonormal.lean`.
3. **Earliest viable file.** Among files satisfying (1), pick the earliest/most
   foundational where the needed `open`s/notation are already present and **no new
   heavy import** is required. (Basic already `open`ed `Finsupp`/`ComplexConjugate`
   and transitively had `linearCombination` → the move was import-free.)
4. **Import-cost veto.** If the dependency-correct home would force a heavy new
   import into a foundational file, that's the signal it belongs in a *later /
   specialized* file. (The `linearIsometryEquivSpanOfInnerEq` "→ `LinearMap.lean`?"
   question: `LinearMap.lean` lacks `Finsupp.linearCombination` + `Isomorphisms`, so
   no — answer placement with the dependency delta, not the theme.)

**Anti-patterns that misled us** (each is a *non-*locator):
- *"It's first used here."* Usage ≠ home (`GramMatrix`).
- *"It resembles these lemmas."* Superficial similarity ≠ shared dependencies
  (`Orthonormal.inner_finsupp_eq_sum_left` looked similar but is specialized).
- *"It's thematically about X."* Theme is not the locator; dependencies are.

**For a NEW file you're authoring** (e.g. `CourantFischer.lean`), the dual question:
*does every **public** declaration belong to this file's concept?* A general helper
that doesn't (`specSubspace` — a general orthonormal-subfamily span) should be
`private` (internal scaffolding, no public-API placement claim) **or** moved to its
dependency-correct general home — never left public in a concept-named file it
doesn't match.

## Expected outcome

The final proof reads like a **high-level construction of the isometry between
spans** — named mathematical facts in rewrite-friendly form, `simp` for routine
standard-construction applications, `simpa … using …` for existing theorems
under local defs — not a manual trace through quotient maps, range subtypes, and
coercions.

A fold-this-proof benchmark seeded from this same feedback is
[`benchmark-candidates/lean-questions.md`](benchmark-candidates/lean-questions.md)
Q4.
