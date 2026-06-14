# Mathlib proof-polishing: "folding" proofs

Distilled from reviewer feedback (`@wwylele`, PR #40567, `GramMatrix.lean`,
2026-06-14) on the Gram-rigidity proof. These are durable techniques to apply
when polishing any proof for upstream (ForMathlib candidates first; the DKPS
paper proofs later). Read this before a polishing pass.

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
4. `simp?` / `squeeze_simp` to pin a stable, explicit simp set (don't ship a
   fragile bare `simp` into Mathlib);
5. remove now-unused lemmas/assumptions;
6. re-check `classical` and other dead tactics.

## Expected outcome

The final proof reads like a **high-level construction of the isometry between
spans** — named mathematical facts in rewrite-friendly form, `simp` for routine
standard-construction applications, `simpa … using …` for existing theorems
under local defs — not a manual trace through quotient maps, range subtypes, and
coercions.

A fold-this-proof benchmark seeded from this same feedback is
[`benchmark-candidates/lean-questions.md`](benchmark-candidates/lean-questions.md)
Q4.
