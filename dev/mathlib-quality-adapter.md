# Using the `mathlib-quality` skill in this repo (house-rules adapter)

The [`mathlib-quality`](../skills/mathlib-quality-main) skill (vendored at
`skills/mathlib-quality-main/`) is a Lean-4 code-quality toolkit distilled from
thousands of merged Mathlib PRs. **We use it for polishing the *code* of our
Mathlib-bound proofs** (golfing, structure, naming, style) — both the headline
Gram proof and the rest of the `ForMathlib/` candidates.

Its skills are callable via the `Skill` tool (`mathlib-quality:cleanup`,
`:decompose-proof`, `:generalise`, `:split-file`, …) even though `/plugin
install` is unavailable in this environment.

This file is the **adapter**: what to use, and the *one* thing to do differently
here. Read it before running any `mathlib-quality` skill against a `ForMathlib/`
file.

---

## The carve-out that matters: AI-authorship provenance

The skill is **not** anti-AI-authorship (its `/fix-pr-feedback` even *adds* a
`Co-Authored-By: Claude` commit footer). The only authorship-adjacent steps are
the Mathlib **copyright-header** fix and the golfer's **comment stripping**.
Adapt both:

1. **Keep the staging provenance header.** Every `ForMathlib/` file opens with a
   `/- Staged for Mathlib: … Formalized by Claude … To be re-authored per
   Mathlib's AI-contribution policy at PR time. -/` block. **Do not** replace it
   with a Mathlib `Copyright (c) YYYY … Authors:` header, and **do not** strip
   it. → **Skip cleanup gate `A.1 COPYRIGHT` / `cleanup` step 3.1** on staging
   files; the staging analog of that gate is "provenance header present and
   accurate."
2. **Golfing may strip *redundant inline* `--` comments, never the header or
   docstrings.** The golfer's "remove ALL inline comments" rule is for proof
   clutter. Keep the module `/- … -/` header, every `/-- … -/` docstring, and
   any genuinely-explanatory step comment (the fork keeps a few, e.g.
   `-- Extend the span-to-span isometry to E, then bundle it as an equivalence`).

   The copyright-header swap and the move of provenance into the PR description
   happen **only at PR time, on the Mathlib fork** — never in this repo. (See the
   standing rule: provenance is preserved here; disclosure is done in the PR.)

Everything else in the skill applies unchanged. The diff gates in
[`cleanup-gates.md`](../skills/mathlib-quality-main/skills/mathlib-quality/references/cleanup-gates.md)
(build-green, `definition_protected`, `theorem_statement_protected`, structure,
naming, line-packing) are pure code-safety and are *desirable* here — they're the
same "don't let golf drift the statement" discipline we already follow.

---

## What to use vs. skip

| Use (code polish) | Why |
|---|---|
| `:cleanup` (with the carve-out above) | 10-phase style audit + per-decl golf + gates |
| `:decompose-proof` | break a long proof body into named helper lemmas |
| `:generalise` | weaken hypotheses (e.g. `ℝ` → `RCLike`, drop unused binders) |
| `:split-file` | only if a `ForMathlib/` file grows > ~1500 lines |
| `:pre-submit` | pre-PR checklist (run on the **fork**, not staging) |
| references: `golfing-rules`, `style-rules`, `proof-patterns`, `naming-conventions`, `mathlib-search`, `generalisation-patterns` | the rule corpus itself |

| Skip (not our goal) | Why |
|---|---|
| `:develop`, `:beastmode` | new-development planning/execution; our proofs are done |
| `:blueprint`, `:unformalise`, `:project-status`, `:expert-review` | docs/blueprint/reporting, not code polish |
| `:bump-mathlib`, `:setup-chatgpt`, `:contribute`, `:integrate-learnings` | infra/meta |

`:fix-pr-feedback` is for the **fork** (it addresses Mathlib reviewer comments and
adds the Claude co-author footer — which is consistent with how we already commit
*here*).

---

## Recommended sequence (Gram proof, then the rest)

1. Baseline: `lake build` green (the skill's Phase-0 doctor; we already gate on
   8635 jobs).
2. Per declaration, apply [`golfing-rules.md`](../skills/mathlib-quality-main/skills/mathlib-quality/references/golfing-rules.md)
   Phase 1 (instant wins) → Phase 2 (automation: `grind`/`simpa`/`positivity`/…)
   → Phase 3 (style), verifying compilation after each change. Honor the
   `theorem_statement_protected` gate: golf the *body*, never drift the
   statement.
3. Structure gate: any body > ~60 lines (> ~15 for a headline result) →
   `:decompose-proof` rather than leave it long.
4. After golf, the `/simplify` built-in is the holistic second pass (the skill's
   Phase 6.5 hands off to it).
5. **Provenance check** (our extra gate): header intact, docstrings intact, only
   redundant inline comments removed.

The Gram proof is already close (folded + def-refactored); the highest-value
remaining targets are the other `ForMathlib/` candidates that haven't had a golf
pass.

---

## `lemma` vs `theorem` (cross-check)

The skill's `naming-conventions.md` treats `lemma` and `theorem` identically
(both return `Prop`, both `snake_case`) — there is **no** semantic naming rule
distinguishing them. This matches our empirical finding: the choice is stylistic
and **decided by the destination file's local area** (Analysis/InnerProductSpace
is ~86% `theorem`, reserving `lemma` for trivial `gram_apply`-tier definitional
glue). See [`mathlib-proof-polishing.md`](mathlib-proof-polishing.md) and the
[`lessons_learned.md`](journals/lessons_learned.md) entry.
