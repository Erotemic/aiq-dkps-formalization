# Acharyya2024 — DKPS consistency (Lean formalization)

**Paper:** Aranyak Acharyya, Michael Trosset, Carey E. Priebe, Hayden Helm.
*Consistent estimation of generative model representations in the data kernel
perspective space.* arXiv:2409.17308. A markdown transcription is in
[`prose/`](prose/).

This library formalizes the **asymptotic DKPS / raw-stress MDS consistency**
results. It is intentionally separate from `Acharyya2025`, which tracks the
later finite-sample concentration paper.

> **For the authors:** this README maps your Theorems 1–5 onto the Lean
> statements so you can check faithfulness without reading Lean proofs. Start
> with the [crosswalk](#paper--lean-crosswalk) and [where-to-start](#where-to-start).

---

## How to read these files (a 2-minute Lean primer for non-Lean readers)

A theorem in Lean looks like this:

```lean
/-- <plain-English description of what this claims> -/
theorem some_name
    (h1 : <hypothesis 1>)        -- <role of h1, tied to your paper>
    (h2 : <hypothesis 2>)        -- ...
    -- Conclusion: <plain-English statement of the claim>
    : <the conclusion> := by
  <proof — you can ignore everything after `:= by`>
```

- Everything **before** `:= by` is the *claim* (hypotheses, then the
  conclusion). Everything **after** `:= by` is the machine-checked *proof* —
  you can skip it.
- We annotated every statement: a `/-- … -/` description above each, inline
  `--` comments tying hypotheses to your paper, and a `-- Conclusion:` line
  marking the claim.
- Anything the Lean needs that your paper does **not** state explicitly is
  flagged **"extra (implicit) assumption beyond the paper."** See
  [Assumptions beyond the paper](#what-to-scrutinize-assumptions-beyond-the-paper).
- **Symbol glossary:** `∀` for all · `∃` there exists · `→` implies · `‖x‖`
  norm · `ℝ`/`ℕ` reals/naturals · `Dᵢᵢ'` empirical dissimilarity, `∆` its
  limit, `ψ`/`ψ̂` true/estimated perspectives · `ConvergesInProbability`,
  `→P` convergence in probability · `Tendsto f atTop (𝓝 L)` means `f → L` ·
  `MDS n d Δ` the set of raw-stress minimizers (configurations in `ℝ^d`).
- **Why the build status matters.** `lake build` succeeds with **0 `sorry`**
  and **0 `axiom`**: every statement is *proved true relative to its stated
  hypotheses*, so your review reduces to **do the hypotheses and conclusion
  match the paper?**

---

## Where to start

Open **[`Consistency.lean`](Consistency.lean)** — the paper-facing consistency
results. Read:

1. `fixed_models_fixed_queries_consistency_of_uniqueProfile` — the **Theorem 1 / Lemma 1**
   shape (fixed `n`, fixed `m`): a raw-stress minimizer `ψ̂` converges to `ψ`
   up to an affine transformation.
2. `fixed_models_growing_queries_consistency_of_uniqueProfile` — **Theorems 2 + 3** (fixed
   models, growing queries), built on the dissimilarity-concentration step.
3. `growing_models_growing_queries_perStage_consistency_of_uniqueProfile` — the **Theorems 4 / 5**
   (triangular-array) shape.

---

## Paper → Lean crosswalk

| Paper result | Lean declaration | File |
|---|---|---|
| **Theorem 1 / Lemma 1** — minimizer `ψ̂ → ψ` up to affine (fixed `n`,`m`) | `fixed_models_fixed_queries_consistency_of_uniqueProfile`, `rawStress_mds_stability` | `Consistency.lean` |
| … unconditional set form of the stability | `rawStress_mds_stability_set` | `Consistency.lean` |
| … in-probability raw-stress stability | `mds_stability_inProbability_set`, `mds_stability_inProbability_of_uniqueProfile` | `RawStress.lean` |
| **Theorem 2** — covariance `Σ`; `Dᵢᵢ'` concentrates (rate `γᵢⱼ/r`) | `dissimilarity_convergesInProbability_of_secondMoment` | `Probability.lean` |
| … second-moment algebra `E‖X̄−μ‖² = trace(Σ)/r` | `integral_norm_sq_sampleMean_sub_mean`, `…_le_of_bound` | `SecondMoment.lean` |
| **Theorems 2 + 3** — fixed models, growing queries | `fixed_models_growing_queries_consistency_of_uniqueProfile`, `growing_queries_dissimilarity_converges` | `Consistency.lean` |
| **Theorems 4 / 5** — growing models & queries (finite per-stage form) | `growing_models_growing_queries_perStage_consistency_of_uniqueProfile`, `…_of_sample_limit_uniqueProfile` | `Consistency.lean` |
| Raw stress; MDS minimizer set; existence | `rawStress`, `MDS`, `mds_nonempty` | `RawStress.lean` |
| Translation/affine invariance (Remark 1) | `rawStress_translate`, `center_mem_mds` | `RawStress.lean` |

---

## What to scrutinize: assumptions beyond the paper

- **`UniquePairProfile` (the `huniq` hypothesis).** The paper's fixed-`ψ`
  Theorem-1 shape is stated up to affine transformation along a subsequence.
  The Lean proves the *unconditional* truth as a statement about the minimizer
  **set** (`…_set`); recovering the literal fixed-`ψ` form uses an explicit
  uniqueness hypothesis `UniquePairProfile` that the paper leaves implicit. (A
  bonus: under it the convergence holds along the **full** sequence — no
  subsequence needed.)
- **No measurable selection.** The in-probability stability is proved via a
  modulus of continuity at the limit matrix plus outer-measure event inclusion,
  *replacing* the measurable-selection argument the paper leaves implicit.
- **`ConfigError`** is a stronger (non-affine-quotiented) closeness than the
  paper's "up to affine transformation"; this is flagged at its definition in
  `Common.lean`.
- **`*_meas`** measurability hypotheses and `MemLp`/integrability side-conditions
  are required by Lean to take probabilities/expectations; the paper leaves
  them implicit. `SecondMoment.lean` also proves the variance algebra under
  **pairwise independence**, slightly generalizing the paper's iid.
- **Scope caveat:** the `Lᵖ`-over-model-distribution form of the conclusion is
  not formalized; this is noted in `Consistency.lean`.

---

## Status

COMPLETE: **zero sorries, zero axioms** — every statement is proved, and
statements that were false as written in the original scaffold have been
repaired with honest hypotheses (`hsample`/`hlimit`/`huniq`) before being
proved. The diagonal argument the paper uses for Theorems 4/5 is unnecessary
here because the repaired layer-1 stability converges along the full sequence.
See [`../planning/acharyya-plan.md`](../planning/acharyya-plan.md) for the
work-package history and `../planning/acharyya-graveyard.md` for dead ends.

*Provenance:* the original scaffold session's model label is recorded as
`Codex 5.5 High`; the proofs were formalized by Claude Fable 5
(claude-fable-5[1m]), per user-observed model labels.

## File guide

| File | Contents |
|---|---|
| [`Consistency.lean`](Consistency.lean) | **Start here.** Paper-facing consistency theorems (Theorems 1–5 shapes, repaired hypotheses). |
| [`RawStress.lean`](RawStress.lean) | Raw-stress MDS toolkit: √-stress Lipschitz continuity, translation invariance, minimizer existence, deterministic subsequence stability, modulus of continuity, and the in-probability stability theorems. |
| [`Probability.lean`](Probability.lean) | The Theorem 2 probability step (Chebyshev + union bound + squeeze) from second-moment hypotheses. |
| [`SecondMoment.lean`](SecondMoment.lean) | iid sample-mean second-moment algebra (pairwise independence suffices; `≤ γ/r` corollary). |
| [`Common.lean`](Common.lean) | Shared finite-dimensional DKPS / MDS definitions. |
| [`WellKnown.lean`](WellKnown.lean) | Paper-independent norm inequalities and high-probability bookkeeping. |
| [`Basic.lean`](Basic.lean) | Library entry point (imports). |
| [`prose/`](prose/) | Markdown transcription of the paper. |

## Build / sanity checks

```bash
lake build Acharyya2024
grep -RIn '\baxiom\b' Acharyya2024     # expect: no matches
grep -RIn '\bsorry\b' Acharyya2024     # expect: no matches
```
