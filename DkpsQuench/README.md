# DkpsQuench — "Query-efficient model evaluation" (Lean formalization)

**Paper:** Hayden Helm, Ben Johnson, Carey E. Priebe.
*Query-efficient model evaluation using cached responses*
([arXiv:2605.07096](https://arxiv.org/abs/2605.07096), 2026).
A transcription is in [`prose/`](prose/) and the LaTeX source in
[`prose/quench-tex-src/`](prose/quench-tex-src/).

> **For the authors:** this README is a map for checking that the Lean
> statements faithfully encode your **Theorem 2** (query efficiency). You do
> **not** need to read any Lean proofs — only the *statements*. Start with the
> [crosswalk](#paper--lean-crosswalk) and the [where-to-start](#where-to-start)
> pointer below.

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
  you can skip it entirely.
- We annotated every statement to help you: a `/-- … -/` description sits above
  each one, inline `--` comments tie each hypothesis to your paper's
  assumptions, and a `-- Conclusion:` line marks where the claim begins.
- Anything the Lean needs that your paper does **not** state explicitly (a
  measurability condition, an abstract estimator, a rate side-condition) is
  flagged **"extra (implicit) assumption beyond the paper."** Those are the
  lines to scrutinize most — see [Assumptions beyond the paper](#what-to-scrutinize-assumptions-beyond-the-paper).
- **Symbol glossary:** `∀` for all · `∃` there exists · `→` implies (or
  "function to") · `≤` · `‖x‖` length/norm of `x` · `|x|` absolute value ·
  `ℝ` reals · `ℕ` naturals · `Pf` the distribution over models · `∫ … ∂Pf`
  expectation over models drawn from `Pf` · `Measure` / `IsProbabilityMeasure`
  measure-theoretic probability · `HighProbAtTop μ E` is our encoding of
  "**with high probability**": for every `δ > 0`, the event `E n` has
  probability `≥ 1 − δ` for all large enough sample sizes `n`.
- **Why the build status matters.** `lake build` succeeds with **0 `sorry`**
  (no unproved gaps) and **0 `axiom`** (no unchecked assumptions). So every
  statement here is *proved true relative to its stated hypotheses*. Your
  review therefore reduces to one question per theorem: **do the hypotheses and
  the conclusion match the paper?**

---

## Where to start

Open **[`Theorem2.lean`](Theorem2.lean)** — the paper-facing file. Read:

1. `yNN_paper`, `yQ`, `yFull` — the estimator `ŷ_NN`, the subset baseline
   `ŷ_Q`, and the target `y`.
2. **`highProb_queryEfficient_nn`** — this is your **Theorem 2**: with high
   probability, `MSE(ŷ_NN) ≤ MSE(ŷ_Q)` (the nearest-neighbor estimator is
   query-efficient relative to the subset baseline).
3. `highProb_mse_nn_le` — the supporting half (Part 1): `MSE(ŷ_NN) ≤ ε` with
   high probability.

The concentration event your Theorem 2 inherits from the DKPS estimation
theory is *assumed* in `Theorem2.lean`; it is *discharged* from the
Acharyya2025 spectral chain in [`AcharyyaBridge.lean`](AcharyyaBridge.lean) —
see the bridge row of the crosswalk.

---

## Paper → Lean crosswalk

| Paper object | Lean declaration | File |
|---|---|---|
| Nearest-neighbor estimator `ŷ_NN` | `yNN_paper` | `Theorem2.lean` |
| Subset baseline `ŷ_Q`; target `y` | `yQ`; `yFull` | `Theorem2.lean` |
| Mean-squared error `MSE(·)` | `MSE` | `Basic.lean` |
| **Theorem 2, Part 1** — `MSE(ŷ_NN) ≤ ε` w.h.p. | `highProb_mse_nn_le` | `Theorem2.lean` |
| **Theorem 2, Part 2** — `ŷ_NN` query-efficient vs `ŷ_Q` | `highProb_queryEfficient_nn` | `Theorem2.lean` |
| Assumption 1 (Lipschitz score) | `LipschitzScore` | `Basic.lean` |
| Assumption 2 (reference-model coverage) | the `h_cover` hypothesis | `Theorem2.lean` |
| "Query-efficient" predicates | `QQueryEfficient`, `mQueryEfficient` | `Basic.lean` |
| Abstract engine (arbitrary embedding estimator) | `highProb_mse_le_of_concentration`, `highProb_queryEfficient_of_concentration` | `Internal.lean` |
| Theorem 2 with the concentration event **derived** from the spectral chain | `queryEfficient_nn_of_aligned_spectral`, `queryEfficient_nn_of_response_mean`, `queryEfficient_nn_of_second_moment` | `AcharyyaBridge.lean` |

The three `Theorem2.lean` headline theorems each also have a
`*_of_subevent` variant that takes a *measurable* high-probability sub-event
instead of the raw embedding-error event; these are what the bridge consumes,
and are equivalent when the sub-event is the event itself.

---

## What to scrutinize: assumptions beyond the paper

The Lean is faithful to Theorem 2 but, being fully formal, makes a few things
explicit that the paper leaves implicit. Each is flagged in-line; the notable
ones:

- **Measurability hypotheses** (`h_conc_meas`, `h_cover_meas`, the `E`/`hE_meas`
  sub-event machinery). The paper does not discuss measurability of its
  high-probability events; Lean requires it to take probabilities. In the
  bridge this is reduced to one *trivially-true* primitive (`Measurable Dhat`:
  the sample dissimilarity matrix is measurable in the sample) — the measurable
  high-probability sub-event is the CMDS-entrywise event itself, which is
  directly Borel and deterministically contained in the embedding-error event.
- **The concentration event is assumed, not derived, in `Theorem2.lean`.** The
  rate `c n → 0` (the DKPS estimation content) enters as a hypothesis
  `h_conc`. It is genuinely derived only in `AcharyyaBridge.lean`, from the
  Acharyya2025 spectral chain.
- **Abstractness.** The engine theorems in `Internal.lean` hold for an
  *arbitrary* embedding estimator `ψHat`; the paper has a specific one. This is
  a generalization, not a weakening.
- **`hm : Qsub.card < Qstar.card`** (the paper's `m < M`) is recorded in Part 2
  for fidelity but is *not used* by the formal argument — only `MSE(ŷ_Q) > 0`
  drives the conclusion. This is noted at the hypothesis.

---

## File guide

| File | Contents |
|---|---|
| [`Basic.lean`](Basic.lean) | Core definitions: model/perspective types, the NN estimator, `MSE`/`Risk`, the query-efficiency predicates, `LipschitzScore` (Assumption 1), the `HighProbAtTop` "with high probability" encoding. |
| [`Internal.lean`](Internal.lean) | Machinery: high-probability event helpers, the per-model error-analysis steps, and the abstract concentration→MSE engine theorems. |
| [`Theorem2.lean`](Theorem2.lean) | **Start here.** The paper-facing statements of Theorem 2 (Parts 1 & 2) for the nearest-neighbor estimator `ŷ_NN`. |
| [`AcharyyaBridge.lean`](AcharyyaBridge.lean) | Discharges the concentration hypothesis from the Acharyya2025 spectral/statistical chain, yielding Theorem 2 from genuine statistical inputs. |

## Build / sanity checks

```bash
lake build DkpsQuench          # type-checks every statement and proof
grep -RIn '\bsorry\b' DkpsQuench   # expect: no matches
grep -RIn '\baxiom\b' DkpsQuench   # expect: no matches
```
