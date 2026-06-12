# Helm2025 — "Statistical inference on black-box generative models in the DKPS" (Lean formalization)

**Paper:** Hayden Helm, Aranyak Acharyya, Youngser Park, Brandon Duderstadt, et al.
*Statistical inference on black-box generative models in the data kernel
perspective space.* A transcription is in [`prose/`](prose/) and the LaTeX
source in [`prose/statistical-black-box-dkps-tex-src/`](prose/statistical-black-box-dkps-tex-src/).

> **For the authors:** this README maps your **Theorem 1** (fixed-`n` risk
> convergence) and **Theorem 2** (consistency transfer) onto the Lean
> statements, so you can check faithfulness without reading Lean proofs. Start
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
- We annotated every statement: a `/-- … -/` description sits above each, inline
  `--` comments tie each hypothesis to your Assumptions A1–A4 / Eq. (3), and a
  `-- Conclusion:` line marks where the claim begins.
- Anything the Lean needs that your paper does **not** state explicitly is
  flagged **"extra (implicit) assumption beyond the paper."** See
  [Assumptions beyond the paper](#what-to-scrutinize-assumptions-beyond-the-paper).
- **Symbol glossary:** `∀` for all · `∃` there exists · `→` implies (or
  "function to") · `‖x‖` norm · `ℝ` reals · `ℕ` naturals · `𝓝 L` the
  neighborhood filter at `L` · `Tendsto f atTop (𝓝 L)` means `f(n) → L` as
  `n → ∞` (this is how we write your limits) · `Measure` /
  `IsProbabilityMeasure` measure-theoretic probability · `⨆` supremum (our
  encoding of your `max` over training points) · `≃ᵃⁱ[ℝ]` an affine isometry
  (rigid motion `ψ ↦ Wψ + a`).
- **Why the build status matters.** `lake build` succeeds with **0 `sorry`**
  and **0 `axiom`**. Every statement is *proved true relative to its stated
  hypotheses*, so your review reduces to: **do the hypotheses and the conclusion
  match the paper?**

---

## Where to start

Open **[`Inference.lean`](Inference.lean)**, the paper-facing file. It opens
with a **"Notation crosswalk (paper → Lean)"** comment block — read that first.
Then read:

1. **`Theorem1`** — your **Theorem 1**: for fixed sample size `n`, the
   estimated-embedding risk converges to the true-embedding risk as the
   estimation budget grows.
2. **`Theorem2_bayes`** — your **Theorem 2**: along a budget schedule, the
   estimated-embedding risk converges to the Bayes risk (consistency transfers
   from true to estimated embeddings).
3. `Assumption1 … Assumption4` — the named A1–A4 wrappers, each documented with
   how the Lean encoding relates to the paper's statement.

---

## Paper → Lean crosswalk

| Paper object | Lean declaration | File |
|---|---|---|
| **Theorem 1** (fixed-`n` risk convergence) | `Theorem1` (wraps `risk_converges_fixed_n`) | `Inference.lean` / `Internal.lean` |
| **Theorem 2** (consistency transfer) | `Theorem2_bayes` (wraps `consistency_transfer_dkps` via `consistency_transfer_dkps_bayes`) | `Inference.lean` / `Internal.lean` |
| Diagonal-schedule device used for Theorem 2 | `diagonal_convergence` | `Internal.lean` |
| Risk `R_ℓ(P, h(·;T_n))`; estimated risk | `risk` / `Rℓ`; `risk_est` / `Rhatℓ` | `Basic.lean` / `Inference.lean` |
| Assumption 1 (invariance to rigid motions) | `Assumption1` = `InvariantToAffineIsometries` | `Inference.lean` / `Basic.lean` |
| Assumption 2 (continuity of the learning rule) | `Assumption2` = `ContinuousLearningRule` | `Inference.lean` / `Basic.lean` |
| Assumption 3 (closed/bounded/complete image) | `Assumption3` (as written) and `Assumption3'` = `BoundedLearningRule` (used) | `Inference.lean` |
| Assumption 4 (loss continuous in the prediction) | `Assumption4` = `ContinuousLossInPred`; `Assumption4'` = `ContinuousLoss` (used) | `Inference.lean` |
| Alignment consistency, Eq. (3) | `DKPSAlignmentConsistency`; paper wrapper `AlignmentConsistency` | `Basic.lean` / `Inference.lean` |
| Bayes risk over a hypothesis class | `bayesRisk` | `Inference.lean` |
| Helm alignment consistency from the spectral chain | `alignmentConsistency_of_aligned_spectral` | `AcharyyaBridge.lean` |

---

## What to scrutinize: assumptions beyond the paper

Each is flagged in-line; the notable ones:

- **Joint vs. pointwise continuity.** The paper states (A2) and (A4) for the
  perturbed coordinate only (embeddings in A2, predictions in A4). The Lean
  proofs package the sample as `(ψ, y)` pairs and assume **joint** continuity
  (`ContinuousLearningRule`, `ContinuousLoss`). These are standard sufficient
  conditions; both the paper-level and the strengthened predicate are exposed
  (`Assumption2`/`…4` vs. `Assumption4'`).
- **A3 encoding.** The paper's "closed + bounded + complete image" is encoded as
  a uniform compact-range condition `BoundedLearningRule` (`Assumption3'`),
  equivalent in finite-dimensional Euclidean space; the literal form is
  `Assumption3`.
- **Measurability** of the embedding estimators (`h_meas_psi`) is required by
  Lean to take expectations; the paper leaves it implicit.
- **`Eq. (3)` uses `iSup` (supremum) over a finite index** where the paper
  writes `max`; and one **budget index `u`** abstracts the paper's pair
  `(m, r)`.
- **A surfaced assumption in the bridge (the most important thing to scrutinize).**
  `alignmentConsistency_of_aligned_spectral` now *derives* Helm's alignment
  consistency (the per-`ω` alignment event `halign` is no longer assumed). The
  derivation makes one assumption explicit that **Helm does not state**: the
  true latent embeddings `(ω ·).1` are **eigenvalue-stable** in `d` dimensions
  (`α ≤ λ_d` on the population CMDS matrix — exactly *Acharyya 2025's
  Assumption 2*). This is required because the bridge realizes the DKPS estimator
  as the **classical/spectral** MDS embedding (Davis–Kahan needs an eigengap);
  Helm's own argument avoids it by citing the *asymptotic raw-stress* consistency
  (Acharyya 2024), which is eigengap-free. The formalization thus surfaces a
  theory/practice MDS-variant discrepancy: the estimator the experiments use
  (spectral) needs an eigenvalue-stability assumption the paper never states. See
  the `ASSUMPTION SURFACED BY THE FORMALIZATION` note above that theorem.

---

## File guide

| File | Contents |
|---|---|
| [`Basic.lean`](Basic.lean) | Core definitions: learning rule, loss, `risk`/`risk_est`, the paper-notation wrappers (`Rℓ`, `Rhatℓ`, `TrainingSet`), the A1–A4 regularity predicates, and `DKPSAlignmentConsistency` (Eq. (3)). |
| [`Internal.lean`](Internal.lean) | Analysis machinery and the two **core theorems** `risk_converges_fixed_n` (Theorem 1) and `consistency_transfer_dkps` (Theorem 2). |
| [`Inference.lean`](Inference.lean) | **Start here.** Paper-facing Assumptions A1–A4, Bayes-risk objects, and `Theorem1` / `Theorem2_bayes`, with a notation crosswalk at the top. |
| [`AcharyyaBridge.lean`](AcharyyaBridge.lean) | Bridges the Acharyya2025 spectral concentration to Helm's alignment-consistency interface; `halign` is now derived from estimation closeness + an explicit latent eigenvalue-stability assumption (Acharyya 2025 Assumption 2, surfaced — not in Helm). |

## Build / sanity checks

```bash
lake build Helm2025            # type-checks every statement and proof
grep -RIn '\bsorry\b' Helm2025     # expect: no matches
grep -RIn '\baxiom\b' Helm2025     # expect: no matches
```
