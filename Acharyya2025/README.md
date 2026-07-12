# Acharyya2025 — DKPS concentration (Lean formalization)

**Paper:** Aranyak Acharyya, Joshua Agterberg, Youngser Park, Carey E. Priebe.
*Concentration bounds on response-based vector embeddings of black-box
generative models.* arXiv:2511.08307. A markdown transcription is in
[`prose/`](prose/).

This library formalizes the **finite-sample / high-probability DKPS
concentration** result — the load-bearing hypothesis used downstream by the
`DkpsQuench` and `Helm2025` formalizations.

> **For the authors:** this README maps your Theorems 1–2 / Corollaries 1–2 /
> Assumptions 1–2 onto the Lean statements so you can check faithfulness without
> reading Lean proofs. Start with the [crosswalk](#paper--lean-crosswalk) and
> [where-to-start](#where-to-start).

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
  `--` comments tying hypotheses to your Assumptions/Theorems, and a
  `-- Conclusion:` line marking the claim.
- Anything the Lean needs that your paper does **not** state explicitly is
  flagged **"extra (implicit) assumption beyond the paper."** See
  [Assumptions beyond the paper](#what-to-scrutinize-assumptions-beyond-the-paper).
- **Symbol glossary:** `∀` for all · `∃` there exists · `→` implies · `‖x‖`
  norm · `ℝ`/`ℕ` reals/naturals · `B`/`B̂` the true/sample (double-centered)
  CMDS matrix · `ψ`/`ψ̂` true/estimated perspectives · `W*` the aligning
  orthogonal map · `α`,`Λ` the eigenvalue floor / cap (your `C₁`, `C₂` from
  Assumption 2) · `IsHermitian`, `PosSemidef` symmetric / positive-semidefinite
  · `rank` matrix rank · `Tendsto f atTop (𝓝 0)` means `f → 0`.
- **Why the build status matters.** `lake build` succeeds with **0 `sorry`**
  and **0 `axiom`**: every statement is *proved true relative to its stated
  hypotheses*, so your review reduces to **do the hypotheses and conclusion
  match the paper?**

---

## Where to start

The result is assembled in layers; read them in this order:

1. **[`Bridge.lean`](Bridge.lean)** — `EntrywiseClose` and
   `entrywise_close_to_cmds_entrywise_close_of_bounded`: the **Theorem 1**
   content (the centered dissimilarity matrix `B̂` concentrates entrywise
   around `B`).
2. **[`ConfigPerturbation.lean`](ConfigPerturbation.lean)** —
   `exists_isometry_configError_spectralConfig_le` and the explicit
   `configBound`: the **deterministic core of Theorem 2** — an orthogonal `W*`
   with `‖ψ̂W* − ψ‖ ≤ configBound`, via Weyl + Davis–Kahan.
3. **[`AlignedPipeline.lean`](AlignedPipeline.lean)** —
   `highProb_aligned_configError_of_entrywise_close`: the **high-probability
   Theorem 2** (feed the Theorem-1 event through the deterministic bound).
4. **[`RateChain.lean`](RateChain.lean)** — `endToEndRate` /
   `tendsto_endToEndRate_zero`: the **Corollary 2** vanishing rate as the
   replicate budget grows.

---

## Paper → Lean crosswalk

| Paper result | Lean declaration | File |
|---|---|---|
| **Theorem 1** — covariance `Σ`; entrywise `B̂ − B` concentration | `EntrywiseClose`, `entrywise_close_to_cmds_entrywise_close_of_bounded` | `Bridge.lean` |
| **Corollary 1** — spectral-norm bound `‖B̂ − B‖` | `MatrixOperatorNormClose` (predicate shape) | `MathlibBridge.lean` |
| **Assumption 1** (`rank B = d`) | rank-`≤ d` hypotheses; `CMDSpectralAssumptions` | `ConfigPerturbation.lean`, `SpectralPipeline.lean` |
| **Assumption 2** (eigenvalue stability `λ_d > C₁`, `λ₁ < C₂`) | eigenvalue floor `α` / cap `Λ` hypotheses | `ConfigPerturbation.lean`, `MatrixPerturbation.lean` |
| **Theorem 2**, deterministic core — `∃ W*∈O(d)`, `‖ψ̂W*−ψ‖ ≤ configBound` | `exists_isometry_configError_spectralConfig_le`, `configBound` | `ConfigPerturbation.lean` |
| **Theorem 2**, high-probability form | `highProb_aligned_configError_of_entrywise_close`, `…_of_response_mean` | `AlignedPipeline.lean` |
| **Corollary 2** — vanishing rate as budgets grow | `endToEndRate`, `tendsto_endToEndRate_zero`, `tendsto_configBound_zero` | `RateChain.lean` |
| Weyl's eigenvalue inequality | `abs_eigenvalues_sub_le` | `Weyl.lean` |
| Davis–Kahan sin-Θ bound; rank-`d` eigengap | `sum_cross_inner_sq_le`; rank-gap lemmas | `DavisKahan.lean`, `RankGap.lean` |
| The aligning orthogonal map `W*` | `alignedSpectralConfig`, `AlignExists`; Gram rigidity / polar factor | `AlignedPipeline.lean`, `GramRigidity.lean`, `PolarFactor.lean`, `Overlap.lean` |
| PSD rank-`≤d` ⇒ Gram of a `d`-config (produces the population `ψ`) | `exists_config_gram_eq_of_posSemidef_rank_le` | `GramRealization.lean` |
| Matrix-world capstone (entrywise `η` ⇒ aligned `ConfigError`) | `exists_isometry_configError_le_of_entrywise_close` | `MatrixPerturbation.lean` |

---

## What to scrutinize: assumptions beyond the paper

- **Measurability of the raw spectral embedding** (`hmeas_spec` in the aligned
  pipeline / downstream bridges). This is the one genuine
  Borel-measurability primitive Lean needs to take probabilities; it concerns a
  *fixed* eigendecomposition map (no data-dependent choice).
- **`AlignExists` / `Classical.choose` alignment.** `alignedSpectralConfig`
  selects the aligning `W*` nonconstructively; to stay choice-free for
  measurability we route through the existential predicate `AlignExists`. This
  is machinery the paper does not need (it argues classically).
- **Assumptions 1–2 are encoded** as `IsHermitian` / `PosSemidef` / `rank ≤ d`
  and explicit eigenvalue floor `α` / cap `Λ` hypotheses; the numeric
  **smallness conditions** (`hsmall`, `hpolar`) make the paper's "`r = ω(n³)`,
  `supᵢⱼ γᵢⱼ = O(1)`" regime concrete and are flagged where used.
- **Rates are loose, not sharp.** `cmdsEntrywiseRate` / `configBound` /
  `endToEndRate` are *valid but non-optimal* propagation rates (the module
  docstrings compare them with the paper's `Poly₃((n³/r)^{1/2−δ})` bookkeeping).
  The qualitative content — bounds that vanish in the stated regime — matches;
  the constants/exponents are not claimed to be the paper's sharp ones.
- **Response boundedness in growing bridges.** The preferred Quench-facing
  response theorem no longer assumes separate uniform bounds for every sample
  and population dissimilarity. A population response-norm envelope, together
  with the response-mean event, derives both bounds where they are needed.
- **Finite-dimensionality** of the ambient space is assumed throughout, as the
  paper intends.

---

## Status

COMPLETE: **zero sorries, zero axioms** — every statement in the library is
proved and true as written. The full chain is formally connected:

> iid responses → second moments (`trace(Σ)/r`) → Chebyshev + union bound →
> dissimilarity entrywise events → CMDS double-centering → Weyl /
> Davis–Kahan / polar-factor perturbation → aligned embedding error
> (`alignedSpectralConfig`, explicit `configBound`) → Quench's uniform
> embedding-error hypothesis and Helm's alignment consistency,

with the explicit fixed-dimension end-to-end rate composed in `RateChain.lean`.
`GrowingPipeline.lean` additionally removes coordinate alignment from
nearest-neighbor consumers by proving pairwise-distance control directly and
packages the extra rate obligations that appear when the matrix dimension grows.
Four legacy scaffold statements that were false as written were retired (kept
as prose records pointing at their proved replacements; originals in git history). See
[`../planning/acharyya-plan.md`](../planning/acharyya-plan.md) for the
work-package history.

*Provenance:* the original scaffold session's model label is recorded as
`Codex 5.5 High`; the spectral bridge, aligned pipeline, rate chain, and
retirement pass were formalized by Claude Fable 5 (claude-fable-5[1m]), per
user-observed model labels.

## File guide

| File | Contents |
|---|---|
| [`Bridge.lean`](Bridge.lean) | Theorem-1 event chain: response-mean → Frobenius → entrywise → CMDS-entrywise closeness predicates and propagation. |
| [`ConfigPerturbation.lean`](ConfigPerturbation.lean) | **The bridge theorem** `exists_isometry_configError_spectralConfig_le` + explicit `configBound` — deterministic core of Theorem 2. |
| [`AlignedPipeline.lean`](AlignedPipeline.lean) | `alignedSpectralConfig` (choice-based aligned estimator) + the high-probability aligned-`ConfigError` theorems (entrywise and response-mean versions). |
| [`GrowingPipeline.lean`](GrowingPipeline.lean) | Choice-free pairwise-distance perturbation, target-augmented growing-dimension foundations, and `GrowingConfigControl` for joint model/response schedules. |
| [`RateChain.lean`](RateChain.lean) | The explicit end-to-end rate: HP lemma, `configBound` continuity at 0, `endToEndRate` and its vanishing (Corollary 2). |
| [`MatrixPerturbation.lean`](MatrixPerturbation.lean) | Matrix-world capstone: entrywise `η` ⇒ aligned `ConfigError ≤ configBound`, with rank transport for trailing eigenvalues. |
| [`Weyl.lean`](Weyl.lean) | Discrete Courant–Fischer + Weyl's eigenvalue perturbation inequality. |
| [`DavisKahan.lean`](DavisKahan.lean) | Cross-term identity + Davis–Kahan cross-block sin-Θ bound. |
| [`RankGap.lean`](RankGap.lean) | Eigengap derivation from rank-`d` / floor structure via Weyl. |
| [`Overlap.lean`](Overlap.lean) | Eigenvector overlap matrix, `QᵀQ − I` deviation, Sylvester commutator identity. |
| [`PolarFactor.lean`](PolarFactor.lean) | Quantitative polar factor: near-isometry ⇒ exact isometry within `2δ`. |
| [`GramRigidity.lean`](GramRigidity.lean) | Exact Gram rigidity: equal Grams ⇒ isometry-related (the `κ = 0` limit of `W*`). |
| [`GramRealization.lean`](GramRealization.lean) | PSD rank-`≤d` matrices are Gram matrices of `d`-dimensional configurations. |
| [`SpectralPipeline.lean`](SpectralPipeline.lean) | World-map between DKPS/CMDS, matrix, spectral, and configuration layers; `CMDSpectralAssumptions`; population CMDS Gram realization. |
| [`OperatorBridge.lean`](OperatorBridge.lean) | Honest `ℓ²→ℓ²` operator-norm transport between the matrix and operator worlds. |
| [`Deterministic.lean`](Deterministic.lean) | Finite-dimensional centering / double-centering definitions and stability. |
| [`MathlibBridge.lean`](MathlibBridge.lean) | Conversions from curried `DisMat` objects to Mathlib `Matrix`; symmetry / Frobenius / operator-bound predicates. |
| [`Basic.lean`](Basic.lean) | Library entry point (imports). |
| [`prose/`](prose/) | Markdown transcription of the paper. |

Downstream consumers of this library:
[`../DkpsQuench/AcharyyaBridge.lean`](../DkpsQuench/AcharyyaBridge.lean) and
[`../Helm2025/AcharyyaBridge.lean`](../Helm2025/AcharyyaBridge.lean).

## Build / sanity checks

```bash
lake build Acharyya2025
grep -RIn '\baxiom\b' Acharyya2025     # expect: no matches
grep -RIn '\bsorry\b' Acharyya2025     # expect: no matches
```

### Growing response concentration

`GrowingResponse.lean` extends the response-level concentration chain to
stage-dependent finite populations.  It provides:

- sample means constructed from concrete replicate arrays;
- the matrix-valued iid second-moment bound for those averages;
- Chebyshev and union bounds with a varying population size;
- a finite-target double union bound;
- response-mean to CMDS-entrywise propagation when the matrix dimension varies.

This is the response-level input used by the growing target-augmented Quench
bridge.  For infinite target classes, uniform target concentration remains an
explicit statistical condition rather than being inferred from pointwise
second moments.
