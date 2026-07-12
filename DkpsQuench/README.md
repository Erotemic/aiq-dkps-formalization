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

Open **[`QueryEfficiency.lean`](QueryEfficiency.lean)** for the strongest
paper-shaped theorem layer. Read:

1. `yNNTieAverage_paper` — the literal estimator that averages the full scores
   of every tied estimated nearest neighbor.
2. `highProbQQueryEfficient_tieAverage_of_compact_iid_fullSupport` — the
   fixed-subset theorem with an eventual high-probability risk comparison and
   coverage derived from compactness, full support, and iid reference sampling.
3. `highProbMQueryEfficient_tieAverage_of_certificates` and
   `highProbQueryEfficient_tieAverage_of_certificates` — the size-`m` and
   complete all-proper-subsets theorem shapes, explicitly restricted to
   `Qsub ⊆ Qstar`.
4. In [`AcharyyaBridge.lean`](AcharyyaBridge.lean),
   `highProbQQueryEfficient_tieAverage_of_second_moment_canonical_topEigenvalue_iid`
   additionally derives the embedding-concentration event from the
   Acharyya2025 second-moment and spectral chain.

[`Theorem2.lean`](Theorem2.lean) retains the earlier selected-neighbor theorem
and abstract coverage assumptions for compatibility.  The newer
`QueryEfficiency.lean` and [`Coverage.lean`](Coverage.lean) layers supersede
those assumptions without deleting the simpler theorem engine.

---

## Paper → Lean crosswalk

| Paper object | Lean declaration | File |
|---|---|---|
| Literal tie-averaged nearest-neighbor estimator `ŷ_NN` | `yNNTieAverage_paper` | `QueryEfficiency.lean` |
| Selected-neighbor compatibility estimator | `yNN_paper` | `Theorem2.lean` |
| Subset baseline `ŷ_Q`; target `y` | `yQ`; `yFull` | `Theorem2.lean` |
| Mean-squared error `MSE(·)` | `MSE` | `Basic.lean` |
| Eventual fixed-`Q` query efficiency | `HighProbQQueryEfficient` | `Basic.lean` |
| Eventual size-`m` query efficiency | `HighProbMQueryEfficient` | `Basic.lean` |
| Eventual query efficiency below an arbitrary budget | `HighProbQueryEfficientBelow` | `Basic.lean` |
| Complete eventual query efficiency for every proper subset of `Qstar` | `HighProbQueryEfficient` | `Basic.lean` |
| Tie-averaged MSE convergence from concentration and coverage subevents | `highProb_mse_tieAverage_of_subevents` | `QueryEfficiency.lean` |
| Fixed-`Q` theorem with compact/full-support/iid coverage | `highProbQQueryEfficient_tieAverage_of_compact_iid_fullSupport` | `QueryEfficiency.lean` |
| Size-`m` and all-budget capstones | `highProbMQueryEfficient_tieAverage_of_certificates`; `highProbQueryEfficientBelow_tieAverage_of_certificates` | `QueryEfficiency.lean` |
| Positive mass in every perspective ball | `PerspectiveFullSupport` | `Coverage.lean` |
| Finite iid joint law of reference samples | `IIDReferenceSampler` | `Coverage.lean` |
| Compactness/full support/iid imply uniform coverage | `coverageSubevents_of_compact_iid_fullSupport`; `highProb_uniformCoverage_of_compact_iid_fullSupport` | `Coverage.lean` |
| Assumption 1 (Lipschitz score) | `LipschitzScore` | `Basic.lean` |
| Abstract selected-neighbor engine | `highProb_mse_le_of_concentration`; `highProb_queryEfficient_of_concentration` | `Internal.lean` |
| Second moments through canonical CMDS to literal eventual Quench theorem | `highProbQQueryEfficient_tieAverage_of_second_moment_canonical_topEigenvalue_iid` | `AcharyyaBridge.lean` |
| Distance-only radial Quench engine | `highProbQQueryEfficient_radialTieAverage_of_compact_iid_fullSupport` | `Radial.lean` |
| Growing target-augmented CMDS theorem without finite model factorization | `highProbQQueryEfficient_tieAverage_of_growing_augmented_cmds` | `GrowingAcharyyaBridge.lean` |
| Hypothesis-reduced growing CMDS theorem: Gram witness derives PSD/rank | `highProbQQueryEfficient_tieAverage_of_growing_augmented_cmds_of_gram` | `GrowingAcharyyaBridge.lean` |
| Finite-model response theorem: Gram witness derives PSD/rank and finiteness derives compactness | `highProbQQueryEfficient_tieAverage_of_growing_augmented_secondMoment_of_gram` | `GrowingResponseBridge.lean` |
| Preferred finite-model response theorem: population norm additionally derives sample/population dissimilarity bounds | `highProbQQueryEfficient_tieAverage_of_growing_augmented_secondMoment_of_gram_of_population_norm` | `GrowingResponseBridge.lean` |

## What to scrutinize: remaining assumptions and scope

The strongest fixed-population theorem now derives both formerly abstract
probabilistic inputs:

- embedding concentration is obtained from the Acharyya2025 second-moment,
  CMDS, and aligned-spectral chain;
- uniform reference coverage is obtained from a compact perspective image,
  positive mass in every positive-radius perspective ball, and the finite iid
  joint law of each reference sample.

The fixed-population second-moment theorem still factors the model class through
one finite configuration, but this is no longer a limitation of the strongest
Quench theorem shape.  `GrowingAcharyyaBridge.lean` adjoins each target to the
stage-`n` reference sample, applies CMDS on `Fin (n+1)`, and controls only the
resulting target-to-reference distances.  It therefore needs no global
`indexOf : Model → Fin N` and no globally aligned estimated coordinate map.

The response-level bridge now derives the measurable high-probability CMDS
event from response means, and the finite-model second-moment theorem closes
that concentration step by a double union bound.  The preferred finite-model
capstone derives compactness from finiteness, derives population PSD/rank from
the supplied Gram configuration, and derives both sample and population
dissimilarity bounds from one population response-norm envelope on the same
good event.  The remaining major statistical seam is uniform response
concentration for infinite model classes under concrete regularity or entropy
assumptions.

Other explicit conditions worth reviewing are:

- `PerspectiveFullSupport` states the exact positive-ball-mass condition used
  by the finite-net proof.  It replaces the paper prose about positive mass on
  compact subsets, which is not the right measure-theoretic formulation.
- `IIDReferenceSampler` packages iid sampling through the finite joint-product
  law needed by the proof.  This is an interface theorem assumption, not an
  assumption that coverage itself already holds.
- The size-`m` and all-budget capstones take a `QuerySubsetCertificate` for each
  relevant `Qsub ⊆ Qstar`.  Thus the quantifier shape is complete, while uniform
  derivation of every subset's spectral/Lipschitz certificate remains a
  separate application-level task.

## File guide

| File | Contents |
|---|---|
| [`Basic.lean`](Basic.lean) | Core model, risk, selected- and tie-aware NN definitions; deterministic and high-probability query-efficiency predicates. |
| [`Internal.lean`](Internal.lean) | High-probability event algebra, selected/tie-averaged deterministic error bounds, MSE integration, and the abstract theorem engine. |
| [`Coverage.lean`](Coverage.lean) | Finite perspective nets, full support, iid reference sampling, geometric miss probabilities, and measurable uniform-coverage subevents. |
| [`QueryEfficiency.lean`](QueryEfficiency.lean) | Strongest coordinate-based fixed-`Q`, size-`m`, and all-strict-budget capstones for the literal tie-averaged estimator. |
| [`Radial.lean`](Radial.lean) | Distance-only tie-averaged NN engine; avoids requiring a global estimated perspective map. |
| [`GrowingAcharyyaBridge.lean`](GrowingAcharyyaBridge.lean) | Target-augmented `Fin (n+1)` CMDS bridge and fixed-`Q` theorem with no finite factorization of the model class; the `_of_gram` capstone derives PSD/rank from the population Gram witness. |
| [`Theorem2.lean`](Theorem2.lean) | Earlier compatibility statements using a selected nearest neighbor and caller-supplied coverage events. |
| [`AcharyyaBridge.lean`](AcharyyaBridge.lean) | Derives embedding concentration from the Acharyya2025 spectral/statistical chain and composes it with the new iid coverage theorem. |
| [`GrowingResponseBridge.lean`](GrowingResponseBridge.lean) | Derives growing CMDS events from response means; the preferred finite capstone removes explicit compactness, PSD, rank, and separate sample/population dissimilarity-bound hypotheses. |

## Build / sanity checks

```bash
lake build DkpsQuench          # type-checks every statement and proof
grep -RIn '\bsorry\b' DkpsQuench   # expect: no matches
grep -RIn '\baxiom\b' DkpsQuench   # expect: no matches
```

### Growing response-level bridge

`GrowingResponseBridge.lean` lowers the remaining statistical interface of the
target-augmented theorem from CMDS entries to response means.  Its main theorem
constructs the sample and population dissimilarity matrices directly from
augmented response-mean batches and derives the CMDS event deterministically.

For finite model classes, the second-moment capstone additionally derives the
uniform target-wise response event by a double union bound.  The remaining
infinite-class task is therefore sharply isolated: replace that finite-target
union bound by a uniform concentration argument for the application model
class, such as a metric-entropy or stochastic-equicontinuity theorem.

### Hypothesis-reduction policy

The current low-level spectral proof retains its proved cross-energy and polar
factor route.  The newer sharp Davis--Kahan projector theory will be integrated
only when it removes or weakens a caller-visible condition, such as the polar
smallness requirement.  Refactoring solely for a cleaner internal proof is
deliberately deferred.
