/-
Deterministic bridges from finite Acharyya DKPS concentration statements to the
Quench query-efficiency concentration hypothesis.

Quench's theorem is stated over an abstract model space and assumes a uniform
embedding-error event over all models.  Acharyya's DKPS concentration theorems
are finite-configuration statements.  The bridge therefore explicitly assumes a
factorization of the Quench embedding maps through a finite Acharyya
configuration.
-/

import Acharyya2025.Concentration
import Acharyya2025.AlignedPipeline
import DkpsQuench.Basic

open scoped BigOperators Topology
open Filter MeasureTheory

namespace DkpsQuench.AcharyyaBridge

open Acharyya2024

universe u v

variable {Q : Type u}
variable {X : Type v} [MeasurableSpace X]
variable {Ω : Type} [MeasurableSpace Ω]

/--
Finite Acharyya configuration concentration gives Quench's uniform model-space
embedding concentration when the true and estimated Quench embeddings factor
through the finite configuration by an index map.

The factorization hypothesis is essential: without it, a bound over `Fin n`
cannot imply a bound over an arbitrary model type.

Formalized by Codex 5.5 High, per user-observed model label.
-/
theorem quench_uniform_embedding_error_of_finite_configError
    (μ : Nat → Measure Ω)
    (hμ : ∀ n, IsProbabilityMeasure (μ n))
    {n d : Nat}
    (indexOf : Model Q X → Fin n)
    (ψFinite : Config n d)
    (ψhatFinite : Nat → Ω → Config n d)
    (ψ : Model Q X → Vec d)
    (ψHat : Nat → Ω → Model Q X → Vec d)
    (c : Nat → Real)
    (hψ : ∀ f, ψ f = ψFinite (indexOf f))
    (hψHat : ∀ u ω f, ψHat u ω f = ψhatFinite u ω (indexOf f))
    (hfinite :
      Acharyya2024.HighProbAtTop μ
        (fun u => {ω | ConfigError (ψhatFinite u ω) ψFinite ≤ c u})) :
    _root_.HighProbAtTop μ hμ
      (fun u => {ω | ∀ f, ‖ψHat u ω f - ψ f‖ ≤ c u}) := by
  intro δ hδ
  obtain ⟨N, hN⟩ := hfinite δ hδ
  refine ⟨N, fun u hu => ?_⟩
  exact (hN u hu).trans (MeasureTheory.measure_mono fun ω hω f => by
    calc
      ‖ψHat u ω f - ψ f‖
          = ‖ψhatFinite u ω (indexOf f) - ψFinite (indexOf f)‖ := by
            simp [hψ f, hψHat u ω f]
      _ ≤ ConfigError (ψhatFinite u ω) ψFinite :=
            norm_config_le_ConfigError (ψhatFinite u ω) ψFinite (indexOf f)
      _ ≤ c u := hω)

/--
**Quench uniform embedding error from the aligned CMDS spectral estimator.**

A thin, honest composition: the matrix-world spectral capstone (via
`Acharyya2025.AlignedPipeline.highProb_aligned_configError_of_entrywise_close`)
produces a high-probability bound on `ConfigError (alignedSpectralConfig …) ψ`,
and the existing generic
`quench_uniform_embedding_error_of_finite_configError` lifts it to Quench's
uniform model-space embedding-error event, provided the Quench embedding maps
factor through the finite Acharyya configuration by an index map.

What is composed end-to-end: the entrywise CMDS-closeness HP event `hcenter` is
fed through the proved capstone to produce the aligned-`ConfigError` HP event,
which is then transported by the index-map factorization.  What is hypothesized:
the factorization data (`indexOf`, `hψ`, `hψHat`), the spectral hypotheses of the
capstone (PSD/rank/floor/cap/smallness/polar), the Gram realization of `ψ`, and
the entrywise-closeness HP event `hcenter`.

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
theorem quench_uniform_embedding_error_of_aligned_spectral
    (μ : Nat → Measure Ω)
    (hμ : ∀ k, IsProbabilityMeasure (μ k))
    {n d : Nat} (hd : d ≤ n)
    (Dhat : Nat → Ω → Acharyya2024.DisMat n) (D : Acharyya2024.DisMat n)
    (hsym : ∀ u ω,
      (Acharyya2025.MathlibBridge.disMatToMatrix
        (Acharyya2025.Deterministic.classicalMDSMatrix (Dhat u ω))).IsHermitian)
    (hB : (Acharyya2025.MathlibBridge.disMatToMatrix
        (Acharyya2025.Deterministic.classicalMDSMatrix D)).PosSemidef)
    (hrank : (Acharyya2025.MathlibBridge.disMatToMatrix
        (Acharyya2025.Deterministic.classicalMDSMatrix D)).rank ≤ d)
    {α Λ : Real} (hα_pos : 0 < α)
    (hfloor : ∀ i : Fin n, (i : ℕ) < d →
      α ≤ Acharyya2025.MatrixPerturbation.sortedEigenvalues hB.isHermitian i)
    (hΛ : ∀ l, Acharyya2025.MatrixPerturbation.sortedEigenvalues hB.isHermitian l ≤ Λ)
    (ψFinite : Config n d)
    (hψFinite : ∀ i j, (∑ k, ψFinite i k * ψFinite j k)
      = Acharyya2025.Deterministic.classicalMDSMatrix D i j)
    (rate : Nat → Real) (hrate_nonneg : ∀ u, 0 ≤ rate u)
    (hsmall : ∀ u, (n : Real) * rate u ≤ α / 2)
    (hpolar : ∀ u, (d : Real) *
      (4 * (n : Real) * ((n : Real) * rate u)^2 / α^2) ≤ 1/2)
    (hcenter : Acharyya2024.HighProbAtTop μ (fun u => {ω |
      Acharyya2025.Bridge.EntrywiseClose
        (Acharyya2025.Deterministic.classicalMDSMatrix (Dhat u ω))
        (Acharyya2025.Deterministic.classicalMDSMatrix D) (rate u)}))
    (indexOf : Model Q X → Fin n)
    (ψ : Model Q X → Vec d)
    (ψHat : Nat → Ω → Model Q X → Vec d)
    (hψ : ∀ f, ψ f = ψFinite (indexOf f))
    (hψHat : ∀ u ω f, ψHat u ω f =
      Acharyya2025.AlignedPipeline.alignedSpectralConfig hd Dhat hsym ψFinite
        (fun u => Acharyya2025.ConfigPerturbation.configBound n d α Λ
          ((n : Real) * rate u)) u ω (indexOf f)) :
    _root_.HighProbAtTop μ hμ
      (fun u => {ω | ∀ f, ‖ψHat u ω f - ψ f‖ ≤
        Acharyya2025.ConfigPerturbation.configBound n d α Λ
          ((n : Real) * rate u)}) := by
  -- Capstone composition: produce the aligned-`ConfigError` HP event.
  have haligned :=
    Acharyya2025.AlignedPipeline.highProb_aligned_configError_of_entrywise_close
      μ hd Dhat D hsym hB hrank hα_pos hfloor hΛ ψFinite hψFinite
      rate hrate_nonneg hsmall hpolar hcenter
  -- Lift through the index-map factorization with the existing generic theorem.
  exact quench_uniform_embedding_error_of_finite_configError
    μ hμ indexOf ψFinite
    (Acharyya2025.AlignedPipeline.alignedSpectralConfig hd Dhat hsym ψFinite
      (fun u => Acharyya2025.ConfigPerturbation.configBound n d α Λ
        ((n : Real) * rate u)))
    ψ ψHat
    (fun u => Acharyya2025.ConfigPerturbation.configBound n d α Λ
      ((n : Real) * rate u))
    hψ hψHat haligned

end DkpsQuench.AcharyyaBridge
