/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import ForMathlib.Analysis.InnerProductSpace.DavisKahanTheory.SinTheta
import ForMathlib.Analysis.InnerProductSpace.YuWangSamworth
import ForMathlib.Analysis.InnerProductSpace.AlignedBasis

/-!
# Population-gap and statistical Davis--Kahan variants

Literature map:

* `ForMathlib/prose/Yu-Wang-Samworth-2014-core-arguments.tex`, all sections.
* `papers/DavisKahan-formalized-vs-literature.tex`, paragraphs
  "Hoffman--Wielandt and the exact YWS theorem" and
  "The aligned-basis (Procrustes) bound".

This file gives the existing YWS results a canonical subspace-facing API and
records the full interval-block, aligned-basis, and single-vector surfaces.
-/

namespace ForMathlib
namespace DavisKahanTheory

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- Population-only gap around a selected spectral set. -/
def PopulationGap (A : E →ₗ[𝕜] E) (U : Submodule 𝕜 E) (Δ : ℝ) : Prop :=
  InternalGap A U Δ

/-- Frobenius sine distance in canonical subspace notation. -/
noncomputable def sinThetaFrobenius (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : ℝ :=
  UnitarilyInvariantNorm.frobenius 𝕜 E (sinThetaMap U V)

/-- Exact Yu--Wang--Samworth population-gap theorem.

Proof strategy: After replacing arbitrary `V` by the corresponding ordered eigenblock of `B`,
reuse the existing `YuWangSamworth.lean` theorem and bridge its eigenbasis/block notation to
`sinThetaFrobenius`.

Signature audit: False for an arbitrary reducing `V` of `B`: with `B = A`, choose a different
reducing subspace and the right side is zero. `V` must be the corresponding ordered eigenblock
(or a uniquely gap-selected branch).
-/
theorem yuWangSamworth_sinTheta_le
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : Reduces A U) (hV : Reduces B V)
    {d : ℕ} (hrank : finrank 𝕜 U = d) {Δ : ℝ} (hΔ : 0 < Δ)
    (hgap : PopulationGap A U Δ) :
    sinThetaFrobenius U V ≤
      2 * min (Real.sqrt d * ‖(B - A).toContinuousLinearMap‖)
        (UnitarilyInvariantNorm.frobenius 𝕜 E (B - A)) / Δ := by
  sorry

/-- Arbitrary contiguous population eigenblock.

Proof strategy: Restate using contiguous eigenvalue indices (or a continued contour-selected
branch), then apply the preceding YWS theorem with the population gap formed by the adjacent
eigenvalues.

Signature audit: Using the same numerical interval for `B` does not in general select the
corresponding population eigenblock, and its dimension may change. Use ordered eigenvalue
indices, or add a perturbation-smallness/contour continuation hypothesis that fixes the branch.
-/
theorem yuWangSamworth_intervalBlock_le
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {a b Δ : ℝ} (hΔ : 0 < Δ)
    (hgap : InternalGap A (spectralSubspace A (Set.Icc a b)) Δ) :
    let U := spectralSubspace A (Set.Icc a b)
    let V := spectralSubspace B (Set.Icc a b)
    sinThetaFrobenius U V ≤
      2 * min (Real.sqrt (finrank 𝕜 U) * ‖(B - A).toContinuousLinearMap‖)
        (UnitarilyInvariantNorm.frobenius 𝕜 E (B - A)) / Δ := by
  sorry

/-- Procrustes-aligned orthonormal bases.

Proof strategy: Choose principal vector bases and the polar/Procrustes alignment of the overlap
matrix; sum `‖v_i-u_i‖² = 2(1-cos θ_i)` and use `1-cos θ ≤ sin² θ`.
-/
theorem exists_aligned_orthonormalBasis
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] {d : ℕ}
    (hrankU : finrank 𝕜 U = d) (hrankV : finrank 𝕜 V = d) :
    ∃ (u v : Fin d → E), Orthonormal 𝕜 u ∧ Orthonormal 𝕜 v ∧
      Submodule.span 𝕜 (Set.range u) = U ∧
      Submodule.span 𝕜 (Set.range v) = V ∧
      ∑ i, ‖v i - u i‖ ^ 2 ≤ 2 * sinThetaFrobenius U V ^ 2 := by
  sorry

/-- YWS aligned-basis perturbation bound.

Proof strategy: Combine the corrected YWS sine bound with `exists_aligned_orthonormalBasis`,
take square roots, and simplify constants.

Signature audit: False for an arbitrary reducing `V` of `B`; inherit the corrected
corresponding-eigenblock selection from `yuWangSamworth_sinTheta_le` before applying Procrustes
alignment.
-/
theorem yuWangSamworth_alignedBasis_le
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : Reduces A U) (hV : Reduces B V)
    {d : ℕ} (hrankU : finrank 𝕜 U = d) (hrankV : finrank 𝕜 V = d)
    {Δ : ℝ} (hΔ : 0 < Δ) (hgap : PopulationGap A U Δ) :
    ∃ (u v : Fin d → E), Orthonormal 𝕜 u ∧ Orthonormal 𝕜 v ∧
      Submodule.span 𝕜 (Set.range u) = U ∧
      Submodule.span 𝕜 (Set.range v) = V ∧
      Real.sqrt (∑ i, ‖v i - u i‖ ^ 2) ≤
        2 * Real.sqrt 2 *
          min (Real.sqrt d * ‖(B - A).toContinuousLinearMap‖)
            (UnitarilyInvariantNorm.frobenius 𝕜 E (B - A)) / Δ := by
  sorry

/-- Rank-one/sign-aligned eigenvector corollary.

Proof strategy: After selecting the corresponding isolated eigenvector branch, specialize the
aligned-basis theorem to rank one and take the unit scalar supplied by complex/real Procrustes
alignment.

Signature audit: False for an arbitrary eigenvector `v` of `B`: with `B = A`, choose a different
eigenvector. Require the corresponding ordered eigenvalue/eigenvector branch or a hypothesis
locating `μ` in the isolated population cluster.
-/
theorem yuWangSamworth_eigenvector_le
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    {lam μ Δ : ℝ} (hAu : A u = (lam : 𝕜) • u)
    (hBv : B v = (μ : 𝕜) • v) (hΔ : 0 < Δ)
    (hgap : ∀ ν ∈ restrictedSpectrum A (Submodule.span 𝕜 {u})ᗮ,
      Δ ≤ |lam - ν|) :
    ∃ c : 𝕜, ‖c‖ = 1 ∧
      ‖c • v - u‖ ≤ 2 * Real.sqrt 2 * ‖(B - A).toContinuousLinearMap‖ / Δ := by
  sorry

end DavisKahanTheory
end ForMathlib
