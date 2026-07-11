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

/-- `U` and `V` are spectral blocks with the same ordered eigenvalue indices
for `A` and `B`.  This is the finite branch-selection datum used by the
Yu--Wang--Samworth population-gap theorem. -/
def CorrespondingEigenblock {A B : E →ₗ[𝕜] E}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (U V : Submodule 𝕜 E) : Prop :=
  ∃ (n : ℕ) (hn : finrank 𝕜 E = n) (p : Fin n → Prop),
    U = specSubspace (hA.eigenvectorBasis hn) p ∧
      V = specSubspace (hB.eigenvectorBasis hn) p

/-- Frobenius sine distance in canonical subspace notation. -/
noncomputable def sinThetaFrobenius (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : ℝ :=
  UnitarilyInvariantNorm.frobenius 𝕜 E (sinThetaMap U V)

/-- Exact Yu--Wang--Samworth population-gap theorem.

Lean proof route for a weaker agent:

1. After replacing arbitrary `V` by the corresponding ordered eigenblock of `B`, reuse the existing `YuWangSamworth.lean` theorem and bridge its eigenbasis/block notation to `sinThetaFrobenius`.
2. Unpack `hcorr` to obtain one eigenbasis index predicate shared by `A` and `B`.
3. Apply the existing YWS theorem and rewrite its block Frobenius quantity as `sinThetaFrobenius`.

Signature audit: `hcorr` now fixes the perturbed block by the same ordered eigenvalue indices;
this excludes arbitrary reducing subspaces when `B=A`.
-/
theorem yuWangSamworth_sinTheta_le
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : Reduces A U) (hV : Reduces B V)
    (hcorr : CorrespondingEigenblock hA hB U V)
    {d : ℕ} (hrank : finrank 𝕜 U = d) {Δ : ℝ} (hΔ : 0 < Δ)
    (hgap : PopulationGap A U Δ) :
    sinThetaFrobenius U V ≤
      2 * min (Real.sqrt d * ‖(B - A).toContinuousLinearMap‖)
        (UnitarilyInvariantNorm.frobenius 𝕜 E (B - A)) / Δ := by
  sorry

/-- Arbitrary contiguous population eigenblock.

Lean proof route for a weaker agent:

1. Restate using contiguous eigenvalue indices (or a continued contour-selected branch), then apply the preceding YWS theorem with the population gap formed by the adjacent eigenvalues.
2. Rewrite `U` using `hUeq` and unpack `hcorr` to identify the corresponding perturbed block.
3. Apply `yuWangSamworth_sinTheta_le` with `d = finrank 𝕜 U`.

Signature audit: `hUeq` records the population interval while `hcorr` selects the perturbed
block by ordered indices, so eigenvalue drift across the numerical interval does not change the
branch.
-/
theorem yuWangSamworth_intervalBlock_le
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection]
    {a b Δ : ℝ} (hΔ : 0 < Δ)
    (hUeq : U = spectralSubspace A (Set.Icc a b))
    (hcorr : CorrespondingEigenblock hA hB U V)
    (hgap : InternalGap A U Δ) :
    sinThetaFrobenius U V ≤
      2 * min (Real.sqrt (finrank 𝕜 U) * ‖(B - A).toContinuousLinearMap‖)
        (UnitarilyInvariantNorm.frobenius 𝕜 E (B - A)) / Δ := by
  sorry

/-- Procrustes-aligned orthonormal bases.

Lean proof route for a weaker agent:

1. Choose principal vector bases and the polar/Procrustes alignment of the overlap matrix
2. sum `‖v_i-u_i‖² = 2(1-cos θ_i)` and use `1-cos θ ≤ sin² θ`.
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

Lean proof route for a weaker agent:

1. Combine the corrected YWS sine bound with `exists_aligned_orthonormalBasis`, take square roots, and simplify constants.
2. Use `hcorr` in `yuWangSamworth_sinTheta_le`, then obtain aligned bases from `exists_aligned_orthonormalBasis`.
3. Take square roots with explicit nonnegativity facts and simplify the constant to `2 * sqrt 2`.

Signature audit: The aligned-basis theorem now inherits the same `hcorr` branch selection as
the sine-distance theorem.
-/
theorem yuWangSamworth_alignedBasis_le
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : Reduces A U) (hV : Reduces B V)
    (hcorr : CorrespondingEigenblock hA hB U V)
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

Lean proof route for a weaker agent:

1. After selecting the corresponding isolated eigenvector branch, specialize the aligned-basis theorem to rank one and take the unit scalar supplied by complex/real Procrustes alignment.
2. Convert the rank-one `hcorr` statement into the corresponding block premise for the aligned-basis theorem.
3. Extract the unique basis vectors and convert the one-dimensional unitary alignment into a scalar `c` of norm one.

Signature audit: The rank-one `hcorr` premise selects `v` from the corresponding ordered
perturbed eigenline rather than an arbitrary eigenvector of `B`.
-/
theorem yuWangSamworth_eigenvector_le
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    {lam μ Δ : ℝ} (hAu : A u = (lam : 𝕜) • u)
    (hBv : B v = (μ : 𝕜) • v)
    (hcorr : CorrespondingEigenblock hA hB
      (Submodule.span 𝕜 {u}) (Submodule.span 𝕜 {v}))
    (hΔ : 0 < Δ)
    (hgap : ∀ ν ∈ restrictedSpectrum A (Submodule.span 𝕜 {u})ᗮ,
      Δ ≤ |lam - ν|) :
    ∃ c : 𝕜, ‖c‖ = 1 ∧
      ‖c • v - u‖ ≤ 2 * Real.sqrt 2 * ‖(B - A).toContinuousLinearMap‖ / Δ := by
  sorry

end DavisKahanTheory
end ForMathlib
