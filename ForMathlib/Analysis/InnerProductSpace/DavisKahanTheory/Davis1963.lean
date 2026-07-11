/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import ForMathlib.Analysis.InnerProductSpace.DavisKahanTheory.DirectRotation
import ForMathlib.Analysis.InnerProductSpace.RotationBound
import ForMathlib.Analysis.InnerProductSpace.RotationSharp

/-!
# Davis's 1963 finite-dimensional rotation theory

Literature map:

* `ForMathlib/prose/Davis-1963-core-arguments.tex`, all sections.
* `papers/DavisKahan-formalized-vs-literature.tex`, paragraphs
  "Davis's sharper total-rotation estimate" and
  "The per-eigenvector sin2theta/tan2theta theorem".

These declarations provide basis-independent endpoints around the existing
`RotationBound.lean` and `RotationSharp.lean` proofs.
-/

namespace ForMathlib
namespace DavisKahanTheory

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- Squared total rotation of two complete orthogonal decompositions. -/
noncomputable def totalRotationEnergy {m : ℕ}
    (P Q : OrthoProjFamily 𝕜 E m) (hnd : P.NonDegenerate Q) : ℝ := by
  sorry

/-- Diagonal pinch associated with a complete orthogonal projection family. -/
noncomputable def familyPinch {m : ℕ} (P : OrthoProjFamily 𝕜 E m)
    (H : E →ₗ[𝕜] E) : E →ₗ[𝕜] E :=
  ∑ i, P.proj i ∘ₗ H ∘ₗ P.proj i

/-- Sum of squared eigenvalue motions under a chosen canonical matching. -/
noncomputable def eigenvalueMotionEnergy {m : ℕ}
    (lam μ : Fin m → ℝ) : ℝ :=
  ∑ i, (lam i - μ i) ^ 2

/-- Off-diagonal part relative to a complete projection family. -/
noncomputable def familyOffDiagonal {m : ℕ} (P : OrthoProjFamily 𝕜 E m)
    (H : E →ₗ[𝕜] E) : E →ₗ[𝕜] E :=
  H - familyPinch P H

/-- Davis 1963, Theorem 3.2: sharpened total-rotation bound with eigenvalue
motion subtracted from the available perturbation energy.

Proof strategy: Expand the Frobenius norm of `B-A` in the matched projection families, apply the
scalar separation inequality to every off-diagonal block, and sum. This is finite family
combinatorics, not an infinite specialization.
-/
theorem totalRotation_add_eigenvalueMotion_le
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {m : ℕ} (P Q : OrthoProjFamily 𝕜 E m) (hnd : P.NonDegenerate Q)
    (lam μ : Fin m → ℝ) {γ : ℝ} (hγ : 0 < γ)
    (hblocks : ∀ i, SpectrumIn A (LinearMap.range (P.proj i)) {lam i} ∧
      SpectrumIn B (LinearMap.range (Q.proj i)) {μ i})
    (hsep : ∀ i j, i ≠ j →
      γ ^ 2 + (lam i - μ i) ^ 2 ≤ (lam i - μ j) ^ 2) :
    γ ^ 2 * totalRotationEnergy P Q hnd + eigenvalueMotionEnergy lam μ ≤
      UnitarilyInvariantNorm.frobenius 𝕜 E (B - A) ^ 2 := by
  sorry

/-- Davis 1963, Theorem 4.1: under spectral separation and the small
off-diagonal hypothesis, eigenvalue motion is bounded **below** by the
diagonal perturbation energy minus the off-diagonal energy.

Proof strategy: After connecting `μ` to the perturbed spectral blocks, reproduce Davis 1963
Theorem 4.1 by expanding diagonal/off-diagonal Frobenius energies and using the smallness
hypothesis to control the quadratic remainder.

Signature audit: Likely false as stated because `μ` is not connected to `B` or to a perturbed
spectral family. Add a `Q` family and `SpectrumIn B (range (Q.proj i)) {μ i}`, or state the
exact ordered-eigenvalue hypothesis from Davis 1963.
-/
theorem diagonalPerturbation_sub_offDiagonal_le_eigenvalueMotion
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {m : ℕ} (P : OrthoProjFamily 𝕜 E m) (lam μ : Fin m → ℝ)
    (hblocks : ∀ i, SpectrumIn A (LinearMap.range (P.proj i)) {lam i})
    {γ : ℝ} (hγ : 0 < γ)
    (hsepB : ∀ i j, i ≠ j → γ ≤ |μ i - μ j|)
    (hoffSmall : UnitarilyInvariantNorm.frobenius 𝕜 E
        (familyOffDiagonal P (B - A)) ≤ γ / Real.sqrt 2) :
    UnitarilyInvariantNorm.frobenius 𝕜 E (familyPinch P (B - A)) ^ 2 -
        UnitarilyInvariantNorm.frobenius 𝕜 E
          (familyOffDiagonal P (B - A)) ^ 2 ≤
      eigenvalueMotionEnergy lam μ := by
  sorry

/-- Davis's off-diagonal corollary for total rotation.  This combines the
rotation/eigenvalue budget with the lower bound on eigenvalue motion.

Proof strategy: Combine `totalRotation_add_eigenvalueMotion_le` with the corrected
eigenvalue-motion lower bound and cancel the diagonal energy algebraically.
-/
theorem totalRotation_le_two_mul_offDiagonal
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {m : ℕ} (P Q : OrthoProjFamily 𝕜 E m) (hnd : P.NonDegenerate Q)
    (lam μ : Fin m → ℝ) {γ γ' : ℝ} (hγ : 0 < γ)
    (hblocks : ∀ i, SpectrumIn A (LinearMap.range (P.proj i)) {lam i} ∧
      SpectrumIn B (LinearMap.range (Q.proj i)) {μ i})
    (hsepB : ∀ i j, i ≠ j → γ ≤ |μ i - μ j|)
    (hoffSmall : UnitarilyInvariantNorm.frobenius 𝕜 E
        (familyOffDiagonal P (B - A)) ≤ γ / Real.sqrt 2)
    (hsepMixed : ∀ i j, i ≠ j →
      γ' ^ 2 + (lam i - μ i) ^ 2 ≤ (lam i - μ j) ^ 2) :
    γ' ^ 2 * totalRotationEnergy P Q hnd ≤
      2 * UnitarilyInvariantNorm.frobenius 𝕜 E
        (familyOffDiagonal P (B - A)) ^ 2 := by
  sorry

/-- Sharp two-subspace product estimate, the 1963 ancestor of `sin 2Θ`.

Proof strategy: Decompose the perturbed eigenvector into `U` and `Uᗮ`, test the eigen-equation
against both components, subtract the resulting Rayleigh inequalities, and use the perturbation
norm; for the tangent version use vanishing pinch to retain the cosine-difference factor.
-/
theorem sinTwoTheta_eigenvector_product_le
    {A H : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hH : H.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (hU : Reduces A U) {a b ε lam : ℝ} (hab : a < b)
    (hupper : ∀ z ∈ Uᗮ, RCLike.re ⟪A z, z⟫_𝕜 ≤ a * ‖z‖ ^ 2)
    (hlower : ∀ y ∈ U, b * ‖y‖ ^ 2 ≤ RCLike.re ⟪A y, y⟫_𝕜)
    {x : E} (hx : ‖x‖ = 1) (heig : (A + H) x = (lam : 𝕜) • x)
    (hHnorm : ‖H.toContinuousLinearMap‖ ≤ ε) :
    (b - a) * ‖projection U x‖ * ‖complementaryProjection U x‖ ≤ ε := by
  sorry

/-- Vanishing-pinch product estimate, the 1963 ancestor of `tan 2Θ`.

Proof strategy: Decompose the perturbed eigenvector into `U` and `Uᗮ`, test the eigen-equation
against both components, subtract the resulting Rayleigh inequalities, and use the perturbation
norm; for the tangent version use vanishing pinch to retain the cosine-difference factor.
-/
theorem tanTwoTheta_eigenvector_product_le
    {A H : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hH : H.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (hU : Reduces A U) (hoff : IsOffDiagonal U H)
    {a b ε lam : ℝ} (hab : a < b)
    (hupper : ∀ z ∈ Uᗮ, RCLike.re ⟪A z, z⟫_𝕜 ≤ a * ‖z‖ ^ 2)
    (hlower : ∀ y ∈ U, b * ‖y‖ ^ 2 ≤ RCLike.re ⟪A y, y⟫_𝕜)
    {x : E} (hx : ‖x‖ = 1) (heig : (A + H) x = (lam : 𝕜) • x)
    (hHnorm : ‖H.toContinuousLinearMap‖ ≤ ε) :
    (b - a) * ‖projection U x‖ * ‖complementaryProjection U x‖ ≤
      |‖projection U x‖ ^ 2 - ‖complementaryProjection U x‖ ^ 2| * ε := by
  sorry

end DavisKahanTheory
end ForMathlib
