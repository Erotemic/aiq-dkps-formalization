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

Lean proof route for a weaker agent:

1. Expand `B-A` into the rectangular blocks `Q_j (B-A) P_i` and use Frobenius orthogonality of distinct blocks.
2. Rewrite each block with the scalar eigenvalue relations from `hblocks`; isolate the matched term `lam i - μ i` and the off-diagonal rotation coefficients.
3. Apply `hsep` termwise, sum over `i,j`, and identify the resulting sums with `totalRotationEnergy` and `eigenvalueMotionEnergy`.
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

Lean proof route for a weaker agent:

1. Use `hAblocks` and `hBblocks` to turn each diagonal block of `A` and `B` into scalar
   multiplication by `lam i` and `μ i`.
2. Expand the Frobenius square of the diagonal and off-diagonal parts of `B-A` in the `P`
   decomposition.
3. Use `hnd` to express the change-of-resolution coefficients between `P` and `Q` and apply
   the separation bound `hsepB` to the quadratic remainder.
4. Apply `hoffSmall` to absorb the remainder and sum over `i`.

Signature audit: `μ` is now tied to the perturbed spectral family `Q`; the previous free
parameter made the lower bound vacuous or false.
-/
theorem diagonalPerturbation_sub_offDiagonal_le_eigenvalueMotion
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {m : ℕ} (P Q : OrthoProjFamily 𝕜 E m) (hnd : P.NonDegenerate Q)
    (lam μ : Fin m → ℝ)
    (hAblocks : ∀ i, SpectrumIn A (LinearMap.range (P.proj i)) {lam i})
    (hBblocks : ∀ i, SpectrumIn B (LinearMap.range (Q.proj i)) {μ i})
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

Lean proof route for a weaker agent:

1. Combine `totalRotation_add_eigenvalueMotion_le` with the corrected eigenvalue-motion lower bound and cancel the diagonal energy algebraically.
2. Substitute the eigenvalue-motion lower bound and the Frobenius pinch/off-diagonal Pythagorean decomposition.
3. Use `nlinarith` only after all norm squares have been named and nonnegativity facts supplied.
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

Lean proof route for a weaker agent:

1. Set `y := projection U x` and `z := complementaryProjection U x`; prove `x=y+z` and `⟪y,z⟫=0`.
2. Project the eigen-equation to both blocks, pair with `y` and `z`, and subtract the real parts so the eigenvalue term cancels.
3. Apply `hlower`, `hupper`, and Cauchy--Schwarz to the perturbation cross term; use `hx` only at the final normalization step.
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

Lean proof route for a weaker agent:

1. Set `y := projection U x` and `z := complementaryProjection U x`; prove `x=y+z` and `⟪y,z⟫=0`.
2. Project the eigen-equation to both blocks, pair with `y` and `z`, and subtract the real parts so the eigenvalue term cancels.
3. Apply `hlower`, `hupper`, and Cauchy--Schwarz to the perturbation cross term; use `hx` only at the final normalization step.
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
