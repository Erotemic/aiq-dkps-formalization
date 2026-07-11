/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import ForMathlib.Analysis.InnerProductSpace.DavisKahanTheory.Davis1963

/-!
# Sharpness and two-dimensional extremizers

Literature map:

* `ForMathlib/prose/Davis-Kahan-1970-part-III-core-arguments.tex`,
  Section 13.
* Davis--Kahan (1970), Section 2 immediately after the four headline
  theorems, and the two-dimensional models used throughout Sections 6--8.
* `ForMathlib/prose/Davis-1963-core-arguments.tex`, final sharp two-subspace
  section.

The constants in all four classic theorems are optimal.  Direct sums of the
`2 × 2` extremizers attain equality simultaneously for every unitarily
invariant norm.  These facts should be formal theorems, not prose claims.
-/


/-! ## Remaining construction plan

Use a single explicit planar model for every sharpness result.  Define the
reference and rotated one-dimensional subspaces in `EuclideanSpace R (Fin 2)`,
use a diagonal gapped operator, and form sine, tangent, and double-angle
perturbations by rotation/conjugation.  Prove the model projections and
singular values by extensional matrix calculation.  Each sharpness theorem
should then be a scalar trigonometric simplification, making failures at right
angles or quarter turns explicit rather than hidden in abstract geometry.
-/


/-! ## Weak-agent execution plan: explicit planar extremizers

Use the standard basis `e0`, `e1` of `EuclideanSpace 𝕜 (Fin 2)`.  Add local
abbreviations and simp lemmas before defining any operator:

* `uθ := cos θ • e0 + sin θ • e1`;
* `vθ := -sin θ • e0 + cos θ • e1`;
* orthonormality of `uθ,vθ`;
* `modelSubspace = 𝕜 ∙ e0` and
  `rotatedModelSubspace θ = 𝕜 ∙ uθ`.

Prefer `Submodule.span 𝕜 {e0}` and `Submodule.span 𝕜 {uθ}`.  Prove membership
and projection formulas once.  Then establish the `2 × 2` matrices of both
orthogonal projections by `LinearMap.ext` on `e0,e1`.

Define `modelGappedOperator a b` by
`e0 ↦ a • e0`, `e1 ↦ b • e1`.  For the `sin Θ` extremizer, use

`Rθ D Rθ⁻¹ - D`,

where `Rθ` sends `e0,e1` to `uθ,vθ`.  Its eigenvalues are
`±(b-a) sin θ`, so its operator norm is `(b-a) sin θ` on the stated angle
range.  Prove this by an explicit characteristic/eigenvector calculation or
by squaring the matrix to a scalar multiple of the identity.

Do not reuse that perturbation for the tangent and double-angle theorems.
For each remaining model, first write the exact equality conditions from the
corresponding block/Sylvester proof and solve the resulting scalar equations
for the four matrix entries.  Add a private theorem recording those entries,
then define the operator from the solved matrix.  This is safer than guessing a
rotation conjugate and discovering later that the zero-compression or
off-diagonal hypothesis fails.

For every model, prove in this order:

1. symmetry;
2. the required reducing and compression/off-diagonal hypotheses;
3. the exact internal or ordered gap;
4. the singular values of the perturbation;
5. the singular values of the angle operator;
6. the displayed UI-norm equality by unitary invariance and homogeneity.

For a `2 × 2` operator whose square is `r^2 • id`, use that identity to prove
both singular values are `|r|`; avoid expanding the general singular-value
definition repeatedly.  Keep trigonometric side conditions (`sin θ ≥ 0`,
`cos θ > 0`, `cos (2θ) > 0`) as named lemmas.

For direct sums, define the block operator by the decomposition
`Fin (2*m) ≃ Fin m × Fin 2` and transport `m` copies of the planar model.
Prove the singular-value multiset is repeated blockwise before invoking any UI
norm.  The scalar limit theorem should use existing `Real.tendsto_sin_div` and
`Real.tendsto_tan_div`-style lemmas if available; isolate it from the operator
sharpness development.
-/

namespace ForMathlib
namespace DavisKahanTheory

open scoped InnerProductSpace BigOperators
open Filter

variable {𝕜 : Type*} [RCLike 𝕜]

abbrev Plane (𝕜 : Type*) [RCLike 𝕜] := EuclideanSpace 𝕜 (Fin 2)

/-- Coordinate line in the two-dimensional model. -/
noncomputable def modelSubspace : Submodule 𝕜 (Plane 𝕜) := by
  sorry

/-- Line obtained by rotating the coordinate line by angle `θ`. -/
noncomputable def rotatedModelSubspace (θ : ℝ) : Submodule 𝕜 (Plane 𝕜) := by
  sorry

/-! Construct the following five operators as explicit `2 × 2` matrices in
the standard basis.  Start with `diag(a,b)`, conjugate by the planar rotation
for the `sin Θ` model, use the graph residual for `tan Θ`, and take the
reflection/off-diagonal parts for the double-angle models.  Matrix ext reduces
all later norm and equality claims to scalar trigonometric identities. -/

/-- Diagonal gapped operator used by the extremal examples.

Construction route: use the diagonal `2×2` matrix with entries `a,b`; define
the linear map by matrix multiplication and prove the gap from the two
coordinate eigenvectors. -/
noncomputable def modelGappedOperator (a b : ℝ) :
    Plane 𝕜 →ₗ[𝕜] Plane 𝕜 := by
  sorry

/-- Perturbation producing equality in the `sin Θ` model.

Construction route: conjugate the diagonal model by the planar rotation and
subtract the original matrix; simplify entries with sine and cosine identities. -/
noncomputable def modelSinThetaPerturbation (a b θ : ℝ) :
    Plane 𝕜 →ₗ[𝕜] Plane 𝕜 := by
  sorry

/-- Perturbation/residual producing equality in the `tan Θ` model.

Construction route: use the graph residual of the rotated one-dimensional
subspace, with scaling chosen so the ordered Sylvester inequality is an
equality. -/
noncomputable def modelTanThetaPerturbation (a b θ : ℝ) :
    Plane 𝕜 →ₗ[𝕜] Plane 𝕜 := by
  sorry

/-- Reflection-compatible perturbation producing equality in `sin (2 Θ)`.

Construction route: take the reflection-compatible off-diagonal block of the
rotated model and normalize it to realize the double-angle sine equality. -/
noncomputable def modelSinTwoThetaPerturbation (a b θ : ℝ) :
    Plane 𝕜 →ₗ[𝕜] Plane 𝕜 := by
  sorry

/-- Off-diagonal perturbation used by the `tan (2 Θ)` extremizer.

Construction route: choose the purely off-diagonal planar perturbation for
which the Riccati denominator and numerator attain the tangent double-angle
ratio. -/
noncomputable def modelTanTwoThetaPerturbation (a b θ : ℝ) :
    Plane 𝕜 →ₗ[𝕜] Plane 𝕜 := by
  sorry

/-- The model subspaces have exactly the prescribed principal angle.

Lean proof route for a weaker agent:

1. Write the two normalized spanning vectors explicitly, compute the single overlap singular value `|cos θ|`, and use the angle-range hypotheses to simplify `arccos`.
2. Prove the overlap scalar is nonnegative on `[0,π/2]`, so the absolute value disappears.
3. Rewrite the first principal angle with `Real.arccos_cos` and the supplied range bounds.
-/
theorem principalAngles_model (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ Real.pi / 2) :
    principalAngles (modelSubspace (𝕜 := 𝕜)) (rotatedModelSubspace (𝕜 := 𝕜) θ) 0 = θ := by
  sorry

/-- Equality case for the `sin Θ` theorem.

Lean proof route for a weaker agent:

1. First separate the correct planar model for this theorem family.
2. Then compute the two-by-two matrices, their singular values, the gap, and the relevant angle function explicitly; equality should reduce to a scalar trigonometric identity.

Signature audit: The theorem now uses a dedicated `sin Θ` perturbation model; do not reuse it
for the tangent or double-angle families.
-/
theorem sinTheta_model_equality
    (N : UnitarilyInvariantNorm 𝕜 (Plane 𝕜))
    {a b θ : ℝ} (hab : a < b) (hθ0 : 0 ≤ θ) (hθ1 : θ < Real.pi / 2) :
    (b - a) * N (sinAngleOperator (modelSubspace (𝕜 := 𝕜))
      (rotatedModelSubspace (𝕜 := 𝕜) θ)) =
      N (modelSinThetaPerturbation (𝕜 := 𝕜) a b θ) := by
  sorry

/-- Equality case for the `tan Θ` theorem.

Lean proof route for a weaker agent:

1. First separate the correct planar model for this theorem family.
2. Then compute the two-by-two matrices, their singular values, the gap, and the relevant angle function explicitly; equality should reduce to a scalar trigonometric identity.

Signature audit: The dedicated tangent model must include the zero-compression/Galerkin
hypothesis required by the theorem it saturates.
-/
theorem tanTheta_model_equality
    (N : UnitarilyInvariantNorm 𝕜 (Plane 𝕜))
    {a b θ : ℝ} (hab : a < b) (hθ0 : 0 ≤ θ) (hθ1 : θ < Real.pi / 2) :
    (b - a) * N (tanAngleOperator (modelSubspace (𝕜 := 𝕜))
      (rotatedModelSubspace (𝕜 := 𝕜) θ)) =
      N (modelTanThetaPerturbation (𝕜 := 𝕜) a b θ) := by
  sorry

/-- Equality case for the `sin 2Θ` theorem.

Lean proof route for a weaker agent:

1. First separate the correct planar model for this theorem family.
2. Then compute the two-by-two matrices, their singular values, the gap, and the relevant angle function explicitly; equality should reduce to a scalar trigonometric identity.

Signature audit: The dedicated double-angle model is reflection-compatible and is independent
of the single-angle extremizer.
-/
theorem sinTwoTheta_model_equality
    (N : UnitarilyInvariantNorm 𝕜 (Plane 𝕜))
    {a b θ : ℝ} (hab : a < b) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ Real.pi / 2) :
    (b - a) * N (sinTwoAngleOperator (modelSubspace (𝕜 := 𝕜))
      (rotatedModelSubspace (𝕜 := 𝕜) θ)) =
      2 * N (modelSinTwoThetaPerturbation (𝕜 := 𝕜) a b θ) := by
  sorry

/-- Equality case for the `tan 2Θ` theorem.

Lean proof route for a weaker agent:

1. First separate the correct planar model for this theorem family.
2. Then compute the two-by-two matrices, their singular values, the gap, and the relevant angle function explicitly; equality should reduce to a scalar trigonometric identity.
-/
theorem tanTwoTheta_model_equality
    (N : UnitarilyInvariantNorm 𝕜 (Plane 𝕜))
    {a b θ : ℝ} (hab : a < b) (hθ0 : 0 ≤ θ) (hθ1 : θ < Real.pi / 4) :
    (b - a) * N (tanTwoAngleOperator (modelSubspace (𝕜 := 𝕜))
      (rotatedModelSubspace (𝕜 := 𝕜) θ)) =
      2 * N (modelTanTwoThetaPerturbation (𝕜 := 𝕜) a b θ) := by
  sorry

/-- The constant one in the single-angle theorems cannot be decreased.

Lean proof route for a weaker agent:

1. Instantiate the corrected planar equality model at any nonzero admissible angle and use `c < 1` or `c < 2` to obtain the strict counterexample to a smaller universal constant.
2. Choose explicit `a<b` and `0<θ<π/2`, then invoke `sinTheta_model_equality` for the operator norm.
3. Multiply the strict inequality `c<1` by the positive perturbation norm.
-/
theorem sinTheta_constant_optimal :
    ∀ c : ℝ, c < 1 → ∃ (a b θ : ℝ), a < b ∧ 0 < θ ∧
      c * ‖(modelSinThetaPerturbation (𝕜 := 𝕜) a b θ).toContinuousLinearMap‖ <
        (b - a) * ‖(sinAngleOperator (modelSubspace (𝕜 := 𝕜))
          (rotatedModelSubspace (𝕜 := 𝕜) θ)).toContinuousLinearMap‖ := by
  sorry

/-- The factor two in the double-angle theorems cannot be decreased.

Lean proof route for a weaker agent:

1. Instantiate the corrected planar equality model at any nonzero admissible angle and use `c < 1` or `c < 2` to obtain the strict counterexample to a smaller universal constant.
2. Choose an angle with nonzero double-angle map and invoke `sinTwoTheta_model_equality` for the operator norm.
3. Multiply `c<2` by the positive perturbation norm and rewrite the equality.
-/
theorem sinTwoTheta_constant_optimal :
    ∀ c : ℝ, c < 2 → ∃ (a b θ : ℝ), a < b ∧ 0 < θ ∧
      c * ‖(modelSinTwoThetaPerturbation (𝕜 := 𝕜) a b θ).toContinuousLinearMap‖ <
        (b - a) * ‖(sinTwoAngleOperator (modelSubspace (𝕜 := 𝕜))
          (rotatedModelSubspace (𝕜 := 𝕜) θ)).toContinuousLinearMap‖ := by
  sorry

/-- Direct sums of planar equality models attain equality simultaneously for
all unitarily invariant norms.

Lean proof route for a weaker agent:

1. Strengthen the statement first.
2. For the intended result, take an orthogonal direct sum of identical planar extremizers; all singular values occur blockwise, so every symmetric gauge preserves equality.

Signature audit: The conclusion now includes symmetry, reduction, a positive internal gap, and
the exact equality for every UI norm, so it genuinely witnesses simultaneous sharpness.
-/
theorem directSum_models_simultaneous_equality (m : ℕ) :
    ∃ (A H : EuclideanSpace 𝕜 (Fin (2 * m)) →ₗ[𝕜]
        EuclideanSpace 𝕜 (Fin (2 * m)))
      (U V : Submodule 𝕜 (EuclideanSpace 𝕜 (Fin (2 * m))))
      (δ : ℝ),
      A.IsSymmetric ∧ H.IsSymmetric ∧ 0 < δ ∧
      Reduces A U ∧ Reduces (A + H) V ∧ InternalGap A U δ ∧
      ∀ N : UnitarilyInvariantNorm 𝕜 (EuclideanSpace 𝕜 (Fin (2 * m))),
        δ * N (sinTwoAngleOperator U V) = 2 * N H := by
  sorry

/-- To first order in a linear perturbation parameter, all four theorem
conclusions agree.

Lean proof route for a weaker agent:

1. For the current scalar statement, use the standard limits `sin x / x → 1` and `tan x / x → 1`.
2. If the theorem retains its name, add the normalized Davis--Kahan expressions for all four bounds.

Signature audit: The theorem has been renamed to match its scalar content.  The operator-level
first-order comparison should be a separate corollary of the four planar equality theorems.
-/
theorem single_double_sine_tangent_ratios_tendsto_one :
    Tendsto (fun θ : ℝ => Real.sin θ / Real.tan θ) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) ∧
    Tendsto (fun θ : ℝ => Real.sin (2 * θ) / Real.tan (2 * θ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  sorry

end DavisKahanTheory
end ForMathlib
