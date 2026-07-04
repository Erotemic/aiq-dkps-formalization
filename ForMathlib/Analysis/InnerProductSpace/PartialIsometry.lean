/-
Staged for Mathlib: a new `Mathlib/Analysis/InnerProductSpace/PartialIsometry.lean`.

SKELETON (`/develop` Phase 1e Step 2.5): every declaration stated with `sorry`.
-/

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Algebra.Star.StarProjection

/-! # Partial isometries (Sub-dev II)

A **partial isometry** in a star-monoid is an element `u` with `u * star u * u = u`; equivalently
`star u * u` is a projection (`IsStarProjection`). For operators on an inner product space this is
the classical notion: `u` restricts to an isometry on `(ker u)ᗮ` and vanishes on `ker u`.

Mathlib currently has **no** partial-isometry API (grep-confirmed). This packages the unitary factor
of the polar decomposition `A = U |A|`.

Source: Conway, *A Course in Functional Analysis*, 2nd ed., §VI.3 (partial isometries and the polar
decomposition); Reed–Simon, *Methods of Modern Mathematical Physics I*, §VI (before Thm VI.10).
-/

open scoped InnerProductSpace
open LinearMap

/-- **Partial isometry** (algebraic form): `u * star u * u = u`. -/
def IsPartialIsometry {R : Type*} [Monoid R] [StarMul R] (u : R) : Prop :=
  u * star u * u = u

namespace IsPartialIsometry

variable {R : Type*} [Monoid R] [StarMul R]

/-- For a partial isometry, `star u * u` is a projection. Conway VI.3.2. -/
theorem isStarProjection_star_mul_self {u : R} (hu : IsPartialIsometry u) :
    IsStarProjection (star u * u) :=
  isStarProjection_iff'.mpr
    ⟨by rw [mul_assoc, ← mul_assoc u (star u) u, hu], by rw [star_mul, _root_.star_star]⟩

/-- `star u` is a partial isometry when `u` is. -/
theorem star_star {u : R} (hu : IsPartialIsometry u) : IsPartialIsometry (star u) := by
  unfold IsPartialIsometry
  rw [_root_.star_star]
  have h := congrArg star hu
  rwa [star_mul, star_mul, _root_.star_star, ← mul_assoc] at h

/-- A unitary element is a partial isometry (`star u * u = 1`). -/
theorem of_star_mul_self_eq_one {u : R} (h : star u * u = 1) : IsPartialIsometry u := by
  unfold IsPartialIsometry
  rw [mul_assoc, h, mul_one]

end IsPartialIsometry

section Operator

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-- **Operator characterization:** `u` is a partial isometry iff it is norm-preserving on the
orthogonal complement of its kernel. Conway VI.3.2. -/
theorem isPartialIsometry_iff_norm_map {u : E →ₗ[𝕜] E} :
    IsPartialIsometry u ↔ ∀ x ∈ (ker u)ᗮ, ‖u x‖ = ‖x‖ :=
  sorry

/-- The initial projection of a partial isometry is the orthogonal projection onto `(ker u)ᗮ`. -/
theorem IsPartialIsometry.star_mul_self_eq_starProjection {u : E →ₗ[𝕜] E}
    (hu : IsPartialIsometry u) :
    star u * u = ((ker u)ᗮ).starProjection.toLinearMap :=
  sorry

/-- **Constructor** used by the polar decomposition: a linear map that is isometric on a submodule
`K` and vanishes on `Kᗮ` is a partial isometry with initial space `K`. -/
theorem isPartialIsometry_of_isometryOn {u : E →ₗ[𝕜] E} {K : Submodule 𝕜 E}
    (hker : ker u = Kᗮ) (hiso : ∀ x ∈ K, ‖u x‖ = ‖x‖) :
    IsPartialIsometry u :=
  sorry

end Operator
