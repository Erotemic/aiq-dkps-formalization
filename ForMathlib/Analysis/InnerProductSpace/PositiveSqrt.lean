/-
Staged for Mathlib: additions to `Mathlib/Analysis/InnerProductSpace/Positive.lean`
(and a new `Mathlib/Analysis/InnerProductSpace/PositiveSqrt.lean`).

SKELETON (`/develop` Phase 1e Step 2.5): every declaration is stated with `sorry`.
`lake build` must pass (sorries are warnings). Bodies are filled by `/beastmode` tickets.
-/

import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! # The positive square root of a positive symmetric operator (Sub-dev I)

For a positive symmetric operator `T` on a finite-dimensional inner product space over
`𝕜 : RCLike`, we build the unique positive symmetric operator `sqrt T` with `sqrt T ∘ₗ sqrt T = T`,
via the spectral theorem (`sqrt T := ∑ᵢ √λᵢ • rankOne eᵢ eᵢ`).

Source: Horn & Johnson, *Matrix Analysis*, 2nd ed. (2013), **Theorem 7.2.6** (unique positive
semidefinite square root) and **Theorem 7.2.7(b)** (`ker (A⋆A) = ker A`).

This is the `𝕜`-generic (ℝ and ℂ) `LinearMap` counterpart of mathlib's ℂ-only `CFC.sqrt`/`CFC.abs`
on `E →L[ℂ] E`; the RCLike operator route needs it because the C⋆-algebra/CFC instances on
`E →L[𝕜] E` are registered only for `𝕜 = ℂ`.
-/

open scoped InnerProductSpace
open InnerProductSpace

namespace LinearMap.IsPositive

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- **Spectral positive square root** of a positive symmetric operator `T`:
`sqrt T = ∑ᵢ √λᵢ • (rank-one projection onto the `i`-th eigenvector)`, where `λᵢ ≥ 0` are the
eigenvalues of `T`. Source: Horn–Johnson Thm 7.2.6. -/
noncomputable def sqrt {T : E →ₗ[𝕜] E} (_hT : T.IsPositive) : E →ₗ[𝕜] E :=
  sorry

/-- The square root is positive. HJ 7.2.6 (it is the PSD square root). -/
theorem sqrt_isPositive {T : E →ₗ[𝕜] E} (hT : T.IsPositive) :
    hT.sqrt.IsPositive :=
  sorry

/-- The square root is symmetric. -/
theorem sqrt_isSymmetric {T : E →ₗ[𝕜] E} (hT : T.IsPositive) :
    hT.sqrt.IsSymmetric :=
  hT.sqrt_isPositive.isSymmetric

/-- **Defining property:** `sqrt T` squares to `T`. HJ 7.2.6 (`B² = A`). -/
theorem sqrt_mul_self {T : E →ₗ[𝕜] E} (hT : T.IsPositive) :
    hT.sqrt ∘ₗ hT.sqrt = T :=
  sorry

/-- **Uniqueness:** any positive `S` with `S² = T` is `sqrt T`. HJ 7.2.6(a). -/
theorem sqrt_unique {T S : E →ₗ[𝕜] E} (hT : T.IsPositive) (hS : S.IsPositive)
    (h : S ∘ₗ S = T) : S = hT.sqrt :=
  sorry

/-- **The isometry-defect identity** `‖sqrt T x‖² = re ⟪T x, x⟫`. This is the seed of the polar
decomposition norm identity `‖A x‖ = ‖|A| x‖`. -/
theorem sq_norm_sqrt_apply {T : E →ₗ[𝕜] E} (hT : T.IsPositive) (x : E) :
    ‖hT.sqrt x‖ ^ 2 = RCLike.re ⟪T x, x⟫_𝕜 :=
  sorry

/-- `ker (sqrt T) = ker T`. HJ 7.2.7(b) applied through `sqrt T ∘ₗ sqrt T = T`. -/
theorem ker_sqrt {T : E →ₗ[𝕜] E} (hT : T.IsPositive) :
    ker hT.sqrt = ker T :=
  sorry

/-- `range (sqrt T) = range T`. HJ 7.2.6(c). -/
theorem range_sqrt {T : E →ₗ[𝕜] E} (hT : T.IsPositive) :
    range hT.sqrt = range T :=
  sorry

/-- On the invertible (strictly positive) case, `sqrt T` is invertible; this provides the inverse
square root used by the intertwining unitary. -/
theorem isUnit_sqrt_of_isUnit {T : E →ₗ[𝕜] E} (hT : T.IsPositive)
    (hunit : IsUnit T) : IsUnit hT.sqrt :=
  sorry

end LinearMap.IsPositive
