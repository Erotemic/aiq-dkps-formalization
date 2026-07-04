/-
Staged for Mathlib: additions to `Mathlib/Analysis/InnerProductSpace/Positive.lean`
(and a new `Mathlib/Analysis/InnerProductSpace/PositiveSqrt.lean`).

Sub-dev I of the operator polar decomposition project — COMPLETE (sorry-free, axiom-clean:
`propext, Classical.choice, Quot.sound`). Tickets PD-01..PD-04.
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
noncomputable def sqrt {T : E →ₗ[𝕜] E} (hT : T.IsPositive) : E →ₗ[𝕜] E :=
  ∑ i : Fin (Module.finrank 𝕜 E),
    (Real.sqrt (hT.isSymmetric.eigenvalues rfl i) : 𝕜) •
      (InnerProductSpace.rankOne 𝕜 (hT.isSymmetric.eigenvectorBasis rfl i)
        (hT.isSymmetric.eigenvectorBasis rfl i)).toLinearMap

/-- The square root is positive. HJ 7.2.6 (it is the PSD square root). -/
theorem sqrt_isPositive {T : E →ₗ[𝕜] E} (hT : T.IsPositive) :
    hT.sqrt.IsPositive := by
  unfold IsPositive.sqrt
  refine isPositive_sum _ fun i _ => ?_
  refine IsPositive.smul_of_nonneg ?_ (RCLike.ofReal_nonneg.mpr (Real.sqrt_nonneg _))
  exact (InnerProductSpace.isPositive_rankOne_self _).toLinearMap

/-- The square root is symmetric. -/
theorem sqrt_isSymmetric {T : E →ₗ[𝕜] E} (hT : T.IsPositive) :
    hT.sqrt.IsSymmetric :=
  hT.sqrt_isPositive.isSymmetric

/-- `sqrt T` acts on the `k`-th eigenvector as multiplication by `√λₖ` (it is diagonal in the same
eigenbasis as `T`). -/
theorem sqrt_apply_eigenvectorBasis {T : E →ₗ[𝕜] E} (hT : T.IsPositive)
    (k : Fin (Module.finrank 𝕜 E)) :
    hT.sqrt (hT.isSymmetric.eigenvectorBasis rfl k)
      = (Real.sqrt (hT.isSymmetric.eigenvalues rfl k) : 𝕜)
          • hT.isSymmetric.eigenvectorBasis rfl k := by
  classical
  unfold IsPositive.sqrt
  rw [LinearMap.sum_apply]
  refine (Finset.sum_eq_single k ?_ ?_).trans ?_
  · intro i _ hik
    simp [rankOne_apply,
      orthonormal_iff_ite.mp (hT.isSymmetric.eigenvectorBasis rfl).orthonormal i k, if_neg hik]
  · intro hk; exact absurd (Finset.mem_univ k) hk
  · simp [rankOne_apply]

/-- **Defining property:** `sqrt T` squares to `T`. HJ 7.2.6 (`B² = A`). -/
theorem sqrt_mul_self {T : E →ₗ[𝕜] E} (hT : T.IsPositive) :
    hT.sqrt ∘ₗ hT.sqrt = T := by
  apply (hT.isSymmetric.eigenvectorBasis rfl).toBasis.ext
  intro k
  have hnn := hT.nonneg_eigenvalues rfl k
  simp only [OrthonormalBasis.coe_toBasis, LinearMap.comp_apply, sqrt_apply_eigenvectorBasis,
    map_smul, smul_smul, hT.isSymmetric.apply_eigenvectorBasis]
  rw [← RCLike.ofReal_mul, Real.mul_self_sqrt hnn]

omit [FiniteDimensional 𝕜 E] in
/-- Pointwise root: if `S ≥ 0` and `S² v = μ² v` with `μ ≥ 0`, then `S v = μ v`. The crux of
uniqueness — `v` lies in the `μ²`-eigenspace of `S²`, on which the positive `S` acts as `μ`. -/
private theorem sq_root_pointwise {S : E →ₗ[𝕜] E} (hS : S.IsPositive) {v : E} {μ : ℝ}
    (hμ : 0 ≤ μ) (hv : S (S v) = ((μ : 𝕜) * (μ : 𝕜)) • v) :
    S v = (μ : 𝕜) • v := by
  rcases hμ.eq_or_lt with hμ0 | hμpos
  · -- μ = 0: `S² v = 0`, so `‖S v‖² = re⟪v, S² v⟫ = 0`.
    have hμz : (μ : 𝕜) = 0 := by rw [← hμ0]; simp
    rw [hμz, zero_smul]
    have hSSv : S (S v) = 0 := by rw [hv, hμz]; simp
    have h2 : ‖S v‖ ^ 2 = 0 := by
      rw [norm_sq_eq_re_inner (𝕜 := 𝕜), hS.isSymmetric v (S v), hSSv]; simp
    have : ‖S v‖ = 0 := by
      by_contra hne
      exact absurd h2 (ne_of_gt (pow_pos (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)) 2))
    exact norm_eq_zero.mp this
  · -- μ > 0: with `w = S v - μ v`, `(S + μ) w = S² v - μ² v = 0`, and `S ≥ 0` forces `w = 0`.
    set w := S v - (μ : 𝕜) • v with hwdef
    have hkey : S w + (μ : 𝕜) • w = 0 := by
      rw [hwdef, map_sub, map_smul, hv, smul_sub, smul_smul]; abel
    have hSw : S w = (-(μ : 𝕜)) • w := by
      rw [neg_smul, eq_neg_iff_add_eq_zero]; exact hkey
    have h1 := hS.re_inner_nonneg_left w
    rw [hSw, inner_smul_left, map_neg, RCLike.conj_ofReal, ← RCLike.ofReal_neg,
      RCLike.re_ofReal_mul, ← norm_sq_eq_re_inner] at h1
    have hw0 : w = 0 := by
      by_contra hne
      have hpos : 0 < ‖w‖ ^ 2 :=
        pow_pos (lt_of_le_of_ne (norm_nonneg _) (fun hq => hne (norm_eq_zero.mp hq.symm))) 2
      nlinarith [h1, hμpos, hpos]
    rw [hwdef, sub_eq_zero] at hw0
    exact hw0

/-- **Uniqueness:** any positive `S` with `S² = T` is `sqrt T`. HJ 7.2.6(a). -/
theorem sqrt_unique {T S : E →ₗ[𝕜] E} (hT : T.IsPositive) (hS : S.IsPositive)
    (h : S ∘ₗ S = T) : S = hT.sqrt := by
  apply (hT.isSymmetric.eigenvectorBasis rfl).toBasis.ext
  intro i
  rw [OrthonormalBasis.coe_toBasis, sqrt_apply_eigenvectorBasis]
  refine sq_root_pointwise hS (Real.sqrt_nonneg _) ?_
  rw [← LinearMap.comp_apply, h, hT.isSymmetric.apply_eigenvectorBasis,
    ← RCLike.ofReal_mul, Real.mul_self_sqrt (hT.nonneg_eigenvalues rfl i)]

/-- **The isometry-defect identity** `‖sqrt T x‖² = re ⟪T x, x⟫`. This is the seed of the polar
decomposition norm identity `‖A x‖ = ‖|A| x‖`. -/
theorem sq_norm_sqrt_apply {T : E →ₗ[𝕜] E} (hT : T.IsPositive) (x : E) :
    ‖hT.sqrt x‖ ^ 2 = RCLike.re ⟪T x, x⟫_𝕜 := by
  have hss : hT.sqrt (hT.sqrt x) = T x := by
    rw [← LinearMap.comp_apply, sqrt_mul_self]
  rw [norm_sq_eq_re_inner (𝕜 := 𝕜), hT.sqrt_isSymmetric x (hT.sqrt x), hss,
    ← hT.isSymmetric x x]

/-- `ker (sqrt T) = ker T`. HJ 7.2.7(b) applied through `sqrt T ∘ₗ sqrt T = T`. -/
theorem ker_sqrt {T : E →ₗ[𝕜] E} (hT : T.IsPositive) :
    ker hT.sqrt = ker T := by
  have h := LinearMap.ker_adjoint_comp_self hT.sqrt
  rw [hT.sqrt_isPositive.adjoint_eq, hT.sqrt_mul_self] at h
  exact h.symm

/-- `range (sqrt T) = range T`. HJ 7.2.6(c). -/
theorem range_sqrt {T : E →ₗ[𝕜] E} (hT : T.IsPositive) :
    range hT.sqrt = range T := by
  have hs : (ker hT.sqrt)ᗮ = range hT.sqrt := by
    rw [LinearMap.orthogonal_ker, hT.sqrt_isPositive.adjoint_eq]
  have hTr : (ker T)ᗮ = range T := by
    rw [LinearMap.orthogonal_ker, hT.adjoint_eq]
  rw [← hs, ← hTr, ker_sqrt hT]

/-- On the invertible (strictly positive) case, `sqrt T` is invertible; this provides the inverse
square root used by the intertwining unitary. -/
theorem isUnit_sqrt_of_isUnit {T : E →ₗ[𝕜] E} (hT : T.IsPositive)
    (hunit : IsUnit T) : IsUnit hT.sqrt := by
  rw [LinearMap.isUnit_iff_ker_eq_bot] at hunit ⊢
  rwa [ker_sqrt hT]

end LinearMap.IsPositive
