/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 4.8
-/
import ForMathlib.Analysis.InnerProductSpace.DavisKahanExt.SinTheta

/-!
# Complex spectral layer for the infinite-dimensional Davis--Kahan theory

The dimension-free residual, projection, coercive-Sylvester, and one-sided
`sin Θ` core is stated for arbitrary `RCLike` scalars.  The genuine *spectral*
hypotheses (a real bound on `spectrum ℝ T`) require the C\*-algebra order theory,
which at the pinned mathlib revision is available for **complex** operator
algebras only (`E →L[ℂ] E` carries the `CStarAlgebra`/`StarOrderedRing`
instances; the real operator-algebra CFC is not yet provided).  This module
therefore restricts to complex Hilbert spaces.

The two bridges below convert a real spectral bound into an operator quadratic
form bound via the spectral order
`spectrum ℝ T ⊆ (-∞, c] ⟹ T ≤ c • 1 ⟹ 0 ≤ c • 1 - T`, using
`le_algebraMap_of_spectrum_le` and `ContinuousLinearMap.nonneg_iff_isPositive`.
This is the infinite-dimensional analogue of the finite-dimensional
eigenbasis bridge in `DavisKahanTheory.Basic`, and it needs no
numerical-range / convex-hull-of-spectrum theorem.
-/

namespace ForMathlib
namespace DavisKahanExt

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Spectral upper bound ⟹ quadratic-form upper bound.**  If the real spectrum
of a self-adjoint `T` lies in `(-∞, c]`, then `re ⟪T x, x⟫ ≤ c ‖x‖²`.  Via the
C\*-order: `spectrum ℝ T ⊆ Iic c ⟹ T ≤ c • 1 ⟹ c • 1 - T ≥ 0`. -/
theorem re_inner_le_of_spectrum_subset_Iic
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) {c : ℝ}
    (hσ : spectrum ℝ T ⊆ Set.Iic c) (x : H) :
    RCLike.re ⟪T x, x⟫_ℂ ≤ c * ‖x‖ ^ 2 := by
  have hle : T ≤ algebraMap ℝ (H →L[ℂ] H) c :=
    le_algebraMap_of_spectrum_le (fun r hr => hσ hr) hT
  have hpos : (algebraMap ℝ (H →L[ℂ] H) c - T).IsPositive := by
    rw [← ContinuousLinearMap.nonneg_iff_isPositive]; exact sub_nonneg.mpr hle
  have hx := hpos.re_inner_nonneg_left x
  have hcx : RCLike.re ⟪c • x, x⟫_ℂ = c * ‖x‖ ^ 2 := by
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_left, RCLike.conj_ofReal,
      RCLike.re_ofReal_mul, inner_self_eq_norm_sq]
  simp only [ContinuousLinearMap.sub_apply, Algebra.algebraMap_eq_smul_one,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply,
    inner_sub_left, map_sub] at hx
  rw [hcx] at hx
  linarith

/-- **Spectral lower bound ⟹ quadratic-form lower bound.**  If the real spectrum
of a self-adjoint `T` lies in `[c, ∞)`, then `c ‖x‖² ≤ re ⟪T x, x⟫`. -/
theorem le_re_inner_of_Ici_subset_spectrum
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) {c : ℝ}
    (hσ : spectrum ℝ T ⊆ Set.Ici c) (x : H) :
    c * ‖x‖ ^ 2 ≤ RCLike.re ⟪T x, x⟫_ℂ := by
  have hle : algebraMap ℝ (H →L[ℂ] H) c ≤ T :=
    algebraMap_le_of_le_spectrum (fun r hr => hσ hr) hT
  have hpos : (T - algebraMap ℝ (H →L[ℂ] H) c).IsPositive := by
    rw [← ContinuousLinearMap.nonneg_iff_isPositive]; exact sub_nonneg.mpr hle
  have hx := hpos.re_inner_nonneg_left x
  have hcx : RCLike.re ⟪c • x, x⟫_ℂ = c * ‖x‖ ^ 2 := by
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_left, RCLike.conj_ofReal,
      RCLike.re_ofReal_mul, inner_self_eq_norm_sq]
  simp only [ContinuousLinearMap.sub_apply, Algebra.algebraMap_eq_smul_one,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply,
    inner_sub_left, map_sub] at hx
  rw [hcx] at hx
  linarith

/-! ### The sharp projector-difference norm identity

`‖P − Q‖ = max(‖(1−Q)P‖, ‖(1−P)Q‖)` for orthogonal projections, via the block
decomposition `(P−Q)² = P(1−Q)P + (1−P)Q(1−P)` and the C\*-norm identities.  This
is the two-projection fact that upgrades two one-sided `sin Θ` estimates to the
*sharp* (factor-one) projector-difference bound, without any equal-rank
hypothesis.  Complex-only (uses the `CStarRing`/`star` structure). -/

theorem norm_add_eq_max_of_block {P A B : H →L[ℂ] H}
    (hPsa : IsSelfAdjoint P) (hPid : IsIdempotentElem P)
    (hPnorm : ∀ x, ‖P x‖ ≤ ‖x‖) (hcompnorm : ∀ x, ‖(1 - P) x‖ ≤ ‖x‖)
    (hAP : A * P = A) (hPA : P * A = A) (hBP : B * P = 0) (hPB : P * B = 0) :
    ‖A + B‖ = max ‖A‖ ‖B‖ := by
  have hPsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hPsa
  have hPsymC : ∀ x y, ⟪P x, y⟫_ℂ = ⟪x, P y⟫_ℂ := fun x y => hPsym x y
  have app : ∀ (f g : H →L[ℂ] H) (x : H), (f * g) x = f (g x) := fun _ _ _ => rfl
  have hAppx : ∀ x, A (P x) = A x := fun x => by rw [← app]; exact congrFun (congrArg DFunLike.coe hAP) x
  have hPArange : ∀ x, P (A x) = A x := fun x => by rw [← app]; exact congrFun (congrArg DFunLike.coe hPA) x
  have hPBker : ∀ x, P (B x) = 0 := fun x => by
    rw [← app]; have h := congrFun (congrArg DFunLike.coe hPB) x; simpa using h
  have hBPx : ∀ x, B (P x) = 0 := fun x => by
    rw [← app]; have h := congrFun (congrArg DFunLike.coe hBP) x; simpa using h
  have hBcpx : ∀ x, B ((1 - P) x) = B x := fun x => by
    have hb : B * (1 - P) = B := by rw [mul_sub, mul_one, hBP, sub_zero]
    rw [← app]; exact congrFun (congrArg DFunLike.coe hb) x
  have hPcx : ∀ x, P ((1 - P) x) = 0 := fun x => by
    have h0 : P * (1 - P) = 0 := by rw [mul_sub, mul_one, hPid, sub_self]
    rw [← app]; have h := congrFun (congrArg DFunLike.coe h0) x; simpa using h
  have hApx : ∀ x, A ((1 - P) x) = 0 := fun x => by
    have h0 : A * (1 - P) = 0 := by rw [mul_sub, mul_one, hAP, sub_self]
    rw [← app]; have h := congrFun (congrArg DFunLike.coe h0) x; simpa using h
  have hpyth : ∀ x, ‖P x‖ ^ 2 + ‖(1 - P) x‖ ^ 2 = ‖x‖ ^ 2 := fun x => by
    have horth : ⟪P x, (1 - P) x⟫_ℂ = 0 := by rw [hPsymC x ((1 - P) x), hPcx, inner_zero_right]
    have h := norm_add_sq (𝕜 := ℂ) (P x) ((1 - P) x)
    rw [show P x + (1 - P) x = x by
      rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]; abel] at h
    simp only [horth, map_zero, mul_zero, add_zero, zero_add] at h
    linarith
  refine le_antisymm ?_ ?_
  · refine ContinuousLinearMap.opNorm_le_bound _ (le_max_of_le_left (norm_nonneg _)) fun x => ?_
    have horthAB : ⟪A x, B x⟫_ℂ = 0 := by
      rw [← hPArange x, hPsymC (A x) (B x), hPBker, inner_zero_right]
    have hnormsq : ‖(A + B) x‖ ^ 2 = ‖A x‖ ^ 2 + ‖B x‖ ^ 2 := by
      have h := norm_add_sq (𝕜 := ℂ) (A x) (B x)
      simp only [horthAB, map_zero, mul_zero, add_zero, zero_add] at h
      simp only [ContinuousLinearMap.add_apply]; linarith
    have hAxle : ‖A x‖ ≤ max ‖A‖ ‖B‖ * ‖P x‖ := by
      rw [← hAppx x]; exact (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr; exact le_max_left _ _)
    have hBxle : ‖B x‖ ≤ max ‖A‖ ‖B‖ * ‖(1 - P) x‖ := by
      rw [← hBcpx x]; exact (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr; exact le_max_right _ _)
    have hM : (0:ℝ) ≤ max ‖A‖ ‖B‖ := le_max_of_le_left (norm_nonneg _)
    have hkey : ‖(A + B) x‖ ^ 2 ≤ (max ‖A‖ ‖B‖ * ‖x‖) ^ 2 := by
      have e : (max ‖A‖ ‖B‖ * ‖x‖) ^ 2
          = (max ‖A‖ ‖B‖)^2 * ‖P x‖^2 + (max ‖A‖ ‖B‖)^2 * ‖(1 - P) x‖^2 := by
        rw [mul_pow, ← hpyth x]; ring
      rw [hnormsq, e]
      gcongr
      · nlinarith [hAxle, norm_nonneg (A x), norm_nonneg (P x), hM]
      · nlinarith [hBxle, norm_nonneg (B x), norm_nonneg ((1 - P) x), hM]
    have hnn : (0:ℝ) ≤ max ‖A‖ ‖B‖ * ‖x‖ := mul_nonneg hM (norm_nonneg x)
    calc ‖(A + B) x‖ = Real.sqrt (‖(A + B) x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt ((max ‖A‖ ‖B‖ * ‖x‖) ^ 2) := Real.sqrt_le_sqrt hkey
      _ = max ‖A‖ ‖B‖ * ‖x‖ := Real.sqrt_sq hnn
  · refine max_le ?_ ?_
    · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
      have hval : A x = (A + B) (P x) := by
        rw [ContinuousLinearMap.add_apply, hBPx, add_zero, hAppx]
      rw [hval]; exact (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr; exact hPnorm x)
    · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
      have hval : B x = (A + B) ((1 - P) x) := by
        rw [ContinuousLinearMap.add_apply, hApx, zero_add, hBcpx]
      rw [hval]; exact (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr; exact hcompnorm x)

theorem norm_starProjection_sub_eq_max (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    ‖(U.starProjection - V.starProjection : H →L[ℂ] H)‖ =
      max ‖(1 - V.starProjection) ∘L U.starProjection‖
          ‖(1 - U.starProjection) ∘L V.starProjection‖ := by
  set P := U.starProjection with hPdef
  set Q := V.starProjection with hQdef
  have hPsa : IsSelfAdjoint P := isSelfAdjoint_starProjection U
  have hQsa : IsSelfAdjoint Q := isSelfAdjoint_starProjection V
  have hPid : P * P = P := U.isIdempotentElem_starProjection
  have hQid : Q * Q = Q := V.isIdempotentElem_starProjection
  have hPnorm : ∀ x, ‖P x‖ ≤ ‖x‖ := U.norm_starProjection_apply_le
  have hcompeq : (1 - P : H →L[ℂ] H) = Uᗮ.starProjection := by
    rw [hPdef]; exact (Submodule.starProjection_orthogonal' U).symm
  have hcompnorm : ∀ x, ‖(1 - P) x‖ ≤ ‖x‖ := fun x => by
    rw [hcompeq]; exact Uᗮ.norm_starProjection_apply_le x
  set X : H →L[ℂ] H := (1 - Q) * P with hXdef
  set Y : H →L[ℂ] H := (1 - P) * Q with hYdef
  set A : H →L[ℂ] H := P * (1 - Q) * P with hAdef
  set B : H →L[ℂ] H := (1 - P) * Q * (1 - P) with hBdef
  have hQ1id : (1 - Q) * (1 - Q) = 1 - Q := by
    rw [mul_sub, mul_one, sub_mul, one_mul, hQid]; abel
  have hstarX : star X = P * (1 - Q) := by
    rw [hXdef, star_mul, hPsa.star_eq, star_sub, star_one, hQsa.star_eq]
  have hstarY : star Y = Q * (1 - P) := by
    rw [hYdef, star_mul, hQsa.star_eq, star_sub, star_one, hPsa.star_eq]
  have hnormA : ‖A‖ = ‖X‖ ^ 2 := by
    have h : star X * X = A := by
      rw [hstarX, hXdef, hAdef,
        show (P * (1 - Q)) * ((1 - Q) * P) = P * ((1 - Q) * (1 - Q)) * P by noncomm_ring, hQ1id]
    rw [← h, CStarRing.norm_star_mul_self, sq]
  have hnormB : ‖B‖ = ‖Y‖ ^ 2 := by
    have hQP : Q * Q = Q := hQid
    have h : Y * star Y = B := by
      rw [hstarY, hYdef, hBdef,
        show ((1 - P) * Q) * (Q * (1 - P)) = (1 - P) * (Q * Q) * (1 - P) by noncomm_ring, hQP]
    rw [← h, CStarRing.norm_self_mul_star, sq]
  have hAP : A * P = A := by rw [hAdef, mul_assoc, hPid]
  have hPA : P * A = A := by rw [hAdef, ← mul_assoc, ← mul_assoc, hPid]
  have hBP : B * P = 0 := by
    rw [hBdef, mul_assoc, show (1 - P) * P = 0 by rw [sub_mul, one_mul, hPid, sub_self], mul_zero]
  have hPB : P * B = 0 := by
    rw [hBdef, ← mul_assoc, ← mul_assoc,
      show P * (1 - P) = 0 by rw [mul_sub, mul_one, hPid, sub_self], zero_mul, zero_mul]
  have hA' : A = P - P * Q * P := by rw [hAdef, mul_sub, mul_one, sub_mul, hPid]
  have hB' : B = Q - Q * P - P * Q + P * Q * P := by
    rw [hBdef, sub_mul, one_mul, sub_mul, mul_sub, mul_one, mul_sub, mul_one]; abel
  have hPQsq : (P - Q) * (P - Q) = A + B := by
    have lhs : (P - Q) * (P - Q) = P + Q - P * Q - Q * P := by
      rw [sub_mul, mul_sub, mul_sub, hPid, hQid]; abel
    rw [lhs, hA', hB']; abel
  have hnormPQ : ‖(P - Q) * (P - Q)‖ = ‖P - Q‖ ^ 2 := by
    rw [show (P - Q) * (P - Q) = star (P - Q) * (P - Q) by rw [(hPsa.sub hQsa).star_eq],
      CStarRing.norm_star_mul_self, sq]
  have hblock : ‖A + B‖ = max ‖A‖ ‖B‖ :=
    norm_add_eq_max_of_block hPsa hPid hPnorm hcompnorm hAP hPA hBP hPB
  have hsq : ‖(P - Q : H →L[ℂ] H)‖ ^ 2 = (max ‖X‖ ‖Y‖) ^ 2 := by
    rw [← hnormPQ, hPQsq, hblock, hnormA, hnormB]
    rcases le_total ‖X‖ ‖Y‖ with h | h
    · rw [max_eq_right h, max_eq_right (by gcongr)]
    · rw [max_eq_left h, max_eq_left (by gcongr)]
  have hfin : ‖(P - Q : H →L[ℂ] H)‖ = max ‖X‖ ‖Y‖ := by
    have h2 : (0:ℝ) ≤ max ‖X‖ ‖Y‖ := le_max_of_le_left (norm_nonneg _)
    nlinarith [hsq, norm_nonneg (P - Q : H →L[ℂ] H), h2,
      sq_nonneg (‖(P - Q : H →L[ℂ] H)‖ - max ‖X‖ ‖Y‖)]
  rw [hfin]
  rfl

end DavisKahanExt
end ForMathlib
