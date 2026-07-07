/-
Staged for Mathlib: additions to `Mathlib/Analysis/InnerProductSpace/SylvesterBound.lean`
(new file).

Formalized by Claude Fable 5 (claude-fable-5[1m]), plan step W5.1 of
`dev/davis-kahan-gap-closure-plan.md` (v3 reroute).  The classical proofs of
this bound run through an operator-valued integral `∫₀^∞ e^{−tA} Y e^{−tB} dt`
(Bhatia VII.2) or a contour integral (Sylvester–Rosenblum); the proof here is
a purely algebraic absorption argument discovered while planning: writing
`(a + b) • X = Y + (a • 1 − A) X + X (b • 1 − B)` with `a = ‖A‖`, `b = ‖B‖`
and bounding the two correction terms by `(a − δ)‖X‖` and `(b − δ)‖X‖` lets
the operator norm of `X` be solved for directly.  No integrals, no spectral
theorem, no finite-dimensionality, no completeness.
To be re-authored per Mathlib's AI-contribution policy at PR time.
-/

import Mathlib.Analysis.InnerProductSpace.Rayleigh

/-! # An operator-norm bound for the Sylvester equation

For bounded symmetric operators `A` on `E` and `B` on `F` over `𝕜 = ℝ, ℂ`,
and operators `X, Y : F →L[𝕜] E`, this file bounds the solution `X` of the
Sylvester-type equations

* `A ∘L X + X ∘L B = Y` with `A, B` both `δ`-coercive:  `‖X‖ ≤ ‖Y‖ / (2δ)`;
* `A ∘L X - X ∘L B = Y` with the quadratic forms of `A` and `B` separated by
  a gap `g` (that of `A` at least `c + g`, that of `B` at most `c`):
  `‖X‖ ≤ ‖Y‖ / g`.

The separated form is the estimate behind the operator-norm Davis–Kahan
`sin Θ` theorem: there `A` and `B` are compressions of two symmetric
operators to spectral subspaces whose eigenvalue blocks are separated by `g`,
`X` is the compressed cross-projection, and `Y` is a compression of the
perturbation.

The proof is elementary and integral-free.  From the equation,
`((‖A‖ + ‖B‖ : ℝ) : 𝕜) • X = Y + ((‖A‖ : 𝕜) • 1 - A) ∘L X + X ∘L ((‖B‖ : 𝕜) • 1 - B)`,
and the two correction operators have norm at most `‖A‖ - δ` and `‖B‖ - δ`
because a symmetric operator whose quadratic form lies in `[0, κ‖·‖²]` has
norm at most `κ` (via `ContinuousLinearMap.norm_eq_iSup_rayleighQuotient`).
Taking norms and absorbing the two correction terms leaves `2δ‖X‖ ≤ ‖Y‖`.

Neither completeness nor finite-dimensionality is assumed, so the results
apply to bounded symmetric operators on any inner product space; symmetry is
taken in the `LinearMap.IsSymmetric` sense, with no reference to adjoints.

## Main results

* `ForMathlib.ContinuousLinearMap.norm_le_of_abs_re_inner_map_self_le`: a
  symmetric operator with `|re ⟪C x, x⟫| ≤ κ * ‖x‖ ^ 2` has `‖C‖ ≤ κ`.
* `ForMathlib.ContinuousLinearMap.opNorm_le_div_of_comp_add_comp_eq`: the
  coercive (Lyapunov) form, `‖X‖ ≤ ‖Y‖ / (2 * δ)`.
* `ForMathlib.ContinuousLinearMap.opNorm_le_div_of_comp_sub_comp_eq`: the
  separated (Davis–Kahan-facing) form, `‖X‖ ≤ ‖Y‖ / g`.

## References

* R. Bhatia, *Matrix Analysis*, Chapter VII.2 (the Sylvester equation and the
  Davis–Kahan theorems); the bound proved here is the half-line-separation
  case of Theorem VII.2.3, by a different, integral-free proof.
* C. Davis and W. M. Kahan, *The rotation of eigenvectors by a
  perturbation. III*, SIAM J. Numer. Anal. 7 (1970), 1–46.
-/

namespace ForMathlib

open scoped InnerProductSpace

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

namespace ContinuousLinearMap

/-- A symmetric operator whose quadratic form is bounded by `κ * ‖x‖ ^ 2` in
absolute value has operator norm at most `κ`.  Quantitative counterpart of
`ContinuousLinearMap.norm_eq_iSup_rayleighQuotient`. -/
theorem norm_le_of_abs_re_inner_map_self_le {C : E →L[𝕜] E} (hC : C.IsSymmetric)
    {κ : ℝ} (hκ : 0 ≤ κ) (h : ∀ x, |RCLike.re ⟪C x, x⟫_𝕜| ≤ κ * ‖x‖ ^ 2) : ‖C‖ ≤ κ := by
  rw [C.norm_eq_iSup_rayleighQuotient hC]
  refine ciSup_le fun x => ?_
  show |C.reApplyInnerSelf x / ‖x‖ ^ 2| ≤ κ
  rcases eq_or_ne x 0 with rfl | hx
  · simpa [ContinuousLinearMap.reApplyInnerSelf_apply] using hκ
  · rw [ContinuousLinearMap.reApplyInnerSelf_apply, abs_div, abs_sq,
      div_le_iff₀ (by positivity)]
    exact h x

section SylvesterBound

variable {A : E →L[𝕜] E} {B : F →L[𝕜] F} {X Y : F →L[𝕜] E}

/-- The quadratic form of the real shift `(r : 𝕜) • 1 - A`.  Auxiliary. -/
private theorem re_inner_ofReal_smul_one_sub_apply_self (A : E →L[𝕜] E) (r : ℝ) (x : E) :
    RCLike.re ⟪((r : 𝕜) • (1 : E →L[𝕜] E) - A) x, x⟫_𝕜
      = r * ‖x‖ ^ 2 - RCLike.re ⟪A x, x⟫_𝕜 := by
  simp only [sub_apply, smul_apply,
    one_apply_eq_self, inner_sub_left, inner_smul_left, RCLike.conj_ofReal,
    map_sub, RCLike.re_ofReal_mul, inner_self_eq_norm_sq]

/-- The real shift `(r : 𝕜) • 1 - A` of a symmetric operator is symmetric.
Auxiliary. -/
private theorem isSymmetric_ofReal_smul_one_sub (hA : A.IsSymmetric) (r : ℝ) :
    (((r : 𝕜) • (1 : E →L[𝕜] E) - A)).IsSymmetric := fun x y => by
  simp only [ContinuousLinearMap.coe_coe, sub_apply,
    smul_apply, one_apply_eq_self, inner_sub_left,
    inner_sub_right, inner_smul_left, inner_smul_right, RCLike.conj_ofReal]
  congr 1
  exact hA x y

/-- Coercivity forces the norm from below: if `δ * ‖x‖ ^ 2 ≤ re ⟪A x, x⟫` and
some vector is nonzero, then `δ ≤ ‖A‖`.  Auxiliary. -/
private theorem le_opNorm_of_le_re_inner_map_self {δ : ℝ}
    (hAc : ∀ x, δ * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜) {x₀ : E} (hx₀ : x₀ ≠ 0) : δ ≤ ‖A‖ := by
  have hupper : RCLike.re ⟪A x₀, x₀⟫_𝕜 ≤ ‖A‖ * ‖x₀‖ ^ 2 :=
    calc RCLike.re ⟪A x₀, x₀⟫_𝕜 ≤ ‖⟪A x₀, x₀⟫_𝕜‖ := RCLike.re_le_norm _
      _ ≤ ‖A x₀‖ * ‖x₀‖ := norm_inner_le_norm _ _
      _ ≤ ‖A‖ * ‖x₀‖ * ‖x₀‖ := by gcongr; exact A.le_opNorm x₀
      _ = ‖A‖ * ‖x₀‖ ^ 2 := by ring
  have hx₀2 : (0 : ℝ) < ‖x₀‖ ^ 2 := by positivity
  nlinarith [hAc x₀]

/-- The correction term in the absorption identity is small: if the quadratic
form of `A` is at least `δ * ‖·‖ ^ 2`, then `(‖A‖ : 𝕜) • w - A w` has norm at
most `(‖A‖ - δ) * ‖w‖`.  Auxiliary for the Sylvester bound. -/
private theorem norm_opNorm_smul_sub_apply_le (hA : A.IsSymmetric) {δ : ℝ} (hδA : δ ≤ ‖A‖)
    (hAc : ∀ x, δ * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜) (w : E) :
    ‖(‖A‖ : 𝕜) • w - A w‖ ≤ (‖A‖ - δ) * ‖w‖ := by
  have happly : ((‖A‖ : 𝕜) • (1 : E →L[𝕜] E) - A) w = (‖A‖ : 𝕜) • w - A w := rfl
  have hnorm : ‖(‖A‖ : 𝕜) • (1 : E →L[𝕜] E) - A‖ ≤ ‖A‖ - δ := by
    refine norm_le_of_abs_re_inner_map_self_le (isSymmetric_ofReal_smul_one_sub hA ‖A‖)
      (by linarith) fun x => ?_
    rw [re_inner_ofReal_smul_one_sub_apply_self]
    have hupper : RCLike.re ⟪A x, x⟫_𝕜 ≤ ‖A‖ * ‖x‖ ^ 2 :=
      calc RCLike.re ⟪A x, x⟫_𝕜 ≤ ‖⟪A x, x⟫_𝕜‖ := RCLike.re_le_norm _
        _ ≤ ‖A x‖ * ‖x‖ := norm_inner_le_norm _ _
        _ ≤ ‖A‖ * ‖x‖ * ‖x‖ := by gcongr; exact A.le_opNorm x
        _ = ‖A‖ * ‖x‖ ^ 2 := by ring
    rw [abs_of_nonneg (by linarith)]
    linarith [hAc x]
  calc ‖(‖A‖ : 𝕜) • w - A w‖ = ‖((‖A‖ : 𝕜) • (1 : E →L[𝕜] E) - A) w‖ := by rw [happly]
    _ ≤ ‖(‖A‖ : 𝕜) • (1 : E →L[𝕜] E) - A‖ * ‖w‖ := ContinuousLinearMap.le_opNorm _ w
    _ ≤ (‖A‖ - δ) * ‖w‖ := by gcongr

/-- **Operator-norm bound for the Sylvester equation, coercive (Lyapunov)
form.**  If `A` and `B` are symmetric with quadratic forms at least
`δ * ‖·‖ ^ 2`, and `A ∘L X + X ∘L B = Y`, then `‖X‖ ≤ ‖Y‖ / (2 * δ)`.

The proof is integral-free: from the equation,
`((‖A‖ + ‖B‖ : ℝ) : 𝕜) • X = Y + ((‖A‖ : 𝕜) • 1 - A) ∘L X + X ∘L ((‖B‖ : 𝕜) • 1 - B)`,
the two correction operators have norms at most `‖A‖ - δ` and `‖B‖ - δ`, and
taking norms lets `‖X‖` be solved for. -/
theorem opNorm_le_div_of_comp_add_comp_eq (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {δ : ℝ} (hδ : 0 < δ)
    (hAc : ∀ x, δ * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜)
    (hBc : ∀ v, δ * ‖v‖ ^ 2 ≤ RCLike.re ⟪B v, v⟫_𝕜)
    (hXY : A ∘L X + X ∘L B = Y) : ‖X‖ ≤ ‖Y‖ / (2 * δ) := by
  rcases eq_or_ne X 0 with rfl | hX
  · simp only [norm_zero]
    positivity
  -- `X ≠ 0` puts nonzero vectors in both spaces, so coercivity gives `δ ≤ ‖A‖, ‖B‖`.
  obtain ⟨v₀, hv₀⟩ := DFunLike.ne_iff.mp hX
  simp only [zero_apply] at hv₀
  have hδA : δ ≤ ‖A‖ := le_opNorm_of_le_re_inner_map_self hAc hv₀
  have hδB : δ ≤ ‖B‖ :=
    le_opNorm_of_le_re_inner_map_self hBc (x₀ := v₀) fun h => hv₀ (by rw [h]; exact map_zero X)
  -- The absorption identity, applied to a vector.
  have key : ∀ v, ((‖A‖ + ‖B‖ : ℝ) : 𝕜) • X v
      = Y v + ((‖A‖ : 𝕜) • X v - A (X v)) + ((‖B‖ : 𝕜) • X v - X (B v)) := by
    intro v
    have hv : A (X v) + X (B v) = Y v := by
      simpa [add_apply, ContinuousLinearMap.comp_apply] using
        congrArg (fun W : F →L[𝕜] E => W v) hXY
    rw [← hv]
    push_cast
    module
  -- Take norms and absorb the two correction terms.
  have hbound : ∀ v, (‖B‖ + δ) * ‖X v‖ ≤ (‖Y‖ + (‖B‖ - δ) * ‖X‖) * ‖v‖ := by
    intro v
    have hXBv : ‖(‖B‖ : 𝕜) • X v - X (B v)‖ ≤ ‖X‖ * ((‖B‖ - δ) * ‖v‖) := by
      have hmap : (‖B‖ : 𝕜) • X v - X (B v) = X ((‖B‖ : 𝕜) • v - B v) := by
        rw [map_sub, map_smul]
      rw [hmap]
      exact (X.le_opNorm _).trans <| by
        gcongr
        exact norm_opNorm_smul_sub_apply_le hB hδB hBc v
    have h1 : (‖A‖ + ‖B‖) * ‖X v‖
        ≤ ‖Y‖ * ‖v‖ + (‖A‖ - δ) * ‖X v‖ + ‖X‖ * ((‖B‖ - δ) * ‖v‖) :=
      calc (‖A‖ + ‖B‖) * ‖X v‖ = ‖((‖A‖ + ‖B‖ : ℝ) : 𝕜) • X v‖ := by
            rw [norm_smul, RCLike.norm_ofReal, abs_of_nonneg (by linarith)]
        _ = ‖Y v + ((‖A‖ : 𝕜) • X v - A (X v)) + ((‖B‖ : 𝕜) • X v - X (B v))‖ := by
            rw [key v]
        _ ≤ ‖Y v‖ + ‖(‖A‖ : 𝕜) • X v - A (X v)‖ + ‖(‖B‖ : 𝕜) • X v - X (B v)‖ :=
            norm_add₃_le
        _ ≤ ‖Y‖ * ‖v‖ + (‖A‖ - δ) * ‖X v‖ + ‖X‖ * ((‖B‖ - δ) * ‖v‖) := by
            gcongr
            · exact Y.le_opNorm v
            · exact norm_opNorm_smul_sub_apply_le hA hδA hAc (X v)
    linarith
  -- Solve the scalar inequality for `‖X‖`.
  have hXle : ‖X‖ ≤ (‖Y‖ + (‖B‖ - δ) * ‖X‖) / (‖B‖ + δ) := by
    refine X.opNorm_le_bound (by positivity) fun v => ?_
    rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
    calc ‖X v‖ * (‖B‖ + δ) = (‖B‖ + δ) * ‖X v‖ := mul_comm _ _
      _ ≤ (‖Y‖ + (‖B‖ - δ) * ‖X‖) * ‖v‖ := hbound v
  rw [le_div_iff₀ (by linarith)] at hXle
  rw [le_div_iff₀ (by positivity)]
  linarith

/-- **Operator-norm bound for the Sylvester equation, separated (Davis–Kahan)
form.**  If the quadratic form of the symmetric operator `A` is at least
`(c + g) * ‖·‖ ^ 2` while that of the symmetric operator `B` is at most
`c * ‖·‖ ^ 2`, and `A ∘L X - X ∘L B = Y`, then `‖X‖ ≤ ‖Y‖ / g`.

This is the estimate behind the operator-norm Davis–Kahan `sin Θ` theorem,
with `A, B` compressions to spectral subspaces whose eigenvalue blocks are
separated by the gap `g`. -/
theorem opNorm_le_div_of_comp_sub_comp_eq (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {c g : ℝ} (hg : 0 < g)
    (hAc : ∀ x, (c + g) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜)
    (hBc : ∀ v, RCLike.re ⟪B v, v⟫_𝕜 ≤ c * ‖v‖ ^ 2)
    (hXY : A ∘L X - X ∘L B = Y) : ‖X‖ ≤ ‖Y‖ / g := by
  -- Shift both operators to the midpoint `r = c + g/2` and apply the coercive
  -- form with `δ = g/2`.
  set r : ℝ := c + g / 2 with hr
  have hA' : (A - (r : 𝕜) • (1 : E →L[𝕜] E)).IsSymmetric := fun x y => by
    simp only [ContinuousLinearMap.coe_coe, sub_apply, smul_apply, one_apply_eq_self,
      inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, RCLike.conj_ofReal]
    congr 1
    exact hA x y
  have hB' : ((r : 𝕜) • (1 : F →L[𝕜] F) - B).IsSymmetric :=
    isSymmetric_ofReal_smul_one_sub hB r
  have hAc' : ∀ x, g / 2 * ‖x‖ ^ 2 ≤ RCLike.re ⟪(A - (r : 𝕜) • (1 : E →L[𝕜] E)) x, x⟫_𝕜 := by
    intro x
    have hneg : (A - (r : 𝕜) • (1 : E →L[𝕜] E)) x = -(((r : 𝕜) • (1 : E →L[𝕜] E) - A) x) := by
      simp [neg_sub]
    rw [hneg, inner_neg_left, map_neg, re_inner_ofReal_smul_one_sub_apply_self, hr]
    linarith [hAc x]
  have hBc' : ∀ v, g / 2 * ‖v‖ ^ 2 ≤ RCLike.re ⟪((r : 𝕜) • (1 : F →L[𝕜] F) - B) v, v⟫_𝕜 := by
    intro v
    rw [re_inner_ofReal_smul_one_sub_apply_self, hr]
    linarith [hBc v]
  have hXY' : (A - (r : 𝕜) • (1 : E →L[𝕜] E)) ∘L X + X ∘L ((r : 𝕜) • (1 : F →L[𝕜] F) - B) = Y := by
    ext v
    have hv : A (X v) - X (B v) = Y v := by
      simpa [sub_apply, ContinuousLinearMap.comp_apply] using
        congrArg (fun W : F →L[𝕜] E => W v) hXY
    simp only [add_apply, ContinuousLinearMap.comp_apply,
      sub_apply, smul_apply,
      one_apply_eq_self, map_sub, map_smul, ← hv]
    module
  have hfin := opNorm_le_div_of_comp_add_comp_eq hA' hB'
    (by linarith : (0 : ℝ) < g / 2) hAc' hBc' hXY'
  rwa [show 2 * (g / 2) = g by ring] at hfin

end SylvesterBound

end ContinuousLinearMap

end ForMathlib
