/-
Staged for Mathlib: additions to `Mathlib/Analysis/InnerProductSpace/` (new file
`SinThetaOpNorm.lean`).

Formalized by Claude Opus 4.8 (claude-opus-4-8[1m]), plan step W5.2 of
`dev/davis-kahan-gap-closure-plan.md`.

The dimension-free operator-norm Davis–Kahan sin-Θ theorem
`‖Q̂ ∘L P‖ ≤ ε / g`, where `P` projects onto a `T`-invariant subspace `U` whose
quadratic form is `≥ (c+g)‖·‖²` and `Q̂` onto an `S`-invariant subspace `V` whose
quadratic form is `≤ c‖·‖²`.  The operator norm `‖Q̂ ∘L P‖` *is* `‖sinΘ‖_op`.
Built on the Sylvester operator bound (`opNorm_le_div_of_comp_sub_comp_eq`)
without any dimension factor.
To be re-authored per Mathlib's AI-contribution policy at PR time.
-/

import ForMathlib.Analysis.InnerProductSpace.SylvesterBound
import ForMathlib.Analysis.InnerProductSpace.RotationSharp
import ForMathlib.Analysis.InnerProductSpace.CourantFischer
import ForMathlib.Analysis.InnerProductSpace.PrincipalAngles
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! # The operator-norm Davis–Kahan sin-Θ theorem

For symmetric `T, S` on a finite-dimensional inner product space, an invariant
subspace `U` of `T` on which the quadratic form of `T` sits above `c + g`, and
an invariant subspace `V` of `S` on which the form of `S` sits below `c`, the
sines of the principal angles between `U` and `V` are dimension-free bounded:
`‖V.starProjection ∘L U.starProjection‖ ≤ ‖S − T‖_op / g`.

The proof compresses nothing.  On the full space, set `X = P ∘L Q`
(`P = U.starProjection`, `Q = V.starProjection`), and build
`A = T P + (c+g)(1−P)` and `B = S Q + c(1−Q)`; because `U, Uᗮ` are `T`-invariant
and `V, Vᗮ` are `S`-invariant, `A` is globally `(c+g)`-coercive and `B` globally
bounded by `c`, and the block algebra gives the Sylvester relation
`A ∘L X − X ∘L B = P ∘L (T − S) ∘L Q`, whose right side has norm `≤ ε`.  The
Sylvester bound then yields `‖X‖ ≤ ε/g`, and `‖Q ∘L P‖ = ‖P ∘L Q‖` by
self-adjointness of the projections.

## Main results

* `ForMathlib.starProjection_comp_toContinuousLinearMap_comm`: an invariant
  subspace's projection commutes with a symmetric operator.
* `ForMathlib.norm_starProjection_comp_starProjection_le`: the operator-norm
  sin-Θ bound `‖Q̂ ∘L P‖ ≤ ε / g`.

## References

* R. Bhatia, *Matrix Analysis*, Chapter VII (the Davis–Kahan theorems).
* C. Davis and W. M. Kahan, *The rotation of eigenvectors by a
  perturbation. III*, SIAM J. Numer. Anal. 7 (1970), 1–46.
-/

namespace ForMathlib

open scoped InnerProductSpace
open Module (finrank)

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] [CompleteSpace E]

omit [FiniteDimensional 𝕜 E] [CompleteSpace E] in
/-- **A symmetric operator commutes with the projection onto an invariant
subspace.**  If `T` is symmetric and `U` is `T`-invariant (hence `Uᗮ` is too),
then `T (P x) = P (T x)` for `P = U.starProjection`. -/
theorem starProjection_comp_toContinuousLinearMap_comm {T : E →ₗ[𝕜] E}
    (hT : T.IsSymmetric) {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (hUinv : ∀ x ∈ U, T x ∈ U) (x : E) :
    T (U.starProjection x) = U.starProjection (T x) := by
  have hpx : U.starProjection x ∈ U := U.starProjection_apply_mem x
  have hrest : x - U.starProjection x ∈ Uᗮ := U.sub_starProjection_mem_orthogonal x
  have hTpx : T (U.starProjection x) ∈ U := hUinv _ hpx
  have hTrest : T (x - U.starProjection x) ∈ Uᗮ :=
    map_mem_orthogonal_of_forall_map_mem hT hUinv hrest
  have hsplit : T x = T (U.starProjection x) + T (x - U.starProjection x) := by
    rw [← map_add]; congr 1; abel
  have hzero : U.starProjection (T (x - U.starProjection x)) = 0 :=
    Submodule.eq_starProjection_of_mem_orthogonal (Submodule.zero_mem U) (by simpa using hTrest)
  rw [hsplit, map_add, U.starProjection_eq_self_iff.mpr hTpx, hzero, add_zero]

variable {T S : E →ₗ[𝕜] E}

/-- **The norm-free Davis–Kahan setup.**  From the two invariant subspaces and
their quadratic-form separation, builds the coercive `A` and the bounded `B`
whose separated Sylvester equation the cross-projection
`P ∘L Q = U.starProjection ∘L V.starProjection` solves, with residual
`Y = P ∘L (T − S) ∘L Q`.  This is the entire construction of the operator-norm
`sin Θ` theorem *before any norm is taken*, extracted so that both the
operator-norm bound and the unitarily-invariant-norm bound (`SinThetaUINorm`)
can finish it with their respective Sylvester estimates. -/
theorem exists_isSymmetric_comp_sub_comp_eq (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hUinv : ∀ x ∈ U, T x ∈ U) (hVinv : ∀ x ∈ V, S x ∈ V)
    {c g : ℝ}
    (hU : ∀ x ∈ U, (c + g) * ‖x‖ ^ 2 ≤ RCLike.re ⟪T x, x⟫_𝕜)
    (hV : ∀ x ∈ V, RCLike.re ⟪S x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2) :
    ∃ A B : E →L[𝕜] E, A.IsSymmetric ∧ B.IsSymmetric ∧
      (∀ x, (c + g) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜) ∧
      (∀ x, RCLike.re ⟪B x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2) ∧
      A ∘L (U.starProjection ∘L V.starProjection)
          - (U.starProjection ∘L V.starProjection) ∘L B
        = U.starProjection
            ∘L (LinearMap.toContinuousLinearMap T - LinearMap.toContinuousLinearMap S)
            ∘L V.starProjection := by
  set P := U.starProjection with hP
  set Q := V.starProjection with hQ
  set Tc := LinearMap.toContinuousLinearMap T with hTc
  set Sc := LinearMap.toContinuousLinearMap S with hSc
  set A : E →L[𝕜] E := Tc ∘L P + ((c + g : ℝ) : 𝕜) • (1 - P) with hA
  set B : E →L[𝕜] E := Sc ∘L Q + ((c : ℝ) : 𝕜) • (1 - Q) with hB
  set X : E →L[𝕜] E := P ∘L Q with hX
  set Y : E →L[𝕜] E := P ∘L (Tc - Sc) ∘L Q with hY
  -- Self-adjointness of the building blocks.
  have hPsa : IsSelfAdjoint P := isSelfAdjoint_starProjection U
  have hQsa : IsSelfAdjoint Q := isSelfAdjoint_starProjection V
  have hTcsa : IsSelfAdjoint Tc := by
    rw [hTc, ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric, LinearMap.coe_toContinuousLinearMap]
    exact hT
  have hScsa : IsSelfAdjoint Sc := by
    rw [hSc, ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric, LinearMap.coe_toContinuousLinearMap]
    exact hS
  have hcgsa : IsSelfAdjoint ((c + g : ℝ) : 𝕜) := isSelfAdjoint_iff.mpr (RCLike.conj_ofReal _)
  have hcsa : IsSelfAdjoint ((c : ℝ) : 𝕜) := isSelfAdjoint_iff.mpr (RCLike.conj_ofReal _)
  -- Commutations `T P = P T`, `S Q = Q S`.
  have hcommT : Tc ∘L P = P ∘L Tc := by
    ext x
    simp only [ContinuousLinearMap.comp_apply]
    exact starProjection_comp_toContinuousLinearMap_comm hT hUinv x
  have hcommS : Sc ∘L Q = Q ∘L Sc := by
    ext x
    simp only [ContinuousLinearMap.comp_apply]
    exact starProjection_comp_toContinuousLinearMap_comm hS hVinv x
  -- `A`, `B` symmetric.
  have hone : IsSelfAdjoint (1 : E →L[𝕜] E) := IsSelfAdjoint.one _
  have hAsa : IsSelfAdjoint A := by
    have h1 : IsSelfAdjoint (Tc ∘L P) := (IsSelfAdjoint.commute_iff hTcsa hPsa).mp hcommT
    have h2 : IsSelfAdjoint (((c + g : ℝ) : 𝕜) • ((1 : E →L[𝕜] E) - P)) := by
      rw [isSelfAdjoint_iff, star_smul, hcgsa.star_eq, (hone.sub hPsa).star_eq]
    exact hA ▸ h1.add h2
  have hBsa : IsSelfAdjoint B := by
    have h1 : IsSelfAdjoint (Sc ∘L Q) := (IsSelfAdjoint.commute_iff hScsa hQsa).mp hcommS
    have h2 : IsSelfAdjoint (((c : ℝ) : 𝕜) • ((1 : E →L[𝕜] E) - Q)) := by
      rw [isSelfAdjoint_iff, star_smul, hcsa.star_eq, (hone.sub hQsa).star_eq]
    exact hB ▸ h1.add h2
  have hAsym : A.IsSymmetric := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hAsa
  have hBsym : B.IsSymmetric := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hBsa
  -- Coercivity of `A`: `(c+g)‖x‖² ≤ re⟪A x, x⟫`.
  have hAc : ∀ x, (c + g) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜 := by
    intro x
    have hpx : P x ∈ U := U.starProjection_apply_mem x
    have hrest : x - P x ∈ Uᗮ := U.sub_starProjection_mem_orthogonal x
    have hAxeq : A x = T (P x) + ((c + g : ℝ) : 𝕜) • (x - P x) := by
      simp only [hA, hTc, add_apply, ContinuousLinearMap.comp_apply,
        LinearMap.coe_toContinuousLinearMap', smul_apply,
        sub_apply, one_apply_eq_self]
    have hre : RCLike.re ⟪A x, x⟫_𝕜
        = RCLike.re ⟪T (P x), x⟫_𝕜 + (c + g) * RCLike.re ⟪x - P x, x⟫_𝕜 := by
      rw [hAxeq, inner_add_left, inner_smul_left, RCLike.conj_ofReal, map_add,
        RCLike.re_ofReal_mul]
    have h1 : RCLike.re ⟪T (P x), x⟫_𝕜 = RCLike.re ⟪T (P x), P x⟫_𝕜 := by
      have hz : ⟪T (P x), x - P x⟫_𝕜 = 0 :=
        Submodule.inner_right_of_mem_orthogonal (hUinv _ hpx) hrest
      have : ⟪T (P x), x⟫_𝕜 = ⟪T (P x), P x⟫_𝕜 + ⟪T (P x), x - P x⟫_𝕜 := by
        rw [← inner_add_right]; congr 1; abel
      rw [this, hz, add_zero]
    have h2 : RCLike.re ⟪x - P x, x⟫_𝕜 = ‖x - P x‖ ^ 2 := by
      have hz : ⟪x - P x, P x⟫_𝕜 = 0 := Submodule.inner_left_of_mem_orthogonal hpx hrest
      have : ⟪x - P x, x⟫_𝕜 = ⟪x - P x, x - P x⟫_𝕜 := by
        have h' : ⟪x - P x, x⟫_𝕜 = ⟪x - P x, P x⟫_𝕜 + ⟪x - P x, x - P x⟫_𝕜 := by
          rw [← inner_add_right]; congr 1; abel
        rw [h', hz, zero_add]
      rw [this, inner_self_eq_norm_sq]
    have hpyth : ‖x‖ ^ 2 = ‖P x‖ ^ 2 + ‖x - P x‖ ^ 2 := by
      have h0 : RCLike.re ⟪P x, x - P x⟫_𝕜 = 0 := by
        rw [Submodule.inner_right_of_mem_orthogonal hpx hrest]; simp
      have hns := norm_add_sq (𝕜 := 𝕜) (P x) (x - P x)
      rw [show P x + (x - P x) = x by abel, h0] at hns
      linarith
    rw [hre, h1, h2, hpyth]
    have h1' := hU (P x) hpx
    nlinarith [h1']
  -- Upper bound for `B`: `re⟪B x, x⟫ ≤ c‖x‖²`.
  have hBc : ∀ x, RCLike.re ⟪B x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2 := by
    intro x
    have hqx : Q x ∈ V := V.starProjection_apply_mem x
    have hrest : x - Q x ∈ Vᗮ := V.sub_starProjection_mem_orthogonal x
    have hBxeq : B x = S (Q x) + ((c : ℝ) : 𝕜) • (x - Q x) := by
      simp only [hB, hSc, add_apply, ContinuousLinearMap.comp_apply,
        LinearMap.coe_toContinuousLinearMap', smul_apply,
        sub_apply, one_apply_eq_self]
    have hre : RCLike.re ⟪B x, x⟫_𝕜
        = RCLike.re ⟪S (Q x), x⟫_𝕜 + c * RCLike.re ⟪x - Q x, x⟫_𝕜 := by
      rw [hBxeq, inner_add_left, inner_smul_left, RCLike.conj_ofReal, map_add,
        RCLike.re_ofReal_mul]
    have h1 : RCLike.re ⟪S (Q x), x⟫_𝕜 = RCLike.re ⟪S (Q x), Q x⟫_𝕜 := by
      have hz : ⟪S (Q x), x - Q x⟫_𝕜 = 0 :=
        Submodule.inner_right_of_mem_orthogonal (hVinv _ hqx) hrest
      have : ⟪S (Q x), x⟫_𝕜 = ⟪S (Q x), Q x⟫_𝕜 + ⟪S (Q x), x - Q x⟫_𝕜 := by
        rw [← inner_add_right]; congr 1; abel
      rw [this, hz, add_zero]
    have h2 : RCLike.re ⟪x - Q x, x⟫_𝕜 = ‖x - Q x‖ ^ 2 := by
      have hz : ⟪x - Q x, Q x⟫_𝕜 = 0 := Submodule.inner_left_of_mem_orthogonal hqx hrest
      have : ⟪x - Q x, x⟫_𝕜 = ⟪x - Q x, x - Q x⟫_𝕜 := by
        have h' : ⟪x - Q x, x⟫_𝕜 = ⟪x - Q x, Q x⟫_𝕜 + ⟪x - Q x, x - Q x⟫_𝕜 := by
          rw [← inner_add_right]; congr 1; abel
        rw [h', hz, zero_add]
      rw [this, inner_self_eq_norm_sq]
    have hpyth : ‖x‖ ^ 2 = ‖Q x‖ ^ 2 + ‖x - Q x‖ ^ 2 := by
      have h0 : RCLike.re ⟪Q x, x - Q x⟫_𝕜 = 0 := by
        rw [Submodule.inner_right_of_mem_orthogonal hqx hrest]; simp
      have hns := norm_add_sq (𝕜 := 𝕜) (Q x) (x - Q x)
      rw [show Q x + (x - Q x) = x by abel, h0] at hns
      linarith
    rw [hre, h1, h2, hpyth]
    have h1' := hV (Q x) hqx
    nlinarith [h1']
  -- Sylvester relation `A ∘L X − X ∘L B = Y`.
  have hsylv : A ∘L X - X ∘L B = Y := by
    ext x
    have hQxV : Q x ∈ V := V.starProjection_apply_mem x
    have hPP : P (P (Q x)) = P (Q x) :=
      U.starProjection_eq_self_iff.mpr (U.starProjection_apply_mem (Q x))
    have hQrest : Q (x - Q x) = 0 := by
      rw [map_sub, V.starProjection_eq_self_iff.mpr hQxV, sub_self]
    have hQSQ : Q (S (Q x)) = S (Q x) := V.starProjection_eq_self_iff.mpr (hVinv _ hQxV)
    have hTP : T (P (Q x)) = P (T (Q x)) :=
      starProjection_comp_toContinuousLinearMap_comm hT hUinv (Q x)
    have hAX : (A ∘L X) x = T (P (Q x)) := by
      simp only [ContinuousLinearMap.comp_apply, hX, hA, hTc, add_apply,
        smul_apply, sub_apply,
        one_apply_eq_self, LinearMap.coe_toContinuousLinearMap', hPP, sub_self,
        smul_zero, add_zero]
    have hXB : (X ∘L B) x = P (S (Q x)) := by
      simp only [ContinuousLinearMap.comp_apply, hX, hB, hSc, add_apply,
        smul_apply, sub_apply,
        one_apply_eq_self, LinearMap.coe_toContinuousLinearMap', map_add, map_smul,
        hQSQ, hQrest, map_zero, smul_zero, add_zero]
    have hYx : Y x = P (T (Q x)) - P (S (Q x)) := by
      simp only [hY, ContinuousLinearMap.comp_apply, sub_apply, hTc, hSc,
        LinearMap.coe_toContinuousLinearMap', map_sub]
    rw [sub_apply, hAX, hXB, hYx, hTP]
  exact ⟨A, B, hAsym, hBsym, hAc, hBc, hsylv⟩

/-- **The operator-norm Davis–Kahan sin-Θ theorem.**  Let `T, S` be symmetric,
`U` a `T`-invariant subspace with quadratic form `≥ (c+g)‖·‖²`, and `V` an
`S`-invariant subspace with form `≤ c‖·‖²`.  If `‖(S − T) x‖ ≤ ε ‖x‖` and
`g > 0`, then `‖V.starProjection ∘L U.starProjection‖ ≤ ε / g`.  The left side
is `‖sinΘ‖_op`, so this is the dimension-free `‖sinΘ‖_op ≤ ‖S − T‖_op / g`. -/
theorem norm_starProjection_comp_starProjection_le (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hUinv : ∀ x ∈ U, T x ∈ U) (hVinv : ∀ x ∈ V, S x ∈ V)
    {c g ε : ℝ} (hg : 0 < g)
    (hU : ∀ x ∈ U, (c + g) * ‖x‖ ^ 2 ≤ RCLike.re ⟪T x, x⟫_𝕜)
    (hV : ∀ x ∈ V, RCLike.re ⟪S x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2)
    (hε0 : 0 ≤ ε) (hε : ∀ x, ‖(S - T) x‖ ≤ ε * ‖x‖) :
    ‖V.starProjection ∘L U.starProjection‖ ≤ ε / g := by
  obtain ⟨A, B, hAsym, hBsym, hAc, hBc, hsylv⟩ :=
    exists_isSymmetric_comp_sub_comp_eq hT hS hUinv hVinv hU hV
  set P := U.starProjection with hP
  set Q := V.starProjection with hQ
  set Tc := LinearMap.toContinuousLinearMap T with hTc
  set Sc := LinearMap.toContinuousLinearMap S with hSc
  set X : E →L[𝕜] E := P ∘L Q with hX
  set Y : E →L[𝕜] E := P ∘L (Tc - Sc) ∘L Q with hY
  have hPsa : IsSelfAdjoint P := isSelfAdjoint_starProjection U
  have hQsa : IsSelfAdjoint Q := isSelfAdjoint_starProjection V
  -- `‖Y‖ ≤ ε`.
  have hYnorm : ‖Y‖ ≤ ε := by
    refine Y.opNorm_le_bound hε0 fun x => ?_
    have hcontr : ‖P ((Tc - Sc) (Q x))‖ ≤ ‖(Tc - Sc) (Q x)‖ := by
      rw [hP]; exact U.norm_starProjection_apply_le _
    have hTSc : (Tc - Sc) (Q x) = -((S - T) (Q x)) := by
      simp only [hTc, hSc, sub_apply, LinearMap.coe_toContinuousLinearMap',
        LinearMap.sub_apply]; abel
    calc ‖Y x‖ = ‖P ((Tc - Sc) (Q x))‖ := by
          simp only [hY, ContinuousLinearMap.comp_apply]
      _ ≤ ‖(Tc - Sc) (Q x)‖ := hcontr
      _ = ‖(S - T) (Q x)‖ := by rw [hTSc, norm_neg]
      _ ≤ ε * ‖Q x‖ := hε _
      _ ≤ ε * ‖x‖ := by
          refine mul_le_mul_of_nonneg_left ?_ hε0
          rw [hQ]; exact V.norm_starProjection_apply_le x
  -- Sylvester bound: `‖X‖ ≤ ‖Y‖ / g ≤ ε / g`.
  have hXbound : ‖X‖ ≤ ε / g :=
    calc ‖X‖ ≤ ‖Y‖ / g :=
          ContinuousLinearMap.opNorm_le_div_of_comp_sub_comp_eq hAsym hBsym hg hAc hBc hsylv
      _ ≤ ε / g := by gcongr
  -- `‖Q ∘L P‖ = ‖P ∘L Q‖ = ‖X‖`.
  have hstar : star (Q ∘L P) = P ∘L Q := by
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_comp,
      ← ContinuousLinearMap.star_eq_adjoint, ← ContinuousLinearMap.star_eq_adjoint,
      hPsa.star_eq, hQsa.star_eq]
  have hnorm_eq : ‖Q ∘L P‖ = ‖X‖ := by rw [hX, ← hstar]; exact (norm_star _).symm
  rw [hnorm_eq]
  exact hXbound

/-! ### Spectral corollaries (eigenvalue hypotheses)

The literature-facing forms: the invariant subspaces are spans of eigenvector
blocks and the quadratic-form hypotheses are sorted-eigenvalue hypotheses
(plan step E3 of `dev/davis-kahan-expert-completion-plan.md`). -/

section Spectral

variable {n : ℕ}

/-- **Operator-norm Davis–Kahan sin-Θ theorem, spectral form.**  If the
`T`-eigenvalues selected by `s` sit above `c + g` and the `S`-eigenvalues
outside `s'` sit below `c`, then the leading `T`-eigenblock span and the
trailing `S`-eigenblock span satisfy the dimension-free bound
`‖Q̂ ∘L P‖ ≤ ε / g`. -/
theorem norm_starProjection_comp_starProjection_le_of_eigenvalues
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank 𝕜 E = n)
    {s s' : Finset (Fin n)} {c g ε : ℝ} (hg : 0 < g)
    (hs : ∀ i ∈ s, c + g ≤ hT.eigenvalues hn i)
    (hs' : ∀ j ∉ s', hS.eigenvalues hn j ≤ c)
    (hε0 : 0 ≤ ε) (hε : ∀ x, ‖(S - T) x‖ ≤ ε * ‖x‖) :
    ‖(specSubspace (hS.eigenvectorBasis hn) (· ∉ s')).starProjection ∘L
        (specSubspace (hT.eigenvectorBasis hn) (· ∈ s)).starProjection‖ ≤ ε / g :=
  norm_starProjection_comp_starProjection_le hT hS
    (fun _ hx => map_mem_specSubspace hT hn _ hx)
    (fun _ hx => map_mem_specSubspace hS hn _ hx) hg
    (fun _ hx => le_re_inner_map_self_of_mem_specSubspace hT hn (fun i hi => hs i hi) hx)
    (fun _ hx => re_inner_map_self_le_of_mem_specSubspace hS hn (fun j hj => hs' j hj) hx)
    hε0 hε

omit [CompleteSpace E] in
/-- **Davis's sin 2θ theorem, spectral form.**  `U` is the span of the
`T`-eigenvectors selected by `s`; the selected eigenvalues sit above `b` and
the complementary ones below `a`.  For a unit eigenvector `x` of `T + S`
(eigenvalue location unconstrained) and `P` the projection onto `U`,
`(b − a) ‖P x‖ ‖x − P x‖ ≤ ε`. -/
theorem sin_two_theta_le_of_eigenvalues
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank 𝕜 E = n)
    {s : Finset (Fin n)} {a b ε : ℝ}
    (hb : ∀ i ∈ s, b ≤ hT.eigenvalues hn i)
    (ha : ∀ i ∉ s, hT.eigenvalues hn i ≤ a)
    (hε : ∀ v, ‖S v‖ ≤ ε * ‖v‖)
    {x : E} (hx : ‖x‖ = 1) {μ : ℝ} (hμ : T x + S x = (μ : 𝕜) • x) :
    (b - a) * (‖(specSubspace (hT.eigenvectorBasis hn) (· ∈ s)).starProjection x‖
      * ‖x - (specSubspace (hT.eigenvectorBasis hn) (· ∈ s)).starProjection x‖) ≤ ε := by
  refine sin_two_theta_le hT hS (fun u hu => map_mem_specSubspace hT hn _ hu)
    (fun u hu => le_re_inner_map_self_of_mem_specSubspace hT hn (fun i hi => hb i hi) hu)
    (fun w hw => ?_) hε hx hμ
  rw [orthogonal_specSubspace] at hw
  exact re_inner_map_self_le_of_mem_specSubspace hT hn (fun i hi => ha i hi) hw

omit [CompleteSpace E] in
/-- **Davis's tan 2θ theorem, spectral form.**  As `sin_two_theta_le_of_eigenvalues`,
with the vanishing-pinch hypotheses on the perturbation `S` (no diagonal blocks
with respect to the eigenblock splitting), and the sharper conclusion
`(b − a) ‖P x‖ ‖x − P x‖ ≤ |‖P x‖² − ‖x − P x‖²| ε`. -/
theorem tan_two_theta_le_of_eigenvalues
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank 𝕜 E = n)
    {s : Finset (Fin n)} {a b ε : ℝ}
    (hb : ∀ i ∈ s, b ≤ hT.eigenvalues hn i)
    (ha : ∀ i ∉ s, hT.eigenvalues hn i ≤ a)
    (hε : ∀ v, ‖S v‖ ≤ ε * ‖v‖)
    (hSU : ∀ u ∈ specSubspace (hT.eigenvectorBasis hn) (· ∈ s),
      ∀ u' ∈ specSubspace (hT.eigenvectorBasis hn) (· ∈ s), ⟪u, S u'⟫_𝕜 = 0)
    (hSUperp : ∀ w ∈ specSubspace (hT.eigenvectorBasis hn) (· ∉ s),
      ∀ w' ∈ specSubspace (hT.eigenvectorBasis hn) (· ∉ s), ⟪w, S w'⟫_𝕜 = 0)
    {x : E} (hx : ‖x‖ = 1) {μ : ℝ} (hμ : T x + S x = (μ : 𝕜) • x) :
    (b - a) * (‖(specSubspace (hT.eigenvectorBasis hn) (· ∈ s)).starProjection x‖
        * ‖x - (specSubspace (hT.eigenvectorBasis hn) (· ∈ s)).starProjection x‖)
      ≤ |‖(specSubspace (hT.eigenvectorBasis hn) (· ∈ s)).starProjection x‖ ^ 2
          - ‖x - (specSubspace (hT.eigenvectorBasis hn) (· ∈ s)).starProjection x‖ ^ 2| * ε := by
  refine tan_two_theta_le hT hS (fun u hu => map_mem_specSubspace hT hn _ hu)
    (fun u hu => le_re_inner_map_self_of_mem_specSubspace hT hn (fun i hi => hb i hi) hu)
    (fun w hw => ?_) hε hSU (fun w hw w' hw' => ?_) hx hμ
  · rw [orthogonal_specSubspace] at hw
    exact re_inner_map_self_le_of_mem_specSubspace hT hn (fun i hi => ha i hi) hw
  · rw [orthogonal_specSubspace] at hw hw'
    exact hSUperp w hw w' hw'

/-- **Operator-norm sin-Θ bound on the largest principal angle.**  Chaining the
identification `‖Q̂ ∘L P‖ = sin θ_max` with the operator-norm Davis–Kahan
theorem: for `U = span u` (`T`-invariant, form `≥ c + g`) and `W` with
`Wᗮ = span w`-complement... precisely, with `V := (span w)ᗮ` an `S`-invariant
subspace of form `≤ c`, the largest principal angle between `span u` and
`span w` satisfies `sin θ_max ≤ ε / g`. -/
theorem sqrt_one_sub_sq_cosPrincipalAngles_le
    {d : ℕ} {u w : Fin d → E} (hu : Orthonormal 𝕜 u) (hw : Orthonormal 𝕜 w) (hd : 0 < d)
    (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (hUinv : ∀ x ∈ Submodule.span 𝕜 (Set.range u), T x ∈ Submodule.span 𝕜 (Set.range u))
    (hVinv : ∀ x ∈ (Submodule.span 𝕜 (Set.range w))ᗮ,
      S x ∈ (Submodule.span 𝕜 (Set.range w))ᗮ)
    {c g ε : ℝ} (hg : 0 < g)
    (hU : ∀ x ∈ Submodule.span 𝕜 (Set.range u), (c + g) * ‖x‖ ^ 2 ≤ RCLike.re ⟪T x, x⟫_𝕜)
    (hV : ∀ x ∈ (Submodule.span 𝕜 (Set.range w))ᗮ, RCLike.re ⟪S x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2)
    (hε0 : 0 ≤ ε) (hε : ∀ x, ‖(S - T) x‖ ≤ ε * ‖x‖) :
    Real.sqrt (1 - cosPrincipalAngles hw hu (d - 1) ^ 2) ≤ ε / g := by
  rw [← norm_orthogonal_starProjection_comp_starProjection hu hw hd]
  exact norm_starProjection_comp_starProjection_le hT hS hUinv hVinv hg hU hV hε0 hε

end Spectral

end ForMathlib
