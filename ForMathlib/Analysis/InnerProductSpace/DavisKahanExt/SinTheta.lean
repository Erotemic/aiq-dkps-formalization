/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import ForMathlib.Analysis.InnerProductSpace.DavisKahanExt.Sylvester

/-!
# Infinite-dimensional `sin Θ` theorems

Literature writeup: local TeX, Sections 12--13.  Both residual and perturbation
forms are represented, including general separated spectra and ideal-norm
versions.
-/

namespace ForMathlib
namespace DavisKahanExt

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [CompleteSpace F]

/-- Residual `sin Θ` theorem for an isometric trial map. 

Lean proof route for a weaker agent:

1. Set `Y=(I-P_U)X` and derive `A|_{Uᗮ} Y - Y M = (I-P_U) residual A X M`.
2. Apply the ordered constant-one Sylvester theorem using `hsep`.
3. Bound the projected residual by the full residual norm.
4. Identify `Y` with `sinThetaEmbedding U X`.


Ext-agent signature audit (GPT 5.6 High): Correct as a directed residual theorem. The
isometric embedding is needed for the subspace interpretation, although the raw
Sylvester norm estimate itself uses only boundedness.

Preferred dependency route: Derive the cross-block Sylvester equation and specialize the
strongest available Sylvester theorem; only then translate cross-block norms into
directed or full subspace angles.
-/
theorem sinTheta_residual
    {A : E →L[𝕜] E} (hA : IsSelfAdjointOperator A)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (hU : Reduces A U)
    {X : F →L[𝕜] E} (hX : IsometricEmbedding X)
    {M : F →L[𝕜] F} (hM : IsSelfAdjointOperator M)
    {d : ℝ} (hd : 0 < d)
    (hsep : OrderedSpectraSeparated M ⊤ A Uᗮ d) :
    d * ‖sinThetaEmbedding U X‖ ≤ ‖residual A X M‖ := by
  sorry

/-- One-sided perturbation theorem for spectral subspaces. 

Lean proof route for a weaker agent:

1. Derive the off-diagonal Sylvester equation for `X=(I-P_V)P_U`.
2. Use the interval/exterior decomposition to apply the constant-one ordered Sylvester estimate to the lower and upper pieces.
3. Bound the right-hand residual by `‖B-A‖`.
4. Rewrite `‖X‖` as the directed gap.


Ext-agent signature audit (GPT 5.6 High): Correct as a one-sided directed-angle theorem.
One mixed interval/exterior gap is intentionally insufficient for a full
projector-difference conclusion.

Preferred dependency route: Derive the cross-block Sylvester equation and specialize the
strongest available Sylvester theorem; only then translate cross-block norms into
directed or full subspace angles.
-/
theorem sinTheta_perturbation
    {A B : E →L[𝕜] E}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : Reduces A U) (hV : Reduces B V)
    {left right d : ℝ} (hd : 0 < d)
    (hgap : IntervalExteriorSeparated A U B Vᗮ left right d) :
    d * directedGap U V ≤ ‖B - A‖ := by
  sorry

/-- **The dimension-free operator-norm Davis--Kahan `sin Θ` theorem, coercivity
form.**  For self-adjoint `A, B` on an arbitrary Hilbert space, `U` reducing `A`
with quadratic form `≥ (c+g)‖·‖²` on `U`, and `V` reducing `B` with quadratic
form `≤ c‖·‖²` on `V`,

`‖P_V P_U‖ ≤ ‖B − A‖ / g`.

This is the genuine infinite-dimensional `sin Θ` bound: the analytic core is the
integral-free Sylvester estimate `norm_sylvester_le_of_coercive` (no spectral
measure, no dimension or completeness hypothesis on the *bound* itself), and the
block construction `A ∘L P + (c+g)(1−P)`, `B ∘L Q + c(1−Q)` uses only the
dimension-free projection commutation `projection_apply_comm_of_reduces`.  The
spectrum-predicate forms (`sinTheta_perturbation`, `IntervalExteriorSeparated`)
follow from this once a bounded spectral theorem converts spectral separation to
these coercivity bounds. -/
theorem sinTheta_directed_coercive
    {A B : E →L[𝕜] E} (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : Reduces A U) (hV : Reduces B V)
    {c g : ℝ} (hg : 0 < g)
    (hUc : ∀ x ∈ U, (c + g) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜)
    (hVc : ∀ x ∈ V, RCLike.re ⟪B x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2) :
    ‖(projection V ∘L projection U : E →L[𝕜] E)‖ ≤ ‖B - A‖ / g := by
  set P := projection U with hP
  set Q := projection V with hQ
  set A' : E →L[𝕜] E := A ∘L P + ((c + g : ℝ) : 𝕜) • (1 - P) with hA'
  set B' : E →L[𝕜] E := B ∘L Q + ((c : ℝ) : 𝕜) • (1 - Q) with hB'
  set X : E →L[𝕜] E := P ∘L Q with hX
  set Y : E →L[𝕜] E := P ∘L (A - B) ∘L Q with hY
  have hPsa : IsSelfAdjoint P := isSelfAdjoint_starProjection U
  have hQsa : IsSelfAdjoint Q := isSelfAdjoint_starProjection V
  have hAsa : IsSelfAdjoint A := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mpr hA
  have hBsa : IsSelfAdjoint B := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mpr hB
  have hcgsa : IsSelfAdjoint ((c + g : ℝ) : 𝕜) := isSelfAdjoint_iff.mpr (RCLike.conj_ofReal _)
  have hcsa : IsSelfAdjoint ((c : ℝ) : 𝕜) := isSelfAdjoint_iff.mpr (RCLike.conj_ofReal _)
  have hone : IsSelfAdjoint (1 : E →L[𝕜] E) := IsSelfAdjoint.one _
  -- commutations
  have hcommA : A ∘L P = P ∘L A := by
    ext x; simp only [ContinuousLinearMap.comp_apply]
    exact (projection_apply_comm_of_reduces A U hU x).symm
  have hcommB : B ∘L Q = Q ∘L B := by
    ext x; simp only [ContinuousLinearMap.comp_apply]
    exact (projection_apply_comm_of_reduces B V hV x).symm
  -- self-adjointness of A', B'
  have hA'sa : IsSelfAdjoint A' := by
    have h1 : IsSelfAdjoint (A ∘L P) := (IsSelfAdjoint.commute_iff hAsa hPsa).mp hcommA
    have h2 : IsSelfAdjoint (((c + g : ℝ) : 𝕜) • ((1 : E →L[𝕜] E) - P)) := by
      rw [isSelfAdjoint_iff, star_smul, hcgsa.star_eq, (hone.sub hPsa).star_eq]
    exact hA' ▸ h1.add h2
  have hB'sa : IsSelfAdjoint B' := by
    have h1 : IsSelfAdjoint (B ∘L Q) := (IsSelfAdjoint.commute_iff hBsa hQsa).mp hcommB
    have h2 : IsSelfAdjoint (((c : ℝ) : 𝕜) • ((1 : E →L[𝕜] E) - Q)) := by
      rw [isSelfAdjoint_iff, star_smul, hcsa.star_eq, (hone.sub hQsa).star_eq]
    exact hB' ▸ h1.add h2
  have hA'sym : IsSelfAdjointOperator A' := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mp hA'sa
  have hB'sym : IsSelfAdjointOperator B' := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mp hB'sa
  -- coercivity of A'
  have hA'c : ∀ x, (c + g) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A' x, x⟫_𝕜 := by
    intro x
    have hpx : P x ∈ U := U.starProjection_apply_mem x
    have hrest : x - P x ∈ Uᗮ := U.sub_starProjection_mem_orthogonal x
    have hAxeq : A' x = A (P x) + ((c + g : ℝ) : 𝕜) • (x - P x) := by
      simp only [hA', ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]
    have hre : RCLike.re ⟪A' x, x⟫_𝕜
        = RCLike.re ⟪A (P x), x⟫_𝕜 + (c + g) * RCLike.re ⟪x - P x, x⟫_𝕜 := by
      rw [hAxeq, inner_add_left, inner_smul_left, RCLike.conj_ofReal, map_add, RCLike.re_ofReal_mul]
    have h1 : RCLike.re ⟪A (P x), x⟫_𝕜 = RCLike.re ⟪A (P x), P x⟫_𝕜 := by
      have hz : ⟪A (P x), x - P x⟫_𝕜 = 0 :=
        Submodule.inner_right_of_mem_orthogonal (hU.1 _ hpx) hrest
      have : ⟪A (P x), x⟫_𝕜 = ⟪A (P x), P x⟫_𝕜 + ⟪A (P x), x - P x⟫_𝕜 := by
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
    nlinarith [hUc (P x) hpx]
  -- upper bound for B'
  have hB'c : ∀ x, RCLike.re ⟪B' x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2 := by
    intro x
    have hqx : Q x ∈ V := V.starProjection_apply_mem x
    have hrest : x - Q x ∈ Vᗮ := V.sub_starProjection_mem_orthogonal x
    have hBxeq : B' x = B (Q x) + ((c : ℝ) : 𝕜) • (x - Q x) := by
      simp only [hB', ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]
    have hre : RCLike.re ⟪B' x, x⟫_𝕜
        = RCLike.re ⟪B (Q x), x⟫_𝕜 + c * RCLike.re ⟪x - Q x, x⟫_𝕜 := by
      rw [hBxeq, inner_add_left, inner_smul_left, RCLike.conj_ofReal, map_add, RCLike.re_ofReal_mul]
    have h1 : RCLike.re ⟪B (Q x), x⟫_𝕜 = RCLike.re ⟪B (Q x), Q x⟫_𝕜 := by
      have hz : ⟪B (Q x), x - Q x⟫_𝕜 = 0 :=
        Submodule.inner_right_of_mem_orthogonal (hV.1 _ hqx) hrest
      have : ⟪B (Q x), x⟫_𝕜 = ⟪B (Q x), Q x⟫_𝕜 + ⟪B (Q x), x - Q x⟫_𝕜 := by
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
    nlinarith [hVc (Q x) hqx]
  -- Sylvester relation A' X - X B' = Y
  have hsylv : sylvesterOperator A' B' X = Y := by
    show A' ∘L X - X ∘L B' = Y
    ext x
    have hQxV : Q x ∈ V := V.starProjection_apply_mem x
    have hPP : P (P (Q x)) = P (Q x) :=
      U.starProjection_eq_self_iff.mpr (U.starProjection_apply_mem (Q x))
    have hQrest : Q (x - Q x) = 0 := by
      have hQQ : Q (Q x) = Q x := V.starProjection_eq_self_iff.mpr (V.starProjection_apply_mem x)
      rw [map_sub, hQQ, sub_self]
    have hQBQ : Q (B (Q x)) = B (Q x) := V.starProjection_eq_self_iff.mpr (hV.1 _ hQxV)
    have hAP : A (P (Q x)) = P (A (Q x)) :=
      (projection_apply_comm_of_reduces A U hU (Q x)).symm
    have hAX : (A' ∘L X) x = A (P (Q x)) := by
      simp only [ContinuousLinearMap.comp_apply, hX, hA', ContinuousLinearMap.add_apply,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.one_apply, hPP, sub_self, smul_zero, add_zero]
    have hXB : (X ∘L B') x = P (B (Q x)) := by
      simp only [ContinuousLinearMap.comp_apply, hX, hB', ContinuousLinearMap.add_apply,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.one_apply, map_add, map_smul, hQBQ, hQrest, map_zero, smul_zero, add_zero]
    have hYx : Y x = P (A (Q x)) - P (B (Q x)) := by
      simp only [hY, ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply, map_sub]
    rw [ContinuousLinearMap.sub_apply, hAX, hXB, hYx, hAP]
  -- norm bound
  have hYnorm : ‖Y‖ ≤ ‖B - A‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
    have hc : ‖P ((A - B) (Q x))‖ ≤ ‖(A - B) (Q x)‖ := by
      rw [hP]; exact U.norm_starProjection_apply_le _
    calc ‖Y x‖ = ‖P ((A - B) (Q x))‖ := by simp only [hY, ContinuousLinearMap.comp_apply]
      _ ≤ ‖(A - B) (Q x)‖ := hc
      _ = ‖(B - A) (Q x)‖ := by rw [show A - B = -(B - A) by abel, ContinuousLinearMap.neg_apply, norm_neg]
      _ ≤ ‖B - A‖ * ‖Q x‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖B - A‖ * ‖x‖ := by
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          rw [hQ]; exact V.norm_starProjection_apply_le x
  have hXbound : ‖X‖ ≤ ‖B - A‖ / g :=
    (norm_sylvester_le_of_coercive hA'sym hB'sym hg hA'c hB'c hsylv).trans (by gcongr)
  have hstar : star (Q ∘L P : E →L[𝕜] E) = P ∘L Q := by
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_comp,
      ← ContinuousLinearMap.star_eq_adjoint, ← ContinuousLinearMap.star_eq_adjoint,
      hPsa.star_eq, hQsa.star_eq]
  have : ‖(Q ∘L P : E →L[𝕜] E)‖ = ‖X‖ := by rw [hX, ← hstar]; exact (norm_star _).symm
  calc ‖(projection V ∘L projection U : E →L[𝕜] E)‖ = ‖(Q ∘L P : E →L[𝕜] E)‖ := by rw [hP, hQ]
    _ = ‖X‖ := this
    _ ≤ ‖B - A‖ / g := hXbound

/-- Symmetric projector-difference form requiring both mixed gaps. 

Lean proof route for a weaker agent:

1. Apply `sinTheta_perturbation` to `(U,V)` and again to `(V,U)` using the reverse gap.
2. Use the two-projection norm identity that the full gap is the maximum of the two directed gaps.
3. Combine the two inequalities with `max_le` and simplify the perturbation sign.


Ext-agent signature audit (GPT 5.6 High): Correct with both mixed gaps. The full
projection gap is the maximum of the two directed gaps in operator norm.

Preferred dependency route: Derive the cross-block Sylvester equation and specialize the
strongest available Sylvester theorem; only then translate cross-block norms into
directed or full subspace angles.
-/
theorem sinTheta_symmetric
    {A B : E →L[𝕜] E}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : Reduces A U) (hV : Reduces B V)
    {left right left' right' d : ℝ} (hd : 0 < d)
    (hUV : IntervalExteriorSeparated A U B Vᗮ left right d)
    (hVU : IntervalExteriorSeparated B V A Uᗮ left' right' d) :
    d * subspaceGap U V ≤ ‖B - A‖ := by
  sorry

/-- General separated-spectrum form with the optimal universal `π / 2`
Sylvester constant. 

Lean proof route for a weaker agent:

1. Derive the Sylvester equation for `(I-P_V)P_U` from the two reducing relations.
2. Apply `norm_sylvester_le_of_generalSeparation` with the hybrid spectral gap.
3. Bound the residual block by `‖B-A‖` using projection contractions.
4. Rewrite the block norm as `directedGap U V`.


Ext-agent signature audit (GPT 5.6 High): Correct as a directed theorem with the `π/2`
constant. The hybrid gap matches the cross block `P_{Vᗮ}P_U`.

Preferred dependency route: Derive the cross-block Sylvester equation and specialize the
strongest available Sylvester theorem; only then translate cross-block norms into
directed or full subspace angles.
-/
theorem sinTheta_generalSeparation
    {A B : E →L[𝕜] E}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : Reduces A U) (hV : Reduces B V)
    {d : ℝ} (hd : 0 < d) (hgap : HybridGap A B U V d) :
    d * directedGap U V ≤ (Real.pi / 2) * ‖B - A‖ := by
  sorry

/-- Canonical spectral-projection form. 

Lean proof route for a weaker agent:

1. Convert the four spectral-containment hypotheses into the two `IntervalExteriorSeparated` predicates.
2. Apply `sinTheta_symmetric` to the canonical spectral subspaces, using `reduces_spectralSubspace`.
3. Rewrite the subspace gap as the norm of the two spectral projections.


Ext-agent signature audit (GPT 5.6 High): Correct after the measurable-set hypotheses
were added. The four containments encode exactly the two mixed interval/exterior gaps.

Preferred dependency route: Derive the cross-block Sylvester equation and specialize the
strongest available Sylvester theorem; only then translate cross-block norms into
directed or full subspace angles.
-/
theorem spectralProjection_sinTheta
    {A B : E →L[𝕜] E}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    (s t : Set ℝ) (hs : MeasurableSet s) (ht : MeasurableSet t)
    {left right left' right' d : ℝ} (hd : 0 < d)
    (hAs : SpectrumIn A (spectralSubspace A s) (Set.Icc left right))
    (hBt : SpectrumIn B (spectralSubspace B t)ᗮ
      {x | x ≤ left - d ∨ right + d ≤ x})
    (hBs : SpectrumIn B (spectralSubspace B t) (Set.Icc left' right'))
    (hAt : SpectrumIn A (spectralSubspace A s)ᗮ
      {x | x ≤ left' - d ∨ right' + d ≤ x}) :
    d * ‖spectralProjection A s - spectralProjection B t‖ ≤
      ‖B - A‖ := by
  sorry

/-- Symmetric-ideal form. 

Lean proof route for a weaker agent:

1. Decompose the full sine operator into the two directed off-diagonal blocks.
2. Apply the interval/exterior ideal-valued Sylvester estimate to each block, using `hmem` for the perturbation.
3. Recombine the blocks through the two-projection decomposition or the symmetric-angle identity.
4. Return both ideal membership and the gauge inequality.


Ext-agent signature audit (GPT 5.6 High): Plausible with the full ambient sine
convention because the self-adjoint off-diagonal blocks occur as adjoint pairs. The
proof must establish the corresponding ideal block identity; do not combine two directed
estimates by a triangle inequality, which would lose the sharp constant.

Preferred dependency route: Derive the cross-block Sylvester equation and specialize the
strongest available Sylvester theorem; only then translate cross-block norms into
directed or full subspace angles.
-/
theorem ideal_sinTheta
    (I : SymmetricNormIdeal (𝕜 := 𝕜) (E := E))
    {A B : E →L[𝕜] E}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : Reduces A U) (hV : Reduces B V)
    {left right left' right' d : ℝ} (hd : 0 < d)
    (hUV : IntervalExteriorSeparated A U B Vᗮ left right d)
    (hVU : IntervalExteriorSeparated B V A Uᗮ left' right' d)
    (hmem : I.mem (B - A)) :
    I.mem (sinAngleOperator U V) ∧
      d * I.gauge (sinAngleOperator U V) ≤ I.gauge (B - A) := by
  sorry

end DavisKahanExt
end ForMathlib
