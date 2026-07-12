/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import ForMathlib.Analysis.InnerProductSpace.DavisKahanTheory.Sylvester
import ForMathlib.Analysis.InnerProductSpace.SinThetaUINorm
import ForMathlib.Analysis.InnerProductSpace.SinThetaOpNorm
import ForMathlib.Analysis.InnerProductSpace.DavisKahan.SinTheta
import ForMathlib.Analysis.InnerProductSpace.DavisKahan.Projector

/-!
# The complete finite-dimensional `sin Θ` theorem family

Literature map:

* `ForMathlib/prose/Davis-Kahan-1970-part-III-core-arguments.tex`,
  Section 7, "The sin Theta theorem".
* Davis--Kahan (1970), Section 2 (`sin Θ`) and Section 6 (proof and symmetric
  extension).
* `ForMathlib/prose/Yu-Wang-Samworth-2014-core-arguments.tex`,
  Sections "The symmetric-matrix variant" and "Lower bound on the residual".

The residual theorem is the numerical analyst's form.  The perturbation
version is the operator theorist's form.  Both are stated for every relevant
unitarily invariant norm, followed by the interval, spectral-projector, and
concrete-norm corollaries expected from the final API.
-/

namespace ForMathlib
namespace DavisKahanTheory

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]

/-! ## Residual form -/

/-- **Davis--Kahan `sin Θ`, residual form, every UI norm.**

The spectrum of the approximate coordinate operator `M` lies in `[a,b]`, the
unwanted spectrum of `A` on `Uᗮ` lies outside `(a-δ,b+δ)`, and `R = AX-XM`.
Then `δ ‖sin Θ‖ ≤ ‖R‖`.

Lean proof route for a weaker agent:

1. Project `AX-XM` into `Uᗮ`; reduction of `U` gives a Sylvester equation between `A|Uᗮ` and `M`.
2. Apply the interval/exterior finite UI Sylvester theorem and the projection ideal bound.
-/
theorem sinTheta_residual_le
    (N : RectangularUnitarilyInvariantNorm 𝕜 F E)
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] (hU : Reduces A U)
    (X : F →ₗᵢ[𝕜] E) {M : F →ₗ[𝕜] F} (hM : M.IsSymmetric)
    {a b δ : ℝ} (hδ : 0 < δ)
    (hMspec : SpectrumIn M ⊤ (Set.Icc a b))
    (hAspec : SpectrumIn A Uᗮ {lam | lam ∉ Set.Ioo (a - δ) (b + δ)}) :
    δ * N (sinThetaEmbedding U X) ≤ N (residual A X M) := by
  have hUperp : Reduces A Uᗮ := reduces_orthogonal_of_isSymmetric hA hU
  let AU : Uᗮ →ₗ[𝕜] Uᗮ := A.restrict hUperp
  let Y : F →ₗ[𝕜] Uᗮ :=
    Uᗮ.orthogonalProjectionOnto.toLinearMap ∘ₗ X.toLinearMap
  let C : F →ₗ[𝕜] Uᗮ :=
    Uᗮ.orthogonalProjectionOnto.toLinearMap ∘ₗ residual A X M
  let NU : RectangularUnitarilyInvariantNorm 𝕜 F Uᗮ :=
    N.codomainIsometryTransport Uᗮ.subtypeₗᵢ
  have hAU : AU.IsSymmetric := isSymmetric_restrict hA hUperp
  have hgap : IntervalSylvesterGap AU M a b δ := by
    refine ⟨hMspec, ?_⟩
    exact (spectrumIn_restrict_iff A hUperp _).2 hAspec
  have hEq : AU ∘ₗ Y - Y ∘ₗ M = C := by
    ext x
    have hx := LinearMap.congr_fun
      (sylvester_sinThetaEmbedding_eq_projectedResidual hA hU X M) x
    simpa [AU, Y, C, sinThetaEmbedding, complementaryProjection, projection,
      LinearMap.comp_apply] using hx
  have hY : NU Y = N (sinThetaEmbedding U X) := by
    change N (Uᗮ.subtypeₗᵢ.toLinearMap ∘ₗ Y) = N (sinThetaEmbedding U X)
    congr 1
  have hC : NU C =
      N (complementaryProjection U ∘ₗ residual A X M) := by
    change N (Uᗮ.subtypeₗᵢ.toLinearMap ∘ₗ C) =
      N (complementaryProjection U ∘ₗ residual A X M)
    congr 1
  have hproj : ‖(complementaryProjection U).toContinuousLinearMap‖ ≤ 1 := by
    refine (complementaryProjection U).toContinuousLinearMap.opNorm_le_bound
      zero_le_one fun x => ?_
    change ‖Uᗮ.starProjection x‖ ≤ 1 * ‖x‖
    simpa using Uᗮ.norm_starProjection_apply_le x
  have hC_le : NU C ≤ N (residual A X M) := by
    rw [hC]
    calc
      N (complementaryProjection U ∘ₗ residual A X M)
          ≤ ‖(complementaryProjection U).toContinuousLinearMap‖ *
              N (residual A X M) :=
        N.comp_le_opNorm_mul _ _
      _ ≤ 1 * N (residual A X M) :=
        mul_le_mul_of_nonneg_right hproj (N.nonneg _)
      _ = N (residual A X M) := one_mul _
  have hSylvester :=
    uiNorm_sylvester_le_of_intervalGap NU hAU hM hδ hgap hEq
  rw [hY] at hSylvester
  exact hSylvester.trans hC_le

/-- Ordered half-line residual form.

Lean proof route for a weaker agent:

1. Project the residual onto `Uᗮ`, identify the ordered Sylvester equation, and apply `uiNorm_sylvester_le_of_orderedGap`.
2. The operator-norm core should later specialize the supported `DavisKahan.SinTheta` module.
-/
theorem sinTheta_residual_le_of_orderedGap
    (N : RectangularUnitarilyInvariantNorm 𝕜 F E)
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] (hU : Reduces A U)
    (X : F →ₗᵢ[𝕜] E) {M : F →ₗ[𝕜] F} (hM : M.IsSymmetric)
    {δ : ℝ} (hδ : 0 < δ) (hgap : OrderedGap M ⊤ A Uᗮ δ) :
    δ * N (sinThetaEmbedding U X) ≤ N (residual A X M) := by
  have hUperp : Reduces A Uᗮ := reduces_orthogonal_of_isSymmetric hA hU
  let AU : Uᗮ →ₗ[𝕜] Uᗮ := A.restrict hUperp
  let Y : F →ₗ[𝕜] Uᗮ :=
    Uᗮ.orthogonalProjectionOnto.toLinearMap ∘ₗ X.toLinearMap
  let C : F →ₗ[𝕜] Uᗮ :=
    Uᗮ.orthogonalProjectionOnto.toLinearMap ∘ₗ residual A X M
  let NU : RectangularUnitarilyInvariantNorm 𝕜 F Uᗮ :=
    N.codomainIsometryTransport Uᗮ.subtypeₗᵢ
  have hAU : AU.IsSymmetric := isSymmetric_restrict hA hUperp
  have hgap' : OrderedSylvesterGap AU M δ := by
    left
    intro lam μ hlam hμ
    apply hgap lam μ hlam
    change μ ∈ restrictedSpectrum (A.restrict hUperp) ⊤ at hμ
    rw [restrictedSpectrum_restrict A hUperp] at hμ
    exact hμ
  have hEq : AU ∘ₗ Y - Y ∘ₗ M = C := by
    ext x
    have hx := LinearMap.congr_fun
      (sylvester_sinThetaEmbedding_eq_projectedResidual hA hU X M) x
    simpa [AU, Y, C, sinThetaEmbedding, complementaryProjection, projection,
      LinearMap.comp_apply] using hx
  have hY : NU Y = N (sinThetaEmbedding U X) := by
    change N (Uᗮ.subtypeₗᵢ.toLinearMap ∘ₗ Y) = N (sinThetaEmbedding U X)
    congr 1
  have hC : NU C =
      N (complementaryProjection U ∘ₗ residual A X M) := by
    change N (Uᗮ.subtypeₗᵢ.toLinearMap ∘ₗ C) =
      N (complementaryProjection U ∘ₗ residual A X M)
    congr 1
  have hproj : ‖(complementaryProjection U).toContinuousLinearMap‖ ≤ 1 := by
    refine (complementaryProjection U).toContinuousLinearMap.opNorm_le_bound
      zero_le_one fun x => ?_
    change ‖Uᗮ.starProjection x‖ ≤ 1 * ‖x‖
    simpa using Uᗮ.norm_starProjection_apply_le x
  have hC_le : NU C ≤ N (residual A X M) := by
    rw [hC]
    calc
      N (complementaryProjection U ∘ₗ residual A X M)
          ≤ ‖(complementaryProjection U).toContinuousLinearMap‖ *
              N (residual A X M) :=
        N.comp_le_opNorm_mul _ _
      _ ≤ 1 * N (residual A X M) :=
        mul_le_mul_of_nonneg_right hproj (N.nonneg _)
      _ = N (residual A X M) := one_mul _
  have hSylvester :=
    uiNorm_sylvester_le_of_orderedGap NU hAU hM hδ hgap' hEq
  rw [hY] at hSylvester
  exact hSylvester.trans hC_le

/-- General disjoint-spectrum residual form.  The `π/2` loss is the
Bhatia--Davis--McIntosh extension, not the sharp interval/exterior theorem.
The restriction and projection proof below is complete; the only open input is
`kyFan_sylvester_le_of_spectralDistance` in the Sylvester layer.

Lean proof route for a weaker agent:

1. Project the residual onto `Uᗮ`, obtain the rectangular Sylvester equation, apply `uiNorm_sylvester_le_of_spectralDistance`, and contract the projected residual.
2. Record the exact Sylvester equation as a named local equality before applying the general estimate.
3. Use the projection contraction and positivity of `δ` to normalize the final scalar inequality.
-/
theorem sinTheta_residual_le_of_spectralDistance
    (N : RectangularUnitarilyInvariantNorm 𝕜 F E)
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] (hU : Reduces A U)
    (X : F →ₗᵢ[𝕜] E) {M : F →ₗ[𝕜] F} (hM : M.IsSymmetric)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : SpectraSeparated M ⊤ A Uᗮ δ) :
    δ * N (sinThetaEmbedding U X) ≤ (Real.pi / 2) * N (residual A X M) := by
  have hUperp : Reduces A Uᗮ := reduces_orthogonal_of_isSymmetric hA hU
  let AU : Uᗮ →ₗ[𝕜] Uᗮ := A.restrict hUperp
  let Y : F →ₗ[𝕜] Uᗮ :=
    Uᗮ.orthogonalProjectionOnto.toLinearMap ∘ₗ X.toLinearMap
  let C : F →ₗ[𝕜] Uᗮ :=
    Uᗮ.orthogonalProjectionOnto.toLinearMap ∘ₗ residual A X M
  let NU : RectangularUnitarilyInvariantNorm 𝕜 F Uᗮ :=
    N.codomainIsometryTransport Uᗮ.subtypeₗᵢ
  have hAU : AU.IsSymmetric := isSymmetric_restrict hA hUperp
  have hgap' : SpectraSeparated AU ⊤ M ⊤ δ := by
    intro lam μ hlam hμ
    have hlam' : lam ∈ restrictedSpectrum A Uᗮ := by
      rw [← restrictedSpectrum_restrict A hUperp]
      exact hlam
    have hsep := hgap μ lam hμ hlam'
    simpa [abs_sub_comm] using hsep
  have hEq : AU ∘ₗ Y - Y ∘ₗ M = C := by
    ext x
    have hx := LinearMap.congr_fun
      (sylvester_sinThetaEmbedding_eq_projectedResidual hA hU X M) x
    simpa [AU, Y, C, sinThetaEmbedding, complementaryProjection, projection,
      LinearMap.comp_apply] using hx
  have hY : NU Y = N (sinThetaEmbedding U X) := by
    change N (Uᗮ.subtypeₗᵢ.toLinearMap ∘ₗ Y) = N (sinThetaEmbedding U X)
    congr 1
  have hC : NU C =
      N (complementaryProjection U ∘ₗ residual A X M) := by
    change N (Uᗮ.subtypeₗᵢ.toLinearMap ∘ₗ C) =
      N (complementaryProjection U ∘ₗ residual A X M)
    congr 1
  have hproj : ‖(complementaryProjection U).toContinuousLinearMap‖ ≤ 1 := by
    refine (complementaryProjection U).toContinuousLinearMap.opNorm_le_bound
      zero_le_one fun x => ?_
    change ‖Uᗮ.starProjection x‖ ≤ 1 * ‖x‖
    simpa using Uᗮ.norm_starProjection_apply_le x
  have hC_le : NU C ≤ N (residual A X M) := by
    rw [hC]
    calc
      N (complementaryProjection U ∘ₗ residual A X M)
          ≤ ‖(complementaryProjection U).toContinuousLinearMap‖ *
              N (residual A X M) :=
        N.comp_le_opNorm_mul _ _
      _ ≤ 1 * N (residual A X M) :=
        mul_le_mul_of_nonneg_right hproj (N.nonneg _)
      _ = N (residual A X M) := one_mul _
  have hSylvester :=
    uiNorm_sylvester_le_of_spectralDistance NU hAU hM hδ hgap' hEq
  rw [hY] at hSylvester
  calc
    δ * N (sinThetaEmbedding U X)
        ≤ (Real.pi / 2) * NU C := hSylvester
    _ ≤ (Real.pi / 2) * N (residual A X M) :=
      mul_le_mul_of_nonneg_left hC_le (by positivity)

/-! ## Operator-norm one-sided (directed) form

This is the robust first capstone: the one-sided operator-norm `sin Θ` estimate,
proved by feeding the spectral-gap coercivity bridge into the dimension-free
operator-norm Sylvester theorem `norm_starProjection_comp_starProjection_le`.
No principal-angle or equal-rank geometry is needed. -/

/-- **One-sided operator-norm Davis--Kahan `sin Θ` theorem (spectral-hypothesis
form).**  If `A, B` are symmetric, `U` reduces `A` with `U`-carried spectrum
`≥ c + g`, `V` reduces `B` with `V`-carried spectrum `≤ c`, and
`‖(B − A) x‖ ≤ ε ‖x‖`, then

`‖P_V ∘ P_U‖ ≤ ε / g`.

`‖P_V P_U‖` is the sine of the directed angle between the high `A`-block `U` and
the high `B`-block `Vᗮ`.  **The finite result is dispatched from the
arbitrary-dimension lemma** `DavisKahan.sinTheta_directed_coercive`: the finite
operators are converted to bounded operators, and the *only* finite-dimensional
ingredient is the eigenbasis spectrum ⟹ coercivity bridge
(`le_re_inner_of_spectrumIn` / `re_inner_le_of_spectrumIn`).  The whole sin-Θ
construction and Sylvester estimate are the dimension-free infinite-dimensional
core. -/
theorem opNorm_directed_sinTheta_le {A B : E →ₗ[𝕜] E}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : Reduces A U) (hV : Reduces B V)
    {c g ε : ℝ} (hg : 0 < g)
    (hUspec : SpectrumIn A U (Set.Ici (c + g)))
    (hVspec : SpectrumIn B V (Set.Iic c))
    (hε0 : 0 ≤ ε) (hε : ∀ x, ‖(B - A) x‖ ≤ ε * ‖x‖) :
    ‖(V.starProjection ∘L U.starProjection : E →L[𝕜] E)‖ ≤ ε / g := by
  haveI : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  set Ac : E →L[𝕜] E := A.toContinuousLinearMap with hAc
  set Bc : E →L[𝕜] E := B.toContinuousLinearMap with hBc
  have hApp : ∀ x, Ac x = A x := fun _ => rfl
  have hBpp : ∀ x, Bc x = B x := fun _ => rfl
  have hAself : DavisKahan.IsSelfAdjointOperator Ac := fun x y => hA x y
  have hBself : DavisKahan.IsSelfAdjointOperator Bc := fun x y => hB x y
  have hUperp : Reduces A Uᗮ := reduces_orthogonal_of_isSymmetric hA hU
  have hVperp : Reduces B Vᗮ := reduces_orthogonal_of_isSymmetric hB hV
  have hUred : DavisKahan.Reduces Ac U := ⟨fun x hx => hU x hx, fun x hx => hUperp x hx⟩
  have hVred : DavisKahan.Reduces Bc V := ⟨fun x hx => hV x hx, fun x hx => hVperp x hx⟩
  have hUc : ∀ x ∈ U, (c + g) * ‖x‖ ^ 2 ≤ RCLike.re ⟪Ac x, x⟫_𝕜 :=
    fun x hx => le_re_inner_of_spectrumIn hA hU hUspec hx
  have hVc : ∀ x ∈ V, RCLike.re ⟪Bc x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2 :=
    fun x hx => re_inner_le_of_spectrumIn hB hV hVspec hx
  have hExt := DavisKahan.sinTheta_directed_coercive hAself hBself hUred hVred hg hUc hVc
  have hnorm : ‖(Bc - Ac : E →L[𝕜] E)‖ ≤ ε := by
    refine ContinuousLinearMap.opNorm_le_bound _ hε0 fun x => ?_
    have hsub : (Bc - Ac) x = (B - A) x := by
      simp only [ContinuousLinearMap.sub_apply, LinearMap.sub_apply, hApp, hBpp]
    rw [hsub]; exact hε x
  calc ‖(V.starProjection ∘L U.starProjection : E →L[𝕜] E)‖
      ≤ ‖(Bc - Ac : E →L[𝕜] E)‖ / g := hExt
    _ ≤ ε / g := by gcongr

/-- **Spectral-projection directed operator-norm `sin Θ` theorem.**  The canonical
spectral subspaces automatically reduce their operators, so the one-sided bound
holds for `‖P_{spec B t} ∘ P_{spec A s}‖` under the corresponding spectral-gap
hypotheses.  This is the directed operator-norm form of the canonical
spectral-projector Davis--Kahan theorem. -/
theorem opNorm_spectralSubspace_directed_sinTheta_le {A B : E →ₗ[𝕜] E}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) {s t : Set ℝ}
    {c g ε : ℝ} (hg : 0 < g)
    (hUspec : SpectrumIn A (spectralSubspace A s) (Set.Ici (c + g)))
    (hVspec : SpectrumIn B (spectralSubspace B t) (Set.Iic c))
    (hε0 : 0 ≤ ε) (hε : ∀ x, ‖(B - A) x‖ ≤ ε * ‖x‖) :
    ‖((spectralSubspace B t).starProjection ∘L
        (spectralSubspace A s).starProjection : E →L[𝕜] E)‖ ≤ ε / g :=
  opNorm_directed_sinTheta_le hA hB (reduces_spectralSubspace A s)
    (reduces_spectralSubspace B t) hg hUspec hVspec hε0 hε

/-! ## Two-sided projector-difference operator-norm form

The generic `RCLike` projector theorem now supplies the sharp factor-one bound
without an equal-rank hypothesis.  Finite-dimensional spectral decomposition is
used only to turn the four `SpectrumIn` assumptions into quadratic-form bounds;
all projection geometry and Sylvester analysis are inherited from the supported
dimension-free core. -/

/-- **Sharp finite-dimensional operator-norm Davis--Kahan projector theorem.**
With two-sided spectral gaps for the selected and complementary blocks of both
operators,

`‖P_U - P_W‖ ≤ ε / g`.

This is a finite spectral specialization of
`DavisKahan.opNorm_starProjection_sub_le_of_coercive`.  In particular, there is
no rank hypothesis and no factor-two loss. -/
theorem opNorm_starProjection_sub_le {A B : E →ₗ[𝕜] E}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U W : Submodule 𝕜 E} [U.HasOrthogonalProjection] [W.HasOrthogonalProjection]
    (hU : Reduces A U) (hW : Reduces B W)
    {c g ε : ℝ} (hg : 0 < g)
    (hUhi : SpectrumIn A U (Set.Ici (c + g)))
    (hUlo : SpectrumIn A Uᗮ (Set.Iic c))
    (hWhi : SpectrumIn B W (Set.Ici (c + g)))
    (hWlo : SpectrumIn B Wᗮ (Set.Iic c))
    (hε0 : 0 ≤ ε) (hε : ∀ x, ‖(B - A) x‖ ≤ ε * ‖x‖) :
    ‖(U.starProjection - W.starProjection : E →L[𝕜] E)‖ ≤ ε / g := by
  haveI : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  let Ac : E →L[𝕜] E := A.toContinuousLinearMap
  let Bc : E →L[𝕜] E := B.toContinuousLinearMap
  have hAself : DavisKahan.IsSelfAdjointOperator Ac := by
    intro x y
    change ⟪A x, y⟫_𝕜 = ⟪x, A y⟫_𝕜
    exact hA x y
  have hBself : DavisKahan.IsSelfAdjointOperator Bc := by
    intro x y
    change ⟪B x, y⟫_𝕜 = ⟪x, B y⟫_𝕜
    exact hB x y
  have hUperp : Reduces A Uᗮ := reduces_orthogonal_of_isSymmetric hA hU
  have hWperp : Reduces B Wᗮ := reduces_orthogonal_of_isSymmetric hB hW
  have hUred : DavisKahan.Reduces Ac U :=
    ⟨fun x hx => by simpa [Ac] using hU x hx,
      fun x hx => by simpa [Ac] using hUperp x hx⟩
  have hWred : DavisKahan.Reduces Bc W :=
    ⟨fun x hx => by simpa [Bc] using hW x hx,
      fun x hx => by simpa [Bc] using hWperp x hx⟩
  have hUhiForm : ∀ x ∈ U,
      (c + g) * ‖x‖ ^ 2 ≤ RCLike.re ⟪Ac x, x⟫_𝕜 :=
    fun x hx => by simpa [Ac] using le_re_inner_of_spectrumIn hA hU hUhi hx
  have hUloForm : ∀ x ∈ Uᗮ,
      RCLike.re ⟪Ac x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2 :=
    fun x hx => by simpa [Ac] using re_inner_le_of_spectrumIn hA hUperp hUlo hx
  have hWhiForm : ∀ x ∈ W,
      (c + g) * ‖x‖ ^ 2 ≤ RCLike.re ⟪Bc x, x⟫_𝕜 :=
    fun x hx => by simpa [Bc] using le_re_inner_of_spectrumIn hB hW hWhi hx
  have hWloForm : ∀ x ∈ Wᗮ,
      RCLike.re ⟪Bc x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2 :=
    fun x hx => by simpa [Bc] using re_inner_le_of_spectrumIn hB hWperp hWlo hx
  have hcore := DavisKahan.opNorm_starProjection_sub_le_of_coercive
    hAself hBself hUred hWred hg hUhiForm hUloForm hWhiForm hWloForm
  have hnorm : ‖(Bc - Ac : E →L[𝕜] E)‖ ≤ ε := by
    refine ContinuousLinearMap.opNorm_le_bound _ hε0 fun x => ?_
    simpa [Ac, Bc] using hε x
  exact hcore.trans (by gcongr)

/-- Compatibility corollary with the older factor-two right-hand side.
The sharp theorem `opNorm_starProjection_sub_le` is strictly stronger. -/
theorem opNorm_starProjection_sub_le_two {A B : E →ₗ[𝕜] E}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U W : Submodule 𝕜 E} [U.HasOrthogonalProjection] [W.HasOrthogonalProjection]
    (hU : Reduces A U) (hW : Reduces B W)
    {c g ε : ℝ} (hg : 0 < g)
    (hUhi : SpectrumIn A U (Set.Ici (c + g))) (hUlo : SpectrumIn A Uᗮ (Set.Iic c))
    (hWhi : SpectrumIn B W (Set.Ici (c + g))) (hWlo : SpectrumIn B Wᗮ (Set.Iic c))
    (hε0 : 0 ≤ ε) (hε : ∀ x, ‖(B - A) x‖ ≤ ε * ‖x‖) :
    ‖(U.starProjection - W.starProjection : E →L[𝕜] E)‖ ≤ 2 * (ε / g) := by
  have hsharp := opNorm_starProjection_sub_le hA hB hU hW hg
    hUhi hUlo hWhi hWlo hε0 hε
  have hnonneg : 0 ≤ ε / g := div_nonneg hε0 hg.le
  nlinarith

/-- **Sharp spectral-subspace projector theorem.**  Canonical finite
spectral subspaces reduce their operators automatically, so the sharp
factor-one theorem applies directly. -/
theorem opNorm_spectralSubspace_sub_le {A B : E →ₗ[𝕜] E}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) {s t : Set ℝ}
    {c g ε : ℝ} (hg : 0 < g)
    (hAhi : SpectrumIn A (spectralSubspace A s) (Set.Ici (c + g)))
    (hAlo : SpectrumIn A (spectralSubspace A s)ᗮ (Set.Iic c))
    (hBhi : SpectrumIn B (spectralSubspace B t) (Set.Ici (c + g)))
    (hBlo : SpectrumIn B (spectralSubspace B t)ᗮ (Set.Iic c))
    (hε0 : 0 ≤ ε) (hε : ∀ x, ‖(B - A) x‖ ≤ ε * ‖x‖) :
    ‖((spectralSubspace A s).starProjection
        - (spectralSubspace B t).starProjection : E →L[𝕜] E)‖ ≤ ε / g :=
  opNorm_starProjection_sub_le hA hB (reduces_spectralSubspace A s)
    (reduces_spectralSubspace B t) hg hAhi hAlo hBhi hBlo hε0 hε

/-- **Two-sided operator-norm spectral-projector Davis--Kahan theorem.**  The
projector-difference bound for the canonical spectral subspaces (they reduce
their operators automatically). -/
theorem opNorm_spectralSubspace_sub_le_two {A B : E →ₗ[𝕜] E}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) {s t : Set ℝ}
    {c g ε : ℝ} (hg : 0 < g)
    (hAhi : SpectrumIn A (spectralSubspace A s) (Set.Ici (c + g)))
    (hAlo : SpectrumIn A (spectralSubspace A s)ᗮ (Set.Iic c))
    (hBhi : SpectrumIn B (spectralSubspace B t) (Set.Ici (c + g)))
    (hBlo : SpectrumIn B (spectralSubspace B t)ᗮ (Set.Iic c))
    (hε0 : 0 ≤ ε) (hε : ∀ x, ‖(B - A) x‖ ≤ ε * ‖x‖) :
    ‖((spectralSubspace A s).starProjection
        - (spectralSubspace B t).starProjection : E →L[𝕜] E)‖ ≤ 2 * (ε / g) :=
  opNorm_starProjection_sub_le_two hA hB (reduces_spectralSubspace A s)
    (reduces_spectralSubspace B t) hg hAhi hAlo hBhi hBlo hε0 hε

/-! ## Perturbation form -/

/-- The adjoint of the canonical isometric inclusion of a subspace is its
orthogonal projection onto that subspace.  This is the finite-dimensional
bridge used by `domainIsometryTransport` in the perturbation wrappers below. -/
private theorem adjoint_subtype_eq_orthogonalProjectionOnto
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    LinearMap.adjoint U.subtypeₗᵢ.toLinearMap =
      U.orthogonalProjectionOnto.toLinearMap := by
  rw [eq_comm]
  apply (LinearMap.eq_adjoint_iff
    U.orthogonalProjectionOnto.toLinearMap U.subtype).2
  intro x y
  change ⟪U.starProjection x, (y : E)⟫_𝕜 = ⟪x, (y : E)⟫_𝕜
  rw [U.inner_starProjection_left_eq_right,
    U.starProjection_eq_self_iff.mpr y.2]

/-- Transporting the rectangular sine embedding on `U` back to the ambient
square space gives the one-sided sine cross projection `P_{Vᗮ} P_U`. -/
private theorem domainTransport_sinThetaEmbedding_apply
    (N : UnitarilyInvariantNorm 𝕜 E)
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] :
    (N.toRectangular.domainIsometryTransport U.subtypeₗᵢ)
        (sinThetaEmbedding V U.subtypeₗᵢ) = N (sinThetaMap U V) := by
  change N ((sinThetaEmbedding V U.subtypeₗᵢ) ∘ₗ
      LinearMap.adjoint U.subtypeₗᵢ.toLinearMap) = N (sinThetaMap U V)
  rw [adjoint_subtype_eq_orthogonalProjectionOnto]
  congr 1

/-- The transported residual of the reducing inclusion is bounded by the
ambient perturbation norm. -/
private theorem domainTransport_residual_le
    (N : UnitarilyInvariantNorm 𝕜 E)
    {A B : E →ₗ[𝕜] E} {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] (hU : Reduces A U) :
    (N.toRectangular.domainIsometryTransport U.subtypeₗᵢ)
        (residual B U.subtypeₗᵢ (A.restrict hU)) ≤ N (B - A) := by
  have hres : residual B U.subtypeₗᵢ (A.restrict hU) =
      (B - A) ∘ₗ U.subtype := by
    ext x
    change B (x : E) - A (x : E) = (B - A) (x : E)
    rfl
  change N ((residual B U.subtypeₗᵢ (A.restrict hU)) ∘ₗ
      LinearMap.adjoint U.subtypeₗᵢ.toLinearMap) ≤ N (B - A)
  rw [hres, adjoint_subtype_eq_orthogonalProjectionOnto]
  have hcomp : ((B - A) ∘ₗ U.subtype) ∘ₗ
      U.orthogonalProjectionOnto.toLinearMap =
      (B - A) ∘ₗ projection U := by
    ext x
    rfl
  rw [hcomp]
  calc
    N ((B - A) ∘ₗ projection U) ≤ N (B - A) * 1 :=
      N.apply_comp_le' zero_le_one fun x => by
        change ‖U.starProjection x‖ ≤ 1 * ‖x‖
        simpa using U.norm_starProjection_apply_le x
    _ = N (B - A) := mul_one _


/-- **Davis--Kahan `sin Θ`, perturbation form, every square UI norm.**

Lean proof route for a weaker agent:

1. Represent the perturbed reducing subspace by an isometric embedding, rewrite its residual as `(A-B)X`, apply the corresponding residual theorem, and contract composition by the embedding.
2. The operator-norm instance should be a thin specialization of `DavisKahan.SinTheta`.
-/
theorem sinTheta_perturbation_le
    (N : UnitarilyInvariantNorm 𝕜 E)
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : Reduces A U) (hV : Reduces B V)
    {a b δ : ℝ} (hδ : 0 < δ)
    (hgap : IntervalExteriorGap A B U V a b δ) :
    δ * N (sinThetaMap U V) ≤ N (B - A) := by
  let NU : RectangularUnitarilyInvariantNorm 𝕜 U E :=
    N.toRectangular.domainIsometryTransport U.subtypeₗᵢ
  have hM : (A.restrict hU).IsSymmetric := isSymmetric_restrict hA hU
  have hMspec : SpectrumIn (A.restrict hU) ⊤ (Set.Icc a b) :=
    (spectrumIn_restrict_iff A hU (Set.Icc a b)).2 hgap.1
  have hres :
      δ * NU (sinThetaEmbedding V U.subtypeₗᵢ) ≤
        NU (residual B U.subtypeₗᵢ (A.restrict hU)) :=
    sinTheta_residual_le (A := B) (U := V) (M := A.restrict hU)
      NU hB hV U.subtypeₗᵢ hM hδ hMspec hgap.2
  have hsin :
      NU (sinThetaEmbedding V U.subtypeₗᵢ) = N (sinThetaMap U V) :=
    domainTransport_sinThetaEmbedding_apply N U V
  have hresBound :
      NU (residual B U.subtypeₗᵢ (A.restrict hU)) ≤ N (B - A) :=
    domainTransport_residual_le (B := B) N hU
  calc
    δ * N (sinThetaMap U V) =
        δ * NU (sinThetaEmbedding V U.subtypeₗᵢ) := by rw [hsin]
    _ ≤ NU (residual B U.subtypeₗᵢ (A.restrict hU)) := hres
    _ ≤ N (B - A) := hresBound

/-- **Symmetric sharp `sin Θ` theorem.**  The full-space angle operator
contains both one-sided sine blocks.  For a general UI norm the constant-one
conclusion therefore requires a forward and reverse interval/exterior gap;
two arbitrary mixed spectral-distance gaps support only the separate
`π/2` theory.  A single interval/exterior gap controls only
`sinThetaMap U V` (except in the operator norm).  This is the finite
Davis--Kahan Proposition 6.1 configuration.

Lean proof route for a weaker agent:

1. Apply the one-sided interval/exterior theorem in both directions.
2. Identify the two directed blocks of `P_U-P_V` in the `U ⊕ Uᗮ` to
   `V ⊕ Vᗮ` coordinates.
3. Prove simultaneous Ky Fan prefix bounds for their direct sum and dominate
   the corresponding off-diagonal pinching of `B-A`; finish by Fan dominance.
-/
theorem sinAngleOperator_perturbation_le
    (N : UnitarilyInvariantNorm 𝕜 E)
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : Reduces A U) (hV : Reduces B V)
    {a b c d δ : ℝ} (hδ : 0 < δ)
    (hgapUV : IntervalExteriorGap A B U V a b δ)
    (hgapVU : IntervalExteriorGap B A V U c d δ) :
    δ * N (sinAngleOperator U V) ≤ N (B - A) := by
  sorry

/-- Ordered half-line perturbation form.

Lean proof route for a weaker agent:

1. Represent the perturbed reducing subspace by an isometric embedding, rewrite its residual as `(A-B)X`, apply the corresponding residual theorem, and contract composition by the embedding.
2. The operator-norm instance should be a thin specialization of `DavisKahan.SinTheta`.
-/
theorem sinTheta_perturbation_le_of_orderedGap
    (N : UnitarilyInvariantNorm 𝕜 E)
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : Reduces A U) (hV : Reduces B V)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : OrderedGap A U B Vᗮ δ) :
    δ * N (sinThetaMap U V) ≤ N (B - A) := by
  let NU : RectangularUnitarilyInvariantNorm 𝕜 U E :=
    N.toRectangular.domainIsometryTransport U.subtypeₗᵢ
  have hM : (A.restrict hU).IsSymmetric := isSymmetric_restrict hA hU
  have hgap' : OrderedGap (A.restrict hU) ⊤ B Vᗮ δ := by
    intro lam μ hlam hμ
    apply hgap lam μ
    · rw [← restrictedSpectrum_restrict A hU]
      exact hlam
    · exact hμ
  have hres :
      δ * NU (sinThetaEmbedding V U.subtypeₗᵢ) ≤
        NU (residual B U.subtypeₗᵢ (A.restrict hU)) :=
    sinTheta_residual_le_of_orderedGap
      (A := B) (U := V) (M := A.restrict hU) NU hB hV
      U.subtypeₗᵢ hM hδ hgap'
  have hsin :
      NU (sinThetaEmbedding V U.subtypeₗᵢ) = N (sinThetaMap U V) :=
    domainTransport_sinThetaEmbedding_apply N U V
  have hresBound :
      NU (residual B U.subtypeₗᵢ (A.restrict hU)) ≤ N (B - A) :=
    domainTransport_residual_le (B := B) N hU
  calc
    δ * N (sinThetaMap U V) =
        δ * NU (sinThetaEmbedding V U.subtypeₗᵢ) := by rw [hsin]
    _ ≤ NU (residual B U.subtypeₗᵢ (A.restrict hU)) := hres
    _ ≤ N (B - A) := hresBound

/-- Canonical spectral-projector statement with no eigenbasis in the API.

Lean proof route for a weaker agent:

1. Represent the perturbed reducing subspace by an isometric embedding, rewrite its residual as `(A-B)X`, apply the corresponding residual theorem, and contract composition by the embedding.
2. The operator-norm instance should be a thin specialization of `DavisKahan.SinTheta`.
-/
theorem sinTheta_spectralSubspace_le
    (N : UnitarilyInvariantNorm 𝕜 E)
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {a b δ : ℝ} (hδ : 0 < δ)
    (hAselected : SpectrumIn A (spectralSubspace A (Set.Icc a b)) (Set.Icc a b))
    (hBoutside : SpectrumIn B (spectralSubspace B (Set.Icc a b))ᗮ
      {lam | lam ∉ Set.Ioo (a - δ) (b + δ)}) :
    δ * N (sinThetaMap (spectralSubspace A (Set.Icc a b))
        (spectralSubspace B (Set.Icc a b))) ≤ N (B - A) := by
  exact sinTheta_perturbation_le N hA hB
    (reduces_spectralSubspace A (Set.Icc a b))
    (reduces_spectralSubspace B (Set.Icc a b)) hδ
    ⟨hAselected, hBoutside⟩

/-- **Sharp one-sided interval/exterior `sin Θ` bound in operator norm.**

The analytic estimate is delegated to the polar-absorption Sylvester theorem.
Finite dimensionality enters only through restriction of the two diagonal
blocks and the finite spectral bridge used by that theorem. -/
theorem opNorm_sinThetaMap_le_of_intervalGap
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : Reduces A U) (hV : Reduces B V)
    {a b δ : ℝ} (hδ : 0 < δ)
    (hgap : IntervalExteriorGap A B U V a b δ) :
    δ * ‖(sinThetaMap U V).toContinuousLinearMap‖ ≤
      ‖(B - A).toContinuousLinearMap‖ := by
  have hVperp : Reduces B Vᗮ := reduces_orthogonal_of_isSymmetric hB hV
  let AU : U →ₗ[𝕜] U := A.restrict hU
  let BVperp : Vᗮ →ₗ[𝕜] Vᗮ := B.restrict hVperp
  let X : U →ₗ[𝕜] Vᗮ :=
    Vᗮ.orthogonalProjectionOnto.toLinearMap ∘ₗ U.subtype
  let C : U →ₗ[𝕜] Vᗮ :=
    Vᗮ.orthogonalProjectionOnto.toLinearMap ∘ₗ ((B - A) ∘ₗ U.subtype)
  have hAU : AU.IsSymmetric := isSymmetric_restrict hA hU
  have hBVperp : BVperp.IsSymmetric := isSymmetric_restrict hB hVperp
  have hgap' : IntervalSylvesterGap BVperp AU a b δ := by
    constructor
    · exact (spectrumIn_restrict_iff A hU (Set.Icc a b)).2 hgap.1
    · exact (spectrumIn_restrict_iff B hVperp
        {lam | lam ∉ Set.Ioo (a - δ) (b + δ)}).2 hgap.2
  have hEq : BVperp ∘ₗ X - X ∘ₗ AU = C := by
    ext x
    have hcomm := projection_apply_comm_of_reduces hB hVperp (x : E)
    change Vᗮ.starProjection (B (x : E)) =
      B (Vᗮ.starProjection (x : E)) at hcomm
    change B (Vᗮ.starProjection (x : E)) -
        Vᗮ.starProjection (A (x : E)) =
      Vᗮ.starProjection ((B - A) (x : E))
    rw [← hcomm]
    simp only [LinearMap.sub_apply, map_sub]
  have hXnorm : ‖X.toContinuousLinearMap‖ =
      ‖(sinThetaMap U V).toContinuousLinearMap‖ := by
    apply le_antisymm
    · refine X.toContinuousLinearMap.opNorm_le_bound
        (norm_nonneg (sinThetaMap U V).toContinuousLinearMap) fun x => ?_
      have hxU : U.starProjection (x : E) = (x : E) :=
        U.starProjection_eq_self_iff.mpr x.2
      have hfull := (sinThetaMap U V).toContinuousLinearMap.le_opNorm (x : E)
      change ‖Vᗮ.starProjection (U.starProjection (x : E))‖ ≤
        ‖(sinThetaMap U V).toContinuousLinearMap‖ * ‖x‖ at hfull
      rw [hxU] at hfull
      exact hfull
    · refine (sinThetaMap U V).toContinuousLinearMap.opNorm_le_bound
        (norm_nonneg X.toContinuousLinearMap) fun x => ?_
      let ux : U := ⟨U.starProjection x, U.starProjection_apply_mem x⟩
      have hXu := X.toContinuousLinearMap.le_opNorm ux
      change ‖Vᗮ.starProjection (U.starProjection x)‖ ≤
        ‖X.toContinuousLinearMap‖ * ‖U.starProjection x‖ at hXu
      change ‖Vᗮ.starProjection (U.starProjection x)‖ ≤
        ‖X.toContinuousLinearMap‖ * ‖x‖
      exact hXu.trans (mul_le_mul_of_nonneg_left
        (U.norm_starProjection_apply_le x) (norm_nonneg X.toContinuousLinearMap))
  have hCnorm : ‖C.toContinuousLinearMap‖ ≤
      ‖(B - A).toContinuousLinearMap‖ := by
    refine C.toContinuousLinearMap.opNorm_le_bound
      (norm_nonneg (B - A).toContinuousLinearMap) fun x => ?_
    change ‖Vᗮ.starProjection ((B - A) (x : E))‖ ≤
      ‖(B - A).toContinuousLinearMap‖ * ‖x‖
    exact (Vᗮ.norm_starProjection_apply_le ((B - A) (x : E))).trans
      ((B - A).toContinuousLinearMap.le_opNorm (x : E))
  have hSylvester := opNorm_sylvester_le_of_intervalGap
    hBVperp hAU hδ hgap' hEq
  rw [hXnorm] at hSylvester
  exact hSylvester.trans hCnorm

/-- Difference-of-projectors operator-norm form.

Lean proof route for a weaker agent:

1. Combine the operator-norm one-sided `sin Θ` theorem with the equal-rank projection/cross-gap identity.
2. The analytic bound should specialize the supported Davis--Kahan core; only the finite rank bridge remains local.
-/
theorem opNorm_projection_sub_projection_le
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : Reduces A U) (hV : Reduces B V)
    (hrank : finrank 𝕜 U = finrank 𝕜 V)
    {a b δ : ℝ} (hδ : 0 < δ)
    (hgap : IntervalExteriorGap A B U V a b δ) :
    δ * ‖(projection U - projection V).toContinuousLinearMap‖ ≤
      ‖(B - A).toContinuousLinearMap‖ := by
  rw [opNorm_projection_sub_eq_opNorm_sinThetaMap U V hrank]
  exact opNorm_sinThetaMap_le_of_intervalGap hA hB hU hV hδ hgap

/-- **Canonical finite spectral-projector Davis--Kahan theorem.**

This is the standard interval/exterior projector statement with canonical
spectral subspaces.  The equal-rank hypothesis is exactly what turns the
one-sided cross-projection estimate into the norm of the full projector
difference. -/
theorem opNorm_spectralProjection_sub_spectralProjection_le
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {a b δ : ℝ} (hδ : 0 < δ)
    (hrank : finrank 𝕜 (spectralSubspace A (Set.Icc a b)) =
      finrank 𝕜 (spectralSubspace B (Set.Icc a b)))
    (hAselected : SpectrumIn A (spectralSubspace A (Set.Icc a b)) (Set.Icc a b))
    (hBoutside : SpectrumIn B (spectralSubspace B (Set.Icc a b))ᗮ
      {lam | lam ∉ Set.Ioo (a - δ) (b + δ)}) :
    δ * ‖(spectralProjection A (Set.Icc a b) -
        spectralProjection B (Set.Icc a b)).toContinuousLinearMap‖ ≤
      ‖(B - A).toContinuousLinearMap‖ := by
  simpa [spectralProjection, projection] using
    opNorm_projection_sub_projection_le hA hB
      (reduces_spectralSubspace A (Set.Icc a b))
      (reduces_spectralSubspace B (Set.Icc a b))
      hrank hδ ⟨hAselected, hBoutside⟩

/-- Frobenius form.

Lean proof route for a weaker agent:

1. Instantiate the every-UI perturbation theorem with the existing Frobenius or Ky Fan norm and simplify the evaluation theorem.
2. Instantiate `sinTheta_perturbation_le` with `UnitarilyInvariantNorm.frobenius`.
3. Rewrite the norm application with the Frobenius evaluation lemma and close by `simpa`.
-/
theorem frobenius_sinTheta_le
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : Reduces A U) (hV : Reduces B V)
    {a b δ : ℝ} (hδ : 0 < δ)
    (hgap : IntervalExteriorGap A B U V a b δ) :
    δ * UnitarilyInvariantNorm.frobenius 𝕜 E (sinThetaMap U V) ≤
      UnitarilyInvariantNorm.frobenius 𝕜 E (B - A) := by
  exact sinTheta_perturbation_le (UnitarilyInvariantNorm.frobenius 𝕜 E)
    hA hB hU hV hδ hgap

/-- Ky Fan form, simultaneously controlling every singular-value prefix.

Lean proof route for a weaker agent:

1. Instantiate the every-UI perturbation theorem with the existing Frobenius or Ky Fan norm and simplify the evaluation theorem.
2. Instantiate `sinTheta_perturbation_le` with the finite Ky Fan UI norm.
3. Rewrite both applications using the Ky Fan evaluation theorem.
-/
theorem kyFan_sinTheta_le
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : Reduces A U) (hV : Reduces B V)
    {a b δ : ℝ} (hδ : 0 < δ)
    (hgap : IntervalExteriorGap A B U V a b δ) (k : ℕ) :
    δ * kyFanSum k (sinThetaMap U V) ≤ kyFanSum k (B - A) := by
  let NK : UnitarilyInvariantNorm 𝕜 E :=
    (RectangularUnitarilyInvariantNorm.kyFan
      (𝕜 := 𝕜) (E := E) (F := E) k).toSquare
  have h := sinTheta_perturbation_le NK hA hB hU hV hδ hgap
  simpa [NK, RectangularUnitarilyInvariantNorm.toSquare,
    RectangularUnitarilyInvariantNorm.kyFan_apply,
    RectangularUnitarilyInvariantNorm.rectangularKyFanSum,
    kyFanSum_eq_sum_fin] using h

/-- General two-sided spectral separation with the `π/2` constant.  The
ambient transport proof is complete; the only open analytic input is the Ky Fan
separated reciprocal-multiplier theorem in `Sylvester.lean`.

Lean proof route for a weaker agent:

1. Use the residual equation and the general `π/2` Sylvester estimate.
2. Prefer the experimental general-separation theorem for operator norm and retain finite Fan dominance for arbitrary UI norms.
-/
theorem sinTheta_perturbation_le_of_spectralDistance
    (N : UnitarilyInvariantNorm 𝕜 E)
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : Reduces A U) (hV : Reduces B V)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : SpectraSeparated A U B Vᗮ δ) :
    δ * N (sinThetaMap U V) ≤ (Real.pi / 2) * N (B - A) := by
  let NU : RectangularUnitarilyInvariantNorm 𝕜 U E :=
    N.toRectangular.domainIsometryTransport U.subtypeₗᵢ
  have hM : (A.restrict hU).IsSymmetric := isSymmetric_restrict hA hU
  have hgap' : SpectraSeparated (A.restrict hU) ⊤ B Vᗮ δ := by
    intro lam μ hlam hμ
    apply hgap lam μ
    · rw [← restrictedSpectrum_restrict A hU]
      exact hlam
    · exact hμ
  have hres :
      δ * NU (sinThetaEmbedding V U.subtypeₗᵢ) ≤
        (Real.pi / 2) * NU (residual B U.subtypeₗᵢ (A.restrict hU)) :=
    sinTheta_residual_le_of_spectralDistance
      (A := B) (U := V) (M := A.restrict hU) NU hB hV
      U.subtypeₗᵢ hM hδ hgap'
  have hsin :
      NU (sinThetaEmbedding V U.subtypeₗᵢ) = N (sinThetaMap U V) :=
    domainTransport_sinThetaEmbedding_apply N U V
  have hresBound :
      NU (residual B U.subtypeₗᵢ (A.restrict hU)) ≤ N (B - A) :=
    domainTransport_residual_le (B := B) N hU
  calc
    δ * N (sinThetaMap U V) =
        δ * NU (sinThetaEmbedding V U.subtypeₗᵢ) := by rw [hsin]
    _ ≤ (Real.pi / 2) *
        NU (residual B U.subtypeₗᵢ (A.restrict hU)) := hres
    _ ≤ (Real.pi / 2) * N (B - A) :=
      mul_le_mul_of_nonneg_left hresBound (by positivity)

end DavisKahanTheory
end ForMathlib
