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
  sorry

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
  sorry

/-- General disjoint-spectrum residual form.  The `π/2` loss is the
Bhatia--Davis--McIntosh extension, not the sharp interval/exterior theorem.

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
  sorry

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
  sorry

/-- **Symmetric `sin Θ` theorem.**  The full-space angle operator contains
both one-sided sine blocks.  Consequently the sharp full-space conclusion
requires the reverse mixed gap as well as the forward one; a single mixed gap
controls only `sinThetaMap U V` (except in the operator norm).  This is
Davis--Kahan Proposition 6.1.

Lean proof route for a weaker agent:

1. Apply the one-sided theorem in both directions, identify the two sine blocks of the full angle operator, and use the finite pinching/symmetric-gauge argument.
2. For operator norm, this should specialize the supported `DavisKahan.SinTheta` module.
-/
theorem sinAngleOperator_perturbation_le
    (N : UnitarilyInvariantNorm 𝕜 E)
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : Reduces A U) (hV : Reduces B V)
    {δ : ℝ} (hδ : 0 < δ)
    (hgapUV : HybridGap A B U V δ)
    (hgapVU : HybridGap B A V U δ) :
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
  sorry

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
  sorry

/-- General two-sided spectral separation with the `π/2` constant.

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
  sorry

end DavisKahanTheory
end ForMathlib
