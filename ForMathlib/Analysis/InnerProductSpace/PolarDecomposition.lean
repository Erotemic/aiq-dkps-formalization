/-
Staged for Mathlib: a new `Mathlib/Analysis/InnerProductSpace/PolarDecomposition.lean`.

Sub-dev III of the operator polar decomposition project — COMPLETE (sorry-free, axiom-clean:
`propext, Classical.choice, Quot.sound`). Tickets PD-08..PD-12.
-/

import ForMathlib.Analysis.InnerProductSpace.PositiveSqrt
import ForMathlib.Analysis.InnerProductSpace.PartialIsometry
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.StarOrder

/-! # Operator polar decomposition `A = U |A|` (Sub-dev III)

For an operator `A` on a finite-dimensional inner product space, `A = U |A|`, where
`|A| = (A⋆A)^{1/2}` is the modulus and `U` is a partial isometry with initial space `(ker A)ᗮ`
and `ker U = ker A`. When `A` is invertible, `U` is unitary and `U = A |A|⁻¹`.

* **RCLike route** (`E →ₗ[𝕜] E`, ℝ and ℂ): `|A|` built from the spectral square root
  (`ForMathlib.IsPositive.sqrt`). Serves Davis's real-symmetric application directly.
* **CFC route / headline** (`E →L[ℂ] E`): `|A| = CFC.abs A` literally, transported across the
  definitional `LinearMap ↔ ContinuousLinearMap` adjoint bridge.

Sources: Horn & Johnson, *Matrix Analysis* 2nd ed., **Thm 7.3.1** (statement; `A = UQ`,
`Q = (A⋆A)^{1/2}`, `U` unitary, unique iff nonsingular). Conway, *A Course in Functional Analysis*
2nd ed., **VI.3.9** (the partial-isometry construction `A = U|A|`, `ker U = ker A` — the route
mathlib can follow, since HJ's SVD proof route is unavailable: mathlib has no SVD factorization).
-/

namespace ForMathlib

open scoped InnerProductSpace
open LinearMap InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-! ### The modulus `|A|` (RCLike, LinearMap) -/

/-- The **modulus** `|A| = (A⋆A)^{1/2}` of an operator, via the spectral square root of the
positive operator `A⋆A`. HJ 7.3.1 (`Q = (A⋆A)^{1/2}`). -/
noncomputable def abs (A : E →ₗ[𝕜] E) : E →ₗ[𝕜] E :=
  (LinearMap.isPositive_adjoint_comp_self A).sqrt

@[simp] theorem isPositive_abs (A : E →ₗ[𝕜] E) : (abs A).IsPositive :=
  (LinearMap.isPositive_adjoint_comp_self A).sqrt_isPositive

/-- `|A|² = A⋆A`. -/
theorem abs_mul_self (A : E →ₗ[𝕜] E) : abs A ∘ₗ abs A = A.adjoint ∘ₗ A :=
  (LinearMap.isPositive_adjoint_comp_self A).sqrt_mul_self

/-- **The polar norm identity** `‖|A| x‖ = ‖A x‖`. Not in HJ (SVD route); this is the seed of the
isometry route (Conway VI.3.9). -/
theorem norm_abs_apply (A : E →ₗ[𝕜] E) (x : E) : ‖abs A x‖ = ‖A x‖ := by
  have hsq : ‖abs A x‖ ^ 2 = ‖A x‖ ^ 2 :=
    ((LinearMap.isPositive_adjoint_comp_self A).sq_norm_sqrt_apply x).trans <| by
      rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left, ← norm_sq_eq_re_inner (𝕜 := 𝕜)]
  rw [← Real.sqrt_sq (norm_nonneg (abs A x)), ← Real.sqrt_sq (norm_nonneg (A x)), hsq]

/-- `ker |A| = ker A`. -/
theorem ker_abs (A : E →ₗ[𝕜] E) : ker (abs A) = ker A :=
  ((LinearMap.isPositive_adjoint_comp_self A).ker_sqrt).trans
    (LinearMap.ker_adjoint_comp_self A)

/-- `range |A| = (ker A)ᗮ` — the initial space of the polar factor. -/
theorem range_abs (A : E →ₗ[𝕜] E) : range (abs A) = (ker A)ᗮ := by
  rw [← ker_abs A, LinearMap.orthogonal_ker, (isPositive_abs A).adjoint_eq]

/-- Elementwise form of `range_abs`: every value of the modulus lies in the initial space. -/
theorem abs_apply_mem_orthogonal_ker (A : E →ₗ[𝕜] E) (x : E) : abs A x ∈ (ker A)ᗮ := by
  rw [← range_abs A]
  exact LinearMap.mem_range_self (abs A) x

/-! ### The polar factor `U` and the decomposition -/

/-- The restriction of the modulus `|A|` to `(ker A)ᗮ = range |A|`, as a linear automorphism of
`(ker A)ᗮ` — the invertible core of `|A|`, which the polar factor inverts. -/
private noncomputable def absRestrict (A : E →ₗ[𝕜] E) : ↥((ker A)ᗮ) ≃ₗ[𝕜] ↥((ker A)ᗮ) :=
  LinearEquiv.ofBijective ((abs A).restrict fun x _ => abs_apply_mem_orthogonal_ker A x) <| by
    have hinj : Function.Injective
        ((abs A).restrict (p := (ker A)ᗮ) fun x _ => abs_apply_mem_orthogonal_ker A x) := by
      intro y z hyz
      have habs : abs A ↑y = abs A ↑z := congrArg Subtype.val hyz
      have hker : (↑y - ↑z : E) ∈ ker (abs A) := by
        rw [LinearMap.mem_ker, map_sub, habs, sub_self]
      rw [ker_abs A] at hker
      have hmem : (↑y - ↑z : E) ∈ (ker A)ᗮ := Submodule.sub_mem _ y.2 z.2
      exact Subtype.ext <| sub_eq_zero.mp <|
        Submodule.disjoint_def.mp (Submodule.orthogonal_disjoint (ker A)) _ hker hmem
    exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

/-- The **polar factor** `U` of `A`: the partial isometry that is the isometry `|A| x ↦ A x` on
`range |A| = (ker A)ᗮ`, extended by `0` on `ker A`. Conway VI.3.9. -/
noncomputable def polarFactor (A : E →ₗ[𝕜] E) : E →ₗ[𝕜] E :=
  A ∘ₗ ((ker A)ᗮ).subtype ∘ₗ (absRestrict A).symm.toLinearMap
    ∘ₗ (((ker A)ᗮ).orthogonalProjectionOnto : E →L[𝕜] ↥((ker A)ᗮ)).toLinearMap

/-- The defining property of the polar factor: `U (|A| x) = A x`. -/
theorem polarFactor_apply_abs_apply (A : E →ₗ[𝕜] E) (x : E) :
    polarFactor A (abs A x) = A x := by
  have habs : abs A x ∈ (ker A)ᗮ := abs_apply_mem_orthogonal_ker A x
  have hproj : ((ker A)ᗮ).orthogonalProjectionOnto (abs A x) = ⟨abs A x, habs⟩ :=
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self ⟨abs A x, habs⟩
  show A ↑((absRestrict A).symm (((ker A)ᗮ).orthogonalProjectionOnto (abs A x))) = A x
  rw [hproj]
  have h1 : abs A ↑((absRestrict A).symm ⟨abs A x, habs⟩) = abs A x :=
    congrArg Subtype.val ((absRestrict A).apply_symm_apply ⟨abs A x, habs⟩)
  have hker : (↑((absRestrict A).symm ⟨abs A x, habs⟩) - x : E) ∈ ker (abs A) := by
    rw [LinearMap.mem_ker, map_sub, h1, sub_self]
  rw [ker_abs A] at hker
  have h2 := LinearMap.mem_ker.mp hker
  rwa [map_sub, sub_eq_zero] at h2

/-- **Polar decomposition** `A = U |A|`. Conway VI.3.9; HJ 7.3.1. -/
theorem polar_decomposition (A : E →ₗ[𝕜] E) :
    A = polarFactor A ∘ₗ abs A := by
  ext x
  exact (polarFactor_apply_abs_apply A x).symm

/-- `ker U = ker A`. -/
theorem ker_polarFactor (A : E →ₗ[𝕜] E) : ker (polarFactor A) = ker A := by
  ext x
  simp only [LinearMap.mem_ker]
  constructor
  · intro hUx
    have hyker : (↑((absRestrict A).symm (((ker A)ᗮ).orthogonalProjectionOnto x)) : E) ∈ ker A :=
      LinearMap.mem_ker.mpr hUx
    have hy0 : ((absRestrict A).symm (((ker A)ᗮ).orthogonalProjectionOnto x)) = 0 :=
      Subtype.ext <| Submodule.disjoint_def.mp (Submodule.orthogonal_disjoint (ker A)) _
        hyker ((absRestrict A).symm _).2
    have hproj : ((ker A)ᗮ).orthogonalProjectionOnto x = 0 := by
      have := congrArg (absRestrict A) hy0
      rwa [LinearEquiv.apply_symm_apply, map_zero] at this
    rw [Submodule.orthogonalProjectionOnto_eq_zero_iff, Submodule.orthogonal_orthogonal] at hproj
    exact LinearMap.mem_ker.mp hproj
  · intro hx
    have hproj : ((ker A)ᗮ).orthogonalProjectionOnto x = 0 :=
      Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr
        (by rwa [Submodule.orthogonal_orthogonal])
    show A ↑((absRestrict A).symm (((ker A)ᗮ).orthogonalProjectionOnto x)) = 0
    rw [hproj, map_zero]
    simp

/-- `range U = range A` — the final space of the polar factor. -/
theorem range_polarFactor (A : E →ₗ[𝕜] E) : range (polarFactor A) = range A := by
  refine le_antisymm (fun y hy => ?_) (fun y hy => ?_)
  · obtain ⟨x, rfl⟩ := hy
    exact ⟨_, rfl⟩
  · obtain ⟨x, rfl⟩ := hy
    exact ⟨abs A x, polarFactor_apply_abs_apply A x⟩

/-- `U` restricted to `range |A| = (ker A)ᗮ` is isometric. -/
theorem norm_polarFactor_apply_of_mem {A : E →ₗ[𝕜] E} {x : E} (hx : x ∈ (ker A)ᗮ) :
    ‖polarFactor A x‖ = ‖x‖ := by
  have hproj : ((ker A)ᗮ).orthogonalProjectionOnto x = ⟨x, hx⟩ :=
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self ⟨x, hx⟩
  show ‖A ↑((absRestrict A).symm (((ker A)ᗮ).orthogonalProjectionOnto x))‖ = ‖x‖
  rw [hproj, ← norm_abs_apply,
    show abs A ↑((absRestrict A).symm ⟨x, hx⟩) = x from
      congrArg Subtype.val ((absRestrict A).apply_symm_apply ⟨x, hx⟩)]

/-- `U` is a partial isometry. -/
theorem isPartialIsometry_polarFactor (A : E →ₗ[𝕜] E) :
    IsPartialIsometry (polarFactor A) :=
  isPartialIsometry_of_isometryOn (K := (ker A)ᗮ)
    (by rw [ker_polarFactor, Submodule.orthogonal_orthogonal])
    (fun _ hx => norm_polarFactor_apply_of_mem hx)

/-! ### Invertible case: `U` is unitary -/

/-- When `A` is invertible, `|A|` is invertible and the polar factor is the unitary `U = A |A|⁻¹`,
packaged as a `LinearIsometryEquiv`. HJ 7.3.1(b) (`U` uniquely determined if `A` nonsingular). -/
noncomputable def polarUnitaryEquiv {A : E →ₗ[𝕜] E} (hA : IsUnit A) : E ≃ₗᵢ[𝕜] E :=
  have hinj : Function.Injective (polarFactor A) := by
    rw [← LinearMap.ker_eq_bot, ker_polarFactor]
    exact (LinearMap.isUnit_iff_ker_eq_bot A).mp hA
  { LinearEquiv.ofBijective (polarFactor A)
      ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩ with
    norm_map' := fun x => norm_polarFactor_apply_of_mem <| by
      rw [(LinearMap.isUnit_iff_ker_eq_bot A).mp hA, Submodule.bot_orthogonal_eq_top]
      exact Submodule.mem_top }

@[simp] theorem coe_polarUnitaryEquiv {A : E →ₗ[𝕜] E} (hA : IsUnit A) :
    ((polarUnitaryEquiv hA : E →ₗ[𝕜] E)) = polarFactor A :=
  rfl

theorem polar_decomposition_of_isUnit {A : E →ₗ[𝕜] E} (hA : IsUnit A) :
    A = (polarUnitaryEquiv hA : E →ₗ[𝕜] E) ∘ₗ abs A := by
  rw [coe_polarUnitaryEquiv]
  exact polar_decomposition A

/-! ### CFC bridge — the ℂ / ContinuousLinearMap headline (`|A| = CFC.abs A`) -/

section CFCBridge

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [CompleteSpace H]

/-- The spectral modulus agrees with the C⋆-algebra `CFC.abs` on `E →L[ℂ] E`, transported across
the definitional `LinearMap ↔ ContinuousLinearMap` adjoint bridge (`adjoint_toContinuousLinearMap`
is `rfl`). This is what makes the decomposition literally "via CFC". -/
theorem abs_toContinuousLinearMap_eq_cfcAbs (A : H →ₗ[ℂ] H) :
    (abs A).toContinuousLinearMap = CFC.abs A.toContinuousLinearMap := by
  refine (CFC.sqrt_unique ?_ ?_).symm
  · -- `|A|.toCLM * |A|.toCLM = star A.toCLM * A.toCLM`, transported from `abs_mul_self` across
    -- the definitional `LinearMap ↔ ContinuousLinearMap` adjoint bridge.
    ext x
    exact congrArg (fun f : H →ₗ[ℂ] H => f x) (abs_mul_self A)
  · exact (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
      ((LinearMap.isPositive_toContinuousLinearMap_iff (abs A)).mpr (isPositive_abs A))

/-- **Headline (via CFC):** every `A : H →L[ℂ] H` factors as `A = U ∘L CFC.abs A` with `U` a
partial isometry. -/
theorem continuousLinearMap_polar_decomposition (A : H →L[ℂ] H) :
    ∃ U : H →L[ℂ] H, IsPartialIsometry U ∧ A = U ∘L CFC.abs A := by
  refine ⟨(polarFactor (A : H →ₗ[ℂ] H)).toContinuousLinearMap, ?_, ?_⟩
  · -- transport `IsPartialIsometry` across the (definitional) star-monoid bridge
    have h := isPartialIsometry_polarFactor (A : H →ₗ[ℂ] H)
    ext x
    exact congrArg (fun f : H →ₗ[ℂ] H => f x) h
  · rw [show CFC.abs A = CFC.abs ((A : H →ₗ[ℂ] H)).toContinuousLinearMap from rfl,
      ← abs_toContinuousLinearMap_eq_cfcAbs (A : H →ₗ[ℂ] H)]
    ext x
    exact congrArg (fun f : H →ₗ[ℂ] H => f x) (polar_decomposition (A : H →ₗ[ℂ] H))

end CFCBridge

end ForMathlib
