/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import ForMathlib.Analysis.InnerProductSpace.DavisKahanTheory.RectangularUINorm

/-!
# Compressions, Ritz maps, and residuals

This file scaffolds the coordinate-free numerical-analysis side of the
Davis--Kahan theory.  An isometric embedding `X : F →ₗᵢ[𝕜] E` represents an
orthonormal approximate basis.  Its compression and residual are

`M = X⋆ A X`, `R = A X - X M`.

Literature map:

* `ForMathlib/prose/Davis-Kahan-1970-part-III-core-arguments.tex`,
  Sections 2 and 5.
* Davis--Kahan (1970), Sections 1--2 and the block equations preceding the
  `sin Θ` and `tan Θ` theorems.
* `ForMathlib/prose/Yu-Wang-Samworth-2014-core-arguments.tex`,
  Sections "The proof as an upper/lower sandwich" and
  "Minimal supporting lemmas".
-/


/-! ## Remaining construction plan

The Galerkin/Ritz layer is complete: the adjoint of an isometric embedding
is a left inverse, the Ritz residual is orthogonal to the trial subspace,
vanishing is equivalent to invariance, residuals are unitary-coordinate
covariant, and the Frobenius residual satisfies the exact Pythagorean identity
and Ritz minimality.  The sine embedding now has its correctly directed
principal-sine singular-value dictionary, and transversality is identified with
injectivity of the cosine block.

The remaining work in this file is to define the tangent and double-angle
embeddings with honest totalization.  Under transversality,
`tanThetaEmbedding` should be the sine block composed with the inverse of the
cosine block.  Define `sinTwoThetaEmbedding` polynomially as
`2 sinTheta cosTheta`; define `tanTwoThetaEmbedding` from the corresponding
numerator and the invertible `cos(2 Theta)` block under quarter-turn avoidance.
-/


/-! ## Weak-agent execution plan: residual geometry and total angle embeddings

### A. Do not hide partial inverses inside unconditional definitions

Introduce hypothesis-carrying helpers first:

* `tanThetaEmbeddingOfTransverse U X htrans`;
* `tanTwoThetaEmbeddingOfQuarterTurn U X hquarter`.

For the cosine block, use the coordinate map `cosThetaEmbedding U X : F →ₗ E`.
Its codomain is ambient `E`, so first corestrict it to `U`; transversality gives
injectivity, and equality of finite ranks on the represented subspace gives
bijectivity onto its range.  Build the inverse with `LinearEquiv.ofBijective`
and compose it with the sine block.  Keep subtype coercions in named maps such
as `cosThetaToSubspace`; otherwise `change` goals become unmanageable.

To preserve the present total API, define `tanThetaEmbedding` by
`if h : IsTransverse ... then tanThetaEmbeddingOfTransverse ... h else 0`.
Add an `_eq_of_transverse` simp theorem and make every mathematical theorem use
that lemma.  Use the same pattern for the quarter-turn denominator in
`tanTwoThetaEmbedding`.  Never use an arbitrary classical inverse without an
explicit fallback branch, because downstream simplification would then depend
on proof irrelevance and hidden choices.

### B. Double-angle sine should be polynomial

Define `sinTwoThetaEmbedding` without inverses.  In principal coordinates it
is `2 sin θ cos θ`; at the map level use the sine block followed by the adjoint
or cosine Gram factor that has the same singular values.  First prove a Gram
identity for the chosen formula, then identify its singular values.  Keep this
construction independent of transversality.

### C. Galerkin orthogonality and Pythagoras

Prove a reusable isometry identity

`X.toLinearMap.adjoint ∘ₗ X.toLinearMap = LinearMap.id`.

Then `adjoint_comp_ritzResidual_eq_zero` should be a one-page composition
calculation.  For the Frobenius theorem, first prove the pointwise decomposition

`residual A X M = ritzResidual A X + X.toLinearMap ∘ₗ (compression A X - M)`.

Evaluate on an arbitrary orthonormal basis of `F`.  The cross term vanishes by
Galerkin orthogonality and `LinearMap.adjoint_inner_left`; sum the scalar
Pythagorean identities, then rewrite with `frobenius_apply`.  Derive minimality
from the squared identity using nonnegativity; do not start with square roots.

### D. Singular values of the sine embedding

Use the isometric equivalence from `F` onto `approximateSubspace X`:
corestrict `X.toLinearMap` to its range, prove bijectivity, and package it as a
`LinearIsometryEquiv`.  Precomposition by this equivalence does not change
singular values.  After transport, the map is exactly the canonical cross
projection from `approximateSubspace X` into `Uᗮ`; apply the existing
`singularValues_sinThetaMap` theorem.  Prove the map equality with
`LinearMap.ext` before rewriting singular values.

### E. Residual perturbation bound

After `residual_eq_perturbation_comp`, apply the rectangular right ideal
inequality.  The continuous operator norm of an isometric embedding is one
when `F` is nontrivial; split the subsingleton case first.  Avoid proving a new
singular-value estimate here.

### F. Signature checkpoint

`tanThetaEmbedding_defined_iff` currently describes injectivity of the cosine
block, not whether the totalized definition exists.  Keep it as a kernel
criterion and rename it later if desired.  The actual computation theorem
should be `_eq_of_transverse`; downstream agents must not unfold the `if`
branch manually.
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

/-- Compression of `A` to the isometric coordinate space of `X`. -/
noncomputable def compression (A : E →ₗ[𝕜] E) (X : F →ₗᵢ[𝕜] E) :
    F →ₗ[𝕜] F :=
  X.toLinearMap.adjoint ∘ₗ A ∘ₗ X.toLinearMap

/-- Residual of an approximate invariant pair `(X,M)`. -/
noncomputable def residual (A : E →ₗ[𝕜] E) (X : F →ₗᵢ[𝕜] E)
    (M : F →ₗ[𝕜] F) : F →ₗ[𝕜] E :=
  A ∘ₗ X.toLinearMap - X.toLinearMap ∘ₗ M

/-- Galerkin/Ritz residual. -/
noncomputable def ritzResidual (A : E →ₗ[𝕜] E) (X : F →ₗᵢ[𝕜] E) :
    F →ₗ[𝕜] E :=
  residual A X (compression A X)

/-- The represented approximate subspace. -/
def approximateSubspace (X : F →ₗᵢ[𝕜] E) : Submodule 𝕜 E :=
  LinearMap.range X.toLinearMap

/-- Sine map from approximate coordinates into the orthogonal complement of
an exact subspace. -/
noncomputable def sinThetaEmbedding (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E) : F →ₗ[𝕜] E :=
  complementaryProjection U ∘ₗ X.toLinearMap

/-- Cosine map from approximate coordinates into an exact subspace. -/
noncomputable def cosThetaEmbedding (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E) : F →ₗ[𝕜] E :=
  projection U ∘ₗ X.toLinearMap

/-! Construction route: build all three remaining coordinate maps from the cosine/sine blocks
above.  Under transversality, invert `cosThetaEmbedding` on its range and define
tangent as sine after that inverse.  Define double-angle sine polynomially as
twice the sine/cosine cross term.  Define double-angle tangent only after
quarter-turn avoidance makes the corresponding cosine block invertible.  Each
definition should come with a singular-value identification before it is used
in a norm theorem. -/

/-- Tangent map in approximate coordinates. -/
noncomputable def tanThetaEmbedding (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E) : F →ₗ[𝕜] E := by
  sorry

/-- Double-angle sine map in approximate coordinates. -/
noncomputable def sinTwoThetaEmbedding (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E) : F →ₗ[𝕜] E := by
  sorry

/-- Double-angle tangent map in approximate coordinates. -/
noncomputable def tanTwoThetaEmbedding (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E) : F →ₗ[𝕜] E := by
  sorry

/-- No principal angle between `U` and `range X` is `π/4`. -/
def AvoidsQuarterTurnEmbedding (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E) : Prop :=
  AvoidsQuarterTurn U (approximateSubspace X)

/-- Compression of a symmetric operator is symmetric.

Lean proof route for a weaker agent:

1. Unfold `compression` and the definition of `LinearMap.IsSymmetric`.
2. Reassociate compositions and move adjoints through them; rewrite the ambient adjoint using `hA`.
3. Evaluate both sides on arbitrary vectors and simplify the isometry inner-product identities.
-/
theorem isSymmetric_compression {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    (X : F →ₗᵢ[𝕜] E) : (compression A X).IsSymmetric := by
  intro p q
  simp only [compression, LinearMap.comp_apply]
  rw [LinearMap.adjoint_inner_left, hA, ← LinearMap.adjoint_inner_right]

/-- The adjoint of an isometric embedding is a left inverse. -/
@[simp] theorem adjoint_comp_linearIsometry_eq_id (X : F →ₗᵢ[𝕜] E) :
    X.toLinearMap.adjoint ∘ₗ X.toLinearMap = LinearMap.id := by
  ext x
  refine ext_inner_right 𝕜 fun y => ?_
  simp only [LinearMap.comp_apply, LinearMap.id_apply]
  rw [LinearMap.adjoint_inner_left]
  change ⟪X x, X y⟫_𝕜 = ⟪x, y⟫_𝕜
  exact X.inner_map_map x y

/-- The Ritz residual is orthogonal to the trial subspace.

Lean proof route for a weaker agent:

1. Unfold the Ritz residual and compression, then simplify `X⋆X = I` for a linear isometry.
2. Reassociate compositions before rewriting the isometry identity `X⋆X = I`.
3. Finish by `LinearMap.ext` if the simplifier does not normalize composition subtraction.
-/
theorem adjoint_comp_ritzResidual_eq_zero (A : E →ₗ[𝕜] E)
    (X : F →ₗᵢ[𝕜] E) :
    X.toLinearMap.adjoint ∘ₗ ritzResidual A X = 0 := by
  ext x
  refine ext_inner_right 𝕜 fun y => ?_
  simp only [LinearMap.comp_apply, ritzResidual, residual, compression,
    LinearMap.sub_apply, LinearMap.zero_apply, inner_zero_left]
  rw [LinearMap.adjoint_inner_left, inner_sub_left]
  change ⟪A (X x), X y⟫_𝕜 -
      ⟪X (X.toLinearMap.adjoint (A (X x))), X y⟫_𝕜 = 0
  apply sub_eq_zero.mpr
  exact (LinearMap.adjoint_inner_left X.toLinearMap y (A (X x))).symm |>.trans
    (X.inner_map_map (X.toLinearMap.adjoint (A (X x))) y).symm

/-- Vanishing Ritz residual is equivalent to invariance of the represented
subspace.

Lean proof route for a weaker agent:

1. Forward: unfold `ritzResidual`; from residual zero derive `A ∘ X = X ∘ compression A X`, then apply this equality to a range witness.
2. Reverse: use `hReduces` on `X y`, choose a coordinate witness for `A (X y)`, and recover that witness by applying `X.adjoint` and `X⋆X=I`.
3. Prove the operator equality by `LinearMap.ext`, then fold it back into `ritzResidual = 0`.
-/
theorem ritzResidual_eq_zero_iff_reduces {A : E →ₗ[𝕜] E}
    (X : F →ₗᵢ[𝕜] E) :
    ritzResidual A X = 0 ↔ Reduces A (approximateSubspace X) := by
  constructor
  · intro hR x hx
    rcases hx with ⟨y, rfl⟩
    have hpoint := LinearMap.congr_fun hR y
    change A (X y) - X (compression A X y) = 0 at hpoint
    exact ⟨compression A X y, (sub_eq_zero.mp hpoint).symm⟩
  · intro hred
    ext y
    have hmem : A (X y) ∈ approximateSubspace X :=
      hred (X y) ⟨y, rfl⟩
    rcases hmem with ⟨z, hz⟩
    have hz' : A (X.toLinearMap y) = X.toLinearMap z := hz.symm
    have hcomp : compression A X y = z := by
      change X.toLinearMap.adjoint (A (X.toLinearMap y)) = z
      rw [hz']
      have hleft := LinearMap.congr_fun (adjoint_comp_linearIsometry_eq_id X) z
      change X.toLinearMap.adjoint (X.toLinearMap z) = z at hleft
      exact hleft
    change A (X.toLinearMap y) - X.toLinearMap (compression A X y) = 0
    rw [hcomp, hz', sub_self]

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
/-- Residuals transform naturally under a unitary change of approximate
coordinates.

Lean proof route for a weaker agent:

1. Unfold `residual` on both sides and expand the transformed coordinate operator.
2. Reassociate every composition so `V.toLinearMap ∘ V.symm.toLinearMap` and the reverse product become visible.
3. Cancel the unitary inverse pairs, then finish by `LinearMap.ext` and `simp` on addition/subtraction.
-/
theorem residual_comp_unitary (A : E →ₗ[𝕜] E) (X : F →ₗᵢ[𝕜] E)
    (M : F →ₗ[𝕜] F) (V : F ≃ₗᵢ[𝕜] F) :
    residual A (X.comp V.toLinearIsometry)
        (V.symm.toLinearMap ∘ₗ M ∘ₗ V.toLinearMap) =
      residual A X M ∘ₗ V.toLinearMap := by
  ext x
  simp [residual, LinearMap.comp_apply]

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
/-- If `(X,M)` is invariant for `B`, its residual for `A` is exactly the
perturbation applied to `X`.

Lean proof route for a weaker agent:

1. Substitute the invariant-pair equation for `B X`, expand `A-B`, and use linear-map extensionality.
2. Use `LinearMap.ext` and evaluate at an arbitrary coordinate vector.
3. Rewrite `hBX` pointwise and discharge the remaining additive algebra.
-/
theorem residual_eq_perturbation_comp {A B : E →ₗ[𝕜] E}
    (X : F →ₗᵢ[𝕜] E) (M : F →ₗ[𝕜] F)
    (hBX : B ∘ₗ X.toLinearMap = X.toLinearMap ∘ₗ M) :
    residual A X M = (A - B) ∘ₗ X.toLinearMap := by
  show A ∘ₗ X.toLinearMap - X.toLinearMap ∘ₗ M = (A - B) ∘ₗ X.toLinearMap
  rw [LinearMap.sub_comp, hBX]

omit [FiniteDimensional 𝕜 F] in
/-- **The projected-residual (cross-block) Sylvester identity.**  For `A`
symmetric and `U` an `A`-invariant subspace, the sine embedding
`Y = P_{Uᗮ} X` satisfies the Sylvester equation
`A Y - Y M = P_{Uᗮ} (A X - X M)`, i.e. its residual is the `Uᗮ`-projection of the
ambient residual.  This is the algebraic heart of the residual `sin Θ` theorem;
it uses only the commutation of `A` with the complementary projection. -/
theorem sylvester_sinThetaEmbedding_eq_projectedResidual
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (hU : Reduces A U)
    (X : F →ₗᵢ[𝕜] E) (M : F →ₗ[𝕜] F) :
    A ∘ₗ sinThetaEmbedding U X - sinThetaEmbedding U X ∘ₗ M =
      complementaryProjection U ∘ₗ residual A X M := by
  ext x
  simp only [sinThetaEmbedding, residual, LinearMap.comp_apply, LinearMap.sub_apply, map_sub]
  rw [complementaryProjection_apply_comm_of_reduces hA hU (X.toLinearMap x)]

/-- A unitarily invariant norm of the invariant-pair residual is bounded by
that of the ambient perturbation.

Lean proof route for a weaker agent:

1. Rewrite with `residual_eq_perturbation_comp`, then use the operator-norm ideal inequality and that the isometric embedding has norm one.
2. Apply the composition norm inequality after converting both maps to continuous linear maps.
3. Rewrite the norm of the isometric embedding as one, treating the zero-dimensional domain separately if required.
-/
theorem opNorm_residual_le_perturbation
    {A B : E →ₗ[𝕜] E} (X : F →ₗᵢ[𝕜] E) (M : F →ₗ[𝕜] F)
    (hBX : B ∘ₗ X.toLinearMap = X.toLinearMap ∘ₗ M) :
    RectangularUnitarilyInvariantNorm.opNorm (residual A X M) ≤
      ‖(A - B).toContinuousLinearMap‖ := by
  rw [residual_eq_perturbation_comp X M hBX,
    RectangularUnitarilyInvariantNorm.opNorm_apply]
  have hcomp :
      ((A - B) ∘ₗ X.toLinearMap).toContinuousLinearMap =
        (A - B).toContinuousLinearMap ∘L X.toLinearMap.toContinuousLinearMap := by
    ext x
    rfl
  have hX : ‖X.toLinearMap.toContinuousLinearMap‖ ≤ 1 := by
    refine X.toLinearMap.toContinuousLinearMap.opNorm_le_bound zero_le_one fun x => ?_
    rw [one_mul]
    exact le_of_eq (X.norm_map x)
  rw [hcomp]
  calc
    ‖(A - B).toContinuousLinearMap ∘L X.toLinearMap.toContinuousLinearMap‖
        ≤ ‖(A - B).toContinuousLinearMap‖ *
            ‖X.toLinearMap.toContinuousLinearMap‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖(A - B).toContinuousLinearMap‖ * 1 :=
      mul_le_mul_of_nonneg_left hX (norm_nonneg _)
    _ = ‖(A - B).toContinuousLinearMap‖ := mul_one _

/-- Orthogonal decomposition of a general residual into the Ritz residual and
compression error.

Lean proof route for a weaker agent:

1. Decompose `AX-XM` as the Ritz residual plus `X(compression-M)`; Galerkin orthogonality makes the two rectangular maps Hilbert--Schmidt orthogonal.
2. Expand the Frobenius square in an orthonormal basis.
-/
theorem residual_frobenius_pythagoras (A : E →ₗ[𝕜] E)
    (X : F →ₗᵢ[𝕜] E) (M : F →ₗ[𝕜] F) :
    RectangularUnitarilyInvariantNorm.frobenius (residual A X M) ^ 2 =
      RectangularUnitarilyInvariantNorm.frobenius (ritzResidual A X) ^ 2 +
      RectangularUnitarilyInvariantNorm.frobenius (compression A X - M) ^ 2 := by
  let b := stdOrthonormalBasis 𝕜 F
  have hdecomp : residual A X M =
      ritzResidual A X + X.toLinearMap ∘ₗ (compression A X - M) := by
    ext x
    change A (X x) - X (M x) =
      (A (X x) - X ((compression A X) x)) +
        X (((compression A X) x) - M x)
    rw [map_sub]
    abel
  have hpoint : ∀ i, ‖residual A X M (b i)‖ ^ 2 =
      ‖ritzResidual A X (b i)‖ ^ 2 +
        ‖(compression A X - M) (b i)‖ ^ 2 := by
    intro i
    have hgal := LinearMap.congr_fun (adjoint_comp_ritzResidual_eq_zero A X) (b i)
    change X.toLinearMap.adjoint (ritzResidual A X (b i)) = 0 at hgal
    have horth :
        ⟪ritzResidual A X (b i),
            X.toLinearMap ((compression A X - M) (b i))⟫_𝕜 = 0 := by
      rw [← LinearMap.adjoint_inner_left, hgal, inner_zero_left]
    let d := (compression A X - M) (b i)
    change ⟪ritzResidual A X (b i), X d⟫_𝕜 = 0 at horth
    rw [LinearMap.congr_fun hdecomp (b i)]
    simp only [LinearMap.add_apply, LinearMap.comp_apply]
    change
      ‖ritzResidual A X (b i) + X d‖ ^ 2 =
        ‖ritzResidual A X (b i)‖ ^ 2 + ‖d‖ ^ 2
    have hpythCodomain :
        ‖ritzResidual A X (b i) + X d‖ *
            ‖ritzResidual A X (b i) + X d‖ =
          ‖ritzResidual A X (b i)‖ * ‖ritzResidual A X (b i)‖ +
            ‖X d‖ * ‖X d‖ :=
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
        (ritzResidual A X (b i)) (X d) horth
    have hnorm : ‖X d‖ = ‖d‖ := X.norm_map d
    rw [pow_two, pow_two, pow_two]
    calc
      ‖ritzResidual A X (b i) + X d‖ *
          ‖ritzResidual A X (b i) + X d‖ =
        ‖ritzResidual A X (b i)‖ * ‖ritzResidual A X (b i)‖ +
          ‖X d‖ * ‖X d‖ := hpythCodomain
      _ = ‖ritzResidual A X (b i)‖ * ‖ritzResidual A X (b i)‖ +
          ‖d‖ * ‖d‖ := by rw [hnorm]
  rw [RectangularUnitarilyInvariantNorm.frobenius_apply (residual A X M) b,
    RectangularUnitarilyInvariantNorm.frobenius_apply (ritzResidual A X) b,
    RectangularUnitarilyInvariantNorm.frobenius_apply (compression A X - M) b,
    Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity),
    Real.sq_sqrt (by positivity)]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => hpoint i


/-- The Ritz compression minimizes the Frobenius residual over all coordinate
operators.

Lean proof route for a weaker agent:

1. Apply the preceding Pythagorean identity and drop the nonnegative compression-error term.
2. Rewrite the Pythagorean identity as `ritz² ≤ residual²` using nonnegativity of the compression-error square.
3. Pass from squared norms to norms using nonnegativity.
-/
theorem ritzResidual_frobenius_minimal (A : E →ₗ[𝕜] E)
    (X : F →ₗᵢ[𝕜] E) (M : F →ₗ[𝕜] F) :
    RectangularUnitarilyInvariantNorm.frobenius (ritzResidual A X) ≤
      RectangularUnitarilyInvariantNorm.frobenius (residual A X M) := by
  have hpyth := residual_frobenius_pythagoras A X M
  have hsq :
      RectangularUnitarilyInvariantNorm.frobenius (ritzResidual A X) ^ 2 ≤
        RectangularUnitarilyInvariantNorm.frobenius (residual A X M) ^ 2 := by
    rw [hpyth]
    exact le_add_of_nonneg_right (sq_nonneg _)
  exact le_of_sq_le_sq hsq
    (RectangularUnitarilyInvariantNorm.frobenius.nonneg _)

/-- The orthogonal projection onto the range of an isometric embedding is
`X X⋆`. -/
theorem projection_approximateSubspace_eq_comp_adjoint (X : F →ₗᵢ[𝕜] E) :
    projection (approximateSubspace X) =
      X.toLinearMap ∘ₗ X.toLinearMap.adjoint := by
  ext y
  change (approximateSubspace X).starProjection y =
    X.toLinearMap (X.toLinearMap.adjoint y)
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · change X.toLinearMap (X.toLinearMap.adjoint y) ∈
      LinearMap.range X.toLinearMap
    exact ⟨X.toLinearMap.adjoint y, rfl⟩
  · intro w hw
    change w ∈ LinearMap.range X.toLinearMap at hw
    rcases hw with ⟨z, rfl⟩
    rw [inner_sub_left]
    apply sub_eq_zero.mpr
    change ⟪y, X z⟫_𝕜 =
      ⟪X (X.toLinearMap.adjoint y), X z⟫_𝕜
    exact (LinearMap.adjoint_inner_left X.toLinearMap z y).symm |>.trans
      (X.inner_map_map (X.toLinearMap.adjoint y) z).symm

/-- The singular values of `sinThetaEmbedding U X = P_{Uᗮ}X` are the
principal sines directed from `range X` toward `U`.

The proof identifies the projection onto `range X` with `X X⋆`, precomposes by
`X⋆`, and uses coisometry padding to show that the ambient cross projection has
exactly the same singular-value sequence as the rectangular embedding map.
-/
theorem singularValues_sinThetaEmbedding (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E) :
    (sinThetaEmbedding U X).singularValues =
      principalSines (approximateSubspace X) U := by
  have hmap :
      sinThetaEmbedding U X ∘ₗ X.toLinearMap.adjoint =
        sinThetaMap (approximateSubspace X) U := by
    rw [sinThetaEmbedding, sinThetaMap,
      projection_approximateSubspace_eq_comp_adjoint X]
    simp only [LinearMap.comp_assoc]
  calc
    (sinThetaEmbedding U X).singularValues =
        (sinThetaEmbedding U X ∘ₗ X.toLinearMap.adjoint).singularValues :=
      (singularValues_comp_adjoint_linearIsometry X (sinThetaEmbedding U X)).symm
    _ = (sinThetaMap (approximateSubspace X) U).singularValues := by rw [hmap]
    _ = principalSines (approximateSubspace X) U :=
      singularValues_sinThetaMap (approximateSubspace X) U

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
/-- The tangent map is finite exactly when the represented subspace is
transverse to `U`.

Lean proof route for a weaker agent:

1. Resolve the signature first.
2. For the one-sided statement, identify the cosine map with the restricted projection `P_U : range X → U`; its kernel is exactly `range X ∩ Uᗮ`.

Signature audit: Valid because `IsTransverse (range X) U` is the one-sided injectivity of
`P_U` on `range X`, exactly the kernel statement on the right.
-/
theorem tanThetaEmbedding_defined_iff (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E) :
    IsTransverse (approximateSubspace X) U ↔
      LinearMap.ker (cosThetaEmbedding U X) = ⊥ := by
  constructor
  · intro htrans
    rw [LinearMap.ker_eq_bot]
    intro x y hxy
    have hproj : U.starProjection (X (x - y)) = 0 := by
      change cosThetaEmbedding U X (x - y) = 0
      rw [map_sub, hxy, sub_self]
    have hXzero : X (x - y) = 0 :=
      htrans (X (x - y)) ⟨x - y, rfl⟩ hproj
    have hxyzero : x - y = 0 := by
      apply X.injective
      simpa using hXzero
    exact sub_eq_zero.mp hxyzero
  · intro hker x hx hproj
    rcases hx with ⟨y, rfl⟩
    have hyker : y ∈ LinearMap.ker (cosThetaEmbedding U X) := by
      simpa [cosThetaEmbedding, projection, LinearMap.comp_apply] using hproj
    rw [hker] at hyker
    have hy : y = 0 := by simpa using hyker
    rw [hy, map_zero]

end DavisKahanTheory
end ForMathlib
