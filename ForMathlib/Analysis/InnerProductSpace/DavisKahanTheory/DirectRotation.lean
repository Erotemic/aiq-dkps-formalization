/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import ForMathlib.Analysis.InnerProductSpace.DavisKahanTheory.TanTwoTheta
import ForMathlib.Analysis.InnerProductSpace.IntertwiningUnitary

/-!
# Direct rotation of two subspaces

Literature map:

* `ForMathlib/prose/Davis-Kahan-1970-part-III-core-arguments.tex`,
  Sections 4 and 12.
* Davis--Kahan (1970), Sections 3--4.
* `ForMathlib/prose/Davis-1963-core-arguments.tex`, Section
  "Canonical matching of subspaces".

This is the basis-independent completion of the existing
`OrthoProjFamily.intertwiningUnitary`.  The direct rotation is the canonical
unitary carrying one subspace to the other.  Its extremal properties are stated
with the qualifications in Davis--Kahan Section 4: the positive displacement
square is minimized for every UI norm, whereas `‖I-W‖` itself needs an angle
restriction for arbitrary UI norms.
-/

namespace ForMathlib
namespace DavisKahanTheory

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- The partial complex structure on the nontrivial two-subspace planes. -/
noncomputable def angleComplexStructure (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →ₗ[𝕜] E := by
  sorry

/-- Canonical direct rotation from `U` to `V`. -/
noncomputable def directRotation (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) : E ≃ₗᵢ[𝕜] E := by
  sorry

/-- The direct rotation maps `U` onto `V`.

Lean proof route for a weaker agent:

1. Preferred route: specialize the corresponding bounded theorem from `DavisKahanExt.DirectRotation` through the finite continuous-linear-map/isometry equivalence bridge
2. prove only the bundle/coercion normalization locally.
-/
theorem directRotation_map_eq (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    U.map (directRotation U V hacute).toLinearMap = V := by
  sorry

/-- Intertwining identity `W P_U = P_V W`.

Lean proof route for a weaker agent:

1. Preferred route: specialize the corresponding bounded theorem from `DavisKahanExt.DirectRotation` through the finite continuous-linear-map/isometry equivalence bridge
2. prove only the bundle/coercion normalization locally.
-/
theorem directRotation_comp_projection (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    (directRotation U V hacute).toLinearMap ∘ₗ projection U =
      projection V ∘ₗ (directRotation U V hacute).toLinearMap := by
  sorry

/-- Reversing the pair gives the inverse rotation.

Lean proof route for a weaker agent:

1. Preferred route: specialize the corresponding bounded theorem from `DavisKahanExt.DirectRotation` through the finite continuous-linear-map/isometry equivalence bridge
2. prove only the bundle/coercion normalization locally.
-/
theorem directRotation_symm (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    directRotation V U hacute.symm = (directRotation U V hacute).symm := by
  sorry

/-- The direct rotation is the identity on the common and doubly-orthogonal
parts.

Lean proof route for a weaker agent:

1. Preferred route: specialize the corresponding bounded theorem from `DavisKahanExt.DirectRotation` through the finite continuous-linear-map/isometry equivalence bridge
2. prove only the bundle/coercion normalization locally.
-/
theorem directRotation_apply_eq_self_of_mem_common (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) {x : E}
    (hx : x ∈ U ⊓ V ⊔ (U ⊔ V)ᗮ) :
    directRotation U V hacute x = x := by
  sorry

/-- Polar-factor construction from the two projections.

Lean proof route for a weaker agent:

1. Preferred route: specialize the corresponding bounded theorem from `DavisKahanExt.DirectRotation` through the finite continuous-linear-map/isometry equivalence bridge
2. prove only the bundle/coercion normalization locally.
-/
theorem directRotation_eq_polarFactor (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    (directRotation U V hacute).toLinearMap =
      polarFactor (projection V ∘ₗ projection U +
        complementaryProjection V ∘ₗ complementaryProjection U) := by
  sorry

/-- Trigonometric formula `W = cos Θ + J sin Θ`.

Lean proof route for a weaker agent:

1. Specialize the Ext polar-factor direct rotation, then use the finite two-projection functional calculus to identify the cosine, sine, and complex-structure factors.
2. This should follow after the Ext operator-angle layer.
-/
theorem directRotation_eq_cos_add_J_sin (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    (directRotation U V hacute).toLinearMap =
      cosAngleOperator U V + angleComplexStructure U V ∘ₗ sinAngleOperator U V := by
  sorry

/-- Square of the direct rotation is the product of the two reflections.

Lean proof route for a weaker agent:

1. Preferred route: specialize the corresponding bounded theorem from `DavisKahanExt.DirectRotation` through the finite continuous-linear-map/isometry equivalence bridge
2. prove only the bundle/coercion normalization locally.
-/
theorem directRotation_sq (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    (directRotation U V hacute).toLinearMap ∘ₗ
        (directRotation U V hacute).toLinearMap =
      V.reflection.toLinearMap ∘ₗ U.reflection.toLinearMap := by
  sorry

/-- The angle operator commutes with the direct rotation.

Lean proof route for a weaker agent:

1. Specialize the Ext polar-factor direct rotation, then use the finite two-projection functional calculus to identify the cosine, sine, and complex-structure factors.
2. This should follow after the Ext operator-angle layer.
-/
theorem directRotation_comm_angleOperator (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    (directRotation U V hacute).toLinearMap ∘ₗ angleOperator U V =
      angleOperator U V ∘ₗ (directRotation U V hacute).toLinearMap := by
  sorry

/-- Uniqueness among acute rotations with the correct intertwining and positive
real part.

Lean proof route for a weaker agent:

1. Use `hsq` to identify `W` and `directRotation U V hacute` as square roots of the same
   unitary product of reflections.
2. Use `hre` to select the positive-real-part square-root branch on each principal two-plane.
3. On the common and doubly orthogonal summands, use `hmap` and the branch condition to show
   both operators are the identity.
4. Finish by extensionality over the principal-plane orthogonal decomposition.

Signature audit: The reflection-square hypothesis removes the counterexamples obtained by
rotating the common complement while still mapping `U` onto `V`.
-/
theorem directRotation_unique (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) (W : E ≃ₗᵢ[𝕜] E)
    (hmap : U.map W.toLinearMap = V)
    (hsq : W.toLinearMap ∘ₗ W.toLinearMap =
      V.reflection.toLinearMap ∘ₗ U.reflection.toLinearMap)
    (hre : ∀ x, 0 ≤ RCLike.re ⟪W x, x⟫_𝕜) :
    W = directRotation U V hacute := by
  sorry

/-- Davis--Kahan Proposition 4.3: for every UI norm the direct rotation
minimizes the positive displacement square `(I-W⋆)(I-W)`.  This is the
unconditional all-UI extremal statement.

Lean proof route for a weaker agent:

1. Use the finite principal-plane decomposition and Davis--Kahan Section 4 scalar inequalities on each `2 × 2` block, then apply symmetric-gauge/Fan dominance.
2. The Ext operator-norm minimizer supplies geometry but not the arbitrary finite UI conclusion.
-/
theorem directRotation_minimizes_displacementSquare_uiNorm
    (N : UnitarilyInvariantNorm 𝕜 E) (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) (W : E ≃ₗᵢ[𝕜] E)
    (hmap : U.map W.toLinearMap = V) :
    N ((LinearMap.id - (directRotation U V hacute).symm.toLinearMap) ∘ₗ
        (LinearMap.id - (directRotation U V hacute).toLinearMap)) ≤
      N ((LinearMap.id - W.symm.toLinearMap) ∘ₗ
        (LinearMap.id - W.toLinearMap)) := by
  sorry

/-- Davis--Kahan Proposition 4.4: if the largest principal angle is at most
`π/3`, the direct rotation minimizes `N (I-W)` for every UI norm.  Without
this restriction the statement is false for some UI norms.

Lean proof route for a weaker agent:

1. Use the finite principal-plane decomposition and Davis--Kahan Section 4 scalar inequalities on each `2 × 2` block, then apply symmetric-gauge/Fan dominance.
2. The Ext operator-norm minimizer supplies geometry but not the arbitrary finite UI conclusion.
-/
theorem directRotation_minimizes_uiNorm_of_largestAngle_le_pi_div_three
    (N : UnitarilyInvariantNorm 𝕜 E) (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V)
    (hangle : principalAngles U V 0 ≤ Real.pi / 3)
    (W : E ≃ₗᵢ[𝕜] E) (hmap : U.map W.toLinearMap = V) :
    N (LinearMap.id - (directRotation U V hacute).toLinearMap) ≤
      N (LinearMap.id - W.toLinearMap) := by
  sorry

/-- Pointwise maximum-displacement extremal property.

Lean proof route for a weaker agent:

1. Preferred route: specialize the corresponding bounded theorem from `DavisKahanExt.DirectRotation` through the finite continuous-linear-map/isometry equivalence bridge
2. prove only the bundle/coercion normalization locally.
-/
theorem directRotation_minimizes_max_displacement
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hacute : IsAcute U V)
    (W : E ≃ₗᵢ[𝕜] E) (hmap : U.map W.toLinearMap = V) :
    ‖((directRotation U V hacute).toLinearMap - LinearMap.id).toContinuousLinearMap‖ ≤
      ‖(W.toLinearMap - LinearMap.id).toContinuousLinearMap‖ := by
  sorry

/-- Orthonormal-basis extremal property from Davis--Kahan Proposition 4.2.

Lean proof route for a weaker agent:

1. Use the finite principal-plane decomposition and Davis--Kahan Section 4 scalar inequalities on each `2 × 2` block, then apply symmetric-gauge/Fan dominance.
2. The Ext operator-norm minimizer supplies geometry but not the arbitrary finite UI conclusion.
-/
theorem directRotation_minimizes_sum_sq_basis_angles
    {n : ℕ} (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hacute : IsAcute U V)
    (b : OrthonormalBasis (Fin n) 𝕜 E) (W : E ≃ₗᵢ[𝕜] E)
    (hmap : U.map W.toLinearMap = V) :
    ∑ i, ‖directRotation U V hacute (b i) - b i‖ ^ 2 ≤
      ∑ i, ‖W (b i) - b i‖ ^ 2 := by
  sorry

end DavisKahanTheory
end ForMathlib
