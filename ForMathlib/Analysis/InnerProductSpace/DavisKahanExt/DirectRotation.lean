/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import ForMathlib.Analysis.InnerProductSpace.DavisKahanExt.GraphSubspace
import ForMathlib.Analysis.InnerProductSpace.DavisKahanExt.DoubleAngle

/-!
# Infinite-dimensional direct rotations

Literature writeup: local TeX, Section 25.  The direct rotation is the
canonical unitary transporting one acute closed subspace to another.
-/

namespace ForMathlib
namespace DavisKahanExt

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- Canonical direct rotation.

Construction strategy: set

`S = P_V P_U + P_{Vᗮ} P_{Uᗮ}`.

For an acute pair, prove `S* S` is bounded below by a positive scalar.  Define
the direct rotation as the polar factor `S (S* S)^{-1/2}` using continuous
functional calculus.  This construction automatically yields a unitary that
intertwines the two projections and is stable under finite specialization. -/
noncomputable def directRotation (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) : E →L[𝕜] E := by
  sorry

/-- The direct rotation is unitary. 

Lean proof route for a weaker agent:

1. For `S = QP+(I-Q)(I-P)`, show acuteness makes `S*S` bounded below and invertible.
2. Define the polar factor `W=S(S*S)^{-1/2}` and compute `W*W=I`.
3. Prove surjectivity from invertibility or similarly compute `WW*=I`.
4. Translate those identities to `IsUnitaryOperator`.


Ext-agent signature audit (GPT 5.6 High): Correct for acute pairs using the polar factor
of the canonical intertwiner.

Preferred dependency route: Construct the polar factor of `QP + QᗮPᗮ`; prove
intertwining before extremality, and use the Halmos decomposition only for the final
minimization theorem.
-/
theorem directRotation_unitary
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hacute : IsAcute U V) :
    IsUnitaryOperator (directRotation U V hacute) := by
  sorry

/-- The direct rotation maps one subspace onto the other. 

Lean proof route for a weaker agent:

1. Convert the intertwining identity into inclusion of `U.map W` in `V`.
2. Use unitarity/surjectivity to compare orthogonal complements or apply the inverse rotation for the reverse inclusion.
3. Conclude equality of submodules by antisymmetry.


Ext-agent signature audit (GPT 5.6 High): Correct and should be derived from projection
intertwining plus unitarity, not from basis choices.

Preferred dependency route: Construct the polar factor of `QP + QᗮPᗮ`; prove
intertwining before extremality, and use the Halmos decomposition only for the final
minimization theorem.
-/
theorem directRotation_maps_subspace
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hacute : IsAcute U V) :
    U.map (directRotation U V hacute).toLinearMap = V := by
  sorry

/-- Intertwining of orthogonal projections. 

Lean proof route for a weaker agent:

1. Unfold the polar-factor construction of `directRotation`.
2. Prove the pre-polar operator `S = QP+(I-Q)(I-P)` satisfies `S P = Q S`.
3. Show `S*S` commutes with `P`; functional calculus then gives commutation of its inverse square root.
4. Reassemble to obtain `W P = Q W`.


Ext-agent signature audit (GPT 5.6 High): Correct; this is the foundational
direct-rotation theorem and should be proved before the range and square formulas.

Preferred dependency route: Construct the polar factor of `QP + QᗮPᗮ`; prove
intertwining before extremality, and use the Halmos decomposition only for the final
minimization theorem.
-/
theorem directRotation_intertwines
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hacute : IsAcute U V) :
    directRotation U V hacute ∘L projection U =
      projection V ∘L directRotation U V hacute := by
  sorry

/-- Square of the direct rotation is the product of reflections. 

Lean proof route for a weaker agent:

1. Use the polar/trigonometric formula for the direct rotation on the two-projection decomposition.
2. Verify the scalar `2×2` identity that two equal angle rotations compose to the product of reflections.
3. Extend the identity over the trivial reducing summands and close by operator extensionality.


Ext-agent signature audit (GPT 5.6 High): Correct with the stated reflection order for
the convention that the direct rotation maps `U` to `V`; verify the orientation on the
planar model before general assembly.

Preferred dependency route: Construct the polar factor of `QP + QᗮPᗮ`; prove
intertwining before extremality, and use the Halmos decomposition only for the final
minimization theorem.
-/
theorem directRotation_sq
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hacute : IsAcute U V) :
    directRotation U V hacute ∘L directRotation U V hacute =
      reflectionOperator V ∘L reflectionOperator U := by
  sorry

/-- Direct rotation minimizes maximal displacement from the identity.

Proof strategy: reduce by the two-projection decomposition to scalar
`2 x 2` angle fibers.  On each generic fiber, every unitary carrying the first
line to the second has displacement at least that of the shorter rotation.
Take the supremum over the angle spectrum.  State and prove any necessary
angle restriction explicitly; do not infer an unrestricted extremal theorem
for arbitrary symmetric ideal gauges from the operator-norm result. 

Lean proof route for a weaker agent:

1. Reduce the pair of projections to the Halmos two-projection decomposition.
2. On each generic two-dimensional angle fiber, prove the shorter rotation minimizes `‖W-I‖` among unitaries sending the first line to the second.
3. Take the essential supremum over the angle spectrum and handle common/orthogonal summands separately.
4. Check that the stated acuteness hypothesis excludes the ambiguous `π/2` branch.


Ext-agent signature audit (GPT 5.6 High): Correct as an operator-norm extremal statement
for acute pairs. It must not be generalized automatically to every symmetric ideal
gauge.

Preferred dependency route: Construct the polar factor of `QP + QᗮPᗮ`; prove
intertwining before extremality, and use the Halmos decomposition only for the final
minimization theorem.
-/
theorem directRotation_minimal
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hacute : IsAcute U V)
    (W : E →L[𝕜] E) (hW : IsUnitaryOperator W)
    (hmap : U.map W.toLinearMap = V) :
    ‖directRotation U V hacute - ContinuousLinearMap.id 𝕜 E‖ ≤
      ‖W - ContinuousLinearMap.id 𝕜 E‖ := by
  sorry

end DavisKahanExt
end ForMathlib
