/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import ForMathlib.Analysis.InnerProductSpace.DavisKahanExt.Basic

/-!
# Operator angles between closed subspaces

Literature writeup: local TeX, Sections 7--8.  This includes the two-projection
calculus, gap topology, graph representation, and direct-angle functions.
-/


/-! ## Construction plan

Construct the angle family in one functional-calculus pipeline rather than as
independent choices.

1. Define `operatorAbsoluteValue T` as the positive square root of `T⋆T`.
2. On the Halmos generic part of two projections, use the positive contraction
   `P Q P`; define the cosine as its square root, the sine from `1-cos²`, and
   the angle by `arccos` continuous functional calculus.
3. Extend by the canonical values on the common and orthogonal summands.
4. Define tangent only after an acute hypothesis supplies a bounded inverse of
   the cosine.  Define double-angle sine polynomially from sine and cosine;
   define double-angle tangent only under the quarter-angle hypothesis.
5. For real scalars, either prove the required real continuous functional
   calculus or transfer the complex construction through a norm-preserving
   complexification.  Keep all projection-algebra lemmas scalar-generic.
-/

namespace ForMathlib
namespace DavisKahanExt

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- Absolute value `(T* T)^(1/2)` of a bounded operator.

Construction route: apply continuous functional calculus square root to the
positive operator `star T * T`; for real scalars, transfer this construction
through the real spectral bridge or complexification. -/
noncomputable def operatorAbsoluteValue (T : E →L[𝕜] E) : E →L[𝕜] E := by
  sorry

/-- Positive operator angle between two closed subspaces.

Construction route: use the Halmos two-projection decomposition, define the
cosine from the positive contraction `P_U P_V P_U`, and apply `arccos` by
continuous functional calculus on the generic block with canonical endpoint
values on the common and defect blocks. -/
noncomputable def angleOperator (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →L[𝕜] E := by
  sorry

/-- Sine of the operator angle.

Construction route: define it as the positive square root of
`1 - cosAngleOperator U V ^ 2`, or equivalently as the modulus of the
projector difference after proving the two-projection decomposition. -/
noncomputable def sinAngleOperator (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →L[𝕜] E := by
  sorry

/-- Cosine of the operator angle.

Construction route: take the positive square root of the compression
`P_U P_V P_U` on the generic block and extend by the canonical values one and
zero on the common and orthogonal defect summands. -/
noncomputable def cosAngleOperator (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →L[𝕜] E := by
  sorry

/-- Bounded tangent of the operator angle in the acute regime.

The proof argument is part of the definition because `tan` is unbounded at
`π / 2`; there is no canonical bounded operator for a non-acute pair.

Construction route: use `sinAngleOperator * (cosAngleOperator)⁻¹`; obtain the
bounded inverse from the acute gap and prove the two factors commute by their
common functional-calculus origin. -/
noncomputable def tanAngleOperator (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) : E →L[𝕜] E := by
  sorry

/-- Sine of twice the operator angle.

Construction route: define this polynomially as `2 * sinTheta * cosTheta` on
the Halmos two-projection decomposition.  This avoids tangent poles and keeps
the result bounded for every pair of closed subspaces.  Prove agreement with
the reflection-defect/cross-block formula before exposing functional-calculus
identities. -/
noncomputable def sinTwoAngleOperator (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →L[𝕜] E := by
  sorry

/-- Bounded tangent of twice the operator angle below the quarter-angle
pole.

Construction route: form `sinTwoAngleOperator * (cosTwoAngleOperator)⁻¹`, with
invertibility supplied by `hquarter`; alternatively apply `tan (2 * ·)` in the
same functional calculus used for `angleOperator`. -/
noncomputable def tanTwoAngleOperator (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hquarter : IsQuarterAcute U V) : E →L[𝕜] E := by
  sorry

/-- An angular operator maps `U` into `Uᗮ` and vanishes on `Uᗮ`. -/
def IsAngularOperator (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : E →L[𝕜] E) : Prop :=
  X ∘L projection U = X ∧ projection U ∘L X = 0

/-- Maximal operator angle. -/
noncomputable def maximalAngle (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : ℝ :=
  Real.arcsin (subspaceGap U V)

/-- The sine operator is the absolute value of the projector difference.

Proof strategy:

1. Write `P = projection U` and `Q = projection V` and use the canonical
   two-projection decomposition into common, orthogonal, and generic parts.
2. On the generic part, identify both operators through the positive
   contraction `P Q P`; the nontrivial scalar fibers are the standard
   `2 x 2` projection pair with parameter `cos^2 theta`.
3. Use continuous functional calculus to take the positive square root of
   `(P-Q)^*(P-Q)` and identify its scalar function with `sin theta`.
4. Reassemble the reducing summands and discharge the common/orthogonal blocks
   by projection algebra.

For an initial implementation, prove the squared identity first and derive the
positive square-root equality by uniqueness.  This theorem should depend only
on bounded projection geometry, not on Borel spectral projections. 

Lean proof route for a weaker agent:

1. Prove the squared identity between the positive sine operator and `(P-Q)*(P-Q)` on the Halmos decomposition.
2. Establish positivity of both candidate square roots.
3. Use uniqueness of the positive square root in the C*-algebra of bounded operators.
4. Avoid any dependence on spectral projections of `A`; this is pure two-projection geometry.


Ext-agent signature audit (GPT 5.6 High): Sound if `angleOperator` is defined by the
canonical two-projection functional calculus on the full ambient space. This fixes the
multiplicity convention used by all ideal statements.

Preferred dependency route: Use Halmos two-projection geometry and continuous functional
calculus for positive contractions; avoid spectral decompositions tied to compactness or
finite dimension.
-/
theorem sinAngleOperator_eq_abs_projection_sub
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] :
    sinAngleOperator U V =
      operatorAbsoluteValue (projection U - projection V) := by
  sorry

/-- Operator norm of `sin Θ` equals the subspace gap. 

Lean proof route for a weaker agent:

1. Rewrite `sinAngleOperator` using `sinAngleOperator_eq_abs_projection_sub`.
2. Apply the C*-identity `‖|T|‖=‖T‖` for bounded operators on a Hilbert space.
3. Unfold `subspaceGap`.


Ext-agent signature audit (GPT 5.6 High): Correct from the absolute-value identity and
the C*-norm law.

Preferred dependency route: Use Halmos two-projection geometry and continuous functional
calculus for positive contractions; avoid spectral decompositions tied to compactness or
finite dimension.
-/
theorem norm_sinAngleOperator (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    ‖sinAngleOperator U V‖ = subspaceGap U V := by
  sorry

/-- Directed and symmetric gaps agree in the equal-defect/acute setting. 

Lean proof route for a weaker agent:

1. Use the two-projection decomposition and write both norms as suprema of the same sine-angle function.
2. Acuteness removes unmatched `π/2` defect summands, which are the only source of asymmetry.
3. Conclude equality by the norm formula on each reducing block.


Ext-agent signature audit (GPT 5.6 High): Correct: `‖P-Q‖<1` excludes unmatched defect
summands, which are precisely what can make the two directed gaps unequal.

Preferred dependency route: Use Halmos two-projection geometry and continuous functional
calculus for positive contractions; avoid spectral decompositions tied to compactness or
finite dimension.
-/
theorem directedGap_eq_subspaceGap_of_acute
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (h : IsAcute U V) :
    directedGap U V = subspaceGap U V := by
  sorry

/-- Acute subspaces admit bounded graph representations.

Proof strategy: restrict `P_U` to `V`.  Acuteness gives injectivity and a
uniform lower bound controlled by `1 - ‖P_U-P_V‖`; closed range plus the
orthogonal defect condition gives surjectivity onto `U`.  Apply the bounded
inverse theorem, then define

`X = P_{Uᗮ}|_V ∘ (P_U|_V)⁻¹`.

Show that every `v ∈ V` is uniquely `u + X u`, that `X` vanishes on `Uᗮ`, and
that the reverse construction produces an acute graph.  This proof is the
preferred bridge to both finite direct rotations and Riccati theory. 

Lean proof route for a weaker agent:

1. Restrict `projection U` to `V` and prove it is bounded below from `subspaceGap U V < 1`.
2. Prove surjectivity onto `U` using the corresponding estimate for the complementary projection.
3. Apply the bounded inverse theorem and define `X = P_{Uᗮ} ∘ (P_U|_V)⁻¹`, extended by zero on `Uᗮ`.
4. For the reverse implication, compute the graph projection or directly bound `‖P_U-P_V‖` by the graph norm formula.


Ext-agent signature audit (GPT 5.6 High): Correct for closed subspaces with orthogonal
projections. The graph operator is ambient but constrained to vanish on `Uᗮ`; this
avoids a separate bundled map `U → Uᗮ`.

Preferred dependency route: Use Halmos two-projection geometry and continuous functional
calculus for positive contractions; avoid spectral decompositions tied to compactness or
finite dimension.
-/
theorem acute_iff_exists_bounded_angularOperator
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] :
    IsAcute U V ↔ ∃ X : E →L[𝕜] E,
      IsAngularOperator U X ∧
      V = LinearMap.range (projection U + X ∘L projection U).toLinearMap := by
  sorry

/-- Norm of the angular operator is `tan` of the maximal angle. 

Lean proof route for a weaker agent:

1. Take the graph operator furnished by `acute_iff_exists_bounded_angularOperator`.
2. Identify its graph with `V` and use the graph projection formula.
3. Compute `‖P_U-P_V‖ = ‖X‖/sqrt(1+‖X‖²)` through functional calculus.
4. Apply `tan (arcsin (x/sqrt(1+x²))) = x` and return the full graph witness.


Ext-agent signature audit (GPT 5.6 High): Correct only on the acute branch, which is
present. Return of the actual graph witness prevents the earlier underdetermined
existential norm statement.

Preferred dependency route: Use Halmos two-projection geometry and continuous functional
calculus for positive contractions; avoid spectral decompositions tied to compactness or
finite dimension.
-/
theorem norm_angularOperator_eq_tan_maximalAngle
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (h : IsAcute U V) :
    ∃ X : E →L[𝕜] E,
      IsAngularOperator U X ∧
      V = LinearMap.range (projection U + X ∘L projection U).toLinearMap ∧
      ‖X‖ = Real.tan (maximalAngle U V) := by
  sorry

/-- Orthogonal complementation preserves the operator angle. 

Lean proof route for a weaker agent:

1. Express both angle operators through the two-projection decomposition.
2. Observe that replacing `P,Q` by `I-P,I-Q` leaves the generic angle block unchanged and swaps only the trivial summands.
3. Finish by functional-calculus extensionality on the common reducing decomposition.


Ext-agent signature audit (GPT 5.6 High): Correct for the full ambient angle convention
`arcsin |P-Q|`, since complementing both projections leaves their difference unchanged
up to sign.

Preferred dependency route: Use Halmos two-projection geometry and continuous functional
calculus for positive contractions; avoid spectral decompositions tied to compactness or
finite dimension.
-/
theorem angleOperator_orthogonalComplement
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] :
    angleOperator Uᗮ Vᗮ = angleOperator U V := by
  sorry

/-- Triangle inequality for the maximal angle. 

Lean proof route for a weaker agent:

1. Use the known triangle inequality for the gap angle of three orthogonal projections.
2. Alternatively compose the canonical direct rotations and compare their operator-norm distances from the identity.
3. Reduce the remaining scalar inequality to monotonicity/addition bounds for `arcsin` on `[0,1]`.


Ext-agent signature audit (GPT 5.6 High): Expected to be correct for the gap angle
`arcsin ‖P-Q‖`, but it needs the established projection-angle metric theorem. A scalar
`arcsin` manipulation alone is not sufficient.

Preferred dependency route: Use Halmos two-projection geometry and continuous functional
calculus for positive contractions; avoid spectral decompositions tied to compactness or
finite dimension.
-/
theorem maximalAngle_triangle
    (U V W : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] [W.HasOrthogonalProjection] :
    maximalAngle U W ≤ maximalAngle U V + maximalAngle V W := by
  sorry

end DavisKahanExt
end ForMathlib
