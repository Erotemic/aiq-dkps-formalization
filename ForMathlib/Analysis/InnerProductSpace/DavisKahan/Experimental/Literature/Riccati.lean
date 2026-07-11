/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import ForMathlib.Analysis.InnerProductSpace.DavisKahanExt.GraphSubspace

/-!
# Bounded block operator matrices and Riccati equations

Literature writeup: local TeX, Sections 18--20, following the geometric
Riccati approach of Kostrykin--Makarov--Motovilov.
-/

namespace ForMathlib
namespace DavisKahanExt

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E0 : Type*} [NormedAddCommGroup E0] [InnerProductSpace 𝕜 E0]
  [CompleteSpace E0]
variable {E1 : Type*} [NormedAddCommGroup E1] [InnerProductSpace 𝕜 E1]
  [CompleteSpace E1]

/-- Self-adjoint `2 × 2` bounded block operator data. -/
structure BlockOperatorData where
  A0 : E0 →L[𝕜] E0
  A1 : E1 →L[𝕜] E1
  B01 : E1 →L[𝕜] E0
  B10 : E0 →L[𝕜] E1
  selfAdjoint0 : IsSelfAdjointOperator A0
  selfAdjoint1 : IsSelfAdjointOperator A1
  offDiagonalAdjoint : ∀ x y, ⟪B01 y, x⟫_𝕜 = ⟪y, B10 x⟫_𝕜

/-- Bounded block operator on the Hilbert direct sum. -/
noncomputable def blockOperator
    (H : BlockOperatorData (𝕜 := 𝕜) (E0 := E0) (E1 := E1)) :
    WithLp 2 (E0 × E1) →L[𝕜] WithLp 2 (E0 × E1) := by
  sorry

/-- Graph of a bounded angular operator in the Hilbert direct sum. -/
noncomputable def blockGraph (X : E0 →L[𝕜] E1) :
    Submodule 𝕜 (WithLp 2 (E0 × E1)) := by
  sorry

/-- Block-diagonal operator on the Hilbert direct sum. -/
noncomputable def blockDiagonalOperator
    (D0 : E0 →L[𝕜] E0) (D1 : E1 →L[𝕜] E1) :
    WithLp 2 (E0 × E1) →L[𝕜] WithLp 2 (E0 × E1) := by
  sorry

/-- Riccati defect `A₁X - XA₀ - XB₀₁X + B₁₀`. -/
def riccatiDefect (H : BlockOperatorData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (X : E0 →L[𝕜] E1) : E0 →L[𝕜] E1 :=
  H.A1 ∘L X - X ∘L H.A0 - X ∘L H.B01 ∘L X + H.B10

/-- A bounded solution of the operator Riccati equation. -/
def SolvesRiccati (H : BlockOperatorData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (X : E0 →L[𝕜] E1) : Prop :=
  riccatiDefect H X = 0

/-- The graph of a Riccati solution reduces the block operator matrix. 

Lean proof route for a weaker agent:

1. Expand `blockOperator H` on a graph vector `(u,Xu)`.
2. Graph invariance is equivalent to the second component being `X` of the first, which simplifies to `riccatiDefect H X=0`.
3. Use self-adjointness of the block operator and closedness of the graph to upgrade invariance to reduction.
4. Prove the reverse direction by the same block calculation.


Ext-agent signature audit (GPT 5.6 High): Correct for the self-adjoint block data: graph
invariance is equivalent to the Riccati equation, and self-adjointness upgrades
invariance of the closed graph to reduction.

Preferred dependency route: Use graph invariance for algebraic equivalence, the ordered
Sylvester inverse for contraction estimates, and the canonical graph rotation for
unitary block diagonalization.
-/
theorem graph_reduces_iff_solvesRiccati
    (H : BlockOperatorData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (X : E0 →L[𝕜] E1) :
    Reduces (blockOperator H) (blockGraph X) ↔ SolvesRiccati H X := by
  sorry

/-- Existence of a bounded solution when one diagonal spectrum lies in a gap
of the other and the coupling satisfies a conservative contraction threshold.

Preferred proof strategy:

1. follow the path from the diagonal operator to the coupled block operator;
2. use a uniformly separating contour to continue the target spectral
   projection in norm;
3. prove the continued range stays acute with respect to the first coordinate
   subspace while the projection distance is below one;
4. apply the graph-subspace theorem to obtain a bounded angular operator `X`;
5. expand invariance of the graph to obtain the Riccati equation.

A contraction mapping on
`X ↦ S⁻¹ (X B01 X - B10)`, where `S X = A1 X - X A0`, can supply a local
small-coupling theorem and norm estimates, but continuation is the better
construction for selecting the correct spectral branch. 

Lean proof route for a weaker agent:

1. Continue the isolated spectral projection from the diagonal block operator to the coupled operator.
2. Use the smallness threshold to prove the continued range remains acute relative to the first coordinate subspace.
3. Represent the range as a graph and invoke `graph_reduces_iff_solvesRiccati`.
4. Derive contractivity and the displayed norm estimate from the scalar Riccati majorant before packaging the witness.


Ext-agent signature audit (GPT 5.6 High): The `2‖B01‖<d` condition is a conservative
contraction threshold, not the sharp continuation threshold. The half-angle majorant is
compatible with this local branch.

Preferred dependency route: Use graph invariance for algebraic equivalence, the ordered
Sylvester inverse for contraction estimates, and the canonical graph rotation for
unitary block diagonalization.
-/
theorem exists_riccati_solution_of_gap
    (H : BlockOperatorData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    {left right d : ℝ} (hd : 0 < d)
    (hgap : IntervalExteriorSeparated H.A0 ⊤ H.A1 ⊤ left right d)
    (hsmall : 2 * ‖H.B01‖ < d) :
    ∃ X : E0 →L[𝕜] E1,
      SolvesRiccati H X ∧ ‖X‖ < 1 ∧
      ‖X‖ ≤ Real.tan (Real.arctan (2 * ‖H.B01‖ / d) / 2) := by
  sorry

/-- Sharp a priori norm estimate for the Riccati solution. 

Lean proof route for a weaker agent:

1. Pair the Riccati equation with near norm-attaining vectors for `X` or use its polar decomposition.
2. Apply the interval/exterior separation to the linear Sylvester part.
3. Bound the quadratic term by `‖B01‖‖X‖²` and obtain the scalar quadratic inequality.
4. Use `hXc` and `hsmall` to select the smaller root and rewrite it as the displayed half-angle tangent.


Ext-agent signature audit (GPT 5.6 High): Correct only for the selected contractive
branch; `hXc` is essential because the scalar quadratic inequality has a second, large
root.

Preferred dependency route: Use graph invariance for algebraic equivalence, the ordered
Sylvester inverse for contraction estimates, and the canonical graph rotation for
unitary block diagonalization.
-/
theorem norm_riccati_solution_le
    (H : BlockOperatorData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    {left right d : ℝ} (hd : 0 < d)
    (hgap : IntervalExteriorSeparated H.A0 ⊤ H.A1 ⊤ left right d)
    (hsmall : 2 * ‖H.B01‖ < d)
    {X : E0 →L[𝕜] E1} (hX : SolvesRiccati H X)
    (hXc : ‖X‖ < 1) :
    ‖X‖ ≤ Real.tan (Real.arctan (2 * ‖H.B01‖ / d) / 2) := by
  sorry

/-- Uniqueness of the contractive Riccati solution associated with the
spectral graph subspace. 

Lean proof route for a weaker agent:

1. Subtract the two Riccati equations and obtain a Sylvester equation for `X-Y` with coefficients modified by `X,Y`.
2. Use contractivity and the small-coupling hypothesis to retain a positive spectral/separation lower bound.
3. Apply the ordered Sylvester estimate to force `X-Y=0`.
4. Alternatively identify both graphs with the same continued spectral projection and use uniqueness of the graph operator.


Ext-agent signature audit (GPT 5.6 High): Expected under the conservative small-coupling
hypothesis. If subtraction of equations does not retain ordered separation, identify
both graphs with the same continued spectral projection instead.

Preferred dependency route: Use graph invariance for algebraic equivalence, the ordered
Sylvester inverse for contraction estimates, and the canonical graph rotation for
unitary block diagonalization.
-/
theorem unique_contractive_riccati_solution
    (H : BlockOperatorData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    {left right d : ℝ} (hd : 0 < d)
    (hgap : IntervalExteriorSeparated H.A0 ⊤ H.A1 ⊤ left right d)
    (hsmall : 2 * ‖H.B01‖ < d)
    {X Y : E0 →L[𝕜] E1}
    (hX : SolvesRiccati H X) (hY : SolvesRiccati H Y)
    (hXc : ‖X‖ < 1) (hYc : ‖Y‖ < 1) :
    X = Y := by
  sorry

/-- Block diagonalization by the graph transform.

Proof strategy: form the triangular graph transform
`T = [[I,-X*],[X,I]]`, prove its inverse using `I+X*X` and `I+XX*`, and use the
Riccati equation to cancel the off-diagonal blocks of `T⁻¹ L T`.  Normalize
`T` by the inverse square roots of those positive operators to obtain a
unitary transform in the self-adjoint case.  Domain-free bounded block algebra
should be completed here before attempting the unbounded analogue. 

Lean proof route for a weaker agent:

1. Use `graph_reduces_iff_solvesRiccati` to show the graph and its orthogonal complement reduce the self-adjoint block operator.
2. Construct the canonical unitary graph rotation from the coordinate subspace to `blockGraph X`; take its adjoint/inverse as `Winv`.
3. Intertwine the two reducing decompositions and expand `Winv ∘ blockOperator H ∘ W`.
4. Define the two diagonal restrictions `D0,D1`, prove the conjugation equality, and package unitary and inverse identities.


Ext-agent signature audit (GPT 5.6 High): The strengthened signature now returns unitary
inverse data as well as the conjugation equality. This matches self-adjoint
reducing-graph geometry rather than a merely triangular similarity.

Preferred dependency route: Use graph invariance for algebraic equivalence, the ordered
Sylvester inverse for contraction estimates, and the canonical graph rotation for
unitary block diagonalization.
-/
theorem blockDiagonalization_of_riccati
    (H : BlockOperatorData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    {X : E0 →L[𝕜] E1} (hX : SolvesRiccati H X) :
    ∃ W Winv : WithLp 2 (E0 × E1) →L[𝕜] WithLp 2 (E0 × E1),
      ∃ D0 : E0 →L[𝕜] E0, ∃ D1 : E1 →L[𝕜] E1,
      IsUnitaryOperator W ∧ IsUnitaryOperator Winv ∧
      Winv ∘L W = ContinuousLinearMap.id 𝕜 (WithLp 2 (E0 × E1)) ∧
      W ∘L Winv = ContinuousLinearMap.id 𝕜 (WithLp 2 (E0 × E1)) ∧
      Winv ∘L blockOperator H ∘L W = blockDiagonalOperator D0 D1 := by
  sorry

end DavisKahanExt
end ForMathlib
