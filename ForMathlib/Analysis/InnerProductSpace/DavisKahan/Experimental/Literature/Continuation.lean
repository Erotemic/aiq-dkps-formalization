/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import ForMathlib.Analysis.InnerProductSpace.DavisKahanExt.DoubleAngle
import ForMathlib.Analysis.InnerProductSpace.DavisKahanExt.Resolvent

/-!
# Spectral projection continuation and branch selection

Literature writeup: local TeX, Sections 15 and 20--24.  The infinite-
dimensional tangent theorems require selecting the perturbed spectral
component by a norm-continuous path of Riesz projections.
-/


/-! ## Weak-agent execution plan: continuation

Split this module into a local analytic theorem and a global topological
argument.

Local theorem: under a fixed separating contour and a uniform resolvent bound,
prove norm continuity of the Riesz projection from the second resolvent
identity.  State a quantitative Lipschitz estimate; continuity is its
corollary.

Global theorem: for a continuous path of projections `P t`, prove rank or
component constancy.  In finite dimension use `‖P-Q‖ < 1` to construct an
isomorphism between the ranges.  In infinite dimension use the same estimate
to obtain the graph representation.  Cover the parameter interval by local
neighborhoods and use connectedness/clopen reasoning.

Keep the spectral identification separate: show the continued Riesz
projection equals the requested spectral projection only after the path
argument.  This prevents a cycle between continuity and spectral selection.
-/

namespace ForMathlib
namespace DavisKahanExt

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- Linear perturbation path. -/
def operatorPath (A H : E →L[𝕜] E) (t : ℝ) : E →L[𝕜] E :=
  A + (t : 𝕜) • H

/-- Continued spectral projection selected by a separating contour. -/
noncomputable def continuedProjection (A H : E →L[𝕜] E)
    (contour : ℝ → 𝕜) (t : ℝ) : E →L[𝕜] E :=
  rieszProjection (operatorPath A H t) contour

/-- Norm continuity of the selected projection path.

Proof strategy: fix a contour that remains uniformly inside the resolvent set.
Use the second resolvent identity to prove uniform norm continuity of
`z ↦ (z-A_t)⁻¹` in the path parameter, dominate the contour integrand by the
inverse distance to the spectrum, and pass continuity through the contour
Bochner integral.  Derive an explicit Lipschitz estimate when the contour
margin is quantitative. 

Lean proof route for a weaker agent:

1. Unfold `continuedProjection` and `operatorPath` and reuse the local resolvent estimates from `continuous_rieszProjection_path`.
2. At each `t∈[0,1]`, obtain a neighborhood on which the fixed contour remains in the resolvent set; this suffices for `ContinuousWithinAt`.
3. Pass the local resolvent continuity through the contour integral and assemble the pointwise statements into `ContinuousOn`.


Ext-agent signature audit (GPT 5.6 High): The corrected `ContinuousOn [0,1]` signature
asks only for separation on the path segment actually used. A global continuity theorem
remains available in the resolvent module.

Preferred dependency route: Use a uniformly separating Riesz contour on `[0,1]`,
norm-continuity of resolvents, and local equivalences of close projection ranges.
-/
theorem continuous_continuedProjection
    (A H : E →L[𝕜] E) (s : Set ℝ) (contour : ℝ → 𝕜)
    (hsep : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ContourSeparatesSpectrum (operatorPath A H t) s contour) :
    ContinuousOn (continuedProjection A H contour) (Set.Icc (0 : ℝ) 1) := by
  sorry

/-- Two orthogonal projections belong to the same norm-continuous component. -/
def SameProjectionComponent (P Q : E →L[𝕜] E) : Prop :=
  ∃ path : ℝ → E →L[𝕜] E,
    ContinuousOn path (Set.Icc (0 : ℝ) 1) ∧ path 0 = P ∧ path 1 = Q ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, IsOrthogonalProjection (path t)

/-- The continued projection remains in the component selected at `t = 0`. 

Lean proof route for a weaker agent:

1. Use the supplied continued projection path restricted to `[0,1]` as the witness.
2. Reuse `hcontinuous` for path continuity and `hproj` for projection-valuedness.
3. Normalize the endpoints with `rfl`; no spectral argument is needed in this lemma.


Ext-agent signature audit (GPT 5.6 High): Correct after `SameProjectionComponent` was
localized to continuity on `[0,1]`; global continuity would be unnecessary
overstrengthening.

Preferred dependency route: Use a uniformly separating Riesz contour on `[0,1]`,
norm-continuity of resolvents, and local equivalences of close projection ranges.
-/
theorem continuedProjection_same_component
    (A H : E →L[𝕜] E) (contour : ℝ → 𝕜)
    (hcontinuous : ContinuousOn (continuedProjection A H contour)
      (Set.Icc (0 : ℝ) 1))
    (hproj : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      IsOrthogonalProjection (continuedProjection A H contour t)) :
    SameProjectionComponent
      (continuedProjection A H contour 0)
      (continuedProjection A H contour 1) := by
  sorry

/-- Continued Riesz projections select the spectral component born from the
initial component. 

Lean proof route for a weaker agent:

1. Use `rieszProjection_eq_spectralProjection` at `t=1`, passing `hs`.
2. Verify that `operatorPath A H 1 = A+H` by `simp [operatorPath]`.
3. Specialize the uniformly separating-contour hypothesis at `1 ∈ [0,1]`.


Ext-agent signature audit (GPT 5.6 High): Correct with the explicit measurability
premise if the fixed contour encloses the same Borel spectral component throughout the
path. At `t=1`, self-adjointness follows from `hA` and `hH`.

Preferred dependency route: Use a uniformly separating Riesz contour on `[0,1]`,
norm-continuity of resolvents, and local equivalences of close projection ranges.
-/
theorem continuedProjection_eq_spectralProjection
    (A H : E →L[𝕜] E) (hA : IsSelfAdjointOperator A)
    (hH : IsSelfAdjointOperator H) (s : Set ℝ) (hs : MeasurableSet s)
    (contour : ℝ → 𝕜)
    (hsep : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ContourSeparatesSpectrum (operatorPath A H t) s contour) :
    continuedProjection A H contour 1 = spectralProjection (A + H) s := by
  sorry

/-- Norm-close projections have canonically isomorphic ranges; this is the
local step used to propagate dimension and Fredholm-index data along a path.

Proof strategy: for projections `P,Q` with `‖P-Q‖<1`, show `Q|Ran(P)` is
bounded below and `P|Ran(Q)` is its inverse up to the invertible positive
operators `PQP` and `QPQ`.  Construct the canonical range equivalence using
the polar factor of `QP`, or equivalently `(PQP)^{-1/2}`.  This lemma replaces
finite rank counting in the infinite branch-selection proof. 

Lean proof route for a weaker agent:

1. Prove `Q` restricted to `Ran P` is bounded below by `1-‖P-Q‖`.
2. Show its range is closed and its orthogonal complement is trivial, hence it is bijective onto `Ran Q`.
3. Take the polar factor of `QP` to obtain a unitary between the ranges and extend it over complements.
4. Verify the global intertwining equation.


Ext-agent signature audit (GPT 5.6 High): Correct. Close orthogonal projections have
unitarily equivalent ranges and complements; the global unitary intertwiner is stronger
than a mere range isomorphism but standard.

Preferred dependency route: Use a uniformly separating Riesz contour on `[0,1]`,
norm-continuity of resolvents, and local equivalences of close projection ranges.
-/
theorem range_equiv_of_projection_norm_lt_one
    (P Q : E →L[𝕜] E)
    (hP : IsOrthogonalProjection P) (hQ : IsOrthogonalProjection Q)
    (hclose : ‖P - Q‖ < 1) :
    ∃ W : E →L[𝕜] E, IsUnitaryOperator W ∧ W ∘L P = Q ∘L W := by
  sorry

end DavisKahanExt
end ForMathlib
