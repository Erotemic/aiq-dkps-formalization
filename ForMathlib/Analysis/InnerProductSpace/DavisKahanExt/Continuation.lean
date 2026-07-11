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
margin is quantitative. -/
theorem continuous_continuedProjection
    (A H : E →L[𝕜] E) (s : Set ℝ) (contour : ℝ → 𝕜)
    (hsep : ∀ t : ℝ,
      ContourSeparatesSpectrum (operatorPath A H t) s contour) :
    Continuous (continuedProjection A H contour) := by
  sorry

/-- Two orthogonal projections belong to the same norm-continuous component. -/
def SameProjectionComponent (P Q : E →L[𝕜] E) : Prop :=
  ∃ path : ℝ → E →L[𝕜] E,
    Continuous path ∧ path 0 = P ∧ path 1 = Q ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, IsOrthogonalProjection (path t)

/-- The continued projection remains in the component selected at `t = 0`. -/
theorem continuedProjection_same_component
    (A H : E →L[𝕜] E) (contour : ℝ → 𝕜)
    (hproj : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      IsOrthogonalProjection (continuedProjection A H contour t)) :
    SameProjectionComponent
      (continuedProjection A H contour 0)
      (continuedProjection A H contour 1) := by
  sorry

/-- Continued Riesz projections select the spectral component born from the
initial component. -/
theorem continuedProjection_eq_spectralProjection
    (A H : E →L[𝕜] E) (hA : IsSelfAdjointOperator A)
    (hH : IsSelfAdjointOperator H) (s : Set ℝ)
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
finite rank counting in the infinite branch-selection proof. -/
theorem range_equiv_of_projection_norm_lt_one
    (P Q : E →L[𝕜] E)
    (hP : IsOrthogonalProjection P) (hQ : IsOrthogonalProjection Q)
    (hclose : ‖P - Q‖ < 1) :
    ∃ W : E →L[𝕜] E, IsUnitaryOperator W ∧ W ∘L P = Q ∘L W := by
  sorry

end DavisKahanExt
end ForMathlib
