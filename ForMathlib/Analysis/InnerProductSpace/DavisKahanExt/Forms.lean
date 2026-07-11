/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import ForMathlib.Analysis.InnerProductSpace.DavisKahanExt.UnboundedRiccati

/-!
# Quadratic-form perturbations

Literature writeup: local TeX, Sections 30--31.  Form perturbations are needed
for Schrödinger operators and PDE applications where operator differences are
not bounded on the ambient Hilbert space.
-/

namespace ForMathlib
namespace DavisKahanExt

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- Closed symmetric sesquilinear form, represented at roadmap level. -/
structure ClosedForm where
  domain : Submodule 𝕜 E
  form : domain → domain → 𝕜
  dense_domain : Dense (domain : Set E)
  hermitian : ∀ x y, star (form x y) = form y x
  closedness : Prop

/-- Relative form boundedness. -/
def FormRelativelyBounded (a v : ClosedForm (𝕜 := 𝕜) (E := E))
    (alpha beta : ℝ) : Prop :=
  ∃ hdom : v.domain = a.domain,
    ∀ x : a.domain,
      ‖v.form (hdom.symm ▸ x) (hdom.symm ▸ x)‖ ≤
        alpha * ‖(x : E)‖ ^ 2 + beta * ‖a.form x x‖

/-- Closed form sum, constructed under a relative-bound hypothesis. -/
noncomputable def formSum
    (a v : ClosedForm (𝕜 := 𝕜) (E := E)) :
    ClosedForm (𝕜 := 𝕜) (E := E) := by
  sorry

/-- Operator associated with a closed semibounded form. -/
noncomputable def ClosedForm.associatedOperator
    (a : ClosedForm (𝕜 := 𝕜) (E := E)) :
    ClosedOperator (𝕜 := 𝕜) (E := E) := by
  sorry

/-- KLMN theorem.

Proof strategy: shift the reference form to make its form norm coercive and
complete.  Relative form bound below one proves equivalence of the original
and perturbed form norms, hence closedness of the sum.  Establish lower
semiboundedness by absorbing the relative term.  The representation theorem
then produces the associated self-adjoint operator.  Formalization should
first package the form-domain Hilbert space and bounded inclusion into the
ambient space. -/
theorem klmn
    (a v : ClosedForm (𝕜 := 𝕜) (E := E))
    {alpha beta : ℝ} (hrel : FormRelativelyBounded a v alpha beta)
    (hbeta : beta < 1) :
    (formSum a v).closedness := by
  sorry

/-- Form-version `sin Θ` theorem. -/
theorem sinTheta_formPerturbation
    (a v : ClosedForm (𝕜 := 𝕜) (E := E))
    {alpha beta d : ℝ} (hrel : FormRelativelyBounded a v alpha beta)
    (hbeta : beta < 1) (hd : 0 < d) (s t : Set ℝ) :
    ‖a.associatedOperator.spectralProjection s -
      (formSum a v).associatedOperator.spectralProjection t‖ ≤
      (alpha + beta) / d := by
  sorry

end DavisKahanExt
end ForMathlib
