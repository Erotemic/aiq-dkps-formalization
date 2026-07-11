/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import ForMathlib.Analysis.InnerProductSpace.DavisKahan.Projector
import Mathlib.Analysis.InnerProductSpace.Rayleigh

/-!
# Real spectral bridge roadmap

The supported bounded theorem is already scalar-generic.  This module records
the missing real-Hilbert-space bridge from actual spectra to quadratic-form
bounds.  A direct Rayleigh-shift proof is preferred; complexification is a
secondary route.  The declarations here are excluded from the supported
umbrella until the bridge is discharged.
-/


/-! ## Weak-agent execution plan: the real spectral-order bridge

Do not try to prove `upperFormBoundOn_top_of_spectrum_subset_Iic` by rewriting
complex CFC theorems under real scalars; the missing instance is the substance
of the problem.  Choose one of the following routes and complete its helper
API first.

### Preferred route: minimal norm-preserving complexification

1. Introduce a complex Hilbert space `Complexification E` and an isometric
   real-linear embedding `ofReal : E →ₗᵢ[ℝ] Complexification E`.
2. Extend a real bounded operator `A` to a complex-linear operator
   `complexify A`, with simp lemmas for application to `ofReal x`, adjoint,
   subtraction, scalar shifts, and quadratic forms.
3. Prove self-adjointness transports and prove the real spectrum is the real
   part of the complex spectrum for self-adjoint `A`.  It is enough here to
   prove the one-sided implication needed for the upper spectral bound.
4. Apply the existing complex theorem
   `upperFormBoundOn_top_of_spectrum_subset_Iic` to `complexify A` and pull the
   quadratic-form inequality back along `ofReal`.

Keep complexification lemmas in the dedicated foundation module; this bridge
should contain only the final transport.

### Alternative route: real CFC/star order

Construct the missing real continuous-functional-calculus instance for
self-adjoint operators, then prove that spectrum containment of `cI-A` in
`[0,∞)` implies positivity.  Convert positivity to the displayed quadratic
form inequality.  Do not use the norm bound `‖A‖ ≤ c`; it loses sign
information and is insufficient.

### Proof organization

First prove a global theorem on `⊤`; the lower theorem is negation, and the
restricted theorems should remain pure transport through
`ContinuousLinearMap.IsSymmetric.restrict_of_invariant`.  Test every coercion
between continuous and plain linear maps in a tiny local `example` before
embedding it into the restriction proof.
-/

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace Foundation
namespace RealSpectralBridge

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Real spectral upper bound implies a global quadratic-form upper bound.

This is the one genuinely missing theorem in the real bridge.  The preferred
proof is the direct Rayleigh-shift argument:

1. choose `m > ‖A‖` and set `S = A + m • 1`;
2. translate the spectrum with `spectrum.singleton_add_eq`, so every spectral
   value of `S` lies in `(0, m + c]`;
3. use `ContinuousLinearMap.spectralRadius_eq_nnnorm` for the self-adjoint
   operator `S` and positivity of its real spectrum to show `‖S‖ ≤ m + c`;
4. apply `abs_re_inner_le_norm` (or the Rayleigh quotient bound) to `S x` and
   subtract `m * ‖x‖ ^ 2`.

The technical seam is step 3: `spectralRadius` records absolute values, so the
proof must explicitly use the positive shifted spectrum before converting the
spectral-radius supremum into the upper endpoint.  Do not replace this theorem
with an opaque real-spectrum definition; all downstream real results reduce to
this single bridge.

Implementation strategy: isolate lemmas for shifted-spectrum positivity,
nonemptiness of a real self-adjoint spectrum from
`spectralRadius_eq_nnnorm`, and conversion of the attained spectral radius to
an ordinary real norm before assembling the final Rayleigh estimate. -/
theorem upperFormBoundOn_top_of_spectrum_subset_Iic
    (A : E →L[ℝ] E) (hA : A.IsSymmetric) {c : ℝ}
    (hσ : spectrum ℝ A ⊆ Set.Iic c) :
    UpperFormBoundOn A ⊤ c := by
  sorry

/-- Real spectral lower bound implies a global quadratic-form lower bound.

This is derived from the upper bridge by negating the operator; it is not a
second spectral-theorem obligation. -/
theorem lowerFormBoundOn_top_of_spectrum_subset_Ici
    (A : E →L[ℝ] E) (hA : A.IsSymmetric) {c : ℝ}
    (hσ : spectrum ℝ A ⊆ Set.Ici c) :
    LowerFormBoundOn A ⊤ c := by
  have hnegA : (-A).IsSymmetric := by
    intro x y
    change ⟪-A x, y⟫_ℝ = ⟪x, -A y⟫_ℝ
    simpa using congrArg Neg.neg (hA x y)
  have hnegσ : spectrum ℝ (-A) ⊆ Set.Iic (-c) := by
    intro r hr
    have hr' : r ∈ -spectrum ℝ A := by
      rwa [spectrum.neg_eq]
    have hmr : -r ∈ spectrum ℝ A := by
      simpa only [Set.mem_neg] using hr'
    have := hσ hmr
    linarith
  have hupper := upperFormBoundOn_top_of_spectrum_subset_Iic (-A) hnegA hnegσ
  intro x hx
  have hx' := hupper x hx
  simp only [ContinuousLinearMap.neg_apply, inner_neg_left, map_neg] at hx'
  linarith

/-- Real restriction-spectrum upper bridge on an orthogonally complemented
subspace.  Completeness and symmetry of the actual restriction reduce this to
the global upper bridge. -/
theorem upperFormBoundOn_of_restriction_spectrum_subset_Iic
    {A : E →L[ℝ] E} (hA : A.IsSymmetric)
    {U : Submodule ℝ E} [U.HasOrthogonalProjection]
    (hU : ∀ x ∈ U, A x ∈ U) {c : ℝ}
    (hσ : spectrum ℝ (A.restrict hU) ⊆ Set.Iic c) :
    UpperFormBoundOn A U c := by
  letI : CompleteSpace U :=
    completeSpace_coe_iff_isComplete.mpr U.isComplete_coe_of_hasOrthogonalProjection
  have hres : (A.restrict hU).IsSymmetric :=
    ContinuousLinearMap.IsSymmetric.restrict_of_invariant (A := A) hA hU
  have htop := upperFormBoundOn_top_of_spectrum_subset_Iic
    (A.restrict hU) hres hσ
  intro x hx
  have h := htop (⟨x, hx⟩ : U) Submodule.mem_top
  change RCLike.re ⟪A x, x⟫_ℝ ≤ c * ‖x‖ ^ 2 at h
  exact h

/-- Real restriction-spectrum lower bridge on an orthogonally complemented
subspace.  Completeness and symmetry of the actual restriction reduce this to
the global lower bridge. -/
theorem lowerFormBoundOn_of_restriction_spectrum_subset_Ici
    {A : E →L[ℝ] E} (hA : A.IsSymmetric)
    {U : Submodule ℝ E} [U.HasOrthogonalProjection]
    (hU : ∀ x ∈ U, A x ∈ U) {c : ℝ}
    (hσ : spectrum ℝ (A.restrict hU) ⊆ Set.Ici c) :
    LowerFormBoundOn A U c := by
  letI : CompleteSpace U :=
    completeSpace_coe_iff_isComplete.mpr U.isComplete_coe_of_hasOrthogonalProjection
  have hres : (A.restrict hU).IsSymmetric :=
    ContinuousLinearMap.IsSymmetric.restrict_of_invariant (A := A) hA hU
  have htop := lowerFormBoundOn_top_of_spectrum_subset_Ici
    (A.restrict hU) hres hσ
  intro x hx
  have h := htop (⟨x, hx⟩ : U) Submodule.mem_top
  change c * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℝ at h
  exact h

/-- Target sharp real Davis--Kahan theorem from spectra of actual
restrictions. -/
theorem opNorm_starProjection_sub_le_of_restriction_spectra
    {A B : E →L[ℝ] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U W : Submodule ℝ E} [U.HasOrthogonalProjection]
    [W.HasOrthogonalProjection]
    (hU : A.Reduces U) (hW : B.Reduces W)
    {c g : ℝ} (hg : 0 < g)
    (hUhi : spectrum ℝ (A.restrict hU.1) ⊆ Set.Ici (c + g))
    (hUlo : spectrum ℝ (A.restrict hU.2) ⊆ Set.Iic c)
    (hWhi : spectrum ℝ (B.restrict hW.1) ⊆ Set.Ici (c + g))
    (hWlo : spectrum ℝ (B.restrict hW.2) ⊆ Set.Iic c) :
    ‖(U.starProjection - W.starProjection : E →L[ℝ] E)‖ ≤ ‖B - A‖ / g := by
  apply DavisKahan.opNorm_starProjection_sub_le_of_formBounds hA hB hU hW hg
  · exact lowerFormBoundOn_of_restriction_spectrum_subset_Ici hA hU.1 hUhi
  · exact upperFormBoundOn_of_restriction_spectrum_subset_Iic hA hU.2 hUlo
  · exact lowerFormBoundOn_of_restriction_spectrum_subset_Ici hB hW.1 hWhi
  · exact upperFormBoundOn_of_restriction_spectrum_subset_Iic hB hW.2 hWlo

end RealSpectralBridge
end Foundation
end Experimental
end DavisKahan
end ForMathlib
