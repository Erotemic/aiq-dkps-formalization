/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import ForMathlib.Analysis.InnerProductSpace.DavisKahanExt.SymmetricIdeals
import ForMathlib.Analysis.InnerProductSpace.DavisKahanExt.Resolvent

/-!
# Infinite-dimensional Sylvester equations

The operator equation `A X - X B = C` is the analytic engine behind the
infinite-dimensional `sin Θ` and residual theorems.

Literature writeup: local TeX, Sections 10--11.
-/

namespace ForMathlib
namespace DavisKahanExt

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [CompleteSpace F]

/-- Sylvester operator `X ↦ A X - X B`. -/
def sylvesterOperator (A : F →L[𝕜] F) (B : E →L[𝕜] E)
    (X : E →L[𝕜] F) : E →L[𝕜] F :=
  A ∘L X - X ∘L B

/-- Resolvent/Bochner integral candidate for the Sylvester solution. -/
noncomputable def sylvesterResolventIntegral (A : F →L[𝕜] F)
    (B : E →L[𝕜] E) (C : E →L[𝕜] F) : E →L[𝕜] F := by
  sorry

/-- Canonical solution selected by the resolvent integral. -/
noncomputable def solveSylvester (A : F →L[𝕜] F)
    (B : E →L[𝕜] E) (C : E →L[𝕜] F) : E →L[𝕜] F := by
  sorry

/-- Bochner/resolvent integral representation of the solution.

Proof strategy for the ordered case: shift the operators so that `A >= d/2`
and `B <= -d/2`, then use the semigroup formula

`X = ∫ t in Set.Ioi 0, exp(-t A) ∘ C ∘ exp(t B)`.

Prove strong measurability of the operator-valued integrand, dominate its norm
by `exp(-d t) ‖C‖`, and obtain Bochner integrability.  Evaluate finite-interval
integrals using the derivative of the exponential product, then pass to the
limit.  Keep the contour/Fourier representation as a separate implementation
for arbitrary separated spectra; it is responsible for the `pi/2` constant. 

Lean proof route for a weaker agent:

1. Unfold `solveSylvester`; if it is defined by uniqueness, show the integral candidate solves the equation.
2. Justify Bochner integrability using the separated-spectrum resolvent or semigroup bounds.
3. Differentiate/integrate the truncated formula and pass to the limit.
4. Invoke `sylvester_unique` to identify the canonical solution with the integral.


Ext-agent signature audit (GPT 5.6 High): This unconditional equality is sound only
because `solveSylvester` is intended to be defined by the displayed integral (or by a
choice provably equal to it). It is not an existence theorem without separation.

Preferred dependency route: Prove the ordered semigroup estimate first, then the general
Fourier-multiplier estimate; derive uniqueness and ideal variants from those inverse
bounds.
-/
theorem solveSylvester_eq_resolventIntegral
    (A : F →L[𝕜] F) (B : E →L[𝕜] E) (C : E →L[𝕜] F) :
    solveSylvester A B C = sylvesterResolventIntegral A B C := by
  sorry

/-- The resolvent solution satisfies the equation under separated spectra. 

Lean proof route for a weaker agent:

1. Use `solveSylvester_eq_resolventIntegral`.
2. Evaluate the Sylvester operator on truncated contour/semigroup integrals.
3. Show the boundary terms converge to zero from spectral separation.
4. Pass the bounded linear Sylvester operator through the integral and obtain `C`.


Ext-agent signature audit (GPT 5.6 High): Correct under positive spectral separation.
The implementation should make the selected solution independent of auxiliary contours.

Preferred dependency route: Prove the ordered semigroup estimate first, then the general
Fourier-multiplier estimate; derive uniqueness and ideal variants from those inverse
bounds.
-/
theorem sylvester_solve
    {A : F →L[𝕜] F} {B : E →L[𝕜] E}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {d : ℝ} (hd : 0 < d)
    (hsep : SpectraSeparated A ⊤ B ⊤ d)
    (C : E →L[𝕜] F) :
    sylvesterOperator A B (solveSylvester A B C) = C := by
  sorry

/-- Uniqueness of the bounded Sylvester solution. 

Lean proof route for a weaker agent:

1. Apply the general separated-spectrum norm estimate to `X-Y` with right-hand side zero.
2. Use linearity of `sylvesterOperator` and `hX` to prove its defect is zero.
3. Since `d>0`, conclude `‖X-Y‖=0`, then extensionality gives `X=Y`.


Ext-agent signature audit (GPT 5.6 High): Correct and best proved from the general
separated-spectrum estimate, not by duplicating resolvent algebra.

Preferred dependency route: Prove the ordered semigroup estimate first, then the general
Fourier-multiplier estimate; derive uniqueness and ideal variants from those inverse
bounds.
-/
theorem sylvester_unique
    {A : F →L[𝕜] F} {B : E →L[𝕜] E}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {d : ℝ} (hd : 0 < d)
    (hsep : SpectraSeparated A ⊤ B ⊤ d)
    {X Y : E →L[𝕜] F}
    (hX : sylvesterOperator A B X = sylvesterOperator A B Y) :
    X = Y := by
  sorry

/-- Sharp constant-one estimate when one spectrum lies in a gap or the convex
hulls are disjoint.

Proof strategy: reduce the spectral hypothesis to ordered quadratic-form
bounds by an affine shift and, when necessary, split the exterior spectrum
into its lower and upper pieces.  Apply the semigroup solution formula and the
bounds

`‖exp(-t A)‖ <= exp(-a t)` and `‖exp(t B)‖ <= exp(b t)`.

Integrating gives `‖X‖ <= ‖C‖ / (a-b)`.  For interval/exterior separation,
solve the two orthogonal spectral pieces separately and recombine them using
orthogonality.  This is the first analytic theorem to prove because its finite
specialization immediately replaces duplicated operator-norm arguments. 

Lean proof route for a weaker agent:

1. Shift `A,B` so the spectral bounds become `A≥d/2` and `B≤-d/2`.
2. Represent `X` by the semigroup integral `∫₀∞ exp(-tA) C exp(tB) dt`.
3. Bound the integrand by `exp(-dt)‖C‖` using functional calculus.
4. Integrate, use uniqueness, and multiply by `d`.


Ext-agent signature audit (GPT 5.6 High): The orientation is correct for `A X - X B`:
the hypothesis says the spectrum of `A` lies at least `d` above that of `B`.
Interval/exterior splitting should be a separate corollary.

Preferred dependency route: Prove the ordered semigroup estimate first, then the general
Fourier-multiplier estimate; derive uniqueness and ideal variants from those inverse
bounds.
-/
theorem norm_sylvester_le_of_orderedSeparation
    {A : F →L[𝕜] F} {B : E →L[𝕜] E} {X C : E →L[𝕜] F}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {d : ℝ} (hd : 0 < d)
    (hsep : OrderedSpectraSeparated B ⊤ A ⊤ d)
    (hEq : sylvesterOperator A B X = C) :
    d * ‖X‖ ≤ ‖C‖ := by
  sorry

/-- General separated-spectrum estimate with the `π / 2` constant.

Proof strategy: do not derive this from the ordered theorem.  Choose a scalar
function `f` with Fourier transform representing `1 / (lam-mu)` on pairs of
spectral points at distance at least `d`.  Express the inverse Sylvester map as
an operator integral of left and right unitary groups.  The scalar multiplier
lemma gives total variation `pi/(2*d)`, hence the norm bound.  Formalization
should isolate:

1. the scalar Fourier/multiplier construction;
2. Bochner integration of the two-sided unitary orbit;
3. evaluation of the Sylvester defect;
4. the final `L1` estimate.

This theorem belongs after the constant-one ordered theory. 

Lean proof route for a weaker agent:

1. Use the scalar Fourier multiplier for `1/(a-b)` on pairs separated by `d`.
2. Represent `X` as an integral of `exp(itA) C exp(-itB)` against that measure.
3. Bound every unitary orbit term by `‖C‖` and integrate total variation `π/(2d)`.
4. Use uniqueness of the Sylvester solution to identify the integral with the given `X`.


Ext-agent signature audit (GPT 5.6 High): Correct with the universal `π/2` constant for
arbitrary separated self-adjoint spectra. Do not accidentally claim constant one from
absolute pairwise separation alone.

Preferred dependency route: Prove the ordered semigroup estimate first, then the general
Fourier-multiplier estimate; derive uniqueness and ideal variants from those inverse
bounds.
-/
theorem norm_sylvester_le_of_generalSeparation
    {A : F →L[𝕜] F} {B : E →L[𝕜] E} {X C : E →L[𝕜] F}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {d : ℝ} (hd : 0 < d)
    (hsep : SpectraSeparated A ⊤ B ⊤ d)
    (hEq : sylvesterOperator A B X = C) :
    d * ‖X‖ ≤ (Real.pi / 2) * ‖C‖ := by
  sorry

/-- Symmetric-ideal Sylvester estimate. 

Lean proof route for a weaker agent:

1. Represent the inverse Sylvester map by the same Fourier/resolvent integral used for the operator norm theorem.
2. Use the ideal bound to estimate each left/right unitary translate without changing the gauge.
3. Integrate the scalar total variation to get `π/(2d)`.
4. Approximate the integral by finite sums to prove the solution remains in the complete ideal, then return membership and the bound.


Ext-agent signature audit (GPT 5.6 High): Correct for a square symmetric ideal on one
Hilbert space. A rectangular ideal version would require a separate bimodule API and
should not be inferred from this signature.

Preferred dependency route: Prove the ordered semigroup estimate first, then the general
Fourier-multiplier estimate; derive uniqueness and ideal variants from those inverse
bounds.
-/
theorem ideal_sylvester_le
    (I : SymmetricNormIdeal (𝕜 := 𝕜) (E := E))
    {A B X C : E →L[𝕜] E}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {d : ℝ} (hd : 0 < d)
    (hsep : SpectraSeparated A ⊤ B ⊤ d)
    (hEq : sylvesterOperator A B X = C) (hCmem : I.mem C) :
    I.mem X ∧ d * I.gauge X ≤ (Real.pi / 2) * I.gauge C := by
  sorry

end DavisKahanExt
end ForMathlib
