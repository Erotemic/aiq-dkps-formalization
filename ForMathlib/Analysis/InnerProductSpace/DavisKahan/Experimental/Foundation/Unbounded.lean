/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import ForMathlib.Analysis.InnerProductSpace.DavisKahanExt.DirectRotation

/-!
# Closed and unbounded self-adjoint operators

This file introduces an explicit roadmap-level closed-operator interface.  It
is intended to be reconciled with mathlib's `LinearPMap` API as that API gains
closedness, graph norms, resolvents, and unbounded spectral calculus.

Literature writeup: local TeX, Sections 26--29.
-/


/-! ## Construction plan

The current roadmap structures should be replaced by graph-based analytic
objects before the literature theorems depend on them.

1. Represent a densely defined operator by a domain submodule and a linear map
   into the ambient Hilbert space; define closedness through its graph.
2. Construct the adjoint from bounded functionals on the graph/domain and prove
   density/closedness properties.
3. Define addition of a bounded operator by restricting it to the same domain;
   prove graph-norm equivalence for relatively bounded perturbations.
4. Obtain the real spectrum and spectral projections only for self-adjoint
   closed operators through the unbounded spectral theorem.
5. Define `addRelative` and the spectral projection constructor from these
   verified operations rather than from arbitrary total choices.
-/

namespace ForMathlib
namespace DavisKahanExt

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- Densely defined closed operator. -/
structure ClosedOperator where
  domain : Submodule 𝕜 E
  toLinearMap : domain →ₗ[𝕜] E
  dense_domain : Dense (domain : Set E)
  closed_graph : IsClosed (Set.range fun x : domain => ((x : E), toLinearMap x))

namespace ClosedOperator

/-- Extension relation for partially defined operators. -/
def Extends (A B : ClosedOperator (𝕜 := 𝕜) (E := E)) : Prop :=
  ∃ hdom : A.domain ≤ B.domain,
    ∀ x : A.domain,
      B.toLinearMap ⟨(x : E), hdom x.property⟩ = A.toLinearMap x

/-- Symmetric closed operator. -/
def IsSymmetric (A : ClosedOperator (𝕜 := 𝕜) (E := E)) : Prop :=
  ∀ x y : A.domain, ⟪A.toLinearMap x, (y : E)⟫_𝕜 = ⟪(x : E), A.toLinearMap y⟫_𝕜

/-- Adjoint of a densely defined closed operator.  The implementation should
be reconciled with mathlib's partial-linear-map adjoint API.

Construction route: define the domain as vectors `y` for which
`x ↦ ⟪A x, y⟫` is ambient-norm bounded on the dense domain, use Riesz
representation for the representing vector, and prove the resulting graph is
closed. -/
noncomputable def adjoint
    (A : ClosedOperator (𝕜 := 𝕜) (E := E)) :
    ClosedOperator (𝕜 := 𝕜) (E := E) := by
  sorry

/-- A closed operator is self-adjoint when it equals its Hilbert-space adjoint.

Maximal symmetry alone is not used here: a maximal symmetric operator can fail
to be self-adjoint when its deficiency indices are unequal. -/
def IsSelfAdjoint (A : ClosedOperator (𝕜 := 𝕜) (E := E)) : Prop :=
  A.adjoint = A

/-- Graph norm. -/
noncomputable def graphNorm (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (x : A.domain) : ℝ :=
  Real.sqrt (‖(x : E)‖ ^ 2 + ‖A.toLinearMap x‖ ^ 2)

/-- Sum with a bounded perturbation, on the original domain.

Construction route: retain `A.domain`, define the graph map by
`x ↦ A x + V x`, and prove closedness by showing the new graph norm is
equivalent to the old one using boundedness of `V`. -/
noncomputable def addBounded (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (V : E →L[𝕜] E) : ClosedOperator (𝕜 := 𝕜) (E := E) := by
  sorry

/-- Relative boundedness with respect to a closed operator. -/
def RelativelyBounded (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (V : A.domain →ₗ[𝕜] E) (a b : ℝ) : Prop :=
  ∀ x, ‖V x‖ ≤ a * ‖(x : E)‖ + b * ‖A.toLinearMap x‖

/-- Real spectrum of a self-adjoint closed operator.

Construction route: define the resolvent through bijectivity and boundedness of
`A - z`, obtain the complex spectrum first, and use self-adjointness to prove it
lies on the real axis.  The permanent API should be tied to the unbounded
spectral theorem rather than chosen independently. -/
noncomputable def realSpectrum
    (A : ClosedOperator (𝕜 := 𝕜) (E := E)) : Set ℝ := by
  sorry

/-- Spectral-set separation for closed operators, possibly acting on
different Hilbert spaces.  The separation condition depends only on the two
real spectra, so requiring a common ambient space would be artificial and
would block the diagonal-block Riccati theory. -/
def SpectralSetsSeparated
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    [CompleteSpace F]
    (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (B : ClosedOperator (𝕜 := 𝕜) (E := F))
    (s t : Set ℝ) (d : ℝ) : Prop :=
  ∀ a ∈ A.realSpectrum, a ∈ s →
    ∀ b ∈ B.realSpectrum, b ∈ t → d ≤ |a - b|

/-- Sum with a relatively bounded operator on the same domain.

The relative-bound hypotheses are part of the constructor because an arbitrary
linear perturbation on `A.domain` need not have closed graph. -/
noncomputable def addRelative
    (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (V : A.domain →ₗ[𝕜] E) {a b : ℝ}
    (ha : 0 ≤ a) (hb0 : 0 ≤ b)
    (hrel : RelativelyBounded A V a b) (hb : b < 1) :
    ClosedOperator (𝕜 := 𝕜) (E := E) := by
  sorry

/-- Unbounded spectral projection. -/
noncomputable def spectralProjection
    (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (s : Set ℝ) : E →L[𝕜] E := by
  sorry

/-- Kato--Rellich theorem for bounded perturbations. 

Lean proof route for a weaker agent:

1. Show the bounded sum has the same dense domain and closed graph as `A` by graph-norm equivalence.
2. Prove symmetry using `hA` and `hV`.
3. Apply bounded Kato--Rellich, or factor the nonreal resolvent and use a Neumann series for sufficiently large imaginary part.
4. Use the adjoint/resolvent characterization to prove equality with the Hilbert-space adjoint.


Ext-agent signature audit (GPT 5.6 High): Correct Kato--Rellich bounded-perturbation
target. It depends on the genuine adjoint equality, not maximal symmetry.

Preferred dependency route: Reconcile `ClosedOperator` with a genuine partial-operator
adjoint/resolvent API before attempting Kato--Rellich or unbounded spectral projection
arguments.
-/
theorem isSelfAdjoint_addBounded
    (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) (V : E →L[𝕜] E)
    (hV : IsSelfAdjointOperator V) :
    (A.addBounded V).IsSelfAdjoint := by
  sorry

/-- Kato--Rellich theorem for relatively bounded perturbations with relative
bound below one.

Proof strategy: equip the common domain with the graph norm of `A`.  Relative
boundedness with coefficient below one makes the perturbed graph norm
equivalent to the original graph norm, so `A+B` is closed.  Prove surjectivity
of `A+B-z` for one nonreal `z` by factoring

`A+B-z = (I + B(A-z)⁻¹)(A-z)`

and applying a Neumann series after choosing `|Im z|` large enough.  Symmetry
plus surjectivity at `z` and `conj z` yields self-adjointness.  Reconcile the
local `ClosedOperator` structure with mathlib's partial-map adjoint API before
attempting this proof. 

Lean proof route for a weaker agent:

1. Use `ha`, `hb0`, `hrel`, and `hb<1` to prove equivalence of the graph norms of `A` and `A+V`.
2. Deduce closedness and density of the perturbed operator and use `hV` for symmetry.
3. Choose a nonreal spectral parameter with small `V(A-z)⁻¹` norm and invert by Neumann series.
4. Use the standard resolvent criterion for self-adjointness.


Ext-agent signature audit (GPT 5.6 High): Correct after `addRelative` was made to carry
nonnegative relative-bound parameters and a bound below one. The symmetry hypothesis on
`V` remains essential.

Preferred dependency route: Reconcile `ClosedOperator` with a genuine partial-operator
adjoint/resolvent API before attempting Kato--Rellich or unbounded spectral projection
arguments.
-/
theorem isSelfAdjoint_of_relativelyBounded
    (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) (V : A.domain →ₗ[𝕜] E)
    (hV : ∀ x y : A.domain,
      ⟪V x, (y : E)⟫_𝕜 = ⟪(x : E), V y⟫_𝕜)
    {a b : ℝ} (ha : 0 ≤ a) (hb0 : 0 ≤ b)
    (hrel : RelativelyBounded A V a b) (hb : b < 1) :
    (A.addRelative V ha hb0 hrel hb).IsSelfAdjoint := by
  sorry

/-- Unbounded-operator `sin Θ` theorem with bounded difference. 

Lean proof route for a weaker agent:

1. Use the unbounded spectral theorem to form the two spectral projections.
2. Derive the weak Sylvester equation between their ranges on `dom A`; the bounded perturbation supplies the residual.
3. Apply the unbounded general separated-spectrum Sylvester estimate in both directions using `hsepAB,hsepBA`.
4. Recombine the directed bounds and retain the universal `π/2` constant. Add a separate interval/exterior corollary for constant one.


Ext-agent signature audit (GPT 5.6 High): Corrected to the generic `π/2` constant for
arbitrary separated spectral sets. Both mixed gaps are still needed for the full
projection difference; a later interval/exterior theorem should recover constant one.

Preferred dependency route: Reconcile `ClosedOperator` with a genuine partial-operator
adjoint/resolvent API before attempting Kato--Rellich or unbounded spectral projection
arguments.
-/
theorem sinTheta_unbounded_boundedPerturbation
    (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) (V : E →L[𝕜] E)
    (hV : IsSelfAdjointOperator V) (s t : Set ℝ)
    (hs : MeasurableSet s) (ht : MeasurableSet t)
    {d : ℝ} (hd : 0 < d)
    (hsepAB : SpectralSetsSeparated A (A.addBounded V) s tᶜ d)
    (hsepBA : SpectralSetsSeparated (A.addBounded V) A t sᶜ d) :
    d * ‖A.spectralProjection s - (A.addBounded V).spectralProjection t‖ ≤
      (Real.pi / 2) * ‖V‖ := by
  sorry

end ClosedOperator
end DavisKahanExt
end ForMathlib
