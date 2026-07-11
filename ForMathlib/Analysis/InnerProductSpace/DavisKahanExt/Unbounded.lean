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

/-- Self-adjointness represented as maximal symmetry. -/
def IsSelfAdjoint (A : ClosedOperator (𝕜 := 𝕜) (E := E)) : Prop :=
  IsSymmetric A ∧
    ∀ B : ClosedOperator (𝕜 := 𝕜) (E := E),
      Extends A B → IsSymmetric B → B.domain = A.domain

/-- Graph norm. -/
noncomputable def graphNorm (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (x : A.domain) : ℝ :=
  Real.sqrt (‖(x : E)‖ ^ 2 + ‖A.toLinearMap x‖ ^ 2)

/-- Sum with a bounded perturbation, on the original domain. -/
noncomputable def addBounded (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (V : E →L[𝕜] E) : ClosedOperator (𝕜 := 𝕜) (E := E) := by
  sorry

/-- Relative boundedness with respect to a closed operator. -/
def RelativelyBounded (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (V : A.domain →ₗ[𝕜] E) (a b : ℝ) : Prop :=
  ∀ x, ‖V x‖ ≤ a * ‖(x : E)‖ + b * ‖A.toLinearMap x‖

/-- Real spectrum of a self-adjoint closed operator. -/
noncomputable def realSpectrum
    (A : ClosedOperator (𝕜 := 𝕜) (E := E)) : Set ℝ := by
  sorry

/-- Spectral-set separation for closed operators. -/
def SpectralSetsSeparated
    (A B : ClosedOperator (𝕜 := 𝕜) (E := E))
    (s t : Set ℝ) (d : ℝ) : Prop :=
  s ⊆ A.realSpectrum ∧ t ⊆ B.realSpectrum ∧
    ∀ a ∈ s, ∀ b ∈ t, d ≤ |a - b|

/-- Sum with a relatively bounded operator on the same domain. -/
noncomputable def addRelative
    (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (V : A.domain →ₗ[𝕜] E) : ClosedOperator (𝕜 := 𝕜) (E := E) := by
  sorry

/-- Unbounded spectral projection. -/
noncomputable def spectralProjection
    (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (s : Set ℝ) : E →L[𝕜] E := by
  sorry

/-- Kato--Rellich theorem for bounded perturbations. -/
theorem isSelfAdjoint_addBounded
    (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) (V : E →L[𝕜] E)
    (hV : IsSelfAdjointOperator V) :
    (A.addBounded V).IsSelfAdjoint := by
  sorry

/-- Kato--Rellich theorem for relatively bounded perturbations with relative
bound below one. -/
theorem isSelfAdjoint_of_relativelyBounded
    (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) (V : A.domain →ₗ[𝕜] E)
    {a b : ℝ} (hrel : RelativelyBounded A V a b) (hb : b < 1) :
    (A.addRelative V).IsSelfAdjoint := by
  sorry

/-- Unbounded-operator `sin Θ` theorem with bounded difference. -/
theorem sinTheta_unbounded_boundedPerturbation
    (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) (V : E →L[𝕜] E)
    (hV : IsSelfAdjointOperator V) (s t : Set ℝ)
    {d : ℝ} (hd : 0 < d)
    (hsep : SpectralSetsSeparated A (A.addBounded V) s tᶜ d) :
    d * ‖A.spectralProjection s - (A.addBounded V).spectralProjection t‖ ≤
      ‖V‖ := by
  sorry

end ClosedOperator
end DavisKahanExt
end ForMathlib
