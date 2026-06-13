/-
# AIQ DKPS ForMathlib inventory challenge: Gram geometry and near-isometry

This file imports only Mathlib and mirrors one PR-oriented slice of the
project's `ForMathlib` staging library. The theorem bodies are left as `sorry`
so comparator can check that the project implementation proves the same
declarations.

This is a focused inventory/calibration challenge, not a proposal to upstream
all listed declarations in one PR.
-/
import Mathlib

/-!
## Source: `ForMathlib/Analysis/InnerProductSpace/GramMatrix.lean`
-/
/-
Staged for Mathlib: additions to `Mathlib/Analysis/InnerProductSpace/GramMatrix.lean`.

Formalized by Claude Fable 5 (claude-fable-5[1m]);
to be re-authored per Mathlib's AI-contribution policy at PR time.
-/


/-! # Gram matrix rigidity (exact Procrustes)

Two families of vectors in a finite-dimensional inner product space over
`𝕜 = ℝ, ℂ` have equal Gram matrices if and only if they are related by a single
linear isometry equivalence of the ambient space.

This is the rigidity statement underlying *Procrustes alignment* in classical
multidimensional scaling: a configuration recovered from a Gram matrix is
determined exactly up to an orthogonal (unitary) transformation.

## Main results

* `ForMathlib.inner_linearCombination_linearCombination`: the inner product of two
  finite linear combinations of a vector family, expanded over its Gram data.
* `ForMathlib.exists_linearIsometry_map_eq_of_inner_eq`: the span-level core (two
  possibly-different ambient spaces, no finiteness) — equal pairwise inner
  products give a linear isometry from `span 𝕜 (range φ)` into `F`.
* `ForMathlib.exists_linearIsometryEquiv_map_eq_of_inner_eq`: equal pairwise inner
  products yield a linear isometry equivalence mapping one family to the other.
* `ForMathlib.Matrix.gram_eq_gram_iff_exists_linearIsometryEquiv_map_eq`: the same
  statement packaged as a characterization of `Matrix.gram` equality.

## References

* R. Sibson, *Studies in the robustness of multidimensional scaling:
  Perturbational analysis of classical scaling*, J. Roy. Statist. Soc. Ser. B
  **41** (1979), 217–229.
* I. Borg and P. J. F. Groenen, *Modern Multidimensional Scaling*, 2nd ed.,
  Springer, 2005, Ch. 12.
-/

namespace ForMathlib

open scoped InnerProductSpace

variable {𝕜 E F ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/--
The inner product of two finite linear combinations of a vector family, expanded
over the family's Gram data.
-/
theorem inner_linearCombination_linearCombination (v : ι → E) (a b : ι →₀ 𝕜) :
    ⟪Finsupp.linearCombination 𝕜 v a, Finsupp.linearCombination 𝕜 v b⟫_𝕜
      = a.sum fun i s => b.sum fun j t => starRingEnd 𝕜 s * t * ⟪v i, v j⟫_𝕜 := by
  sorry

/--
**Gram rigidity, span-to-span core.** If two families in possibly different inner
product spaces have equal pairwise inner products, then the map sending one
family to the other is a linear isometry from the first span to the second.
-/
theorem exists_linearIsometry_span_map_eq_of_inner_eq {φ : ι → E} {ψ : ι → F}
    (h : ∀ i j, ⟪φ i, φ j⟫_𝕜 = ⟪ψ i, ψ j⟫_𝕜) :
    ∃ L : (Submodule.span 𝕜 (Set.range φ)) →ₗᵢ[𝕜] (Submodule.span 𝕜 (Set.range ψ)),
      ∀ i, (L ⟨φ i, Submodule.subset_span ⟨i, rfl⟩⟩ : F) = ψ i := by
  sorry

/--
**Gram rigidity, span-to-ambient form.** The span-to-span core composed with the
inclusion `span 𝕜 (range ψ) ↪ F`.
-/
theorem exists_linearIsometry_map_eq_of_inner_eq {φ : ι → E} {ψ : ι → F}
    (h : ∀ i j, ⟪φ i, φ j⟫_𝕜 = ⟪ψ i, ψ j⟫_𝕜) :
    ∃ L : (Submodule.span 𝕜 (Set.range φ)) →ₗᵢ[𝕜] F,
      ∀ i, L ⟨φ i, Submodule.subset_span ⟨i, rfl⟩⟩ = ψ i := by
  sorry

variable [FiniteDimensional 𝕜 E]

/--
**Gram rigidity.** If two families `φ ψ : ι → E` of vectors in a
finite-dimensional inner product space have equal pairwise inner products,
then there is a linear isometry equivalence `W` of `E` with `W (φ i) = ψ i`
for every `i`.
-/
theorem exists_linearIsometryEquiv_map_eq_of_inner_eq {φ ψ : ι → E}
    (h : ∀ i j, ⟪φ i, φ j⟫_𝕜 = ⟪ψ i, ψ j⟫_𝕜) :
    ∃ W : E ≃ₗᵢ[𝕜] E, ∀ i, W (φ i) = ψ i := by
  sorry

namespace Matrix

open _root_.Matrix

/--
**Gram rigidity, `Matrix.gram` form.** Two families of vectors in a
finite-dimensional inner product space have equal Gram matrices if and only if
a linear isometry equivalence of the ambient space maps one family to the other.
-/
theorem gram_eq_gram_iff_exists_linearIsometryEquiv_map_eq {φ ψ : ι → E} :
    gram 𝕜 φ = gram 𝕜 ψ ↔ ∃ W : E ≃ₗᵢ[𝕜] E, ∀ i, W (φ i) = ψ i := by
  sorry
end Matrix

end ForMathlib
/-!
## Source: `ForMathlib/Analysis/InnerProductSpace/NearIsometry.lean`
-/
/-
Staged for Mathlib: a proposed new file `Mathlib/Analysis/InnerProductSpace/NearIsometry.lean`.

Formalized by Claude Fable 5 (claude-fable-5[1m]);
to be re-authored per Mathlib's AI-contribution policy at PR time.
-/


/-! # Quantitative polar factor for a near-isometry

A linear map `M` on a finite-dimensional real inner product space whose quadratic form
`x ↦ ⟪M x, M x⟫` is uniformly `δ`-close to `x ↦ ⟪x, x⟫` (with `δ ≤ 1 / 2`) lies within
`2 * δ` of a genuine linear isometry equivalence: there is `W : E ≃ₗᵢ[ℝ] E` with
`‖M x - W x‖ ≤ 2 * δ * ‖x‖` for all `x`.

The isometry is the *polar factor* `W = M ∘ (Mᵀ ∘ M)^(-1/2)`: the inverse square root of the
Gram operator `G = Mᵀ ∘ M` is built directly from its orthonormal eigenbasis
(`LinearMap.IsSymmetric.eigenvectorBasis`), so the proof uses neither the continuous functional
calculus nor a singular value decomposition.  Mathlib currently has no polar decomposition in
any form, and a future CFC-based polar decomposition would not directly give the quantitative
bound proved here.

The constant `2 * δ` is not sharp: the construction actually yields `√(1 + δ) * δ`, which is
the known sharp constant, but the statement rounds it up to `2 * δ` for usability (as in the
source development).

## Main results

* `ForMathlib.Real.abs_one_sub_inv_sqrt_le`: the scalar inequality `|1 - (√μ)⁻¹| ≤ δ` for
  `|μ - 1| ≤ δ ≤ 1 / 2`, used to control the eigenvalue rescaling.  It belongs with the
  `Real.sqrt` API (`Mathlib/Analysis/Real/Sqrt.lean`) and is staged here next to its consumer.
* `ForMathlib.LinearMap.exists_linearIsometryEquiv_norm_sub_le`: the quantitative polar
  factor, with the pointwise quadratic-form hypothesis
  `|⟪M x, M x⟫ - ⟪x, x⟫| ≤ δ * ⟪x, x⟫`.
* `ForMathlib.ContinuousLinearMap.exists_linearIsometryEquiv_norm_sub_le`: the corollary for
  the operator-norm hypothesis `‖adjoint M * M - 1‖ ≤ δ`.

## TODO

* `TODO(RCLike)`: generalize the two operator results from `ℝ` to `RCLike 𝕜`.  The eigenbasis
  machinery (`LinearMap.IsSymmetric.eigenvectorBasis`) already works over `RCLike`; only the
  real-inner-product bookkeeping below would need to be redone.

## References

* N. J. Higham, *Functions of Matrices: Theory and Computation*, SIAM, 2008, Ch. 8
  (the unitary polar factor as the nearest isometry).
-/

namespace ForMathlib

open scoped RealInnerProductSpace InnerProductSpace
open Module (finrank)

namespace Real

/-- If `|μ - 1| ≤ δ ≤ 1 / 2`, then `|1 - (√μ)⁻¹| ≤ δ`.

The point: `1 - (√μ)⁻¹ = (μ - 1) / (μ + √μ)` and the denominator `μ + √μ ≥ 1` when
`μ ≥ 1 / 2`. -/
theorem abs_one_sub_inv_sqrt_le {μ δ : ℝ} (hδ : δ ≤ 1 / 2) (hμ : |μ - 1| ≤ δ) :
    |1 - (Real.sqrt μ)⁻¹| ≤ δ := by
  sorry
end Real

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

namespace LinearMap

/-- **Quantitative polar factor for a near-isometry.**  If the quadratic form of a linear map
`M` on a finite-dimensional real inner product space is uniformly `δ`-close to the identity
quadratic form (`|⟪M x, M x⟫ - ⟪x, x⟫| ≤ δ * ⟪x, x⟫`, with `δ ≤ 1 / 2`), then `M` differs
from a linear isometry equivalence `W` by at most `2 * δ` pointwise:
`‖M x - W x‖ ≤ 2 * δ * ‖x‖`.

`W` is the polar factor `M ∘ G^(-1/2)` where `G = Mᵀ ∘ M` is the Gram operator; its inverse
square root is built from the orthonormal eigenbasis of `G`, with the eigenvalue rescaling
controlled by `ForMathlib.Real.abs_one_sub_inv_sqrt_le`.  The constant `2 * δ` is not sharp:
the construction gives `√(1 + δ) * δ` (the known sharp constant), and the statement rounds it
up to `2 * δ`. -/
theorem exists_linearIsometryEquiv_norm_sub_le (M : E →ₗ[ℝ] E) {δ : ℝ} (hδ : δ ≤ 1 / 2)
    (hM : ∀ x : E, |⟪M x, M x⟫_ℝ - ⟪x, x⟫_ℝ| ≤ δ * ⟪x, x⟫_ℝ) :
    ∃ W : E ≃ₗᵢ[ℝ] E, ∀ x : E, ‖M x - W x‖ ≤ 2 * δ * ‖x‖ := by
  sorry
end LinearMap

namespace ContinuousLinearMap

/-- **Quantitative polar factor, operator-norm form.**  If a continuous linear map `M` on a
finite-dimensional real inner product space satisfies `‖adjoint M * M - 1‖ ≤ δ` with
`δ ≤ 1 / 2`, then `M` differs from a linear isometry equivalence `W` by at most `2 * δ`
pointwise: `‖M x - W x‖ ≤ 2 * δ * ‖x‖`.

This is a corollary of `ForMathlib.LinearMap.exists_linearIsometryEquiv_norm_sub_le` via
Cauchy–Schwarz: `|⟪M x, M x⟫ - ⟪x, x⟫| = |⟪(adjoint M * M - 1) x, x⟫| ≤ δ * ⟪x, x⟫`. -/
theorem exists_linearIsometryEquiv_norm_sub_le (M : E →L[ℝ] E) {δ : ℝ} (hδ : δ ≤ 1 / 2)
    (hM : ‖ContinuousLinearMap.adjoint M * M - 1‖ ≤ δ) :
    ∃ W : E ≃ₗᵢ[ℝ] E, ∀ x : E, ‖M x - W x‖ ≤ 2 * δ * ‖x‖ := by
  sorry
end ContinuousLinearMap

end ForMathlib
