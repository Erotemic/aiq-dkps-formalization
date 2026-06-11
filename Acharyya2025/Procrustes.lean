/-
# Procrustes rigidity (exact Gram case)

Two configurations of vectors with identical Gram matrices (all pairwise inner
products equal) are related by a single linear isometry of the ambient space.

This is the deterministic, exact-data core underlying *Procrustes alignment* in
classical multidimensional scaling (CMDS): a configuration recovered from a
Gram matrix is determined only up to an orthogonal transformation, so any two
configurations realizing the same Gram matrix are orthogonally congruent.  In
the finite-sample CMDS perturbation theorems this rigidity is what makes the
"up to `W ∈ O(d)`" alignment in the conclusion *statable*: it is the exact
limit of the approximate alignment.

References:
* T. F. Cox and M. A. A. Cox, *Multidimensional Scaling*, 2nd ed.,
  Chapman & Hall/CRC, 2001, §2.2 (classical scaling and the role of the Gram
  matrix `B`).
* I. Borg and P. J. F. Groenen, *Modern Multidimensional Scaling*, 2nd ed.,
  Springer, 2005, Ch. 12 (Procrustes problems).
* R. Sibson, "Studies in the robustness of multidimensional scaling:
  Perturbational analysis of classical scaling", *J. Roy. Statist. Soc. Ser. B*
  **41** (1979), 217–229.

Formalized by Claude Fable 5, per user-observed model label (claude-fable-5[1m]).
-/

import Acharyya2024.Common
import ForMathlib.Analysis.InnerProductSpace.GramMatrix

open scoped RealInnerProductSpace BigOperators

namespace Acharyya2025.Procrustes

/--
**Procrustes rigidity (abstract form).**

If two families `φ ψ : ι → E` of vectors in a finite-dimensional real inner
product space have equal Gram matrices, i.e. `⟪φ i, φ j⟫ = ⟪ψ i, ψ j⟫` for all
`i, j`, then there is a linear isometry equivalence `W` of `E` with
`W (φ i) = ψ i` for every `i`.

Thin `ℝ`-instantiation of the Mathlib-staged
`ForMathlib.exists_linearIsometryEquiv_of_inner_eq` (which is stated over
`RCLike 𝕜`); kept under its original name for downstream call-sites.

Formalized by Claude Fable 5, per user-observed model label (claude-fable-5[1m]).
-/
theorem exists_linearIsometryEquiv_of_inner_eq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {ι : Type*} (φ ψ : ι → E)
    (h : ∀ i j, ⟪φ i, φ j⟫ = ⟪ψ i, ψ j⟫) :
    ∃ W : E ≃ₗᵢ[ℝ] E, ∀ i, W (φ i) = ψ i :=
  ForMathlib.exists_linearIsometryEquiv_of_inner_eq h

/--
**Procrustes rigidity for DKPS configurations.**

Specialization of `exists_linearIsometryEquiv_of_inner_eq` to the DKPS
configuration type `Acharyya2024.Config n d = Fin n → EuclideanSpace ℝ (Fin d)`,
with the Gram condition phrased entrywise as `∑ k, φ i k * φ j k`.

Formalized by Claude Fable 5, per user-observed model label (claude-fable-5[1m]).
-/
theorem exists_linearIsometryEquiv_of_gram_eq
    {n d : Nat} (φ ψ : Acharyya2024.Config n d)
    (h : ∀ i j, ∑ k : Fin d, φ i k * φ j k = ∑ k : Fin d, ψ i k * ψ j k) :
    ∃ W : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d),
      ∀ i, W (φ i) = ψ i := by
  apply exists_linearIsometryEquiv_of_inner_eq φ ψ
  intro i j
  -- Over ℝ, ⟪x, y⟫ on EuclideanSpace is ∑ k, x k * y k (conj is identity).
  rw [show (⟪φ i, φ j⟫ : ℝ) = ∑ k : Fin d, φ i k * φ j k by
        simp [PiLp.inner_apply, mul_comm],
      show (⟪ψ i, ψ j⟫ : ℝ) = ∑ k : Fin d, ψ i k * ψ j k by
        simp [PiLp.inner_apply, mul_comm]]
  exact h i j

end Acharyya2025.Procrustes
