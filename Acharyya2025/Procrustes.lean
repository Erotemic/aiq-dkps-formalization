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

Formalized by Claude Fable 5 (claude-fable-5[1m]).
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
`ForMathlib.exists_linearIsometryEquiv_map_eq_of_inner_eq` (which is stated over
`RCLike 𝕜`); kept under its original name for downstream call-sites.

Paper correspondence: this is the **exact (noise-free) limit** of the alignment
in Theorem 2.  When the two configurations have *equal* Gram matrices, the
aligning orthogonal map `W*` exists exactly and achieves zero error; the
finite-sample Theorem 2 is the approximate version of this rigidity.

Note (extra implicit assumptions beyond the paper): `E` is assumed to be a
finite-dimensional real inner-product space — a Lean modelling choice matching
the Euclidean embedding space of the paper.

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
theorem exists_linearIsometryEquiv_of_inner_eq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]               -- extra (implicit) assumption: finite-dimensional ambient space
    {ι : Type*} (φ ψ : ι → E)
    (h : ∀ i j, ⟪φ i, φ j⟫ = ⟪ψ i, ψ j⟫) :  -- hypothesis: the two families have equal Gram matrices
    -- Conclusion: there is an orthogonal map `W` (linear isometry equivalence of `E`)
    -- aligning the families exactly, `W (φ i) = ψ i` for all `i` — the exact case of W*.
    ∃ W : E ≃ₗᵢ[ℝ] E, ∀ i, W (φ i) = ψ i :=
  ForMathlib.exists_linearIsometryEquiv_map_eq_of_inner_eq h

/--
**Procrustes rigidity for DKPS configurations.**

Specialization of `exists_linearIsometryEquiv_of_inner_eq` to the DKPS
configuration type `Acharyya2024.Config n d = Fin n → EuclideanSpace ℝ (Fin d)`,
with the Gram condition phrased entrywise as `∑ k, φ i k * φ j k`.

Paper correspondence: the DKPS-typed exact-alignment statement.  Two
configurations realizing the same classical-MDS Gram matrix are related by an
orthogonal `W ∈ O(d)` — the exact (κ = 0) instance of the alignment in
Theorem 2.

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
theorem exists_linearIsometryEquiv_of_gram_eq
    {n d : Nat} (φ ψ : Acharyya2024.Config n d)
    -- hypothesis: the two DKPS configurations have equal Gram matrices (entrywise)
    (h : ∀ i j, ∑ k : Fin d, φ i k * φ j k = ∑ k : Fin d, ψ i k * ψ j k) :
    -- Conclusion: an orthogonal map `W` of `EuclideanSpace ℝ (Fin d)` aligns them
    -- exactly, `W (φ i) = ψ i` for all `i`.
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
