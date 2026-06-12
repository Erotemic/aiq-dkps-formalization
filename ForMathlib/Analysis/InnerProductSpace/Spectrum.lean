/-
Staged for Mathlib: additions to `Mathlib/Analysis/InnerProductSpace/Spectrum.lean`.

Formalized by Claude Fable 5 (claude-fable-5[1m]);
to be re-authored per Mathlib's AI-contribution policy at PR time.
-/

import Mathlib.Analysis.InnerProductSpace.Spectrum

/-! # Eigenvector cross-term identity for a perturbation

For symmetric operators `T`, `S` on a finite-dimensional inner product space,
with `u i` the `i`-th eigenvector of `T` (eigenvalue `λ i`) and `v j` the
`j`-th eigenvector of `S` (eigenvalue `μ j`),

`⟪u i, (S - T) (v j)⟫ = (μ j - λ i) * ⟪u i, v j⟫`.

This three-line identity is the seed of every Davis–Kahan-style subspace
perturbation bound: cross terms between well-separated parts of the spectra
are controlled by the perturbation `S - T` divided by the eigenvalue gap.
-/

namespace ForMathlib

open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} {T S : E →ₗ[𝕜] E}

/--
**Cross-term identity.** The matrix entry of the perturbation `S - T` between
the `i`-th eigenvector of `T` and the `j`-th eigenvector of `S` is the
eigenvalue difference times the overlap of the two eigenvectors.
-/
theorem inner_eigenvectorBasis_map_sub_eigenvectorBasis
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : Module.finrank 𝕜 E = n)
    (i j : Fin n) :
    ⟪hT.eigenvectorBasis hn i, (S - T) (hS.eigenvectorBasis hn j)⟫_𝕜
      = ((hS.eigenvalues hn j - hT.eigenvalues hn i : ℝ) : 𝕜)
          * ⟪hT.eigenvectorBasis hn i, hS.eigenvectorBasis hn j⟫_𝕜 := by
  have hSterm : ⟪hT.eigenvectorBasis hn i, S (hS.eigenvectorBasis hn j)⟫_𝕜
      = ((hS.eigenvalues hn j : ℝ) : 𝕜)
          * ⟪hT.eigenvectorBasis hn i, hS.eigenvectorBasis hn j⟫_𝕜 := by
    rw [hS.apply_eigenvectorBasis, inner_smul_right]
  have hTterm : ⟪hT.eigenvectorBasis hn i, T (hS.eigenvectorBasis hn j)⟫_𝕜
      = ((hT.eigenvalues hn i : ℝ) : 𝕜)
          * ⟪hT.eigenvectorBasis hn i, hS.eigenvectorBasis hn j⟫_𝕜 := by
    rw [← hT (hT.eigenvectorBasis hn i) (hS.eigenvectorBasis hn j),
      hT.apply_eigenvectorBasis, inner_smul_left, RCLike.conj_ofReal]
  rw [LinearMap.sub_apply, inner_sub_right, hSterm, hTterm, RCLike.ofReal_sub]
  ring

end ForMathlib
