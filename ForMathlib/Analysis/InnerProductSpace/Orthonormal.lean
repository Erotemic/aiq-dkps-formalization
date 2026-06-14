/-
Staged for Mathlib: additions to `Mathlib/Analysis/InnerProductSpace/Orthonormal.lean`.

Formalized by Claude Fable 5 (claude-fable-5[1m]); relocated here from the
Gram-matrix staging file by Claude Opus 4.8 (claude-opus-4-8[1m]) to mirror the
Mathlib fork, where the lemma lives in `Orthonormal.lean` (next to the other
`Finsupp`/inner-product machinery it is built from) rather than in `GramMatrix.lean`
— it is a general inner-product identity, independent of Gram matrices.
To be re-authored per Mathlib's AI-contribution policy at PR time.
-/

import Mathlib.Analysis.InnerProductSpace.Orthonormal

/-! # Inner products of linear combinations

A general identity expanding the inner product of two finite linear combinations of a
vector family over the family's pairwise inner products `⟪v i, v j⟫`.  It involves no
Gram matrix and no rigidity hypothesis; it is the reusable algebraic core behind the
Gram-rigidity development in `Mathlib/Analysis/InnerProductSpace/GramMatrix.lean`.

## Main results

* `ForMathlib.inner_linearCombination_linearCombination`: expands
  `⟪Σ aᵢ • v i, Σ bⱼ • v j⟫` as `Σᵢ Σⱼ conj aᵢ * bⱼ * ⟪v i, v j⟫`.
-/

namespace ForMathlib

open scoped InnerProductSpace

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/--
The inner product of two finite linear combinations `Σ aᵢ • v i` and `Σ bⱼ • v j`
of a vector family `v`, expanded over the family's Gram data
`⟪v i, v j⟫`:
`⟪Σ aᵢ • vᵢ, Σ bⱼ • vⱼ⟫ = Σᵢ Σⱼ conj aᵢ * bⱼ * ⟪vᵢ, vⱼ⟫`.
-/
theorem inner_linearCombination_linearCombination (v : ι → E) (a b : ι →₀ 𝕜) :
    ⟪Finsupp.linearCombination 𝕜 v a, Finsupp.linearCombination 𝕜 v b⟫_𝕜
      = a.sum fun i s => b.sum fun j t => starRingEnd 𝕜 s * t * ⟪v i, v j⟫_𝕜 := by
  rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply, Finsupp.sum_inner]
  refine Finsupp.sum_congr fun i _ => ?_
  rw [Finsupp.inner_sum]
  refine Finsupp.sum_congr fun j _ => ?_
  rw [inner_smul_left, inner_smul_right, ← mul_assoc]

end ForMathlib
