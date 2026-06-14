/-
Staged for Mathlib: addition to `Mathlib/Analysis/InnerProductSpace/Basic.lean`.

Formalized by Claude Fable 5 (claude-fable-5[1m]).  Placement history: originally
in the Gram-matrix staging file, then moved to `Orthonormal.lean` to sit by the
`Finsupp`/inner-product machinery; following @wwylele's review (PR #40567) it
moved here to `Basic.lean` — the lemma involves no `Orthonormal`, and `Basic`
already hosts `Finsupp.sum_inner` / `Finsupp.inner_sum` (its dependencies) and
`open`s `Finsupp` + `ComplexConjugate`, so no new import is needed.
To be re-authored per Mathlib's AI-contribution policy at PR time.
-/

import Mathlib.Analysis.InnerProductSpace.Basic

/-! # Inner products of linear combinations

A general identity expanding the inner product of two finite linear combinations of a
vector family over the family's pairwise inner products `⟪v i, v j⟫`.  It involves no
orthonormality, no Gram matrix, and no rigidity hypothesis; it is the reusable algebraic
core behind the Gram-rigidity development in
`Mathlib/Analysis/InnerProductSpace/GramMatrix.lean`, and belongs next to
`Finsupp.sum_inner` / `Finsupp.inner_sum`.

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
