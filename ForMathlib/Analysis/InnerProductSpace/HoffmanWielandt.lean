/-
Staged for Mathlib: additions to `Mathlib/Analysis/InnerProductSpace/` (new file
`HoffmanWielandt.lean`).

Formalized by Claude Opus 4.8 (claude-opus-4-8[1m]), plan step W2 of
`dev/davis-kahan-gap-closure-plan.md`.  This file will build up to the
Hoffman–Wielandt eigenvalue-perturbation inequality; it currently supplies the
sorted-rearrangement ingredient (W2.1).
To be re-authored per Mathlib's AI-contribution policy at PR time.
-/

import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Data.Real.Basic

/-! # Hoffman–Wielandt building blocks

The Hoffman–Wielandt inequality bounds the ℓ² distance between the sorted
spectra of two symmetric operators by the Frobenius norm of their difference.
Its proof factors through the von Neumann trace inequality, whose sorted core is
the rearrangement inequality recorded here.

## Main results

* `ForMathlib.sum_mul_comp_perm_le_sum_mul_of_antitone`: for two decreasingly
  sorted real tuples `f, g` and any permutation `σ`,
  `∑ i, f (σ i) * g i ≤ ∑ i, f i * g i` — pairing the sorted tuples in order
  maximises the inner product.

## References

* A. J. Hoffman and H. W. Wielandt, *The variation of the spectrum of a normal
  matrix*, Duke Math. J. 20 (1953), 37–39.
* G. H. Hardy, J. E. Littlewood, G. Pólya, *Inequalities*, 2nd ed., §10.2
  (the rearrangement inequality).
-/

namespace ForMathlib

open scoped BigOperators

/-- **Sorted rearrangement inequality.** For two decreasingly sorted (antitone)
real tuples `f, g : Fin n → ℝ` and any permutation `σ`, permuting one tuple can
only decrease the pointwise product sum:
`∑ i, f (σ i) * g i ≤ ∑ i, f i * g i`.

The in-order pairing of two similarly sorted tuples maximises `∑ f i * g i`.
Immediate from Mathlib's rearrangement inequality once antitone tuples are seen
to monovary. -/
theorem sum_mul_comp_perm_le_sum_mul_of_antitone {n : ℕ} {f g : Fin n → ℝ}
    (hf : Antitone f) (hg : Antitone g) (σ : Equiv.Perm (Fin n)) :
    ∑ i, f (σ i) * g i ≤ ∑ i, f i * g i := by
  simpa only [smul_eq_mul] using (hf.monovary hg).sum_comp_perm_smul_le_sum_smul (σ := σ)

end ForMathlib
