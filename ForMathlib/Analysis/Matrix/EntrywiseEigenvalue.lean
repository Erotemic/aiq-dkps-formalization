/-
Staged for Mathlib: addition to `Mathlib/Analysis/Matrix/Spectrum.lean`
(eigenvalue perturbation from entrywise closeness).

Formalized by Claude Opus 4.8 (claude-opus-4-8[1m]);
to be re-authored per Mathlib's AI-contribution policy at PR time.
-/

import ForMathlib.Analysis.InnerProductSpace.CourantFischer
import ForMathlib.Analysis.Matrix.EntrywiseOpNorm
import ForMathlib.Analysis.Matrix.SpectralFunctionMeasurable

/-! # Eigenvalue perturbation from entrywise closeness

Weyl's inequality bounds the eigenvalue perturbation by the *operator* norm of the
difference.  Combined with the entrywise→operator-norm comparison
`‖toEuclideanLin A‖ ≤ n · (entrywise sup of A)`, this gives a directly usable
**entrywise** eigenvalue-perturbation bound: if two real symmetric `n × n`
matrices are entrywise `ε`-close, their sorted eigenvalues differ by at most
`n · ε`.

## Main result

* `ForMathlib.Matrix.abs_sortedEig_sub_le_of_entry_le`
-/

open scoped Matrix
open Module

namespace ForMathlib.Matrix

variable {n : ℕ}

/-- **Entrywise eigenvalue perturbation.**  If two real symmetric matrices `A`,
`Ahat` are entrywise `ε`-close, their `k`-th sorted eigenvalues differ by at most
`n · ε` (Weyl's inequality through the entrywise → operator-norm comparison). -/
theorem abs_sortedEig_sub_le_of_entry_le {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (hAhat : Ahat.IsHermitian)
    {ε : ℝ} (hentry : ∀ i j, |Ahat i j - A i j| ≤ ε) (k : Fin n) :
    |sortedEig hAhat k - sortedEig hA k| ≤ (n : ℝ) * ε := by
  -- Operator-norm bound on the difference, from the entrywise bound.
  have hop : ∀ x : EuclideanSpace ℝ (Fin n),
      ‖(Matrix.toEuclideanLin Ahat - Matrix.toEuclideanLin A) x‖ ≤ ((n : ℝ) * ε) * ‖x‖ := by
    intro x
    have hsub : (Matrix.toEuclideanLin Ahat - Matrix.toEuclideanLin A) x
        = Matrix.toEuclideanLin (Ahat - A) x := by
      rw [map_sub]
    rw [hsub]
    have hentry' : ∀ i j, |(Ahat - A) i j| ≤ ε := by
      intro i j; simpa [Matrix.sub_apply] using hentry i j
    exact ForMathlib.norm_toEuclideanLin_le_of_entry_le hentry' x
  -- Weyl on the symmetric operators.
  exact abs_eigenvalues_sub_le (opSym hAhat) (opSym hA) finrank_euclideanSpace_fin hop k

end ForMathlib.Matrix
