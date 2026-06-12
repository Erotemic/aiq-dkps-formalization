/-
Deterministic finite-dimensional plumbing for Acharyya et al. DKPS concentration.

The goal of this file is to push inside the hard Acharyya layer without mixing in
probability.  The lemmas here are reusable by both the finite-sample
concentration paper and the asymptotic consistency scaffold:

sample/mean response errors
  → dissimilarity-matrix errors
  → centered-matrix perturbations
  → spectral/MDS perturbation hypotheses.
-/

import Acharyya2024.Common

open scoped BigOperators Topology

namespace Acharyya2025.Deterministic

open Acharyya2024

/-! ## Classical-MDS double centering -/

/-- Row mean of a finite real matrix represented as a curried dissimilarity matrix. -/
noncomputable def rowMean {n : Nat} (A : DisMat n) (i : Fin n) : Real :=
  ((n : Real)⁻¹) * ∑ j : Fin n, A i j

/-- Column mean of a finite real matrix represented as a curried dissimilarity matrix. -/
noncomputable def colMean {n : Nat} (A : DisMat n) (j : Fin n) : Real :=
  ((n : Real)⁻¹) * ∑ i : Fin n, A i j

/-- Grand mean of all entries of a finite real matrix. -/
noncomputable def grandMean {n : Nat} (A : DisMat n) : Real :=
  ((n : Real)⁻¹)^2 * ∑ i : Fin n, ∑ j : Fin n, A i j

/--
The additive double-centering operator `Aᶜᵢⱼ = Aᵢⱼ - rowMeanᵢ - colMeanⱼ + grandMean`.

Classical MDS applies this to squared dissimilarities and then multiplies by
`-1/2`; keeping the centering operator separate makes the deterministic
Lipschitz estimate reusable.
-/
noncomputable def doubleCenter {n : Nat} (A : DisMat n) : DisMat n :=
  fun i j => A i j - rowMean A i - colMean A j + grandMean A

/--
Classical-MDS centered matrix, without choosing an eigendecomposition.

Corresponds to the paper's `B = -½ Hₙ ∆∘² Hₙ` (true distances) and
`B̂ = -½ Hₙ D∘² Hₙ` (sample distances): the doubly-centered, squared
dissimilarity matrix from which CMDS perspectives are extracted (paper §3,
Algorithm 1a, step 4). Here `doubleCenter` plays the role of the centering
matrix `Hₙ (·) Hₙ`, the entry squaring plays the role of `(·)∘²`, and the
`-½` factor matches. The eigendecomposition step that turns this into
embeddings is *not* taken here; this is only the matrix `B`/`B̂` itself.
-/
noncomputable def classicalMDSMatrix {n : Nat} (D : DisMat n) : DisMat n :=
  fun i j => -(1 / 2 : Real) * doubleCenter (fun i j => (D i j)^2) i j

/--
Entrywise perturbations bound perturbations of row means.

Formalized by Codex 5.5 High, per user-observed model label.
-/
theorem abs_rowMean_sub_le_of_entrywise
    {n : Nat} (hn : 0 < n)                      -- nonempty index set (n > 0)
    {A B : DisMat n} {ε : Real}
    (hε : ∀ i j : Fin n, |A i j - B i j| ≤ ε)   -- entrywise closeness of A, B
    (i : Fin n) :
    -- Conclusion: row means of two entrywise-ε-close matrices differ by at most ε.
    |rowMean A i - rowMean B i| ≤ ε := by
  have hn_real_pos : 0 < (n : Real) := by exact_mod_cast hn
  have hn_real_nonneg : 0 ≤ (n : Real) := le_of_lt hn_real_pos
  have hinv_nonneg : 0 ≤ ((n : Real)⁻¹) := inv_nonneg.mpr hn_real_nonneg
  have hsum_abs :
      |∑ j : Fin n, (A i j - B i j)| ≤ ∑ j : Fin n, |A i j - B i j| :=
    Finset.abs_sum_le_sum_abs _ _
  have hsum_le : (∑ j : Fin n, |A i j - B i j|) ≤ (n : Real) * ε := by
    calc
      (∑ j : Fin n, |A i j - B i j|) ≤ ∑ _j : Fin n, ε :=
        Finset.sum_le_sum fun j _ => hε i j
      _ = (n : Real) * ε := by simp
  calc
    |rowMean A i - rowMean B i|
        = |((n : Real)⁻¹) * ∑ j : Fin n, (A i j - B i j)| := by
          simp [rowMean, mul_sub, Finset.sum_sub_distrib]
    _ = ((n : Real)⁻¹) * |∑ j : Fin n, (A i j - B i j)| := by
          rw [abs_mul, abs_of_nonneg hinv_nonneg]
    _ ≤ ((n : Real)⁻¹) * ((n : Real) * ε) := by
          exact mul_le_mul_of_nonneg_left (hsum_abs.trans hsum_le) hinv_nonneg
    _ = ε := by
          field_simp [ne_of_gt hn_real_pos]

/--
Entrywise perturbations bound perturbations of column means.

Formalized by Codex 5.5 High, per user-observed model label.
-/
theorem abs_colMean_sub_le_of_entrywise
    {n : Nat} (hn : 0 < n)                      -- nonempty index set (n > 0)
    {A B : DisMat n} {ε : Real}
    (hε : ∀ i j : Fin n, |A i j - B i j| ≤ ε)   -- entrywise closeness of A, B
    (j : Fin n) :
    -- Conclusion: column means of two entrywise-ε-close matrices differ by at most ε.
    |colMean A j - colMean B j| ≤ ε := by
  have hn_real_pos : 0 < (n : Real) := by exact_mod_cast hn
  have hn_real_nonneg : 0 ≤ (n : Real) := le_of_lt hn_real_pos
  have hinv_nonneg : 0 ≤ ((n : Real)⁻¹) := inv_nonneg.mpr hn_real_nonneg
  have hsum_abs :
      |∑ i : Fin n, (A i j - B i j)| ≤ ∑ i : Fin n, |A i j - B i j| :=
    Finset.abs_sum_le_sum_abs _ _
  have hsum_le : (∑ i : Fin n, |A i j - B i j|) ≤ (n : Real) * ε := by
    calc
      (∑ i : Fin n, |A i j - B i j|) ≤ ∑ _i : Fin n, ε :=
        Finset.sum_le_sum fun i _ => hε i j
      _ = (n : Real) * ε := by simp
  calc
    |colMean A j - colMean B j|
        = |((n : Real)⁻¹) * ∑ i : Fin n, (A i j - B i j)| := by
          simp [colMean, mul_sub, Finset.sum_sub_distrib]
    _ = ((n : Real)⁻¹) * |∑ i : Fin n, (A i j - B i j)| := by
          rw [abs_mul, abs_of_nonneg hinv_nonneg]
    _ ≤ ((n : Real)⁻¹) * ((n : Real) * ε) := by
          exact mul_le_mul_of_nonneg_left (hsum_abs.trans hsum_le) hinv_nonneg
    _ = ε := by
          field_simp [ne_of_gt hn_real_pos]

/--
Entrywise perturbations bound perturbations of the grand mean.

Formalized by Codex 5.5 High, per user-observed model label.
-/
theorem abs_grandMean_sub_le_of_entrywise
    {n : Nat} (hn : 0 < n)                      -- nonempty index set (n > 0)
    {A B : DisMat n} {ε : Real}
    (hε : ∀ i j : Fin n, |A i j - B i j| ≤ ε) : -- entrywise closeness of A, B
    -- Conclusion: grand means of two entrywise-ε-close matrices differ by at most ε.
    |grandMean A - grandMean B| ≤ ε := by
  have hn_real_pos : 0 < (n : Real) := by exact_mod_cast hn
  have hn_real_nonneg : 0 ≤ (n : Real) := le_of_lt hn_real_pos
  have hinv_nonneg : 0 ≤ ((n : Real)⁻¹) := inv_nonneg.mpr hn_real_nonneg
  have hinv_sq_nonneg : 0 ≤ ((n : Real)⁻¹)^2 := sq_nonneg _
  have hsum_abs :
      |∑ i : Fin n, ∑ j : Fin n, (A i j - B i j)|
        ≤ ∑ i : Fin n, ∑ j : Fin n, |A i j - B i j| := by
    calc
      |∑ i : Fin n, ∑ j : Fin n, (A i j - B i j)|
          ≤ ∑ i : Fin n, |∑ j : Fin n, (A i j - B i j)| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin n, ∑ j : Fin n, |A i j - B i j| :=
            Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
  have hsum_le :
      (∑ i : Fin n, ∑ j : Fin n, |A i j - B i j|)
        ≤ ((n : Real) * (n : Real)) * ε := by
    calc
      (∑ i : Fin n, ∑ j : Fin n, |A i j - B i j|)
          ≤ ∑ _i : Fin n, ∑ _j : Fin n, ε :=
            Finset.sum_le_sum fun i _ =>
              Finset.sum_le_sum fun j _ => hε i j
      _ = ((n : Real) * (n : Real)) * ε := by simp [mul_assoc]
  calc
    |grandMean A - grandMean B|
        = |((n : Real)⁻¹)^2 *
            ∑ i : Fin n, ∑ j : Fin n, (A i j - B i j)| := by
          simp [grandMean, mul_sub, Finset.sum_sub_distrib]
    _ = ((n : Real)⁻¹)^2 *
          |∑ i : Fin n, ∑ j : Fin n, (A i j - B i j)| := by
          rw [abs_mul, abs_of_nonneg hinv_sq_nonneg]
    _ ≤ ((n : Real)⁻¹)^2 * (((n : Real) * (n : Real)) * ε) := by
          exact mul_le_mul_of_nonneg_left (hsum_abs.trans hsum_le) hinv_sq_nonneg
    _ = ε := by
          field_simp [ne_of_gt hn_real_pos]

/--
Entrywise stability of the double-centering operator.

If every entry of `A - B` is bounded by `ε`, then every entry of the centered
matrices differs by at most `4ε`.  This is the deterministic centering link in
the DKPS/MDS chain.

Formalized by Codex 5.5 High, per user-observed model label.
-/
theorem abs_doubleCenter_sub_le_of_entrywise
    {n : Nat} (hn : 0 < n)                      -- nonempty index set (n > 0)
    {A B : DisMat n} {ε : Real}
    (hε : ∀ i j : Fin n, |A i j - B i j| ≤ ε)   -- entrywise closeness of A, B
    (i j : Fin n) :
    -- Conclusion: double-centering is entrywise 4-Lipschitz, i.e. it inflates an
    -- entrywise ε bound to at most 4ε (the centering link in the CMDS chain).
    |doubleCenter A i j - doubleCenter B i j| ≤ 4 * ε := by
  have hrow := abs_rowMean_sub_le_of_entrywise hn hε i
  have hcol := abs_colMean_sub_le_of_entrywise hn hε j
  have hgrand := abs_grandMean_sub_le_of_entrywise hn hε
  have hrow_rev : |rowMean B i - rowMean A i| ≤ ε := by
    simpa [abs_sub_comm] using hrow
  have hcol_rev : |colMean B j - colMean A j| ≤ ε := by
    simpa [abs_sub_comm] using hcol
  have hentry := hε i j
  have htriangle :
      |doubleCenter A i j - doubleCenter B i j|
        ≤ |A i j - B i j|
          + |rowMean B i - rowMean A i|
          + |colMean B j - colMean A j|
          + |grandMean A - grandMean B| := by
    calc
      |doubleCenter A i j - doubleCenter B i j|
          = |(A i j - B i j)
              - (rowMean A i - rowMean B i)
              - (colMean A j - colMean B j)
              + (grandMean A - grandMean B)| := by
            simp [doubleCenter]
            ring_nf
      _ ≤ |A i j - B i j|
            + |rowMean B i - rowMean A i|
            + |colMean B j - colMean A j|
            + |grandMean A - grandMean B| := by
            have h₁ :
                |(A i j - B i j) - (rowMean A i - rowMean B i)
                    - (colMean A j - colMean B j)
                    + (grandMean A - grandMean B)|
                  ≤ |(A i j - B i j) - (rowMean A i - rowMean B i)
                    - (colMean A j - colMean B j)|
                    + |grandMean A - grandMean B| := by
                simpa [sub_eq_add_neg, add_assoc] using
                  abs_add_le ((A i j - B i j) - (rowMean A i - rowMean B i)
                    - (colMean A j - colMean B j)) (grandMean A - grandMean B)
            have h₂ :
                |(A i j - B i j) - (rowMean A i - rowMean B i)
                    - (colMean A j - colMean B j)|
                  ≤ |(A i j - B i j) - (rowMean A i - rowMean B i)|
                    + |colMean B j - colMean A j| := by
                have hraw :
                    |((A i j - B i j) - (rowMean A i - rowMean B i))
                        + (-(colMean A j - colMean B j))|
                      ≤ |(A i j - B i j) - (rowMean A i - rowMean B i)|
                        + |-(colMean A j - colMean B j)| :=
                  abs_add_le ((A i j - B i j) - (rowMean A i - rowMean B i))
                    (-(colMean A j - colMean B j))
                simpa [sub_eq_add_neg, add_assoc] using hraw
            have h₃ :
                |(A i j - B i j) - (rowMean A i - rowMean B i)|
                  ≤ |A i j - B i j| + |rowMean B i - rowMean A i| := by
                have hraw :
                    |(A i j - B i j) + (-(rowMean A i - rowMean B i))|
                      ≤ |A i j - B i j| + |-(rowMean A i - rowMean B i)| :=
                  abs_add_le (A i j - B i j) (-(rowMean A i - rowMean B i))
                simpa [sub_eq_add_neg] using hraw
            linarith
  linarith

end Acharyya2025.Deterministic
