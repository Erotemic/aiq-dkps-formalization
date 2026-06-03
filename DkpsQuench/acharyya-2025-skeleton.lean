/-
DKPS / raw-stress MDS consistency: compilation-focused refactor + proof sketches.

This version avoids subtle type-synonym issues by defining the Frobenius norm
*directly* as a double sum, rather than via `EuclideanSpace` / `PiLp`.

It also fixes:
- `Trosset_Lemma1` visibility,
- section/variable scoping problems that cause "unexpected token 'variable'",
- named-argument mismatches,
- and provides a stable API for later formalizations.

Deterministic lemma from Appendix A.2 is fully proved.
All other proofs are either:
- proved by composing axioms (where the paper cites external results), or
- left as `axiom` with detailed comments describing the intended proof.
-/

import Mathlib

open MeasureTheory
open Filter
open scoped BigOperators Topology

namespace DKPS

/-! # Core types -/

abbrev Rvec (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev Mat (m s : ℕ) := EuclideanSpace ℝ (Fin m × Fin s)

/-- Curried dissimilarity matrix on `n` points. -/
abbrev DisMat (n : ℕ) := Fin n → Fin n → ℝ

/-- Subsequences of `ℕ`. -/
def Subseq (u : ℕ → ℕ) : Prop := StrictMono u

/-! # Frobenius norm for dissimilarity matrices (defined directly) -/

section Frob

variable {n : ℕ}

/-- Frobenius norm squared (finite sum): `∑_{i,i'} Δ_{ii'}^2`. -/
noncomputable def frobSq (Δ : DisMat n) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, (Δ i j) ^ 2

/-- Frobenius norm (finite): `sqrt (∑ Δ_{ii'}^2)`. -/
noncomputable def frob (Δ : DisMat n) : ℝ :=
  Real.sqrt (frobSq (n:=n) Δ)

/-- Convenience: Frobenius norm of a difference. -/
noncomputable def frobSub (A B : DisMat n) : ℝ :=
  frob (n:=n) (fun i j => A i j - B i j)

/-
TODO: later we can connect this to Mathlib's `Matrix.normF` / `PiLp` norms.
For now this is a concrete, version-stable definition.

Useful lemmas to prove later:
- `frobSq` is nonnegative.
- `frob` is nonnegative and equals 0 iff all entries are 0.
- Triangle inequality: `frob (A+B) ≤ frob A + frob B`.
  (Can be obtained by identifying with `EuclideanSpace` or by Cauchy-Schwarz.)

For the current paper skeleton, we mostly need to *state convergence* of `frob`.
-/

end Frob

/-! # Raw-stress MDS (finite n) -/

noncomputable def rawStress (n d : ℕ) (Δ : DisMat n) (z : Fin n → Rvec d) : ℝ :=
  ∑ i, ∑ j, (‖z i - z j‖ - Δ i j)^2

def MDS (n d : ℕ) (Δ : DisMat n) : Set (Fin n → Rvec d) :=
  { z | ∀ z', rawStress n d Δ z ≤ rawStress n d Δ z' }

noncomputable def pairDist {n d : ℕ} (z : Fin n → Rvec d) (i j : Fin n) : ℝ :=
  ‖z i - z j‖

noncomputable def pairDistErr {n d : ℕ} (z z' : Fin n → Rvec d) (i j : Fin n) : ℝ :=
  |pairDist z i j - pairDist z' i j|

/-! # DKPS setting: D, Δ, Δ∞ -/

section Setting

variable {n m s : ℕ}

noncomputable def DEntry (Xbar : Fin n → Mat m s) (i j : Fin n) : ℝ :=
  ((m : ℝ)⁻¹) * ‖Xbar i - Xbar j‖

noncomputable def DeltaEntry (mu : Fin n → Mat m s) (i j : Fin n) : ℝ :=
  ((m : ℝ)⁻¹) * ‖mu i - mu j‖

noncomputable def Dmat (Xbar : Fin n → Mat m s) : DisMat n :=
  fun i j => DEntry (n:=n) (m:=m) (s:=s) Xbar i j

noncomputable def Deltamat (mu : Fin n → Mat m s) : DisMat n :=
  fun i j => DeltaEntry (n:=n) (m:=m) (s:=s) mu i j

noncomputable def DeltaInf {q : ℕ} (phi : Fin n → Rvec q) : DisMat n :=
  fun i j => ‖phi i - phi j‖

/-- Deterministic Appendix A.2 inequality (fully proved). -/
theorem abs_DEntry_sub_DeltaEntry_le
    (Xbar mu : Fin n → Mat m s) (i j : Fin n) :
    |DEntry (n:=n) (m:=m) (s:=s) Xbar i j - DeltaEntry (n:=n) (m:=m) (s:=s) mu i j|
      ≤ ((m : ℝ)⁻¹) * (‖Xbar i - mu i‖ + ‖Xbar j - mu j‖) := by
  classical
  set a := Xbar i - Xbar j
  set b := mu i - mu j

  have hm_nonneg : 0 ≤ ((m : ℝ)⁻¹) := by
    have : 0 ≤ (m : ℝ) := by exact_mod_cast Nat.zero_le m
    exact inv_nonneg.2 this

  have hsub :
      DEntry (n:=n) (m:=m) (s:=s) Xbar i j - DeltaEntry (n:=n) (m:=m) (s:=s) mu i j
        = ((m : ℝ)⁻¹) * (‖a‖ - ‖b‖) := by
    simp [DEntry, DeltaEntry, a, b, mul_sub]

  have h1 : |‖a‖ - ‖b‖| ≤ ‖a - b‖ :=
    abs_norm_sub_norm_le a b

  have hab : a - b = (Xbar i - mu i) - (Xbar j - mu j) := by
    simp [a, b]
    abel

  have h2 : ‖a - b‖ ≤ ‖Xbar i - mu i‖ + ‖Xbar j - mu j‖ := by
    simpa [hab] using (norm_sub_le (Xbar i - mu i) (Xbar j - mu j))

  calc
    |DEntry (n:=n) (m:=m) (s:=s) Xbar i j - DeltaEntry (n:=n) (m:=m) (s:=s) mu i j|
        = |((m : ℝ)⁻¹) * (‖a‖ - ‖b‖)| := by simpa [hsub]
    _ = ((m : ℝ)⁻¹) * |‖a‖ - ‖b‖| := by
      simp [abs_mul, abs_of_nonneg hm_nonneg]
    _ ≤ ((m : ℝ)⁻¹) * ‖a - b‖ :=
      mul_le_mul_of_nonneg_left h1 hm_nonneg
    _ ≤ ((m : ℝ)⁻¹) * (‖Xbar i - mu i‖ + ‖Xbar j - mu j‖) :=
      mul_le_mul_of_nonneg_left h2 hm_nonneg

end Setting

/-! # Convergence in probability -/

section Prob

variable {Ω : Type} [MeasurableSpace Ω]

def ConvergesInProbability (P : Measure Ω) {α : Type} [PseudoMetricSpace α]
    (X : ℕ → Ω → α) (x : α) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    Tendsto (fun n => P {ω | dist (X n ω) x > ε}) atTop (𝓝 0)

def ConvergesInProbability₀ (P : Measure Ω) {α : Type} [PseudoMetricSpace α]
    (X : ℕ → Ω → α) : Prop :=
  ConvergesInProbability (Ω:=Ω) P X (0:α)

end Prob

/-! # Axioms capturing the cited MDS-stability results ([23]) -/

section Trosset

variable {Ω : Type} [MeasurableSpace Ω]

axiom Trosset_Lemma1
  (P : Measure Ω)
  {n d : ℕ}
  (Dseq : ℕ → Ω → DisMat n)
  (Δ∞ : DisMat n)
  (ψhat : ℕ → Ω → (Fin n → Rvec d))
  (hψhat : ∀ r ω, ψhat r ω ∈ MDS n d (Dseq r ω))
  (hD : ConvergesInProbability₀ (Ω:=Ω) P (fun r ω => frobSub (n:=n) (Dseq r ω) Δ∞))
  : ∃ u : ℕ → ℕ,
      Subseq u ∧
      ∃ ψ : Fin n → Rvec d,
        ψ ∈ MDS n d Δ∞ ∧
        ∀ i j : Fin n,
          ConvergesInProbability (Ω:=Ω) P (fun t ω => pairDistErr (ψhat (u t) ω) ψ i j) 0

end Trosset

/-! # Main theorems: statements and proof sketches -/

section Main

/-! ## Regime A: fixed n,m -/

section Fixed_nm

variable {Ω : Type} [MeasurableSpace Ω]
variable (P : Measure Ω)
variable {n m s d : ℕ}

variable (Xbar : ℕ → Ω → Fin n → Mat m s)
variable (mu : Fin n → Mat m s)

noncomputable def Dseq : ℕ → Ω → DisMat n :=
  fun r ω => Dmat (n:=n) (m:=m) (s:=s) (Xbar r ω)

noncomputable def Δ : DisMat n :=
  Deltamat (n:=n) (m:=m) (s:=s) mu

/-- Theorem 1 (paper): obtained by applying [23] stability theorem. -/
theorem Theorem1
  (ψhat : ℕ → Ω → (Fin n → Rvec d))
  (hψhat : ∀ r ω, ψhat r ω ∈ MDS n d (Dseq (n:=n) (m:=m) (s:=s) Xbar r ω))
  (hD : ConvergesInProbability₀ (Ω:=Ω) P
        (fun r ω => frobSub (n:=n)
          (Dseq (n:=n) (m:=m) (s:=s) Xbar r ω)
          (Δ (n:=n) (m:=m) (s:=s) mu)))
  : ∃ u : ℕ → ℕ,
      Subseq u ∧
      ∃ ψ : Fin n → Rvec d,
        ψ ∈ MDS n d (Δ (n:=n) (m:=m) (s:=s) mu) ∧
        ∀ i j : Fin n,
          ConvergesInProbability (Ω:=Ω) P (fun t ω => pairDistErr (ψhat (u t) ω) ψ i j) 0 := by
  -- This is exactly `Trosset_Lemma1` with `Δ∞ = Δ`.
  simpa [Dseq, Δ] using
    (Trosset_Lemma1 (P:=P)
      (Dseq:=Dseq (n:=n) (m:=m) (s:=s) Xbar)
      (Δ∞:=Δ (n:=n) (m:=m) (s:=s) mu)
      (ψhat:=ψhat)
      (hψhat:=hψhat)
      (hD:=hD))

end Fixed_nm

/-! ## Regime B: fixed n, growing m -/

section Fixed_n_growing_m

/-
We only sketch this regime here; it is where most probability work lives.

Given:
- `m_of_r : ℕ → ℕ` (number of queries at replicate count `r`)
- `Xbar r ω i : Mat (m_of_r r) s`  (sample mean response matrix)
- `mu   r i   : Mat (m_of_r r) s`  (population mean response matrix)

Define:
- `Dseq r ω i i' = (m_of_r r)⁻¹ * ‖Xbar r ω i - Xbar r ω i'‖`
- `Δseq r    i i' = (m_of_r r)⁻¹ * ‖mu r i - mu r i'‖`

Assumption 1 (paper): `Δseq r i i' → ‖phi i - phi i'‖`.

Theorem 2 (paper): a variance/trace condition implies
    `frobSub (Dseq r ω) (Δ∞) →P 0`.
Theorem 3 (paper): combine Theorem 2 with [23] stability to get pairwise-distance
    convergence (possibly along a subsequence).

What remains to formalize for Theorem 2:
- Markov inequality in `MeasureTheory`.
- The chain of event inclusions in Appendix A.2.
- Computation of `E‖row_j(mean) - mean‖^2 = trace(Σ_{ij}) / r`.

We can build this in a later file once we settle a probability API.
-/

end Fixed_n_growing_m

end Main

end DKPS
