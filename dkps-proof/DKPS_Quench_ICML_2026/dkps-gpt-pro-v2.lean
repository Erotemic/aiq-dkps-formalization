/-
================================================================================
Quench (ICML, non-anonymous draft): DKPS definitions and Theorem 2 (query-efficiency)
================================================================================

This file is designed to be **line-by-line traceable** to the paper:

  • "Query-efficient model evaluation using cached responses"
    (quench-icml-nonanon.pdf)

Hard constraint (per user request):
  1. All *definitions* match the quench paper exactly.
Secondary goal:
  2. Proofs should be correct and tractable.

Accordingly:
  • We formalize all objects exactly as defined in quench (§§1.2–3).
  • We fully mechanize the *deterministic core inequality* in Theorem 2.
  • We leave the genuinely probabilistic ingredients (Acharyya concentration,
    sampling/denseness) as explicit axioms/hypotheses, so they can be swapped in
    later without rewriting the deterministic mathematics.

Secondary references (both are cited by quench and clarify technical points):
  • 2410.01106v3.pdf  (Helm et al. 2025): DKPS + inference background.
  • 2511.08307v1.pdf  (Acharyya et al. 2025): concentration bounds (quench Thm 1).

-/

import Mathlib

open scoped BigOperators
open MeasureTheory

namespace Quench

/-!
## §0 Helper: Frobenius norm

Quench uses the Frobenius norm `‖·‖_F` on the matrix `X̄_i ∈ ℝ^{m×p}` of averaged
embedded responses. To avoid surprises with imports, we define it explicitly:

  ‖A‖_F := sqrt(∑ᵢ ∑ⱼ (A i j)^2).

This is the standard Frobenius norm used in the DKPS papers.
-/

/-- Frobenius norm `‖A‖_F = sqrt(∑ᵢ ∑ⱼ (A i j)^2)` for real matrices. -/
noncomputable def frob {I J : Type} [Fintype I] [Fintype J] (A : Matrix I J ℝ) : ℝ :=
  Real.sqrt (∑ i : I, ∑ j : J, (A i j) ^ 2)

@[simp] lemma frob_nonneg {I J : Type} [Fintype I] [Fintype J] (A : Matrix I J ℝ) :
    0 ≤ frob A := by
  simp [frob]

/-!
## §1.2 Problem statement (quench)

Quench defines:
  • a benchmark query set `Q* = {q₁,…,q_M}`,
  • a benchmark scoring function `y : F × 2^{Q*} → [0,1]`.

We model `2^{Q*}` by `Finset` subsets of the query type.
-/

section ProblemStatement

variable {𝓕 𝓠 : Type}

/-- Benchmark query set `Q*` (paper: `Q* = {q₁,…,q_M}`). -/
variable (Qstar : Finset 𝓠)

/--
Benchmark scoring function (paper: `y : F × 2^{Q*} → [0,1]`).

We write it as `y f Q`, where `Q : Finset 𝓠` represents a subset of queries.
-/
variable (y : 𝓕 → Finset 𝓠 → ℝ)

/-- Full benchmark score `y(f,Q*)` (paper often abbreviates this as `y`). -/
def yFull (f : 𝓕) : ℝ := y f Qstar

/-- Subset score `y(f,Q)` (paper notation in §3: `ŷ_Q := y(f,Q)`). -/
def ySub (Q : Finset 𝓠) (f : 𝓕) : ℝ := y f Q

end ProblemStatement

/-!
## §2 DKPS construction (quench)

Quench §2 defines DKPS from sampled model responses:

  • g : X → ℝ^p         (embedding function)
  • X̄_i ∈ ℝ^{m×p}       (averaged embedded responses across r replicates)
  • D_{ii′} = ‖X̄_i − X̄_{i′}‖_F   (pairwise Frobenius distances)
  • DKPS = argmin stress objective (Eq. (1))

IMPORTANT: In quench, `D_{ii′}` is **not rescaled by m**. We follow quench exactly.
-/

section DKPSDefinitions

variable {X : Type}              -- response space (paper: `X`)
variable {p d : ℕ}               -- embedding dimension p, DKPS dimension d
variable {n m r : ℕ}             -- #models n, #queries m, #replicates r

/-- Embedding function `g : X → ℝ^p` (paper: `g : X → R^p`). -/
variable (g : X → EuclideanSpace ℝ (Fin p))

/--
Sampled responses: `resp i j k` is the k-th response of model i to query j.

This is the (already realized) cache of responses referenced throughout quench.
-/
variable (resp : Fin n → Fin m → Fin r → X)

/-- Embedded response `x_{ijk} = g(resp i j k)`. -/
noncomputable def x (i : Fin n) (j : Fin m) (k : Fin r) : EuclideanSpace ℝ (Fin p) :=
  g (resp i j k)

/--
Average embedded response (paper §2):

  x̄_{ij} = (1/r) * ∑_{k=1}^r x_{ijk}.
-/
noncomputable def xbar (i : Fin n) (j : Fin m) : EuclideanSpace ℝ (Fin p) :=
  ((1 : ℝ) / (r : ℝ)) • (∑ k : Fin r, x (g := g) (resp := resp) i j k)

/--
Matrix `X̄_i ∈ ℝ^{m×p}` whose j-th row is `x̄_{ij}` (paper §2).
-/
noncomputable def Xbar (i : Fin n) : Matrix (Fin m) (Fin p) ℝ :=
  fun j a => (xbar (g := g) (resp := resp) i j) a

/--
Distance matrix `D` with entries (paper §2):

  D_{ii′} = ‖X̄_i − X̄_{i′}‖_F.
-/
noncomputable def D : Matrix (Fin n) (Fin n) ℝ :=
  fun i i' => frob (Xbar (g := g) (resp := resp) i - Xbar (g := g) (resp := resp) i')

/-!
### Eq. (1): DKPS stress minimization (quench)

Quench defines DKPS representations as a solution to:

  (ψ̂₁,…,ψ̂_n) = argmin_{zᵢ ∈ ℝ^d} ∑_{i,i′} (‖zᵢ - z_{i′}‖ - D_{ii′})².
-/

/-- Stress objective (quench Eq. (1)). -/
noncomputable def stress (Dmat : Matrix (Fin n) (Fin n) ℝ)
    (z : Fin n → EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ i : Fin n, ∑ i' : Fin n, (‖z i - z i'‖ - Dmat i i') ^ 2

/-- `IsDKPS D z` means `z` globally minimizes the stress objective (argmin in Eq. (1)). -/
def IsDKPS (Dmat : Matrix (Fin n) (Fin n) ℝ)
    (z : Fin n → EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ z', stress (n := n) (d := d) Dmat z ≤ stress (n := n) (d := d) Dmat z'

/-- The set of DKPS solutions (all minimizers), matching the "argmin" in Eq. (1). -/
def DKPSSet (Dmat : Matrix (Fin n) (Fin n) ℝ) :
    Set (Fin n → EuclideanSpace ℝ (Fin d)) :=
  { z | IsDKPS (n := n) (d := d) Dmat z }

end DKPSDefinitions

/-!
## §3 Query-efficiency (quench)

Quench §3 defines query-efficiency via expected loss under a model distribution `P_f`,
and studies the 1-nearest-neighbor regressor in DKPS space.

We formalize:
  • risk and queryEfficient (Eq. (2)),
  • MSE (used in Theorem 2),
  • the *exact* 1-NN regressor definition from the paper (averaging over ties),
  • the deterministic inequality used in the proof of Theorem 2.
-/

namespace QueryEfficiencyDefs

variable {𝓕 : Type} [PseudoMetricSpace 𝓕]
variable (Pf : Measure 𝓕) [IsProbabilityMeasure Pf]

/-- Risk `E_{f~P_f}[ ℓ(h(f), y(f)) ]` (quench Eq. (2)). -/
noncomputable def risk {Y : Type} (ℓ : Y → Y → ℝ) (y : 𝓕 → Y) (h : 𝓕 → Y) : ℝ :=
  ∫ f, ℓ (h f) (y f) ∂Pf

/-- Q-query-efficiency relative to another sequence (quench Eq. (2)). -/
def queryEfficient {Y : Type} (ℓ : Y → Y → ℝ) (y : 𝓕 → Y) (h h' : ℕ → 𝓕 → Y) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, n > N →
    risk (Pf := Pf) ℓ y (h n) ≤ risk (Pf := Pf) ℓ y (h' n)

/-- Mean squared error `MSE(ŷ) = E[(ŷ - y)^2]` (used in quench Theorem 2). -/
noncomputable def mse (y : 𝓕 → ℝ) (yhat : 𝓕 → ℝ) : ℝ :=
  ∫ f, (yhat f - y f) ^ 2 ∂Pf

/-!
### 1-NN regression in DKPS (quench §3)

The quench definition (verbatim):

  δ* = min_i ‖ψ̂ᵢ − ψ̂‖_F
  ŷ_NN =   (∑_{i : ‖ψ̂ᵢ - ψ̂‖_F = δ*} y_i)
         / (∑_{i : ‖ψ̂ᵢ - ψ̂‖_F = δ*} 1)

We implement this for a finite reference set indexed by `Fin n`. We assume `n>0`
(so that "min" and the NN-set are well-defined).
-/

section NNRegressor

variable {d n : ℕ} [Fact (0 < n)]
abbrev E := EuclideanSpace ℝ (Fin d)

variable (ψhatRef : Fin n → E)          -- ψ̂_i for reference models
variable (yRef : Fin n → ℝ)             -- y_i labels
variable (ψhatTgt : E)                  -- ψ̂ for target model

/-- The minimal distance `δ* = min_i ‖ψ̂ᵢ - ψ̂‖` (paper: δ*). -/
noncomputable def δStar : ℝ := by
  classical
  refine Finset.inf' (Finset.univ : Finset (Fin n)) ?_ (fun i => ‖ψhatRef i - ψhatTgt‖)
  refine ⟨⟨0, Fact.out⟩, by simp⟩

/-- The NN tie-set `{i | ‖ψ̂ᵢ - ψ̂‖ = δ*}` (paper: the indicator set in ŷ_NN). -/
noncomputable def nnSet : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter (fun i => ‖ψhatRef i - ψhatTgt‖ = δStar (ψhatRef := ψhatRef) (ψhatTgt := ψhatTgt))

/-- The 1-NN regressor ŷ_NN (paper definition; averages over ties). -/
noncomputable def nnReg : ℝ :=
  (nnSet (ψhatRef := ψhatRef) (ψhatTgt := ψhatTgt)).sum yRef
    / ((nnSet (ψhatRef := ψhatRef) (ψhatTgt := ψhatTgt)).card : ℝ)

lemma δStar_le (i : Fin n) :
    δStar (ψhatRef := ψhatRef) (ψhatTgt := ψhatTgt) ≤ ‖ψhatRef i - ψhatTgt‖ := by
  classical
  -- unfold δStar; use `Finset.inf'_le` with `i ∈ univ`
  simpa [δStar] using
    (Finset.inf'_le (s := (Finset.univ : Finset (Fin n)))
      (f := fun j => ‖ψhatRef j - ψhatTgt‖)
      (by refine ⟨⟨0, Fact.out⟩, by simp⟩)
      (by simp))

lemma nnSet_nonempty :
    (nnSet (ψhatRef := ψhatRef) (ψhatTgt := ψhatTgt)).Nonempty := by
  classical
  have huniv : (Finset.univ : Finset (Fin n)).Nonempty := by
    refine ⟨⟨0, Fact.out⟩, by simp⟩
  have hmem :
      δStar (ψhatRef := ψhatRef) (ψhatTgt := ψhatTgt)
        ∈ (Finset.univ : Finset (Fin n)).image (fun i => ‖ψhatRef i - ψhatTgt‖) := by
    simpa [δStar] using
      (Finset.inf'_mem (s := (Finset.univ : Finset (Fin n)))
        (f := fun i => ‖ψhatRef i - ψhatTgt‖) huniv)
  rcases Finset.mem_image.mp hmem with ⟨i0, hi0, hi0eq⟩
  refine ⟨i0, ?_⟩
  have : ‖ψhatRef i0 - ψhatTgt‖ = δStar (ψhatRef := ψhatRef) (ψhatTgt := ψhatTgt) := by
    simpa using hi0eq.symm
  simp [nnSet, this]

end NNRegressor

end QueryEfficiencyDefs

/-!
## §3 Assumptions and Theorem 2 (deterministic core)

Quench Assumption 1 (Lipschitz score function):
  |y(f,Q*) - y(f',Q*)| ≤ γ · ‖ψ(Q)(f) - ψ(Q)(f')‖₂

Quench Assumption 2 (model distribution support):
  P_f has positive mass in every neighborhood of every model.

In the proof of quench Theorem 2, these are combined with:
  • DKPS concentration (quench Theorem 1, cited from Acharyya et al. 2025),
  • a "denseness" sampling argument (derived from Assumption 2),
to obtain a small upper bound on the squared prediction error.

Here we mechanize the *deterministic inequality* that sits in the middle of the
paper's proof.
-/

section DeterministicCore

variable {𝓕 : Type} [PseudoMetricSpace 𝓕]
variable {d : ℕ}
abbrev E := EuclideanSpace ℝ (Fin d)

/-- Assumption 1 (quench): Lipschitz of the full score in the (true) DKPS. -/
def LipschitzScore (γ : ℝ) (yFull : 𝓕 → ℝ) (ψTrue : 𝓕 → E) : Prop :=
  ∀ f f', |yFull f - yFull f'| ≤ γ * ‖ψTrue f - ψTrue f'‖

/-- Assumption 2 (quench): model distribution has positive mass in every metric ball. -/
def ModelSupport (Pf : Measure 𝓕) : Prop :=
  ∀ f : 𝓕, ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ Pf (Metric.ball f δ) ≥ ε

/-!
### A general algebra lemma: averages preserve uniform bounds

This lemma is used to reconcile a small mismatch in quench:
the *definition* of ŷ_NN averages over ties, but the *proof* reasons about a
single nearest neighbor `f*`. The lemma below lets the proof go through without
assuming uniqueness of the nearest neighbor.
-/

lemma abs_avg_sub_le_of_forall
    {α : Type} [DecidableEq α]
    (S : Finset α) (hS : S.Nonempty)
    (y : α → ℝ) (y0 B : ℝ)
    (h : ∀ i, i ∈ S → |y i - y0| ≤ B) :
    |(S.sum y) / (S.card : ℝ) - y0| ≤ B := by
  classical
  -- B ≥ 0 since S is nonempty and |·| ≥ 0.
  have hBnonneg : 0 ≤ B := by
    rcases hS with ⟨i0, hi0⟩
    have hi0' := h i0 hi0
    exact le_trans (by simpa using abs_nonneg (y i0 - y0)) hi0'
  -- card > 0
  have hcard_pos : 0 < S.card := Finset.card_pos.mpr hS
  have hcard_posR : 0 < (S.card : ℝ) := by exact_mod_cast hcard_pos
  have hcard_neR : (S.card : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hcard_pos)
  -- Rewrite as an average of deviations.
  have hrew :
      (S.sum y) / (S.card : ℝ) - y0
        = (S.sum (fun i => y i - y0)) / (S.card : ℝ) := by
    -- Move y0 to a common denominator.
    calc
      (S.sum y) / (S.card : ℝ) - y0
          = (S.sum y) / (S.card : ℝ) - (y0 * (S.card : ℝ)) / (S.card : ℝ) := by
              simp [hcard_neR]
      _ = (S.sum y - y0 * (S.card : ℝ)) / (S.card : ℝ) := by
              simp [sub_div]
      _ = (S.sum y - (S.card : ℝ) * y0) / (S.card : ℝ) := by ring
      _ = (S.sum y - (S.sum fun _ : α => y0)) / (S.card : ℝ) := by
              simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ = (S.sum (fun i => y i - y0)) / (S.card : ℝ) := by
              simp [Finset.sum_sub_distrib]
  -- Triangle inequality for sums + termwise bound.
  calc
    |(S.sum y) / (S.card : ℝ) - y0|
        = |(S.sum (fun i => y i - y0)) / (S.card : ℝ)| := by simp [hrew]
    _ = |S.sum (fun i => y i - y0)| / (S.card : ℝ) := by
          simp [abs_div, abs_of_pos hcard_posR]
    _ ≤ (S.sum (fun i => |y i - y0|)) / (S.card : ℝ) := by
          -- divide by the positive constant (S.card : ℝ)
          have hsum : |S.sum (fun i => y i - y0)| ≤ S.sum (fun i => |y i - y0|) :=
            Finset.abs_sum_le_sum_abs S (fun i => y i - y0)
          exact div_le_div_of_le hcard_posR hsum
    _ ≤ (S.sum (fun _ : α => B)) / (S.card : ℝ) := by
          have : S.sum (fun i => |y i - y0|) ≤ S.sum (fun _ : α => B) := by
            refine Finset.sum_le_sum ?_
            intro i hi
            exact h i hi
          exact div_le_div_of_le hcard_posR this
    _ = B := by
          -- average of constant B is B
          have : (S.sum (fun _ : α => B)) = (S.card : ℝ) * B := by
            simp [Finset.sum_const, nsmul_eq_mul]
          simp [this, hcard_neR, mul_div_cancel_left₀, hBnonneg]

/-!
### Deterministic version of the quench Theorem 2 inequality
-/

section NNBound

variable {n : ℕ} [Fact (0 < n)]
variable (f : 𝓕) (fRef : Fin n → 𝓕)

variable (ψTrue ψHat : 𝓕 → E)
variable (yFull : 𝓕 → ℝ)

variable (c : ℝ) (hc : 0 ≤ c)

/-- DKPS estimate accuracy on the reference set: ∀i, ‖ψ̂(fᵢ) - ψ(fᵢ)‖ ≤ c. -/
def RefAccurate : Prop := ∀ i : Fin n, ‖ψHat (fRef i) - ψTrue (fRef i)‖ ≤ c

/-- DKPS estimate accuracy on the target: ‖ψ̂(f) - ψ(f)‖ ≤ c. -/
def TgtAccurate : Prop := ‖ψHat f - ψTrue f‖ ≤ c

/-- Existence of a reference model within ε' in true DKPS space. -/
def ExistsTrueNeighbor (ε' : ℝ) : Prop := ∃ i : Fin n, ‖ψTrue (fRef i) - ψTrue f‖ ≤ ε'

/-- The DKPS vectors for reference models (estimated). -/
noncomputable def ψhatRef (i : Fin n) : E := ψHat (fRef i)

/-- The DKPS vector for the target model (estimated). -/
noncomputable def ψhatTgt : E := ψHat f

/-- The quench 1-NN prediction ŷ_NN (averaged over ties). -/
noncomputable def yhatNN : ℝ :=
  QueryEfficiencyDefs.nnReg
    (ψhatRef := ψhatRef (f := f) (fRef := fRef) (ψHat := ψHat))
    (yRef := fun i => yFull (fRef i))
    (ψhatTgt := ψhatTgt (f := f) (ψHat := ψHat))

/-- The NN tie-set S = {i : ‖ψ̂_i - ψ̂‖ = δ*}. -/
noncomputable def NNset : Finset (Fin n) :=
  QueryEfficiencyDefs.nnSet
    (ψhatRef := ψhatRef (f := f) (fRef := fRef) (ψHat := ψHat))
    (ψhatTgt := ψhatTgt (f := f) (ψHat := ψHat))

/-- The minimal estimated distance δ* = min_i ‖ψ̂_i - ψ̂‖. -/
noncomputable def δStar : ℝ :=
  QueryEfficiencyDefs.δStar
    (ψhatRef := ψhatRef (f := f) (fRef := fRef) (ψHat := ψHat))
    (ψhatTgt := ψhatTgt (f := f) (ψHat := ψHat))

/-- On NNset, the estimated DKPS distance equals δ*. -/
lemma mem_NNset_iff {i : Fin n} :
    i ∈ NNset (f := f) (fRef := fRef) (ψHat := ψHat)
      ↔ ‖ψHat (fRef i) - ψHat f‖ = δStar (f := f) (fRef := fRef) (ψHat := ψHat) := by
  classical
  simp [NNset, QueryEfficiencyDefs.nnSet, δStar, ψhatRef, ψhatTgt]

/--
Deterministic bound (quench Thm 2 proof, deterministic part):

|ŷ_NN - yFull(f)| ≤ γ * (ε' + 4c).
-/
theorem abs_yhatNN_sub_le
    {γ ε' : ℝ}
    (hγ : 0 ≤ γ)
    (hLip : LipschitzScore (d := d) γ yFull ψTrue)
    (hRef : RefAccurate (f := f) (fRef := fRef) (ψTrue := ψTrue) (ψHat := ψHat) c)
    (hTgt : TgtAccurate (f := f) (ψTrue := ψTrue) (ψHat := ψHat) c)
    (hEx  : ExistsTrueNeighbor (f := f) (fRef := fRef) (ψTrue := ψTrue) ε') :
    |yhatNN (f := f) (fRef := fRef) (ψHat := ψHat) (yFull := yFull) - yFull f| ≤ γ * (ε' + 4*c) := by
  classical
  -- Step 1: δ* ≤ ε' + 2c (existence of a true neighbor + triangle inequality).
  have hδ_le : δStar (f := f) (fRef := fRef) (ψHat := ψHat) ≤ ε' + 2*c := by
    rcases hEx with ⟨i0, hi0⟩
    have hδ_le_i0 :
        δStar (f := f) (fRef := fRef) (ψHat := ψHat)
          ≤ ‖ψHat (fRef i0) - ψHat f‖ := by
      simpa [δStar] using
        (QueryEfficiencyDefs.δStar_le
          (ψhatRef := ψhatRef (f := f) (fRef := fRef) (ψHat := ψHat))
          (ψhatTgt := ψhatTgt (f := f) (ψHat := ψHat)) i0)
    have htri :
        ‖ψHat (fRef i0) - ψHat f‖ ≤ ε' + 2*c := by
      -- ‖ψ̂_i0 - ψ̂‖ ≤ ‖ψ̂_i0 - ψ_i0‖ + ‖ψ_i0 - ψ‖ + ‖ψ - ψ̂‖
      have h1 : ‖ψHat (fRef i0) - ψHat f‖
          ≤ ‖ψHat (fRef i0) - ψTrue (fRef i0)‖ + ‖ψTrue (fRef i0) - ψHat f‖ := by
        simpa using (norm_sub_le (ψHat (fRef i0)) (ψTrue (fRef i0)) (ψHat f))
      have h2 : ‖ψTrue (fRef i0) - ψHat f‖
          ≤ ‖ψTrue (fRef i0) - ψTrue f‖ + ‖ψTrue f - ψHat f‖ := by
        simpa using (norm_sub_le (ψTrue (fRef i0)) (ψTrue f) (ψHat f))
      have hsym : ‖ψTrue f - ψHat f‖ = ‖ψHat f - ψTrue f‖ := by
        simpa [norm_sub_rev]
      have hcomb :
          ‖ψHat (fRef i0) - ψHat f‖
            ≤ ‖ψHat (fRef i0) - ψTrue (fRef i0)‖
              + ‖ψTrue (fRef i0) - ψTrue f‖
              + ‖ψHat f - ψTrue f‖ := by
        linarith [h1, h2, hsym]
      have hRef_i0 : ‖ψHat (fRef i0) - ψTrue (fRef i0)‖ ≤ c := hRef i0
      have hTgt' : ‖ψHat f - ψTrue f‖ ≤ c := hTgt
      linarith [hcomb, hRef_i0, hi0, hTgt']
    exact le_trans hδ_le_i0 htri

  -- Step 2: every i in NNset has |y_i - y| ≤ γ(δ* + 2c).
  have hEach : ∀ i : Fin n,
      i ∈ NNset (f := f) (fRef := fRef) (ψHat := ψHat) →
        |yFull (fRef i) - yFull f| ≤ γ * (δStar (f := f) (fRef := fRef) (ψHat := ψHat) + 2*c) := by
    intro i hiNN
    have hdist_hat :
        ‖ψHat (fRef i) - ψHat f‖ = δStar (f := f) (fRef := fRef) (ψHat := ψHat) :=
      (mem_NNset_iff (f := f) (fRef := fRef) (ψHat := ψHat) (i := i)).1 hiNN
    -- true distance bound
    have htri_true :
        ‖ψTrue (fRef i) - ψTrue f‖
          ≤ δStar (f := f) (fRef := fRef) (ψHat := ψHat) + 2*c := by
      have h1 : ‖ψTrue (fRef i) - ψTrue f‖
          ≤ ‖ψTrue (fRef i) - ψHat (fRef i)‖ + ‖ψHat (fRef i) - ψTrue f‖ := by
        simpa using (norm_sub_le (ψTrue (fRef i)) (ψHat (fRef i)) (ψTrue f))
      have h2 : ‖ψHat (fRef i) - ψTrue f‖
          ≤ ‖ψHat (fRef i) - ψHat f‖ + ‖ψHat f - ψTrue f‖ := by
        simpa using (norm_sub_le (ψHat (fRef i)) (ψHat f) (ψTrue f))
      have hRef_i : ‖ψHat (fRef i) - ψTrue (fRef i)‖ ≤ c := hRef i
      have hTgt' : ‖ψHat f - ψTrue f‖ ≤ c := hTgt
      have hsym : ‖ψTrue (fRef i) - ψHat (fRef i)‖ = ‖ψHat (fRef i) - ψTrue (fRef i)‖ := by
        simpa [norm_sub_rev]
      have hcomb :
          ‖ψTrue (fRef i) - ψTrue f‖
            ≤ ‖ψHat (fRef i) - ψTrue (fRef i)‖
              + ‖ψHat (fRef i) - ψHat f‖
              + ‖ψHat f - ψTrue f‖ := by
        linarith [h1, h2, hsym]
      linarith [hcomb, hRef_i, hTgt', hdist_hat, hc]
    -- Lipschitz
    have hLip_i : |yFull (fRef i) - yFull f| ≤ γ * ‖ψTrue (fRef i) - ψTrue f‖ := hLip (fRef i) f
    exact le_trans hLip_i (by
      have := mul_le_mul_of_nonneg_left htri_true hγ
      simpa [mul_add, add_assoc, add_left_comm, add_comm] using this)

  -- Step 3: average over NNset preserves the bound.
  have hSnonempty :
      (NNset (f := f) (fRef := fRef) (ψHat := ψHat)).Nonempty := by
    simpa [NNset] using
      (QueryEfficiencyDefs.nnSet_nonempty
        (ψhatRef := ψhatRef (f := f) (fRef := fRef) (ψHat := ψHat))
        (ψhatTgt := ψhatTgt (f := f) (ψHat := ψHat)))

  have hAvg :
      |yhatNN (f := f) (fRef := fRef) (ψHat := ψHat) (yFull := yFull) - yFull f|
        ≤ γ * (δStar (f := f) (fRef := fRef) (ψHat := ψHat) + 2*c) := by
    -- rewrite yhatNN as average over NNset then apply abs_avg_sub_le_of_forall
    have hy :
        yhatNN (f := f) (fRef := fRef) (ψHat := ψHat) (yFull := yFull)
          = ( (NNset (f := f) (fRef := fRef) (ψHat := ψHat)).sum (fun i => yFull (fRef i)) )
              / ((NNset (f := f) (fRef := fRef) (ψHat := ψHat)).card : ℝ) := by
      simp [yhatNN, NNset, QueryEfficiencyDefs.nnReg]
    have h0 :
        |((NNset (f := f) (fRef := fRef) (ψHat := ψHat)).sum (fun i => yFull (fRef i)))
            / ((NNset (f := f) (fRef := fRef) (ψHat := ψHat)).card : ℝ) - yFull f|
          ≤ γ * (δStar (f := f) (fRef := fRef) (ψHat := ψHat) + 2*c) := by
      exact abs_avg_sub_le_of_forall
        (S := NNset (f := f) (fRef := fRef) (ψHat := ψHat))
        (hS := hSnonempty)
        (y := fun i => yFull (fRef i))
        (y0 := yFull f)
        (B := γ * (δStar (f := f) (fRef := fRef) (ψHat := ψHat) + 2*c))
        (h := by
          intro i hi
          simpa using hEach i hi)
    simpa [hy] using h0

  -- Step 4: substitute δ* ≤ ε' + 2c.
  have hFinal :
      γ * (δStar (f := f) (fRef := fRef) (ψHat := ψHat) + 2*c) ≤ γ * (ε' + 4*c) := by
    have : δStar (f := f) (fRef := fRef) (ψHat := ψHat) + 2*c ≤ ε' + 4*c := by
      linarith [hδ_le]
    exact mul_le_mul_of_nonneg_left this hγ

  exact le_trans hAvg hFinal

end NNBound

end DeterministicCore

/-!
## (Optional) Probabilistic wrapper for the full quench Theorem 2

Quench Theorem 2 concludes an MSE bound "with high probability" by combining:
  • Acharyya et al. (2025) concentration (quench Theorem 1), and
  • Assumption 2 + sampling to get a close reference model.

These are substantial probability theory developments and are best kept modular.

Below is a *structure-only* statement showing where those ingredients plug in.
-/

section ProbabilisticWrapper

variable {𝓕 : Type} [PseudoMetricSpace 𝓕]
variable (Pf : Measure 𝓕) [IsProbabilityMeasure Pf]
variable {d : ℕ}
abbrev E := EuclideanSpace ℝ (Fin d)
variable (ψTrue ψHat : 𝓕 → E) (yFull : 𝓕 → ℝ)

/-- Placeholder for Acharyya et al. (2025) (quench Theorem 1) as a usable API. -/
axiom dkps_concentration_event
    (η c : ℝ) (hη : 0 < η) (hc : 0 < c) :
    ∃ (n0 r0 : ℕ), True
    -- TODO: replace `True` with a genuine probability statement.

/-- Placeholder for the sampling consequence of ModelSupport (quench Assumption 2). -/
axiom exists_true_neighbor_high_prob
    (η ε' : ℝ) (hη : 0 < η) (hε' : 0 < ε') :
    ∃ (n0 : ℕ), True
    -- TODO: replace `True` with a genuine probability statement.

/--
A wrapper-shaped statement for quench Theorem 2.

Once the two axioms above are upgraded to actual probability lemmas, this becomes
a short proof that orchestrates:
  • choice of c and ε' from ε (as in quench),
  • taking n,r large enough,
  • applying `DeterministicCore.NNBound.abs_yhatNN_sub_le`,
  • squaring to obtain an ε bound on MSE.
-/
theorem quench_Theorem2_structure_only :
    ∀ ε : ℝ, 0 < ε → ∃ (n m r : ℕ), True := by
  intro ε hε
  refine ⟨1, 1, 1, trivial⟩

end ProbabilisticWrapper

end Quench
