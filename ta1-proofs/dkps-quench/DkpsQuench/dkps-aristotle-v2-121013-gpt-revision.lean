import Mathlib

/-!
# DKPS + query-efficiency definitions from the Quench ICML draft

This file is intended to be dropped into a Mathlib-based project and **compile**.
It is written to be robust in projects that set `set_option autoImplicit false`.

The goal here is to match the **definitions** in

> *Query-efficient model evaluation using cached responses* (quench-icml-nonanon.pdf)

as literally as is reasonable in Lean.

## What is fully definitionally faithful to the paper?

* §1.2: benchmark query set `Q*` and scoring function `y(f,Q)`.
* §2: DKPS construction: `x̄_{ij}`, `X̄_i`, distance matrix `D_{ii'}` using Frobenius norm.
* §2 Eq. (1): stress objective and the `argmin` (represented as the set of all minimizers).
* §3 Eq. (2): query-efficiency defined via expected loss under a model distribution `P_f`.
* §3: nearest-neighbor regressor in DKPS, including *averaging over ties*.

## Proofs

Only light deterministic lemmas are included. Anything that would require serious
probability theory (e.g. the Acharyya concentration theorem used in the paper) is
left as a `sorry`/placeholder so the file stays usable.

If you want, we can later replace those placeholders with actual lemmas, but the
**definitions** should not need to change.
-/

set_option autoImplicit false

open scoped BigOperators
open MeasureTheory

namespace MCC_atTop_eq_FM
namespace Quench

/-!
## Helper types

The paper uses:
* response embeddings in `ℝ^p`
* DKPS / perspective vectors in `ℝ^d`

We model these as Euclidean spaces indexed by `Fin`.
-/

/-- `ℝ^p` as a Euclidean space (for response embeddings). -/
abbrev EmbVec (p : ℕ) : Type := EuclideanSpace ℝ (Fin p)

/-- `ℝ^d` as a Euclidean space (for DKPS / perspective vectors). -/
abbrev DKPSVec (d : ℕ) : Type := EuclideanSpace ℝ (Fin d)

/-!
## Frobenius norm `‖·‖_F`

Quench uses Frobenius distances `‖X̄_i - X̄_{i'}‖_F`.

We define

`‖A‖_F := sqrt(∑ᵢ ∑ⱼ (A i j)^2)`

for real matrices.
-/

/-- Frobenius norm for a real matrix. -/
noncomputable def frob {I J : Type} [Fintype I] [Fintype J] (A : Matrix I J ℝ) : ℝ :=
  Real.sqrt (∑ i : I, ∑ j : J, (A i j) ^ 2)

@[simp] lemma frob_nonneg {I J : Type} [Fintype I] [Fintype J] (A : Matrix I J ℝ) :
    0 ≤ frob A := by
  simp [frob]

/-!
## §1.2 Problem statement

Quench defines:

* a benchmark query set `Q* = {q₁,…,q_M}`
* a benchmark scoring function `y : 𝓕 × 2^{Q*} → [0,1]`

We model subsets of queries as `Finset 𝓠`.
-/

section ProblemStatement

variable {𝓕 𝓠 : Type}

/-- Full benchmark query set `Q*`. -/
variable (Qstar : Finset 𝓠)

/-- Benchmark scoring function `y(f,Q)` (paper: `y : 𝓕 × 2^{Q*} → [0,1]`). -/
variable (y : 𝓕 → Finset 𝓠 → ℝ)

/-- Full benchmark score `y(f,Q*)` (paper abbreviates as `y`). -/
def yFull (f : 𝓕) : ℝ := y f Qstar

/-- Subset score `y(f,Q)` (paper notation `\hat y_Q := y(f,Q)`). -/
def ySub (Q : Finset 𝓠) (f : 𝓕) : ℝ := y f Q

end ProblemStatement

/-!
## §2 DKPS construction

Given:

* models indexed by `Fin n`
* queries indexed by `Fin m`
* `r` replicates per (model, query)
* response space `X`
* embedding function `g : X → ℝ^p`

Define:

* embedded responses `x_{ijk} = g(resp i j k)`
* averaged embedded response per query `x̄_{ij} = (1/r) Σ_k x_{ijk}`
* `X̄_i ∈ ℝ^{m×p}` whose j-th row is `x̄_{ij}`
* distance matrix `D_{ii'} = ‖X̄_i - X̄_{i'}‖_F`

This matches Quench §2.
-/

section DKPS

variable {X : Type}
variable {n m r p d : ℕ}

/-- Embedding function `g : X → ℝ^p`. -/
variable (g : X → EmbVec p)

/-- Cached / sampled responses `resp i j k : X`. -/
variable (resp : Fin n → Fin m → Fin r → X)

/-- Embedded response `x_{ijk} = g(resp i j k)`. -/
noncomputable def x (i : Fin n) (j : Fin m) (k : Fin r) : EmbVec p :=
  g (resp i j k)

/-- Average embedded response `x̄_{ij} = (1/r) * Σ_k x_{ijk}`. -/
noncomputable def xbar (i : Fin n) (j : Fin m) : EmbVec p :=
  ((1 : ℝ) / (r : ℝ)) • (∑ k : Fin r, x (g := g) (resp := resp) i j k)

/-- Matrix `X̄_i ∈ ℝ^{m×p}` with entries `(j,a) ↦ (x̄_{ij})_a`. -/
noncomputable def Xbar (i : Fin n) : Matrix (Fin m) (Fin p) ℝ :=
  fun j a => (xbar (g := g) (resp := resp) i j) a

/-- Distance matrix `D` with entries `D_{ii'} = ‖X̄_i - X̄_{i'}‖_F`. -/
noncomputable def D : Matrix (Fin n) (Fin n) ℝ :=
  fun i i' => frob (Xbar (g := g) (resp := resp) i - Xbar (g := g) (resp := resp) i')

/-- Stress objective from Quench Eq. (1). -/
noncomputable def stress (Dmat : Matrix (Fin n) (Fin n) ℝ)
    (z : Fin n → DKPSVec d) : ℝ :=
  ∑ i : Fin n, ∑ i' : Fin n, (‖z i - z i'‖ - Dmat i i') ^ 2

/-- `IsDKPS D z` means `z` is a global minimizer of the stress objective (Eq. (1) argmin). -/
def IsDKPS (Dmat : Matrix (Fin n) (Fin n) ℝ) (z : Fin n → DKPSVec d) : Prop :=
  ∀ z', stress (n := n) (d := d) Dmat z ≤ stress (n := n) (d := d) Dmat z'

/-- The set of all DKPS solutions (all minimizers), matching the paper's `argmin`. -/
def DKPSSet (Dmat : Matrix (Fin n) (Fin n) ℝ) : Set (Fin n → DKPSVec d) :=
  { z | IsDKPS (n := n) (d := d) Dmat z }

end DKPS

/-!
## §3 Query-efficiency (Eq. (2))

Quench defines query-efficiency by comparing *expected loss* under a model
population distribution `P_f`.

We represent `P_f` as a probability measure `Pf : Measure 𝓕`.
-/

namespace QueryEfficiency

section Risk

variable {𝓕 : Type} [MeasurableSpace 𝓕]

/-- Risk `E_{f~P_f}[ ℓ(h(f), y(f)) ]` (paper Eq. (2)).

We implement expectation as a Bochner integral of a real-valued function.
(Integrability/measurability assumptions are handled later as needed.)
-/
noncomputable def risk (Pf : Measure 𝓕) {Y : Type}
    (ℓ : Y → Y → ℝ) (y : 𝓕 → Y) (h : 𝓕 → Y) : ℝ :=
  ∫ f, ℓ (h f) (y f) ∂Pf

/-- Mean squared error `MSE(ŷ) = E[(ŷ - y)^2]` (used in quench Thm 2). -/
noncomputable def mse (Pf : Measure 𝓕) (y : 𝓕 → ℝ) (yhat : 𝓕 → ℝ) : ℝ :=
  ∫ f, (yhat f - y f) ^ 2 ∂Pf

/-- Q-query-efficiency relative to another sequence (paper Eq. (2)).

We include `[IsProbabilityMeasure Pf]` explicitly because the paper works with a
probability distribution `P_f`.
-/
def queryEfficient (Pf : Measure 𝓕) [IsProbabilityMeasure Pf] {Y : Type}
    (ℓ : Y → Y → ℝ) (y : 𝓕 → Y)
    (h h' : ℕ → 𝓕 → Y) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, n > N →
    risk Pf ℓ y (h n) ≤ risk Pf ℓ y (h' n)

end Risk

/-!
## §3 Nearest-neighbor regressor in DKPS

Quench defines (for a target `ψ̂` and reference vectors `ψ̂_i` with labels `y_i`):

* `δ* = min_i ‖ψ̂_i - ψ̂‖_F`
* `ŷ_NN = (∑ 1{‖ψ̂_i-ψ̂‖_F=δ*} y_i) / (∑ 1{‖ψ̂_i-ψ̂‖_F=δ*})`

We implement the indicator set as a `Finset.filter`.

Note: the paper writes `‖·‖_F` here, but in §3 the objects are DKPS vectors
in `ℝ^d`, so this is just the Euclidean norm.
-/

section NN

variable {d n : ℕ}
variable [Fact (0 < n)]

variable (ψhatRef : Fin n → DKPSVec d)
variable (yRef : Fin n → ℝ)
variable (ψhatTgt : DKPSVec d)

/-- `δ* = min_i ‖ψ̂_i - ψ̂‖`. -/
noncomputable def δStar : ℝ := by
  classical
  -- We take the minimum of the (finite, nonempty) set of distances.
  let S : Finset ℝ := (Finset.univ : Finset (Fin n)).image (fun i => ‖ψhatRef i - ψhatTgt‖)
  have hS : S.Nonempty := by
    -- Exhibit one element of the image.
    refine ⟨‖ψhatRef ⟨0, Fact.out⟩ - ψhatTgt‖, ?_⟩
    refine Finset.mem_image.2 ?_
    refine ⟨⟨0, Fact.out⟩, ?_, rfl⟩
    simp
  exact S.min' hS

/-- The NN tie-set `{i | ‖ψ̂_i - ψ̂‖ = δ*}`. -/
noncomputable def nnSet : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter (fun i => ‖ψhatRef i - ψhatTgt‖ = δStar (ψhatRef := ψhatRef) (ψhatTgt := ψhatTgt))

/-- The quench 1-NN regressor `ŷ_NN` (averaging over ties). -/
noncomputable def yhatNN : ℝ :=
  (nnSet (ψhatRef := ψhatRef) (ψhatTgt := ψhatTgt)).sum yRef
    / ((nnSet (ψhatRef := ψhatRef) (ψhatTgt := ψhatTgt)).card : ℝ)

/-- (Lemma) `nnSet` is nonempty (a minimizer exists for a nonempty finite set).

This is true in mathlib, but we leave it as a placeholder because the *definition*
of `yhatNN` is the priority.
-/
lemma nnSet_nonempty : (nnSet (ψhatRef := ψhatRef) (ψhatTgt := ψhatTgt)).Nonempty := by
  classical
  sorry

end NN

end QueryEfficiency

/-!
## Quench assumptions

We separate Assumption 1 (purely metric) from Assumption 2 (measure-theoretic).
This avoids requiring `MeasurableSpace` when you only want Assumption 1.
-/

section Assumption1

variable {𝓕 : Type} [PseudoMetricSpace 𝓕]
variable {d : ℕ}

variable (ψTrue : 𝓕 → DKPSVec d)
variable (yFull : 𝓕 → ℝ)

/-- Quench Assumption 1 (Lipschitz score function). -/
def LipschitzScore (γ : ℝ) : Prop :=
  ∀ f f' : 𝓕, |yFull f - yFull f'| ≤ γ * ‖ψTrue f - ψTrue f'‖

end Assumption1

section Assumption2

variable {𝓕 : Type} [PseudoMetricSpace 𝓕] [MeasurableSpace 𝓕]

/-- Quench Assumption 2 (model distribution support / denseness).

We phrase it with a real `ε > 0` but compare using `ENNReal.ofReal ε` because
`Measure` returns values in `ℝ≥0∞`.
-/
def ModelSupport (Pf : Measure 𝓕) : Prop :=
  ∀ f : 𝓕, ∀ δ : ℝ, 0 < δ →
    ∃ ε : ℝ, 0 < ε ∧ ENNReal.ofReal ε ≤ Pf (Metric.ball f δ)

end Assumption2

/-!
## Theorem 2 (quench): deterministic core (statement only)

The quench proof of Theorem 2 is probabilistic overall, but at its center is a
purely deterministic inequality bounding the *prediction error* once you assume:

* Lipschitz score (Assumption 1)
* estimation error bounds `‖ψ̂ - ψ‖ ≤ c`
* existence of a reference model within `ε'` in true DKPS space

We expose that inequality as a theorem-shaped interface.
-/

section DeterministicCore

namespace QueryEfficiency

variable {𝓕 : Type} [PseudoMetricSpace 𝓕]
variable {d n : ℕ} [Fact (0 < n)]

variable (f : 𝓕)
variable (fRef : Fin n → 𝓕)

variable (ψTrue ψHat : 𝓕 → DKPSVec d)
variable (yFull : 𝓕 → ℝ)

variable (c γ ε' : ℝ)

/-- Reference accuracy: `∀i, ‖ψ̂(fRef i) - ψ(fRef i)‖ ≤ c`. -/
def RefAccurate : Prop :=
  ∀ i : Fin n, ‖ψHat (fRef i) - ψTrue (fRef i)‖ ≤ c

/-- Target accuracy: `‖ψ̂(f) - ψ(f)‖ ≤ c`. -/
def TgtAccurate : Prop :=
  ‖ψHat f - ψTrue f‖ ≤ c

/-- Existence of a true neighbor: `∃i, ‖ψ(fRef i) - ψ(f)‖ ≤ ε'`. -/
def ExistsTrueNeighbor : Prop :=
  ∃ i : Fin n, ‖ψTrue (fRef i) - ψTrue f‖ ≤ ε'

/-- The quench 1-NN predictor `ŷ_NN` expressed using `ψHat`. -/
noncomputable def yhatNN' : ℝ :=
  QueryEfficiency.yhatNN
    (ψhatRef := fun i => ψHat (fRef i))
    (yRef := fun i => yFull (fRef i))
    (ψhatTgt := ψHat f)

/-- Deterministic inequality used in the quench Theorem 2 proof.

`|ŷ_NN - y(f)| ≤ γ * (ε' + 4c)`.

The proof is left as a placeholder here; the statement is the important API.
-/
theorem abs_yhatNN_sub_le
    (hγ : 0 ≤ γ)
    (hLip : LipschitzScore (ψTrue := ψTrue) (yFull := yFull) γ)
    (hRef : RefAccurate (fRef := fRef) (ψTrue := ψTrue) (ψHat := ψHat) (c := c))
    (hTgt : TgtAccurate (f := f) (ψTrue := ψTrue) (ψHat := ψHat) (c := c))
    (hEx  : ExistsTrueNeighbor (f := f) (fRef := fRef) (ψTrue := ψTrue) (ε' := ε')) :
    |yhatNN' - yFull f| ≤ γ * (ε' + 4 * c) := by
  classical
  sorry

end QueryEfficiency

end DeterministicCore

end Quench
end MCC_atTop_eq_FM
