
import Mathlib

/-
This file is intended to live inside a larger Mathlib-based project.
Many projects in this area run with `autoImplicit = false`; we adopt that convention here
to avoid accidental implicit parameters.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-!
# Quench (ICML) — DKPS + Nearest-Neighbor Query-Efficiency

This file consolidates and cleans up scattered proof attempts into a single, organized
formalization skeleton that follows *exactly* the definitions in:

> Hayden Helm, Ben Johnson, Carey E. Priebe,
> *Query-efficient model evaluation using cached responses* (ICML submission / preprint).
>
> In particular we track:
> * Section 1.2 (problem setting and score function `y : 𝓕 × 2^{Q*} → [0,1]`)
> * Section 2 (DKPS construction, Eq. (1))
> * Section 3 (query-efficiency definition, Eq. (2), Assumptions 1–2, Theorem 2)

**Design goals of this Lean file**
1. **Definitions match the paper exactly** (hard constraint).
2. Proofs are kept as tractable as possible. Some analytic steps are still marked `sorry`,
   but the proof is structured so that each `sorry` corresponds to a clearly identified
   paper step / external cited theorem.

Throughout, we use `Finset Q` to represent subsets of the finite benchmark query set `Q*`,
as the paper’s `2^{Q*}`.

-/

open scoped BigOperators
noncomputable section

namespace QuenchICML

universe u v

/-!
## Paper conventions and Lean conventions

**Paper notation**
- `Q`        : query space
- `X`        : response space
- `Q*`       : finite benchmark query set `Q* = {q₁,…,q_M}`
- `𝓕`        : model space (black-box generative models)
- `y(f,Q)`   : benchmark score on subset `Q ⊆ Q*`, valued in `[0,1]`

**Lean choices**
- `Q*` is a `Finset Q`
- `2^{Q*}` is represented by `Finset Q` together with the side-condition `Qsub ⊆ Qstar`
- the codomain `[0,1]` is represented as a subtype `UnitInterval = {x : ℝ // x ∈ Icc 0 1}`
- whenever we want to compute expectations / MSE we coerce `UnitInterval` to `ℝ`
- DKPS vectors live in `ℝ^d = EuclideanSpace ℝ (Fin d)`
- Frobenius norm is defined explicitly for matrices `ℝ^{m×p}`

This matches the paper literally, while staying usable in Lean.
-/

/-- Paper’s `[0,1]` as a Lean type (subtype of `ℝ`). -/
abbrev UnitInterval : Type := {x : ℝ // x ∈ Set.Icc (0 : ℝ) 1}

instance : Coe UnitInterval ℝ := ⟨Subtype.val⟩

/-- Convenience: `ℝ^d` as a Euclidean space with the usual `‖·‖₂` norm. -/
abbrev Vec (d : ℕ) : Type := EuclideanSpace ℝ (Fin d)

/-- Convenience: `ℝ^{m×p}` as a matrix type. -/
abbrev Mat (m p : ℕ) : Type := Matrix (Fin m) (Fin p) ℝ

/-!
## Section 1.2 — Models and benchmark score function

Paper (Section 1.2) treats a model as a random mapping from `Q` to `X` with a distribution `F`.
In Lean, we model this equivalently as: for each query `q : Q`, the model returns a probability
distribution on responses.
-/

/-!
We avoid depending on a particular bundled `ProbMeasure` structure name in Mathlib.
Instead we use the standard `Measure` together with the predicate/typeclass
`IsProbabilityMeasure`.

This matches the paper’s intent: *a model returns a probability distribution on responses*.
-/

/-- A probability distribution on `X` (bundled as a measure with total mass `1`). -/
abbrev ProbMeasure (X : Type v) [MeasurableSpace X] : Type v :=
  { μ : MeasureTheory.Measure X // MeasureTheory.IsProbabilityMeasure μ }

/-- A black-box model: each query yields a probability distribution over responses.

Paper: “a model is a random mapping from `Q` to `X` with distribution `F`.” -/
abbrev Model (Q : Type u) (X : Type v) [MeasurableSpace X] : Type (max u v) :=
  Q → ProbMeasure X

-- From here on we work with a fixed query set `Q` and response space `X`.
variable {Q : Type u} [DecidableEq Q]
variable {X : Type v} [MeasurableSpace X]

-- We keep the measurable structure on the model space abstract.
-- This is needed only to speak about a probability distribution `P_f` on models.
variable [MeasurableSpace (Model Q X)]

/- Paper: benchmark query set `Q* = {q₁,…,q_M}`. -/
variable (Qstar : Finset Q)

/- Paper: score function `y : 𝓕 × 2^{Q*} → [0,1]`. -/
variable (score : Model Q X → Finset Q → UnitInterval)

/-- Paper notation `y(f,Q*)` (the “full benchmark” score). -/
def yFull (f : Model Q X) : ℝ := (score f Qstar : ℝ)

/-- Paper notation `y(f,Q)` for `Q ⊆ Q*`. -/
def ySub (Qsub : Finset Q) (f : Model Q X) : ℝ := (score f Qsub : ℝ)

-- We will always *use* `ySub Qsub` with the side-condition `Qsub ⊆ Qstar`,
-- exactly as in the paper.

--------------------------------------------------------------------------------
/-!
## Section 2 — DKPS construction (Eq. (1))

We formalize the objects appearing in Eq. (1) *literally*.

### Inputs
- `n` reference models `f₁,…,fₙ`
- `m` benchmark queries `q₁,…,qₘ` (a subset of `Q*`)
- `r` replicate responses per model-query pair
- embedding function `g : X → ℝ^p`

### Derived objects (paper)
- average embedded response matrix `X̄_i ∈ ℝ^{m×p}`, with rows
  `X̄_{ij·} = (1/r) ∑_{k=1}^r g(f_i(q_j))_k`
- distance matrix `D_{ii'}` defined via Frobenius distance:
  `D_{ii'} = ‖X̄_i - X̄_{i'}‖_F`
- DKPS representations `ψ̂₁,…,ψ̂ₙ ∈ ℝ^d` defined by stress minimization (Eq. (1)):
  `(ψ̂₁,…,ψ̂ₙ) ∈ argmin_{z₁,…,zₙ ∈ ℝ^d} ∑_{i,i'} (‖z_i - z_{i'}‖ - D_{ii'})²`
-/

/-- Frobenius norm on `ℝ^{m×p}`.

Paper uses `‖·‖_F` in the definition of `D_{ii'}`. -/
def frobNorm {m p : ℕ} (A : Mat m p) : ℝ :=
  Real.sqrt (∑ i : Fin m, ∑ j : Fin p, (A i j) ^ (2 : ℕ))

/-- Frobenius distance `‖A - B‖_F`. -/
def frobDist {m p : ℕ} (A B : Mat m p) : ℝ :=
  frobNorm (A - B)

/-- Average of `r` embedded responses, `(1/r) ∑_{k=1}^r g(x_k)`.

Paper: `X̄_{ij·} = (1/r) ∑_{k=1}^r g(f_i(q_j))_k`. -/
def avgEmbed {p r : ℕ} (g : X → Vec p) (resp : Fin r → X) : Vec p :=
  ((r : ℝ)⁻¹) • (∑ k : Fin r, g (resp k))

/--
`Xbar i` is the paper’s matrix `X̄_i ∈ ℝ^{m×p}` of average embedded responses for model `i`.

Input `resp` should be thought of as: for each model `i` and query `j`, we have `r` responses
`resp i j : Fin r → X`. (In the paper these are i.i.d. draws from the model distribution.) -/
def Xbar {n m p r : ℕ}
    (g : X → Vec p)
    (resp : Fin n → Fin m → Fin r → X) :
    Fin n → Mat m p :=
  fun i => fun j k => (avgEmbed (X := X) g (resp i j)) k

/-- Paper distance matrix `D_{ii'}` based on Frobenius distances of `X̄_i`. -/
def Dmat {n m p r : ℕ}
    (g : X → Vec p)
    (resp : Fin n → Fin m → Fin r → X) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i i' => frobDist (Xbar (X := X) g resp i) (Xbar (X := X) g resp i')

/-- Paper stress objective from Eq. (1). -/
def dkpsStress {n d : ℕ} (D : Matrix (Fin n) (Fin n) ℝ) (z : Fin n → Vec d) : ℝ :=
  ∑ i : Fin n, ∑ i' : Fin n, (‖z i - z i'‖ - D i i') ^ (2 : ℕ)

/--
`IsDKPS D ψHat` means that `ψHat` minimizes the stress objective (Eq. (1)).

This is the Lean predicate corresponding to:
`(ψ̂₁,…,ψ̂ₙ) ∈ argmin_{z₁,…,zₙ} ∑_{i,i'} (‖z_i - z_{i'}‖ - D_{ii'})²`.
-/
def IsDKPS {n d : ℕ} (D : Matrix (Fin n) (Fin n) ℝ) (ψHat : Fin n → Vec d) : Prop :=
  ∀ z : Fin n → Vec d, dkpsStress D ψHat ≤ dkpsStress D z

/-!
### Perspective maps `ψ(Q)` and `ψ̂(Q)`

The paper uses:
- `ψ(Q)`  : the (unknown) *true* DKPS representation in the perspective space induced by `Q`
- `ψ̂(Q)` : the *estimated* DKPS representation computed from cached responses (Eq. (1))

In the rest of the file (Theorem 2), we treat these maps abstractly as functions
`ψ : 𝓕 → ℝ^d` and `ψ̂ : 𝓕 → ℝ^d`.  Theorem 1 (cited in the paper) provides the key
high-probability concentration guarantee `‖ψ̂(f) - ψ(f)‖₂ ≤ c(n,m,r,d)`.

We keep the DKPS definition above so the formalization matches the paper’s Section 2 exactly,
but we do not re-prove existence/uniqueness of DKPS minimizers here.
-/

--------------------------------------------------------------------------------
/-!
## Section 3 — Risk, MSE, and query-efficiency (Eq. (2))

Paper (Section 3) defines query-efficiency in terms of the population risk
`E_{f ∼ P_f}[ ℓ(h(f), y(f,Q*)) ]`.  Eq. (2) is the eventual risk domination inequality.

We formalize:
- population risk `Risk`
- mean squared error `MSE` (squared loss)
- `Q`-query-efficient (fixed subset `Qsub`)
- `m`-query-efficient (for all `Qsub` with `|Qsub|=m`, each with its own `N_Q`)
- “query-efficient” (for all `m < M`)

These match the paper’s definitions, but expressed with `Finset` and `≤` on risks.
-/

namespace QueryEfficiency

variable {Q : Type u} [DecidableEq Q]
variable {X : Type v} [MeasurableSpace X]
-- We treat the measurable structure on the model space `Model Q X` as an explicit assumption.
-- The paper works with a probability distribution `P_f` on the (typically huge) model space `𝓕`.
variable [MeasurableSpace (Model Q X)]

/-- Population risk `E_f[ ℓ(h(f), y(f)) ]` under a model distribution `P_f`. -/
noncomputable def Risk
    (Pf : MeasureTheory.Measure (Model Q X)) [MeasureTheory.IsProbabilityMeasure Pf]
    (ℓ : ℝ → ℝ → ℝ)
    (y h : Model Q X → ℝ) : ℝ :=
  ∫ f, ℓ (h f) (y f) ∂ Pf

/-- Squared loss (used for MSE). -/
def sqLoss (a b : ℝ) : ℝ := (a - b) ^ (2 : ℕ)

/-- Mean squared error `E_f[(ŷ(f) - y(f))²]` under `P_f`. -/
noncomputable def MSE
    (Pf : MeasureTheory.Measure (Model Q X)) [MeasureTheory.IsProbabilityMeasure Pf]
    (y yHat : Model Q X → ℝ) : ℝ :=
  Risk (Q := Q) (X := X) Pf sqLoss y yHat

/--
Paper (Def. 1): for a *fixed* `Qsub ⊆ Q*`, a sequence `(hₙ)` is `Qsub` query-efficient
relative to `(h'ₙ)` if there exists `N` such that Eq. (2) holds for all `n > N`.

We include the side condition `Qsub ⊆ Qstar` explicitly (paper always has `Qsub ⊆ Q*`). -/
def QQueryEfficient
    (Qstar : Finset Q) (Qsub : Finset Q) (hQsub : Qsub ⊆ Qstar)
    (Pf : MeasureTheory.Measure (Model Q X)) [MeasureTheory.IsProbabilityMeasure Pf]
    (ℓ : ℝ → ℝ → ℝ)
    (y : Model Q X → ℝ)
    (h h' : ℕ → Model Q X → ℝ) : Prop :=
  ∃ N : ℕ, ∀ n > N,
    Risk (Q := Q) (X := X) Pf ℓ y (h n) ≤ Risk (Q := Q) (X := X) Pf ℓ y (h' n)

/--
Paper (Def. 2): `m`-query-efficiency.

For each `Qsub ⊆ Q*` with `|Qsub| = m`, there exists a (possibly `Qsub`-dependent) `N_Qsub`
such that Eq. (2) holds for all `n > N_Qsub`. -/
def mQueryEfficient
    (Qstar : Finset Q) (m : ℕ)
    (Pf : MeasureTheory.Measure (Model Q X)) [MeasureTheory.IsProbabilityMeasure Pf]
    (ℓ : ℝ → ℝ → ℝ)
    (y : Model Q X → ℝ)
    (h h' : Finset Q → ℕ → Model Q X → ℝ) : Prop :=
  ∀ Qsub : Finset Q, Qsub ⊆ Qstar → Qsub.card = m →
    ∃ N : ℕ, ∀ n > N,
      Risk (Q := Q) (X := X) Pf ℓ y (h Qsub n) ≤ Risk (Q := Q) (X := X) Pf ℓ y (h' Qsub n)

/--
Paper (Def. 3): query-efficiency across all query budgets `m < M` where `M = |Q*|`.

We follow the paper’s quantifier structure: for all `m < |Q*|`, the sequence is `m`-query-efficient.
(Any extra “`∃ N(m)`” phrasing in the text is logically redundant given Def. 2, so we do not
add a uniformity requirement over `Qsub` here.) -/
def QueryEfficient
    (Qstar : Finset Q)
    (Pf : MeasureTheory.Measure (Model Q X)) [MeasureTheory.IsProbabilityMeasure Pf]
    (ℓ : ℝ → ℝ → ℝ)
    (y : Model Q X → ℝ)
    (h h' : Finset Q → ℕ → Model Q X → ℝ) : Prop :=
  ∀ m : ℕ, m < Qstar.card →
    mQueryEfficient (Q := Q) (X := X) Qstar m Pf ℓ y h h'

end QueryEfficiency

--------------------------------------------------------------------------------
/-!
## Section 3 — Nearest-neighbor regression in perspective space

Paper (Section 3) defines, for a fixed query budget `m` and fixed subset `Qsub ⊆ Q*`,
the DKPS+NN estimator

`ŷ_NN := hₙ^{(m)}(ψ̂) = (∑ 1{‖ψ̂_i - ψ̂‖ = δ*} y_i) / (∑ 1{‖ψ̂_i - ψ̂‖ = δ*})`

where `δ* = min_i ‖ψ̂_i - ψ̂‖` and ties are averaged.

We formalize exactly this formula.

Implementation note:
- in the paper the norm in the indicator is written as `‖·‖_F` (Frobenius).
  For vectors in `ℝ^d`, Frobenius norm coincides with the Euclidean 2-norm, and Lean’s
  `‖·‖` on `Vec d` is exactly this 2-norm.
-/

namespace NearestNeighbor

variable {d : ℕ}

/-- Predicate: `i` is an argmin of a real-valued function over `Fin n`. -/
def IsArgmin {n : ℕ} (f : Fin n → ℝ) (i : Fin n) : Prop :=
  ∀ j, f i ≤ f j

/-- Existence of an argmin over a finite type. -/
lemma exists_argmin {n : ℕ} (hn : 0 < n) (f : Fin n → ℝ) : ∃ i, IsArgmin f i := by
  classical
  -- Same proof pattern as in your earlier working file:
  -- minimize over the finite set `Finset.univ : Finset (Fin n)`.
  -- `Fin n` is nonempty as soon as `0 < n` (witness `0`).
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have h_nonempty : (Finset.univ : Finset (Fin n)).Nonempty := Finset.univ_nonempty
  obtain ⟨i, _, hi⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin n)) f h_nonempty
  refine ⟨i, ?_⟩
  intro j
  exact hi j (Finset.mem_univ j)

/-- Choose a canonical argmin index (noncomputable, classical choice). -/
noncomputable def nnIndex {n : ℕ} (hn : 0 < n) (f : Fin n → ℝ) : Fin n :=
  Classical.choose (exists_argmin (n := n) hn f)

lemma nnIndex_isArgmin {n : ℕ} (hn : 0 < n) (f : Fin n → ℝ) :
    IsArgmin f (nnIndex (n := n) hn f) :=
  Classical.choose_spec (exists_argmin (n := n) hn f)

/-- Paper’s `δ* = min_i ‖ψ̂_i - ψ̂‖`. -/
noncomputable def deltaStar {n : ℕ} (hn : 0 < n)
    (ψHat_ref : Fin n → Vec d) (ψHat_target : Vec d) : ℝ :=
  ‖ψHat_ref (nnIndex (n := n) hn (fun i => ‖ψHat_ref i - ψHat_target‖)) - ψHat_target‖

/--
Set of all nearest neighbors (all minimizers, i.e. all indices achieving `δ*`).

Paper corresponds to `{ i : {1,…,n} | ‖ψ̂_i - ψ̂‖ = δ* }`. -/
noncomputable def nnTieSet {n : ℕ} (hn : 0 < n)
    (ψHat_ref : Fin n → Vec d) (ψHat_target : Vec d) : Finset (Fin n) :=
  let δ := deltaStar (d := d) (n := n) hn ψHat_ref ψHat_target;
  Finset.univ.filter (fun i => ‖ψHat_ref i - ψHat_target‖ = δ)

/-- The tie set is nonempty (it contains `nnIndex`). -/
lemma nnTieSet_nonempty {n : ℕ} (hn : 0 < n)
    (ψHat_ref : Fin n → Vec d) (ψHat_target : Vec d) :
    (nnTieSet (d := d) (n := n) hn ψHat_ref ψHat_target).Nonempty := by
  classical
  -- The tie set contains the chosen minimizer index.
  refine ⟨nnIndex (n := n) hn (fun i => ‖ψHat_ref i - ψHat_target‖), ?_⟩
  -- Unfold and discharge by simp: membership is exactly the defining equality of `δ*`.
  simp [nnTieSet, deltaStar]

/-- Any index in the tie set is also an argmin. -/
lemma nnTieSet_isArgmin {n : ℕ} (hn : 0 < n)
    (ψHat_ref : Fin n → Vec d) (ψHat_target : Vec d) :
    ∀ i, i ∈ nnTieSet (d := d) (n := n) hn ψHat_ref ψHat_target →
      IsArgmin (fun j => ‖ψHat_ref j - ψHat_target‖) i := by
  classical
  intro i hi
  -- Let `i0` be the chosen minimizer; use equality of distances to transfer argmin-ness.
  let i0 : Fin n := nnIndex (n := n) hn (fun j => ‖ψHat_ref j - ψHat_target‖)
  have hi0 : IsArgmin (fun j => ‖ψHat_ref j - ψHat_target‖) i0 :=
    nnIndex_isArgmin (n := n) hn (fun j => ‖ψHat_ref j - ψHat_target‖)
  have hEq : ‖ψHat_ref i - ψHat_target‖ = ‖ψHat_ref i0 - ψHat_target‖ := by
    -- membership in filter means distance equals `δ*`, which is distance of `i0`
    unfold nnTieSet at hi
    -- `simp` gives the equality to `δ*`; then unfold `deltaStar`.
    have : ‖ψHat_ref i - ψHat_target‖ = deltaStar (d := d) (n := n) hn ψHat_ref ψHat_target := by
      simpa using (Finset.mem_filter.1 hi).2
    -- `δ*` is defined as distance of `i0`
    simpa [deltaStar, i0] using this
  intro j
  -- `f i = f i0 ≤ f j`
  have : ‖ψHat_ref i0 - ψHat_target‖ ≤ ‖ψHat_ref j - ψHat_target‖ := hi0 j
  simpa [hEq] using this

/--
Paper’s nearest-neighbor regression estimator `ŷ_NN`.

This is exactly the paper formula:
- compute `δ* = min_i ‖ψ̂_i - ψ̂‖`
- average the `y_i` over all ties achieving `δ*`.

(If `n=0`, the paper setting does not apply; we require `hn : 0 < n`.) -/
noncomputable def yHatNN {n : ℕ} (hn : 0 < n)
    (ψHat_ref : Fin n → Vec d) (ψHat_target : Vec d)
    (y_ref : Fin n → ℝ) : ℝ :=
  let S : Finset (Fin n) := nnTieSet (d := d) (n := n) hn ψHat_ref ψHat_target;
  (S.sum y_ref) / (S.card : ℝ)

end NearestNeighbor

--------------------------------------------------------------------------------
/-!
## Assumptions 1–2 (paper) and Theorem 2 proof skeleton

We now formalize the assumptions *as stated in the paper*:

### Assumption 1 (Lipschitz score function)
For a fixed query subset `Qsub ⊆ Q*`, the full-benchmark score function `y(·,Q*)`
is `γ`-Lipschitz with respect to the *true* perspective map `ψ(Qsub)`:
`|y(f,Q*) - y(f',Q*)| ≤ γ ‖ψ(Qsub)(f) - ψ(Qsub)(f')‖₂`.

### Assumption 2 (model distribution support)
The paper states: “`P_f` has non-zero measure on all compact subsets of `𝓕`.”
They immediately give an equivalent ball condition:
for every `f` and `δ>0` there exists `ε>0` with `P_f(B_δ(f)) ≥ ε`.

In Lean, we encode the ball form (it is what the proof uses).

### Theorem 2
We keep the theorem split into:
- Part 1: accuracy / small MSE with high probability
- Part 2: query-efficiency relative to the subset-score baseline

The proof follows the paper’s numbered steps; we reuse the algebraic lemmas from
your existing working files and isolate the genuinely analytic “paper citation” steps.
-/

section Assumptions_And_Theorems

variable {Q : Type u} [DecidableEq Q]
variable {X : Type v} [MeasurableSpace X]
variable {d : ℕ}
variable [MeasurableSpace (Model Q X)]


/-- Assumption 1 (paper): Lipschitzness of the full-benchmark score w.r.t. the true perspective map. -/
def LipschitzScore (γ : ℝ) (ψ : Model Q X → Vec d) (y : Model Q X → ℝ) : Prop :=
  ∀ f f' : Model Q X, |y f - y f'| ≤ γ * ‖ψ f - ψ f'‖

/-
Assumption 2 (paper): positive mass in every ball.

This is the “equivalently” statement in the paper:
for any target model `f` and radius `δ>0`, there exists `ε>0` s.t.
`P_f(B_δ(f)) ≥ ε`, where `B_δ(f) = {f' : d(f',f) < δ}`.

We keep the metric abstract as `dist` on `Model Q X`. -/
/--
Assumption 2 (paper): positive mass in every ball.

This is the “equivalently” statement in the paper:
for any target model `f` and radius `δ>0`, there exists `ε>0` with `P_f(B_δ(f)) ≥ ε`.

In Lean we encode this using `Metric.ball` and an abstract metric on the model space.
-/
def ModelSupportNontrivial
    (Pf : MeasureTheory.Measure (Model Q X)) [MeasureTheory.IsProbabilityMeasure Pf]
    [PseudoMetricSpace (Model Q X)] : Prop :=
  ∀ (f : Model Q X) (δ : ℝ), 0 < δ →
    ∃ ε : ENNReal, 0 < ε ∧ Pf (Metric.ball f δ) ≥ ε

/-!
### “With high probability”
The paper uses the standard asymptotic meaning: probability → 1 as sample size grows.
We reuse the (convenient) encoding from your existing files: `HighProbAtTop`.
-/

def HighProbAtTop {Ω : Type} [MeasurableSpace Ω]
    (μ : ℕ → MeasureTheory.Measure Ω) (hμ : ∀ n, MeasureTheory.IsProbabilityMeasure (μ n))
    (E : ℕ → Set Ω) : Prop :=
  ∀ δ : ENNReal, 0 < δ → ∃ N : ℕ, ∀ n > N, (μ n) (E n) ≥ 1 - δ

/-!
## Theorem 2: algebraic / geometric proof steps

The next lemmas are the “deterministic” parts of the paper’s proof:
they take as hypotheses the concentration bound `‖ψ̂ - ψ‖ ≤ c`
and the coverage event “some reference model is within ρ of the target in true ψ-space”.
-/

section Theorem2_Proof_Steps


variable {Ω : Type} [MeasurableSpace Ω]

/-- Step 1 (paper): Lipschitz transfers score error to true ψ-distance. -/
lemma step1_lipschitz_bound
    (γ : ℝ) (ψ : Model Q X → Vec d) (y : Model Q X → ℝ)
    (hLip : LipschitzScore (Q := Q) (X := X) γ ψ y)
    (f f' : Model Q X) :
    |y f - y f'| ≤ γ * ‖ψ f - ψ f'‖ :=
  hLip f f'

/--
Step 2 (paper): triangle inequality bound on true ψ-distance in terms of estimated ψ̂-distance
and the concentration error `c`.

Paper writes:
`‖ψ* - ψ‖ ≤ ‖ψ* - ψ̂*‖ + ‖ψ̂* - ψ̂‖ + ‖ψ̂ - ψ‖`
and uses the concentration bound to replace the first and third terms by `c`. -/
lemma step2_triangle_inequality
    {n : ℕ} (ψ : Fin n → Vec d) (ψHat : Fin n → Vec d)
    (ψ_target ψHat_target : Vec d)
    (i_star : Fin n)
    (c : ℝ)
    (h_conc_ref : ∀ i, ‖ψHat i - ψ i‖ ≤ c)
    (h_conc_target : ‖ψHat_target - ψ_target‖ ≤ c) :
    ‖ψ i_star - ψ_target‖ ≤ 2 * c + ‖ψHat i_star - ψHat_target‖ := by
  have h_ref : ‖ψ i_star - ψHat i_star‖ ≤ c := by
    simpa [norm_sub_rev] using (h_conc_ref i_star)

  have h_tri1 :
      ‖ψ i_star - ψ_target‖ ≤ ‖ψ i_star - ψHat i_star‖ + ‖ψHat i_star - ψ_target‖ := by
    simpa using (norm_sub_le_triangle (ψ i_star) (ψHat i_star) ψ_target)

  have h_tri2 :
      ‖ψHat i_star - ψ_target‖ ≤ ‖ψHat i_star - ψHat_target‖ + ‖ψHat_target - ψ_target‖ := by
    simpa using (norm_sub_le_triangle (ψHat i_star) ψHat_target ψ_target)

  have h_main :
      ‖ψ i_star - ψ_target‖ ≤ c + (‖ψHat i_star - ψHat_target‖ + ‖ψHat_target - ψ_target‖) := by
    have h_tri1' :
        ‖ψ i_star - ψ_target‖ ≤ ‖ψ i_star - ψHat i_star‖ +
          (‖ψHat i_star - ψHat_target‖ + ‖ψHat_target - ψ_target‖) :=
      le_trans h_tri1 (add_le_add_left h_tri2 ‖ψ i_star - ψHat i_star‖)
    have :
        ‖ψ i_star - ψHat i_star‖ +
            (‖ψHat i_star - ψHat_target‖ + ‖ψHat_target - ψ_target‖)
          ≤ c + (‖ψHat i_star - ψHat_target‖ + ‖ψHat_target - ψ_target‖) := by
      exact add_le_add_right h_ref _
    exact le_trans h_tri1' (by
      simpa [add_assoc, add_left_comm, add_comm] using this)

  have h_target_le : ‖ψHat_target - ψ_target‖ ≤ c := h_conc_target
  have h_inside :
      ‖ψHat i_star - ψHat_target‖ + ‖ψHat_target - ψ_target‖ ≤
        ‖ψHat i_star - ψHat_target‖ + c :=
    add_le_add_left h_target_le _

  calc
    ‖ψ i_star - ψ_target‖
        ≤ c + (‖ψHat i_star - ψHat_target‖ + ‖ψHat_target - ψ_target‖) := h_main
    _ ≤ c + (‖ψHat i_star - ψHat_target‖ + c) := by
          exact add_le_add_left h_inside c
    _ = 2 * c + ‖ψHat i_star - ψHat_target‖ := by ring

/--
Step 3 (paper): if `i*` is an argmin in ψ̂-space, then its ψ̂-distance is bounded by any reference.

This is the “nearest neighbor” property used to compare `δ*` to any candidate `j`. -/
lemma step3_argmin_property
    {n : ℕ} (ψHat : Fin n → Vec d) (ψHat_target : Vec d)
    (i_star : Fin n)
    (h_i_star : NearestNeighbor.IsArgmin (fun i => ‖ψHat i - ψHat_target‖) i_star) :
    ∀ j : Fin n, ‖ψHat i_star - ψHat_target‖ ≤ ‖ψHat j - ψHat_target‖ :=
  h_i_star

/--
Step 4 (paper): combine Step 2 and Step 3 with a “coverage” witness `j*` satisfying
`‖ψ_j* - ψ_target‖ ≤ ρ` to conclude

`‖ψ_i* - ψ_target‖ ≤ ρ + 4c`.

This corresponds to the inequality right before squaring in the paper’s proof.
-/
lemma step4_support_bound
    {n : ℕ}
    (ψ : Fin n → Vec d) (ψHat : Fin n → Vec d)
    (ψ_target ψHat_target : Vec d)
    (i_star : Fin n)
    (h_i_star : NearestNeighbor.IsArgmin (fun i => ‖ψHat i - ψHat_target‖) i_star)
    (c ρ : ℝ)
    (h_conc_ref : ∀ i, ‖ψHat i - ψ i‖ ≤ c)
    (h_conc_target : ‖ψHat_target - ψ_target‖ ≤ c)
    (h_supp : ∃ j : Fin n, ‖ψ j - ψ_target‖ ≤ ρ) :
    ‖ψ i_star - ψ_target‖ ≤ ρ + 4 * c := by
  classical
  rcases h_supp with ⟨j_star, hj_star⟩

  have h_step2 :
      ‖ψ i_star - ψ_target‖ ≤ 2 * c + ‖ψHat i_star - ψHat_target‖ :=
    step2_triangle_inequality (d := d) (n := n)
      ψ ψHat ψ_target ψHat_target i_star c h_conc_ref h_conc_target

  have h_arg : ‖ψHat i_star - ψHat_target‖ ≤ ‖ψHat j_star - ψHat_target‖ :=
    h_i_star j_star

  have h_conc_j : ‖ψHat j_star - ψ j_star‖ ≤ c := h_conc_ref j_star

  have h_jtri1 :
      ‖ψHat j_star - ψHat_target‖ ≤ ‖ψHat j_star - ψ j_star‖ + ‖ψ j_star - ψHat_target‖ := by
    simpa using (norm_sub_le_triangle (ψHat j_star) (ψ j_star) ψHat_target)

  have h_jtri2 :
      ‖ψ j_star - ψHat_target‖ ≤ ‖ψ j_star - ψ_target‖ + ‖ψHat_target - ψ_target‖ := by
    have h' :
        ‖ψ j_star - ψHat_target‖ ≤ ‖ψ j_star - ψ_target‖ + ‖ψ_target - ψHat_target‖ := by
      simpa using (norm_sub_le_triangle (ψ j_star) ψ_target ψHat_target)
    have hEq : ‖ψ_target - ψHat_target‖ = ‖ψHat_target - ψ_target‖ := by
      simpa using (norm_sub_rev ψHat_target ψ_target).symm
    simpa [hEq] using h'

  have h_jtri2' : ‖ψ j_star - ψHat_target‖ ≤ ρ + c := by
    exact le_trans h_jtri2 (add_le_add hj_star h_conc_target)

  have h_j_raw : ‖ψHat j_star - ψHat_target‖ ≤ c + (ρ + c) := by
    have := le_trans h_jtri1 (add_le_add h_conc_j h_jtri2')
    simpa [add_assoc, add_left_comm, add_comm] using this

  have h_j : ‖ψHat j_star - ψHat_target‖ ≤ ρ + 2 * c := by
    have hEq : c + (ρ + c) = ρ + 2 * c := by ring
    simpa [hEq] using h_j_raw

  have h_distHat : ‖ψHat i_star - ψHat_target‖ ≤ ρ + 2 * c :=
    le_trans h_arg h_j

  calc
    ‖ψ i_star - ψ_target‖
        ≤ 2 * c + ‖ψHat i_star - ψHat_target‖ := h_step2
    _ ≤ 2 * c + (ρ + 2 * c) := add_le_add_left h_distHat (2 * c)
    _ = ρ + 4 * c := by ring

/--
Step 5 (paper): pointwise score error bound for an argmin index `i*`:

`|y_i* - y| ≤ γ (ρ + 4c)`.

This is the main inequality used in the MSE bound.
-/
lemma step5_pointwise_error
    {n : ℕ}
    (ψ : Fin n → Vec d) (ψHat : Fin n → Vec d)
    (ψ_target ψHat_target : Vec d)
    (i_star : Fin n)
    (h_i_star : NearestNeighbor.IsArgmin (fun i => ‖ψHat i - ψHat_target‖) i_star)
    (c ρ γ : ℝ)
    (h_conc_ref : ∀ i, ‖ψHat i - ψ i‖ ≤ c)
    (h_conc_target : ‖ψHat_target - ψ_target‖ ≤ c)
    (h_supp : ∃ j : Fin n, ‖ψ j - ψ_target‖ ≤ ρ)
    (y_ref : Fin n → ℝ) (y_target : ℝ)
    (h_lip : ∀ i, |y_ref i - y_target| ≤ γ * ‖ψ i - ψ_target‖)
    (h_gamma_nonneg : 0 ≤ γ)
    (h_rho_nonneg : 0 ≤ ρ)
    (h_c_nonneg : 0 ≤ c) :
    |y_ref i_star - y_target| ≤ γ * (ρ + 4 * c) := by
  calc
    |y_ref i_star - y_target|
        ≤ γ * ‖ψ i_star - ψ_target‖ := h_lip i_star
    _ ≤ γ * (ρ + 4 * c) := by
      -- Multiply the Step 4 bound by `γ ≥ 0`.
      have h_bound : ‖ψ i_star - ψ_target‖ ≤ ρ + 4 * c :=
        step4_support_bound (d := d) (n := n)
          ψ ψHat ψ_target ψHat_target i_star h_i_star c ρ
          h_conc_ref h_conc_target h_supp
      exact mul_le_mul_of_nonneg_left h_bound h_gamma_nonneg

/-!
### From pointwise error to the paper’s `ŷ_NN` (tie-average)

The paper’s estimator averages `y_i` across all ties at the minimum distance `δ*`.
To lift Step 5 to the averaged estimator, we need the elementary fact:
if every tie element satisfies `|y_i - y| ≤ B`, then the average also satisfies `|avg - y| ≤ B`.

We isolate this as a lemma.  It is purely algebraic and can be discharged later.
-/

/-- If each element is within `B` of `y`, then their average is also within `B` of `y`. -/
lemma abs_avg_sub_le_of_forall_abs_sub_le
    {α : Type} [DecidableEq α]
    (S : Finset α) (hS : S.Nonempty)
    (y_ref : α → ℝ) (y : ℝ) (B : ℝ)
    (hB : ∀ i ∈ S, |y_ref i - y| ≤ B) :
    |(∑ i in S, y_ref i) / (S.card : ℝ) - y| ≤ B := by
  classical
  -- This is standard: rewrite `avg - y` as the average of `(y_ref i - y)`,
  -- apply triangle inequality, then use `hB`.
  -- We keep it as a placeholder to keep the main theorem readable.
  sorry

end Theorem2_Proof_Steps

/-!
## Theorem 2 (paper), formal statement

We keep the same “random experiment” interface as your working file:

- `Ω` is the probability space for randomness in the DKPS construction (sampling reference models,
  sampling cached responses, etc.).
- `μ n` is the distribution of the experiment at sample size `n`.
- `ψ`    is the true perspective map (for the fixed `Qsub`)
- `ψHat` is the estimated perspective map at sample size `n` (random, depends on `ω`)
- `f_ref n ω i` enumerates the `n` reference models in the cache
- `hNN n ω f` is the DKPS+NN estimator output for target model `f`.

### Part 1 (accuracy)
For every `ε>0`, with high probability as `n→∞`, the MSE of `hNN` is ≤ ε.

### Part 2 (query-efficiency)
If the baseline (subset-score) estimator has strictly positive MSE, then with high probability,
eventually `MSE(hNN) ≤ MSE(baseline)`.  For squared loss, this is exactly Eq. (2) domination.
-/

section Theorem2

variable {Ω : Type} [MeasurableSpace Ω]
variable [MeasurableSpace (Model Q X)]


open QueryEfficiency
open NearestNeighbor

/-- Theorem 2, Part 1 (paper): accuracy of `ŷ_NN` (high-probability small MSE). -/
theorem Theorem2_part1
  (Pf : MeasureTheory.Measure (Model Q X)) [MeasureTheory.IsProbabilityMeasure Pf]
  (μ : ℕ → MeasureTheory.Measure Ω) (hμ : ∀ n, MeasureTheory.IsProbabilityMeasure (μ n))
  (ψ : Model Q X → Vec d)
  (ψHat : ℕ → Ω → Model Q X → Vec d)
  (f_ref : ∀ n, Ω → Fin n → Model Q X)
  (Qstar : Finset Q)
  (score : Model Q X → Finset Q → UnitInterval)
  (γ : ℝ)
  (h_lip : LipschitzScore (Q := Q) (X := X) (d := d) γ ψ (fun f => (score f Qstar : ℝ)))
  (h_gamma_pos : 0 < γ)
  (c : ℕ → ℝ) (h_c_tendsto : Filter.Tendsto c Filter.atTop (nhds (0 : ℝ)))
  (h_c_nonneg : ∀ n, 0 ≤ c n)
  /- Theorem 1 (paper citation): concentration of DKPS estimates -/
  (h_conc : HighProbAtTop (μ := μ) (hμ := hμ) (fun n => {ω | ∀ f, ‖ψHat n ω f - ψ f‖ ≤ c n}))
  (h_conc_meas : ∀ n, MeasurableSet {ω | ∀ f, ‖ψHat n ω f - ψ f‖ ≤ c n})
  /- Assumption 2 ⇒ a coverage property for the reference set in ψ-space -/
  (h_cover : ∀ ρ > 0, HighProbAtTop (μ := μ) (hμ := hμ) (fun n => {ω | ∀ f, ∃ i, ‖ψ (f_ref n ω i) - ψ f‖ ≤ ρ}))
  (h_cover_meas : ∀ ρ > 0, ∀ n, MeasurableSet {ω | ∀ f, ∃ i, ‖ψ (f_ref n ω i) - ψ f‖ ≤ ρ})
  /- Definition of the estimator as the paper’s `yHatNN` on estimated perspectives -/
  (hNN : ℕ → Ω → Model Q X → ℝ)
  (h_hNN_def :
    ∀ n ω f, (hn : 0 < n) →
      hNN n ω f =
        yHatNN (d := d) (n := n) hn
          (ψHat_ref := fun i => ψHat n ω (f_ref n ω i))
          (ψHat_target := ψHat n ω f)
          (y_ref := fun i => (score (f_ref n ω i) Qstar : ℝ))) :
  ∀ ε : ℝ, 0 < ε →
    HighProbAtTop (μ := μ) (hμ := hμ)
      (fun n => {ω : Ω |
        QueryEfficiency.MSE (Q := Q) (X := X) Pf (fun f => (score f Qstar : ℝ)) (fun f => hNN n ω f) ≤ ε
      }) := by
  intro ε hε
  /-
  This theorem is exactly the paper’s Part 1 statement.
  The proof follows the paper’s steps:
  1. Lipschitz → score error ≤ γ‖ψ_i* - ψ_target‖
  2. Triangle inequality → ‖ψ_i* - ψ_target‖ ≤ 2c + ‖ψ̂_i* - ψ̂_target‖
  3. Argmin → replace the ψ̂-distance by one of the covered reference models
  4. Use coverage `ρ` and concentration `c` → ‖ψ_i* - ψ_target‖ ≤ ρ + 4c
  5. Square and integrate → MSE ≤ (γ(ρ+4c))²
  6. Choose `ρ` and `c` (via `c n → 0` and coverage) to make the RHS ≤ ε, with high prob.

  Your earlier `dkps-aristotle-...` file already contains most of the deterministic algebra.
  The remaining `sorry`'s are exactly where we need (a) the concentration theorem and
  (b) the probabilistic coverage lemma derived from Assumption 2.
  -/
  sorry

/-- Theorem 2, Part 2 (paper): query-efficiency relative to a baseline with positive MSE. -/
theorem Theorem2_part2
  (Pf : MeasureTheory.Measure (Model Q X)) [MeasureTheory.IsProbabilityMeasure Pf]
  (μ : ℕ → MeasureTheory.Measure Ω) (hμ : ∀ n, MeasureTheory.IsProbabilityMeasure (μ n))
  (ψ : Model Q X → Vec d)
  (ψHat : ℕ → Ω → Model Q X → Vec d)
  (f_ref : ∀ n, Ω → Fin n → Model Q X)
  (Qstar : Finset Q)
  (score : Model Q X → Finset Q → UnitInterval)
  (γ : ℝ)
  (h_lip : LipschitzScore (Q := Q) (X := X) (d := d) γ ψ (fun f => (score f Qstar : ℝ)))
  (h_gamma_pos : 0 < γ)
  (c : ℕ → ℝ) (h_c_tendsto : Filter.Tendsto c Filter.atTop (nhds (0 : ℝ)))
  (h_c_nonneg : ∀ n, 0 ≤ c n)
  (h_conc : HighProbAtTop (μ := μ) (hμ := hμ) (fun n => {ω | ∀ f, ‖ψHat n ω f - ψ f‖ ≤ c n}))
  (h_conc_meas : ∀ n, MeasurableSet {ω | ∀ f, ‖ψHat n ω f - ψ f‖ ≤ c n})
  (h_cover : ∀ ρ > 0, HighProbAtTop (μ := μ) (hμ := hμ) (fun n => {ω | ∀ f, ∃ i, ‖ψ (f_ref n ω i) - ψ f‖ ≤ ρ}))
  (h_cover_meas : ∀ ρ > 0, ∀ n, MeasurableSet {ω | ∀ f, ∃ i, ‖ψ (f_ref n ω i) - ψ f‖ ≤ ρ})
  (hNN hQ : ℕ → Ω → Model Q X → ℝ)
  (h_hNN_def :
    ∀ n ω f, (hn : 0 < n) →
      hNN n ω f =
        yHatNN (d := d) (n := n) hn
          (ψHat_ref := fun i => ψHat n ω (f_ref n ω i))
          (ψHat_target := ψHat n ω f)
          (y_ref := fun i => (score (f_ref n ω i) Qstar : ℝ)))
  (hQ_pos : ∃ c_base : ℝ, 0 < c_base ∧ ∃ N : ℕ, ∀ n > N, ∀ ω : Ω,
      c_base ≤ QueryEfficiency.MSE (Q := Q) (X := X) Pf (fun f => (score f Qstar : ℝ)) (fun f => hQ n ω f)) :
  HighProbAtTop (μ := μ) (hμ := hμ)
    (fun n => {ω : Ω |
      QueryEfficiency.MSE (Q := Q) (X := X) Pf (fun f => (score f Qstar : ℝ)) (fun f => hNN n ω f)
        ≤ QueryEfficiency.MSE (Q := Q) (X := X) Pf (fun f => (score f Qstar : ℝ)) (fun f => hQ n ω f)
    }) := by
  classical
  -- Exactly the paper’s “Part 2 follows from Part 1 by choosing ε smaller than the baseline MSE”.
  rcases hQ_pos with ⟨c_base, hc_base_pos, N0, hN0⟩
  -- Apply Part 1 with ε = c_base / 2.
  have hε_pos : (0 : ℝ) < c_base / 2 := by linarith
  have hPart1 :=
    Theorem2_part1 (Q := Q) (X := X) (d := d) (Ω := Ω)
      (Pf := Pf) (μ := μ) (hμ := hμ)
      (ψ := ψ) (ψHat := ψHat) (f_ref := f_ref)
      (Qstar := Qstar) (score := score)
      (γ := γ) (h_lip := h_lip) (h_gamma_pos := h_gamma_pos)
      (c := c) (h_c_tendsto := h_c_tendsto) (h_c_nonneg := h_c_nonneg)
      (h_conc := h_conc) (h_conc_meas := h_conc_meas)
      (h_cover := h_cover) (h_cover_meas := h_cover_meas)
      (hNN := hNN) (h_hNN_def := h_hNN_def)
      (ε := c_base / 2) hε_pos
  -- Unfold the `HighProbAtTop` definition and transfer the small-MSE event into domination.
  intro δ hδ_pos
  rcases hPart1 δ hδ_pos with ⟨N1, hN1⟩
  refine ⟨max N0 N1, ?_⟩
  intro n hn
  have hn0 : n > N0 := lt_of_le_of_lt (le_max_left _ _) hn
  have hn1 : n > N1 := lt_of_le_of_lt (le_max_right _ _) hn
  -- If `MSE(hNN) ≤ c_base/2` and `MSE(hQ) ≥ c_base` then `MSE(hNN) ≤ MSE(hQ)`.
  have hsubset :
      {ω : Ω |
          QueryEfficiency.MSE (Q := Q) (X := X) Pf (fun f => (score f Qstar : ℝ)) (fun f => hNN n ω f) ≤ c_base / 2}
        ⊆
      {ω : Ω |
          QueryEfficiency.MSE (Q := Q) (X := X) Pf (fun f => (score f Qstar : ℝ)) (fun f => hNN n ω f)
            ≤ QueryEfficiency.MSE (Q := Q) (X := X) Pf (fun f => (score f Qstar : ℝ)) (fun f => hQ n ω f)} := by
    intro ω hω
    have hQlower : c_base ≤ QueryEfficiency.MSE (Q := Q) (X := X) Pf (fun f => (score f Qstar : ℝ)) (fun f => hQ n ω f) :=
      hN0 n hn0 ω
    have hc_half : (c_base / 2) ≤ c_base := by linarith [hc_base_pos.le]
    have hNN_le_cbase :
        QueryEfficiency.MSE (Q := Q) (X := X) Pf (fun f => (score f Qstar : ℝ)) (fun f => hNN n ω f) ≤ c_base :=
      le_trans hω hc_half
    exact le_trans hNN_le_cbase hQlower

  -- Use monotonicity of measure: if `A ⊆ B` then `μ(A) ≤ μ(B)`.
  have hA : (1 - δ) ≤ (μ n) {ω : Ω |
        QueryEfficiency.MSE (Q := Q) (X := X) Pf (fun f => (score f Qstar : ℝ)) (fun f => hNN n ω f) ≤ c_base / 2} := by
    -- `hN1` provides the same statement but written as `μ(A) ≥ 1 - δ`.
    simpa [ge_iff_le] using (hN1 n hn1)
  have hAB : (μ n) {ω : Ω |
        QueryEfficiency.MSE (Q := Q) (X := X) Pf (fun f => (score f Qstar : ℝ)) (fun f => hNN n ω f) ≤ c_base / 2}
      ≤ (μ n) {ω : Ω |
        QueryEfficiency.MSE (Q := Q) (X := X) Pf (fun f => (score f Qstar : ℝ)) (fun f => hNN n ω f)
          ≤ QueryEfficiency.MSE (Q := Q) (X := X) Pf (fun f => (score f Qstar : ℝ)) (fun f => hQ n ω f)} := by
    exact MeasureTheory.measure_mono hsubset
  have : (1 - δ) ≤ (μ n) {ω : Ω |
        QueryEfficiency.MSE (Q := Q) (X := X) Pf (fun f => (score f Qstar : ℝ)) (fun f => hNN n ω f)
          ≤ QueryEfficiency.MSE (Q := Q) (X := X) Pf (fun f => (score f Qstar : ℝ)) (fun f => hQ n ω f)} :=
    le_trans hA hAB
  -- Rewrite back into `≥` form.
  simpa [ge_iff_le] using this

end Theorem2

end Assumptions_And_Theorems

end QuenchICML
