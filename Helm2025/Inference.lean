/-
Helm 2025 DKPS statistical inference — paper-facing statements.

This file is meant to be read alongside Helm et al. (2025), "Statistical
inference on black-box generative models in the data kernel perspective space".
It names the paper's assumptions (A1-A4), the alignment-consistency condition,
the hypothesis-class / Bayes-risk objects, and states the two theorems in
paper form:

* `Theorem1` — fixed-`n` risk convergence under aligned estimated embeddings;
* `Theorem2_bayes` — consistency transfer to estimated embeddings, specialized
  to Bayes risk over a hypothesis class.

These wrap the machinery in `Helm2025.Internal`.
-/
import Mathlib
import Helm2025.Internal
set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Helm2025
namespace DKPS

open MeasureTheory Filter Topology Metric
open scoped BigOperators

variable {d d' : ℕ}

/-!
# Paper-facing interface

This final section is **only documentation + paper-aligned wrappers** around the core
formalization above.  Nothing earlier in the file is renamed; all new names are added
as conveniences for readers of the paper.

## Notation crosswalk (paper → Lean)

Let `d` be the embedding dimension and `d'` be the label dimension.

* Paper `ψ ∈ ℝ^d`                    → `E d`  (a.k.a. `EuclideanSpace ℝ (Fin d)`)
* Paper `y ∈ ℝ^{d'}`                 → `Y d'`
* Paper learning rule `h(·; T_n)`     → `learn : LearningRule n d d'`
* Paper loss `ℓ : Y × Y → ℝ`          → `loss : LossFunction d'`
* Paper risk `R_ℓ(P_{ψY}, h(·; T_n))` → `risk n d d' P learn loss`
* Paper estimated-embedding risk       → `risk_est n d d' P learn loss psi_hat`

### About the paper's budgets `(m,r)`
The paper has two tuning parameters (estimation budgets) and takes limits as `(m,r) → ∞`.
In Lean we abstract this as **one** index `u : ℕ` and write `psi_hat u` for the estimator
at budget `u`.  (If you want the literal paper form, instantiate `u := (m,r)` using a
pair encoding.)

## Assumptions (paper → Lean)

* **A1** (invariance under orthogonal + translation)
  → `InvariantToAffineIsometries` (we use `AffineIsometryEquiv`, which subsumes `ψ ↦ Wψ + a`)

* **A2** (continuity of the learning rule)
  → `ContinuousLearningRule` (standard topological continuity).
  For convenience, we also define a *sequential* variant `PaperA2_SequentialContinuity`
  and show it follows from `ContinuousLearningRule`.

* **A3** (bounded/closed/complete image of each decision function in the hypothesis class)
  The paper states this for a hypothesis class `H ⊆ (E d → Y d')`.
  We provide the direct translation as `PaperA3_HypothesisClass`.
  Our main proofs above use the stronger `BoundedLearningRule`, which gives a **uniform**
  compact set containing *all* predictions of the learning rule across all training sets.

* **A4** (for every `y`, the map `ŷ ↦ ℓ(ŷ,y)` is continuous)
  → `ContinuousLossInPred`.  Our core development assumes the stronger joint continuity
  `ContinuousLoss`; we prove `ContinuousLoss → ContinuousLossInPred`.

* **Eq. (3)** (alignment consistency)
  → `DKPSAlignmentConsistency`.  The paper writes a `max` over training points; in Lean
  we use `iSup` over a finite index type.

## Theorems (paper → Lean)

* **Theorem 1** (fixed `n`: risk with estimated embeddings converges to risk with true embeddings)
  → `risk_converges_fixed_n`

* **Theorem 2** (diagonal schedule transfers consistency)
  → `consistency_transfer_dkps` (for an abstract limit `L`) and
    `consistency_transfer_dkps_bayes` (specialized to Bayes risk over a hypothesis class).

-/

section PaperFacing

/-- A *decision function* `h : E d → Y d'` (paper's `h ∈ H`). -/
abbrev DecisionFunction (d d' : ℕ) := E d → Y d'

/-- Turn a `LearningRule` plus a fixed training set into a decision function. -/
def decisionFnOfLearn (n d d' : ℕ) (learn : LearningRule n d d')
    (t : Fin n → E d × Y d') : DecisionFunction d d' :=
  fun ψ => learn t ψ

/-- Paper Assumption 4: continuity in the first argument, pointwise in `y`. -/
def ContinuousLossInPred (d' : ℕ) (loss : LossFunction d') : Prop :=
  ∀ y : Y d', Continuous (fun yhat : Y d' => loss yhat y)

/-- Joint continuity implies the paper's pointwise continuity assumption. -/
lemma ContinuousLoss.continuousLossInPred {d' : ℕ} {loss : LossFunction d'}
    (h : ContinuousLoss d' loss) : ContinuousLossInPred d' loss := by
  intro y
  have h' : Continuous (fun p : Y d' × Y d' => loss p.1 p.2) := by
    simpa [ContinuousLoss] using h
  -- compose with yhat ↦ (yhat, y)
  exact h'.comp (continuous_id.prodMk continuous_const)

/-- Paper Assumption 2, written as a sequential continuity statement. -/
def PaperA2_SequentialContinuity (n d d' : ℕ) (learn : LearningRule n d d') : Prop :=
  ∀ (tseq : ℕ → Fin n → E d × Y d') (ψseq : ℕ → E d)
    (t : Fin n → E d × Y d') (ψ : E d),
    Tendsto (fun r => (tseq r, ψseq r)) atTop (𝓝 (t, ψ)) →
      Tendsto (fun r => learn (tseq r) (ψseq r)) atTop (𝓝 (learn t ψ))

/-- `ContinuousLearningRule` implies the paper's sequential continuity formulation of A2. -/
lemma ContinuousLearningRule.paperA2 {n d d' : ℕ} {learn : LearningRule n d d'}
    (h : ContinuousLearningRule n d d' learn) :
    PaperA2_SequentialContinuity n d d' learn := by
  intro tseq ψseq t ψ ht
  have hcont : Continuous (fun p : (Fin n → E d × Y d') × E d => learn p.1 p.2) := by
    simpa [ContinuousLearningRule] using h
  -- `ht : Tendsto (fun r => (tseq r, ψseq r)) atTop (𝓝 (t, ψ))`
  -- apply continuity as a `Tendsto` statement and compose.
  exact (hcont.tendsto (t, ψ)).comp ht

/-- Paper Assumption 3 (as stated): every `h ∈ H` has closed, bounded, complete image. -/
def PaperA3_HypothesisClass (d d' : ℕ) (H : Set (DecisionFunction d d')) : Prop :=
  ∀ h ∈ H,
    IsClosed (Set.range h) ∧
    Bornology.IsBounded (Set.range h) ∧
    IsComplete (Set.range h)

/-- A small helper: `BoundedLearningRule` implies boundedness of each induced decision function's image. -/
lemma BoundedLearningRule.isBounded_range (n d d' : ℕ) {learn : LearningRule n d d'}
    (h : BoundedLearningRule n d d' learn) :
    ∀ t, Bornology.IsBounded (Set.range (decisionFnOfLearn n d d' learn t)) := by
  rcases h with ⟨K, hKc, hK⟩
  intro t
  have hsub : Set.range (decisionFnOfLearn n d d' learn t) ⊆ K := by
    intro y hy
    rcases hy with ⟨ψ, rfl⟩
    exact hK t ψ
  exact hKc.isBounded.subset hsub

/-- Risk of a (measurable) decision function `h : E → Y`. -/
def risk_df (d d' : ℕ) (P : Measure (E d × Y d'))
    (loss : LossFunction d') (h : DecisionFunction d d') : ℝ :=
  ∫ p, loss (h p.1) p.2 ∂P

/-- Bayes risk over a hypothesis class `H`. (Paper's `R^*_\ell(P_{ψY}, H)`.) -/
def bayesRisk (d d' : ℕ) (P : Measure (E d × Y d'))
    (loss : LossFunction d') (H : Set (DecisionFunction d d')) : ℝ :=
  sInf (risk_df (d:=d) (d':=d') P loss '' H)

/-- Appendix-style (expected) consistency: `risk → bayesRisk`. -/
def ConsistentExpected (d d' : ℕ) (P : Measure (E d × Y d'))
    (loss : LossFunction d')
    (learn : (n : ℕ) → LearningRule n d d')
    (H : Set (DecisionFunction d d')) : Prop :=
  Tendsto (fun n => risk n d d' P (learn n) loss) atTop (𝓝 (bayesRisk d d' P loss H))

/-- Theorem 2, specialized to Bayes risk over a hypothesis class. -/
theorem consistency_transfer_dkps_bayes (d d' : ℕ)
    (P : Measure (E d × Y d')) [IsProbabilityMeasure P]
    (learn : (n : ℕ) → LearningRule n d d')
    (loss : LossFunction d')
    (psi_hat : (n : ℕ) → ℕ → (Fin (n + 1) → E d × Y d') → Fin (n + 1) → E d)
    (H : Set (DecisionFunction d d'))
    (h_meas_psi : ∀ n u, Measurable (psi_hat n u))
    (h_align : ∀ n, DKPSAlignmentConsistency n d d' P (psi_hat n))
    (h_inv : ∀ n, InvariantToAffineIsometries n d d' (learn n))
    (h_cont_learn : ∀ n, ContinuousLearningRule n d d' (learn n))
    (h_bound_learn : ∀ n, BoundedLearningRule n d d' (learn n))
    (h_cont_loss : ContinuousLoss d' loss)
    (h_bound_label : BoundedLabelSupport d d' P)
    (h_consistent : ConsistentExpected d d' P loss learn H) :
    ∃ phi : ℕ → ℕ, Tendsto phi atTop atTop ∧
      Tendsto (fun n => risk_est n d d' P (learn n) loss (psi_hat n (phi n))) atTop
        (𝓝 (bayesRisk d d' P loss H)) := by
  -- instantiate the existing abstract theorem with `L = bayesRisk ...`
  simpa [ConsistentExpected] using
    consistency_transfer_dkps (d:=d) (d':=d') (P:=P) (learn:=learn) (loss:=loss) (psi_hat:=psi_hat)
      (L := bayesRisk d d' P loss H)
      h_meas_psi h_align h_inv h_cont_learn h_bound_learn h_cont_loss h_bound_label h_consistent

/-!
## Suggested local `#check`s

These are intended for a lightweight sanity pass (they should be fast, unlike some `#find`s).

Uncomment in a scratch file if you like:

```
-- #check risk
-- #check risk_est
-- #check DKPSAlignmentConsistency
-- #check InvariantToAffineIsometries
-- #check ContinuousLearningRule
-- #check BoundedLearningRule
-- #check ContinuousLoss
-- #check risk_converges_fixed_n
-- #check diagonal_convergence
-- #check consistency_transfer_dkps
-- #check consistency_transfer_dkps_bayes
-- #check ContinuousLossInPred
-- #check PaperA3_HypothesisClass
```

-/

end PaperFacing



/-! ## Paper-facing names

These are thin aliases/wrappers so that theorems can be read directly against the paper.

Note on assumptions:
- The paper states (A2) and (A4) only for the coordinates that are perturbed in the DKPS
  transfer argument (embeddings in (A2), predictions in (A4)).  In the Lean proofs we package
  the training sample as `(ψ, y)` pairs and therefore assume *joint* continuity of the learning
  rule (`ContinuousLearningRule`) and of the loss (`ContinuousLoss`).  These are standard
  sufficient conditions for the paper’s pointwise continuity statements and are satisfied by
  typical learning rules / losses.
- The paper’s (A3) is phrased as “image set is closed, bounded, and complete”.
  In finite-dimensional Euclidean spaces, this is equivalent to having a compact range, which
  we encode as `BoundedLearningRule`.
- Wherever we use a strengthened hypothesis, the wrapper section below exposes both the
  paper-level predicate and the strengthened predicate actually used by the Lean proofs.
-/




/-! ### Small helper definitions for paper-facing assumptions -/

section PaperFacingHelpers
variable {n d d' : ℕ}

/-- The uncurried map associated to a learning rule (used to state paper A3). -/
def learnUncurried (learn : LearningRule n d d') : (TrainingSet n d d') × E d → Y d' :=
  fun p => learn p.1 p.2

/-- (Paper A3) The image of the (uncurried) decision function is closed, bounded, and complete. -/
def PaperA3_ImageClosedBoundedComplete (learn : LearningRule n d d') : Prop :=
  IsClosed (Set.range (learnUncurried (n:=n) (d:=d) (d':=d') learn)) ∧
  Bornology.IsBounded (Set.range (learnUncurried (n:=n) (d:=d) (d':=d') learn)) ∧
  IsComplete (Set.range (learnUncurried (n:=n) (d:=d) (d':=d') learn))

/-- Abbreviation: the “paper A2” wrappers below currently use the stronger joint continuity assumption. -/
abbrev ContinuousLearn (learn : LearningRule n d d') : Prop :=
  ContinuousLearningRule n d d' learn

/-- Abbreviation: compact-range encoding of boundedness. -/
abbrev BoundedLearn (learn : LearningRule n d d') : Prop :=
  BoundedLearningRule n d d' learn

end PaperFacingHelpers

section PaperAPI

variable {n d d' : ℕ}

/-- Paper Assumption 1 (Appendix A.1): invariance to rigid motions of the embedding space. -/
abbrev Assumption1 (learn : LearningRule n d d') : Prop :=
  InvariantToAffineIsometries n d d' learn

/-- Paper Assumption 2 (Appendix A.2): continuity of the learning rule. -/
abbrev Assumption2 (learn : LearningRule n d d') : Prop :=
  ContinuousLearningRule n d d' learn

/-- Paper Assumption 3 (Appendix A.3), as written: image of each decision function is closed/bounded/complete. -/
abbrev Assumption3 (learn : LearningRule n d d') : Prop :=
  PaperA3_ImageClosedBoundedComplete (n:=n) (d:=d) (d':=d') learn

/-- Compact-range formulation used in the Lean development.
In finite-dimensional Euclidean spaces this is an equivalent rephrasing of the paper's A3
(closed + bounded + complete image), since bounded sets are precompact and we may take a closed ball
containing the range. -/
abbrev Assumption3' (learn : LearningRule n d d') : Prop :=
  BoundedLearningRule n d d' learn

/-- Paper Assumption 4 (Appendix A.4): loss is continuous in the *prediction* argument for each fixed label. -/
abbrev Assumption4 (loss : LossFunction d') : Prop :=
  ContinuousLossInPred d' loss


/-- Strengthened loss regularity used in the Lean proofs (joint continuity). -/
abbrev Assumption4' (loss : LossFunction d') : Prop :=
  ContinuousLoss d' loss

/-- Compact support of labels `y` (paper condition in Theorem 1). -/
abbrev LabelCompactSupport (P : Measure (Z d d')) : Prop :=
  BoundedLabelSupport d d' P

/-- Alignment consistency (paper Eq. (3)) for a fixed `n`. -/
abbrev AlignmentConsistency (P : Measure (Z d d'))
    (psi_hat : ℕ → (Sample n d d') → Fin (n + 1) → E d) : Prop :=
  DKPSAlignmentConsistency n d d' P psi_hat


/-- **Theorem 1 (paper)**: fixed-`n` risk convergence under aligned estimated embeddings. -/
theorem Theorem1 (n d d' : ℕ)
    (P : Measure (Z d d')) [IsProbabilityMeasure P]
    (learn : LearningRule n d d')
    (loss : LossFunction d')
    (psi_hat : ℕ → (Sample n d d') → Fin (n + 1) → E d)
    (h_meas_psi : ∀ u, Measurable (psi_hat u))
    (h_align : AlignmentConsistency (n:=n) (d:=d) (d':=d') (P:=P) psi_hat)
    (h_inv : Assumption1 (n:=n) (d:=d) (d':=d') learn)
    (h_cont_learn : Assumption2 (n:=n) (d:=d) (d':=d') learn)
    (h_bound_learn : Assumption3' (n:=n) (d:=d) (d':=d') learn)
    (h_cont_loss : ContinuousLoss d' loss)
    (h_bound_label : LabelCompactSupport (d:=d) (d':=d') P) :
    Tendsto (fun u => Rhatℓ n d d' P learn loss (psi_hat u)) atTop (𝓝 (Rℓ n d d' P learn loss)) := by
  simpa [Rhatℓ, Rℓ, AlignmentConsistency, Assumption1, Assumption2, Assumption3', LabelCompactSupport] using
    (risk_converges_fixed_n (n:=n) (d:=d) (d':=d') (P:=P) (learn:=learn) (loss:=loss)
      (psi_hat:=psi_hat) h_meas_psi h_align h_inv h_cont_learn h_bound_learn h_cont_loss h_bound_label)


/-- **Theorem 2 (paper)**: consistency transfers from true to estimated embeddings along a schedule. -/
theorem Theorem2_bayes (d d' : ℕ)
    (P : Measure (Z d d')) [IsProbabilityMeasure P]
    (learn : (n : ℕ) → LearningRule n d d')
    (loss : LossFunction d')
    (psi_hat : (n : ℕ) → ℕ → (Sample n d d') → Fin (n + 1) → E d)
    (H : Set (E d → Y d'))
    (h_meas_psi : ∀ n u, Measurable (psi_hat n u))
    (h_align : ∀ n, DKPSAlignmentConsistency n d d' P (psi_hat n))
    (h_inv : ∀ n, InvariantToAffineIsometries n d d' (learn n))
    (h_cont_learn : ∀ n, ContinuousLearningRule n d d' (learn n))
    (h_bound_learn : ∀ n, BoundedLearningRule n d d' (learn n))
    (h_cont_loss : ContinuousLoss d' loss)
    (h_bound_label : BoundedLabelSupport d d' P)
    (h_consistent : ConsistentExpected d d' P loss learn H) :
    ∃ phi : ℕ → ℕ, Tendsto phi atTop atTop ∧
      Tendsto (fun n => Rhatℓ n d d' P (learn n) loss (psi_hat n (phi n))) atTop
        (𝓝 (bayesRisk d d' P loss H)) := by
  simpa [Rhatℓ] using
    (consistency_transfer_dkps_bayes (d:=d) (d':=d') (P:=P) (learn:=learn) (loss:=loss)
      (psi_hat:=psi_hat) (H:=H) h_meas_psi h_align h_inv h_cont_learn h_bound_learn
      h_cont_loss h_bound_label h_consistent)


end PaperAPI

end DKPS
end Helm2025
