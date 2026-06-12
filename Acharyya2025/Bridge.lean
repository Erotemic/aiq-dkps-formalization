/-
Reduction bridges for the Acharyya et al. 2025 DKPS concentration theorem.

This file keeps the proof chain explicit:

response-mean event
  → distance-matrix event
  → centered classical-MDS matrix event
  → spectral/MDS perturbation (proved in `Acharyya2025.AlignedPipeline`)
  → downstream DKPS concentration/alignment hypotheses.

Every arrow proved in this file is deterministic event propagation or its
high-probability lift, with explicit rates (`responseFrobRate`,
`cmdsEntrywiseRate`).  The spectral/MDS arrow is fully proved downstream:
`Acharyya2025.AlignedPipeline.highProb_aligned_configError_of_entrywise_close`
consumes the entrywise CMDS-closeness events produced here.  No unproved
statements remain in this file.
-/

import Acharyya2025.Deterministic

open scoped BigOperators Topology
open Filter MeasureTheory

namespace Acharyya2025.Bridge

open Acharyya2024
open Acharyya2025.Deterministic

variable {Ω : Type} [MeasurableSpace Ω]

/-- Entrywise closeness for finite dissimilarity matrices: every entry of `A - B`
is bounded in absolute value by `ε`. With `A = B̂`, `B = B`, `|A i j - B i j| ≤ ε`
is the event `|B̂ᵢⱼ - Bᵢⱼ| ≤ ε for all i,j` of the paper's Theorem 1
(entrywise CMDS closeness). -/
def EntrywiseClose {n : Nat} (A B : DisMat n) (ε : Real) : Prop :=
  ∀ i j : Fin n, |A i j - B i j| ≤ ε

/-- Uniform closeness of row-stacked response-mean matrices: every model's sample
response mean `Xbar i` (the paper's `X̄ᵢ`) is within Frobenius distance `η` of its
population mean `μ i` (the paper's `µᵢ`). This is the per-model input event from
which the dissimilarity-matrix bounds are derived. -/
def UniformResponseMeanClose {n m p : Nat}
    (Xbar μ : Fin n → Mat m p) (η : Real) : Prop :=
  ∀ i : Fin n, ‖Xbar i - μ i‖ ≤ η

/-- Explicit Frobenius dissimilarity rate obtained from uniform response-mean error.
Given a uniform per-model response error `η`, this is the resulting bound on the
Frobenius distance between the sample and population dissimilarity matrices
(`D` vs. `∆`). It is the deterministic rate the response-mean event propagates into. -/
noncomputable def responseFrobRate (n m : Nat) (η : Real) : Real :=
  ((n : Real) * (n : Real)) * (((m : Real)⁻¹) * (2 * η))

/-- Loose entrywise CMDS-matrix rate obtained from bounded dissimilarities and
response error. Composing the squaring step (factor `2R`, with `R` a bound on the
dissimilarity entries) and the double-centering step (factor `4`) on top of
`responseFrobRate`, this is the entrywise `ε` reached for the centered CMDS
matrices `B̂` vs. `B` — i.e. the rate at which entrywise CMDS closeness (Theorem 1)
is established here. The constants are intentionally loose, not the paper's sharp
`16 Σγ/(rmε²)` constant. -/
noncomputable def cmdsEntrywiseRate (n m : Nat) (R η : Real) : Real :=
  4 * ((2 * R) * responseFrobRate n m η)

/--
Frobenius closeness implies entrywise closeness.

Formalized by Codex 5.5 High, per user-observed model label.
-/
theorem frob_close_to_entrywise_close {n : Nat} {A B : DisMat n} {ε : Real}
    (hfrob : frobSub A B ≤ ε) :   -- Frobenius distance ‖A - B‖_F ≤ ε
    -- Conclusion: a Frobenius bound implies the (weaker) entrywise bound, since
    -- each entry is dominated by the Frobenius norm.
    EntrywiseClose A B ε := by
  intro i j
  exact (abs_entry_sub_le_frobSub A B i j).trans hfrob

/--
High-probability Frobenius closeness implies high-probability entrywise
closeness.

Formalized by Codex 5.5 High, per user-observed model label.
-/
theorem frob_close_hp_to_entrywise_close_hp
    (P : Nat → Measure Ω)                 -- family of probability measures, indexed by sample regime u
    {n : Nat}
    (Ahat : Nat → Ω → DisMat n)           -- random sample matrix (the paper's B̂ / D)
    (A : DisMat n)                        -- fixed population matrix (the paper's B / ∆)
    (ε : Nat → Real)
    (hfrob :                              -- high-probability Frobenius closeness as u → ∞
      HighProbAtTop P (fun u => {ω | frobSub (Ahat u ω) A ≤ ε u})) :
    -- Conclusion: the high-probability Frobenius event upgrades to a
    -- high-probability entrywise event (probabilistic lift of the lemma above).
    HighProbAtTop P (fun u => {ω | EntrywiseClose (Ahat u ω) A (ε u)}) := by
  exact HighProbAtTop.mono hfrob
    (fun u ω hω => frob_close_to_entrywise_close hω)

/--
Uniform response-mean closeness propagates to a quantitative Frobenius
dissimilarity-matrix bound.

This is the deterministic event-propagation bridge used before inserting a
probability/concentration inequality.

Formalized by Codex 5.5 High, per user-observed model label.
-/
theorem response_mean_close_event_to_frob_event
    {n m p : Nat} {η : Real}
    (Xbar μ : Fin n → Mat m p)                      -- sample means X̄ᵢ and population means µᵢ
    (hclose : UniformResponseMeanClose Xbar μ η) :   -- each ‖X̄ᵢ - µᵢ‖ ≤ η
    -- Conclusion: a uniform response-mean error η yields a Frobenius bound between
    -- the sample and population dissimilarity matrices (D vs. ∆), at rate
    -- `responseFrobRate`.
    frobSub (responseDist Xbar) (responseDist μ)
      ≤ responseFrobRate n m η := by
  exact frobSub_responseDist_le_of_uniform_errors Xbar μ hclose

/--
High-probability response-mean closeness propagates to a high-probability
Frobenius dissimilarity-matrix bound.

Formalized by Codex 5.5 High, per user-observed model label.
-/
theorem response_mean_close_hp_to_frob_hp
    (P : Nat → Measure Ω)                  -- probability measures, indexed by regime u
    {n m p : Nat}
    (Xbar : Nat → Ω → Fin n → Mat m p)     -- random sample means X̄ᵢ
    (μ : Fin n → Mat m p)                  -- fixed population means µᵢ
    (η : Nat → Real)
    (hclose :                              -- high-probability uniform response-mean closeness
      HighProbAtTop P
        (fun u => {ω | UniformResponseMeanClose (Xbar u ω) μ (η u)})) :
    -- Conclusion: the high-probability response-mean event upgrades to a
    -- high-probability Frobenius dissimilarity-matrix bound (lift of the lemma above).
    HighProbAtTop P
      (fun u => {ω |
        frobSub (responseDist (Xbar u ω)) (responseDist μ)
          ≤ responseFrobRate n m (η u)}) := by
  exact HighProbAtTop.mono hclose
    (fun u ω hω => response_mean_close_event_to_frob_event (Xbar u ω) μ hω)

/--
Entrywise matrix closeness propagates through classical double-centering with
constant `4`.

This is the deterministic centering bridge before the spectral perturbation
step.

Formalized by Codex 5.5 High, per user-observed model label.
-/
theorem entrywise_close_to_centered_entrywise_close
    {n : Nat} (hn : 0 < n)                  -- nonempty index set (n > 0)
    {A B : DisMat n} {ε : Real}
    (hclose : EntrywiseClose A B ε) :       -- entrywise ε-closeness of A, B
    -- Conclusion: double-centering preserves entrywise closeness with the loose
    -- constant 4 (deterministic centering step toward the CMDS matrix B̂/B).
    EntrywiseClose (doubleCenter A) (doubleCenter B) (4 * ε) := by
  intro i j
  exact abs_doubleCenter_sub_le_of_entrywise hn hclose i j

/--
High-probability entrywise matrix closeness propagates through double-centering.

Formalized by Codex 5.5 High, per user-observed model label.
-/
theorem entrywise_close_hp_to_centered_entrywise_close_hp
    (P : Nat → Measure Ω)                  -- probability measures, indexed by regime u
    {n : Nat} (hn : 0 < n)                 -- nonempty index set (n > 0)
    (Ahat : Nat → Ω → DisMat n)            -- random sample matrix
    (A : DisMat n)                         -- fixed population matrix
    (ε : Nat → Real)
    (hclose :                              -- high-probability entrywise closeness
      HighProbAtTop P (fun u => {ω | EntrywiseClose (Ahat u ω) A (ε u)})) :
    -- Conclusion: high-probability entrywise closeness survives double-centering
    -- (probabilistic lift, constant 4).
    HighProbAtTop P
      (fun u => {ω | EntrywiseClose
        (doubleCenter (Ahat u ω)) (doubleCenter A) (4 * ε u)}) := by
  exact HighProbAtTop.mono hclose
    (fun u ω hω => entrywise_close_to_centered_entrywise_close hn hω)

/--
Entrywise closeness of bounded dissimilarities propagates to entrywise closeness
of squared dissimilarities.

Formalized by Codex 5.5 High, per user-observed model label.
-/
theorem entrywise_close_squared_of_bounded
    {n : Nat} {A B : DisMat n} {ε R : Real}
    (hclose : EntrywiseClose A B ε)         -- entrywise ε-closeness of A, B
    -- Boundedness side-conditions (extra, implicit assumption beyond the paper's
    -- statement): all dissimilarity entries lie in [-R, R].
    (hA : ∀ i j : Fin n, |A i j| ≤ R)
    (hB : ∀ i j : Fin n, |B i j| ≤ R) :
    -- Conclusion: squaring entries (the (·)∘² step of CMDS) keeps them close, with
    -- ε inflated to 2R·ε (via |a²-b²| = |a-b|·|a+b| ≤ ε·2R).
    EntrywiseClose (fun i j => (A i j)^2) (fun i j => (B i j)^2) ((2 * R) * ε) := by
  intro i j
  have hε_nonneg : 0 ≤ ε :=
    (abs_nonneg (A i j - B i j)).trans (hclose i j)
  have hR_nonneg : 0 ≤ R :=
    (abs_nonneg (A i j)).trans (hA i j)
  have hsum : |A i j + B i j| ≤ 2 * R := by
    calc
      |A i j + B i j| ≤ |A i j| + |B i j| := abs_add_le _ _
      _ ≤ R + R := add_le_add (hA i j) (hB i j)
      _ = 2 * R := by ring
  have hfactor :
      (A i j)^2 - (B i j)^2 = (A i j - B i j) * (A i j + B i j) := by
    ring
  calc
    |(A i j)^2 - (B i j)^2|
        = |A i j - B i j| * |A i j + B i j| := by
          rw [hfactor, abs_mul]
    _ ≤ ε * (2 * R) := by
          exact mul_le_mul (hclose i j) hsum (abs_nonneg _) hε_nonneg
    _ = (2 * R) * ε := by ring

/--
Squared-dissimilarity closeness propagates to the entrywise classical-MDS
matrix with a clean constant.  The constant is intentionally loose (`4`) so the
lemma depends only on the already-proved double-centering stability.

Formalized by Codex 5.5 High, per user-observed model label.
-/
theorem squared_entrywise_close_to_cmds_entrywise_close
    {n : Nat} (hn : 0 < n)                  -- nonempty index set (n > 0)
    {A B : DisMat n} {ε : Real}
    -- entrywise ε-closeness of the squared dissimilarities
    (hclose : EntrywiseClose (fun i j => (A i j)^2) (fun i j => (B i j)^2) ε) :
    -- Conclusion: entrywise closeness of squared dissimilarities yields entrywise
    -- closeness of the centered CMDS matrices B̂ vs. B (the -½·doubleCenter step),
    -- with constant 4. This is the core entrywise CMDS-closeness link of Theorem 1.
    EntrywiseClose (classicalMDSMatrix A) (classicalMDSMatrix B) (4 * ε) := by
  intro i j
  have hdc := abs_doubleCenter_sub_le_of_entrywise hn hclose i j
  have hhalf :
      |classicalMDSMatrix A i j - classicalMDSMatrix B i j|
        ≤ |doubleCenter (fun i j => (A i j)^2) i j
            - doubleCenter (fun i j => (B i j)^2) i j| := by
    have hnonneg :
        0 ≤ |doubleCenter (fun i j => (A i j)^2) i j
            - doubleCenter (fun i j => (B i j)^2) i j| := abs_nonneg _
    calc
      |classicalMDSMatrix A i j - classicalMDSMatrix B i j|
          = ((2 : Real)⁻¹) *
              |doubleCenter (fun i j => (A i j)^2) i j
                - doubleCenter (fun i j => (B i j)^2) i j| := by
            set x := doubleCenter (fun i j => (A i j)^2) i j
            set y := doubleCenter (fun i j => (B i j)^2) i j
            have hleft : -(2 : Real)⁻¹ * x - (-(2 : Real)⁻¹ * y)
                = -((2 : Real)⁻¹ * (x - y)) := by ring
            calc
              |classicalMDSMatrix A i j - classicalMDSMatrix B i j|
                  = |-(2 : Real)⁻¹ * x - (-(2 : Real)⁻¹ * y)| := by
                    simp [classicalMDSMatrix, x, y, one_div]
              _ = |-((2 : Real)⁻¹ * (x - y))| := by rw [hleft]
              _ = |(2 : Real)⁻¹ * (x - y)| := by rw [abs_neg]
              _ = |(2 : Real)⁻¹| * |x - y| := by rw [abs_mul]
              _ = ((2 : Real)⁻¹) * |x - y| := by
                    rw [abs_of_nonneg]
                    norm_num
              _ = ((2 : Real)⁻¹) *
                    |doubleCenter (fun i j => (A i j)^2) i j
                      - doubleCenter (fun i j => (B i j)^2) i j| := by
                    simp [x, y]
      _ ≤ |doubleCenter (fun i j => (A i j)^2) i j
            - doubleCenter (fun i j => (B i j)^2) i j| := by
            norm_num
            linarith
  exact hhalf.trans hdc

/--
Entrywise closeness of bounded dissimilarities propagates to entrywise closeness
of the classical-MDS centered matrices.

Formalized by Codex 5.5 High, per user-observed model label.
-/
theorem entrywise_close_to_cmds_entrywise_close_of_bounded
    {n : Nat} (hn : 0 < n)                  -- nonempty index set (n > 0)
    {A B : DisMat n} {ε R : Real}
    (hclose : EntrywiseClose A B ε)         -- entrywise ε-closeness of the dissimilarities A, B
    -- Boundedness side-conditions (extra, implicit assumption beyond the paper):
    -- all dissimilarity entries lie in [-R, R].
    (hA : ∀ i j : Fin n, |A i j| ≤ R)
    (hB : ∀ i j : Fin n, |B i j| ≤ R) :
    -- Conclusion: combining the squaring (factor 2R) and centering (factor 4)
    -- steps, entrywise-close bounded dissimilarities give entrywise-close CMDS
    -- matrices B̂ vs. B at rate 4·(2R·ε) — the end-to-end entrywise CMDS closeness
    -- realizing the Theorem 1 content (with loose, non-sharp constants).
    EntrywiseClose (classicalMDSMatrix A) (classicalMDSMatrix B)
      (4 * ((2 * R) * ε)) := by
  exact squared_entrywise_close_to_cmds_entrywise_close hn
    (entrywise_close_squared_of_bounded hclose hA hB)

end Acharyya2025.Bridge
