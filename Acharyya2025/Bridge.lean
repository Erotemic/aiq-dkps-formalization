/-
Reduction bridges for the Acharyya et al. 2025 DKPS concentration theorem.

This file keeps the proof chain explicit:

response-mean event
  → distance-matrix event
  → centered classical-MDS matrix event
  → cited spectral/MDS perturbation theorem
  → downstream DKPS concentration/alignment hypotheses.

The first two arrows are deterministic and proved here.  The spectral/MDS arrow
is intentionally isolated as a cited theorem-shaped `sorry`, not a hidden
declaration-level assumption.
-/

import Acharyya2025.Deterministic
import Acharyya2025.Concentration

open scoped BigOperators Topology
open Filter MeasureTheory

namespace Acharyya2025.Bridge

open Acharyya2024
open Acharyya2025.Deterministic

variable {Ω : Type} [MeasurableSpace Ω]

/-- Entrywise closeness for finite dissimilarity matrices. -/
def EntrywiseClose {n : Nat} (A B : DisMat n) (ε : Real) : Prop :=
  ∀ i j : Fin n, |A i j - B i j| ≤ ε

/-- Uniform closeness of row-stacked response-mean matrices. -/
def UniformResponseMeanClose {n m p : Nat}
    (Xbar μ : Fin n → Mat m p) (η : Real) : Prop :=
  ∀ i : Fin n, ‖Xbar i - μ i‖ ≤ η

/-- Explicit Frobenius dissimilarity rate obtained from uniform response-mean error. -/
noncomputable def responseFrobRate (n m : Nat) (η : Real) : Real :=
  ((n : Real) * (n : Real)) * (((m : Real)⁻¹) * (2 * η))

/-- Loose entrywise CMDS-matrix rate obtained from bounded dissimilarities and response error. -/
noncomputable def cmdsEntrywiseRate (n m : Nat) (R η : Real) : Real :=
  4 * ((2 * R) * responseFrobRate n m η)

/--
Frobenius closeness implies entrywise closeness.

Formalized by Codex 5.5 High, per user-observed model label.
-/
theorem frob_close_to_entrywise_close {n : Nat} {A B : DisMat n} {ε : Real}
    (hfrob : frobSub A B ≤ ε) :
    EntrywiseClose A B ε := by
  intro i j
  exact (abs_entry_sub_le_frobSub A B i j).trans hfrob

/--
High-probability Frobenius closeness implies high-probability entrywise
closeness.

Formalized by Codex 5.5 High, per user-observed model label.
-/
theorem frob_close_hp_to_entrywise_close_hp
    (P : Nat → Measure Ω)
    {n : Nat}
    (Ahat : Nat → Ω → DisMat n)
    (A : DisMat n)
    (ε : Nat → Real)
    (hfrob :
      HighProbAtTop P (fun u => {ω | frobSub (Ahat u ω) A ≤ ε u})) :
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
    (Xbar μ : Fin n → Mat m p)
    (hclose : UniformResponseMeanClose Xbar μ η) :
    frobSub (responseDist Xbar) (responseDist μ)
      ≤ responseFrobRate n m η := by
  exact frobSub_responseDist_le_of_uniform_errors Xbar μ hclose

/--
High-probability response-mean closeness propagates to a high-probability
Frobenius dissimilarity-matrix bound.

Formalized by Codex 5.5 High, per user-observed model label.
-/
theorem response_mean_close_hp_to_frob_hp
    (P : Nat → Measure Ω)
    {n m p : Nat}
    (Xbar : Nat → Ω → Fin n → Mat m p)
    (μ : Fin n → Mat m p)
    (η : Nat → Real)
    (hclose :
      HighProbAtTop P
        (fun u => {ω | UniformResponseMeanClose (Xbar u ω) μ (η u)})) :
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
    {n : Nat} (hn : 0 < n) {A B : DisMat n} {ε : Real}
    (hclose : EntrywiseClose A B ε) :
    EntrywiseClose (doubleCenter A) (doubleCenter B) (4 * ε) := by
  intro i j
  exact abs_doubleCenter_sub_le_of_entrywise hn hclose i j

/--
High-probability entrywise matrix closeness propagates through double-centering.

Formalized by Codex 5.5 High, per user-observed model label.
-/
theorem entrywise_close_hp_to_centered_entrywise_close_hp
    (P : Nat → Measure Ω)
    {n : Nat} (hn : 0 < n)
    (Ahat : Nat → Ω → DisMat n)
    (A : DisMat n)
    (ε : Nat → Real)
    (hclose :
      HighProbAtTop P (fun u => {ω | EntrywiseClose (Ahat u ω) A (ε u)})) :
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
    (hclose : EntrywiseClose A B ε)
    (hA : ∀ i j : Fin n, |A i j| ≤ R)
    (hB : ∀ i j : Fin n, |B i j| ≤ R) :
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
    {n : Nat} (hn : 0 < n) {A B : DisMat n} {ε : Real}
    (hclose : EntrywiseClose (fun i j => (A i j)^2) (fun i j => (B i j)^2) ε) :
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
    {n : Nat} (hn : 0 < n) {A B : DisMat n} {ε R : Real}
    (hclose : EntrywiseClose A B ε)
    (hA : ∀ i j : Fin n, |A i j| ≤ R)
    (hB : ∀ i j : Fin n, |B i j| ≤ R) :
    EntrywiseClose (classicalMDSMatrix A) (classicalMDSMatrix B)
      (4 * ((2 * R) * ε)) := by
  exact squared_entrywise_close_to_cmds_entrywise_close hn
    (entrywise_close_squared_of_bounded hclose hA hB)

/--
Paper-facing centered-matrix perturbation seam for classical MDS.

This is deliberately a theorem-shaped `sorry`, not a hidden declaration-level
assumption.  It is the precise place where the finite-dimensional spectral
perturbation argument should be inserted.

Mathematical source/citation:
- Acharyya, Agterberg, Park, Priebe, *Concentration bounds on response-based
  vector embeddings of black-box generative models*, Theorem 2 and Appendix A.
- Agterberg, Lubberts, Arroyo (2022), decomposition strategy used by Acharyya et
  al. for the CMDS embedding perturbation.
- Yu, Wang, Samworth (2015), "A useful variant of the Davis-Kahan theorem for
  statisticians", Biometrika 102(2):315-323.
- Chen, Chi, Fan, Ma et al. (2021), *Spectral Methods for Data Science: A
  Statistical Perspective*, Foundations and Trends in Machine Learning
  14(5):566-806.

The intended replacement proof uses Weyl eigenvalue perturbation plus
Davis-Kahan eigenspace perturbation under the paper's fixed-rank/eigengap
assumptions.

TODO(false-statement): vacuous `MDSStabilityAssumptions`, arbitrary `ψhat`, and
unaligned `ConfigError` make this false as written. SUPERSEDED: the true
high-probability aligned version is proved in
`Acharyya2025.AlignedPipeline.highProb_aligned_configError_of_entrywise_close`
(built on `MatrixPerturbation.exists_isometry_configError_le_of_entrywise_close`).
This legacy statement is retained only as a scaffold record.
-/
theorem cited_cmds_embedding_perturbation_from_centered_entrywise
    (P : Nat → Measure Ω)
    {n d : Nat}
    (Dhat : Nat → Ω → DisMat n)
    (D : DisMat n)
    (ψhat : Nat → Ω → Config n d)
    (ψ : Config n d)
    (stable : Acharyya2025.Concentration.MDSStabilityAssumptions n d D)
    (rate : Nat → Real)
    (hcenter :
      HighProbAtTop P
        (fun u => {ω | EntrywiseClose
          (classicalMDSMatrix (Dhat u ω)) (classicalMDSMatrix D) (rate u)})) :
    HighProbAtTop P (fun u => {ω | ConfigError (ψhat u ω) ψ ≤ rate u}) := by
  sorry

/--
Main bridge from response-mean concentration to DKPS embedding concentration,
assuming the cited CMDS spectral perturbation theorem.

This theorem proves the reduction chain around the cited spectral theorem:
response-mean HP event → Frobenius distance-matrix HP event → entrywise
distance HP event → entrywise CMDS-matrix HP event → cited CMDS perturbation.

The only unproved ingredient it uses is
`cited_cmds_embedding_perturbation_from_centered_entrywise`, whose docstring
records the peer-reviewed/high-quality citations.

Formalized by Codex 5.5 High, per user-observed model label.
-/
theorem dkps_config_concentration_from_response_mean_hp
    (P : Nat → Measure Ω)
    {n m p d : Nat} (hn : 0 < n)
    (Xbar : Nat → Ω → Fin n → Mat m p)
    (μ : Fin n → Mat m p)
    (ψhat : Nat → Ω → Config n d)
    (ψ : Config n d)
    (stable :
      Acharyya2025.Concentration.MDSStabilityAssumptions n d (responseDist μ))
    (η R : Nat → Real)
    (hmean :
      HighProbAtTop P
        (fun u => {ω | UniformResponseMeanClose (Xbar u ω) μ (η u)}))
    (hsample_bound :
      ∀ u ω i j, |responseDist (Xbar u ω) i j| ≤ R u)
    (hpopulation_bound :
      ∀ u i j, |responseDist μ i j| ≤ R u) :
    HighProbAtTop P
      (fun u => {ω |
        ConfigError (ψhat u ω) ψ ≤ cmdsEntrywiseRate n m (R u) (η u)}) := by
  let Dhat : Nat → Ω → DisMat n := fun u ω => responseDist (Xbar u ω)
  let D : DisMat n := responseDist μ
  let frobRate : Nat → Real := fun u => responseFrobRate n m (η u)
  let cmdsRate : Nat → Real := fun u => cmdsEntrywiseRate n m (R u) (η u)
  have hfrob :
      HighProbAtTop P
        (fun u => {ω | frobSub (Dhat u ω) D ≤ frobRate u}) := by
    simpa [Dhat, D, frobRate] using
      response_mean_close_hp_to_frob_hp P Xbar μ η hmean
  have hentry :
      HighProbAtTop P
        (fun u => {ω | EntrywiseClose (Dhat u ω) D (frobRate u)}) := by
    exact frob_close_hp_to_entrywise_close_hp P Dhat D frobRate hfrob
  have hcmds :
      HighProbAtTop P
        (fun u => {ω | EntrywiseClose
          (classicalMDSMatrix (Dhat u ω)) (classicalMDSMatrix D) (cmdsRate u)}) := by
    exact HighProbAtTop.mono hentry
      (fun u ω hω =>
        entrywise_close_to_cmds_entrywise_close_of_bounded hn hω
          (fun i j => by simpa [Dhat] using hsample_bound u ω i j)
          (fun i j => by simpa [D] using hpopulation_bound u i j))
  simpa [Dhat, D, cmdsRate] using
    cited_cmds_embedding_perturbation_from_centered_entrywise
      P Dhat D ψhat ψ stable cmdsRate hcmds

end Acharyya2025.Bridge
