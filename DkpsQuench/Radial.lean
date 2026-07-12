/-
Distance-only nearest-neighbor foundations for Quench.

Nearest-neighbor score prediction depends only on target-to-reference
distances.  It does not require a single globally aligned coordinate map on the
entire model class.  This file states and proves the corresponding radial
version of the Quench engine, including the literal tie average and the
compact/full-support/iid coverage composition.
-/

import DkpsQuench.QueryEfficiency

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise Topology
open Filter MeasureTheory

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

universe u v w

variable {Q : Type u} [DecidableEq Q]
variable {X : Type v} [MeasurableSpace X]
variable {d : Nat}
variable {Ω : Type w} [MeasurableSpace Ω]

/-- Choose one minimizer of a finite family of estimated radial distances. -/
noncomputable def radialIndex {n : Nat} (hn : n > 0)
    (rhat : Fin n → Real) : Fin n :=
  have h_exists : ∃ i, IsArgmin rhat i := by
    haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
    obtain ⟨i, _, hi⟩ := Finset.exists_min_image
      (Finset.univ : Finset (Fin n)) rhat Finset.univ_nonempty
    exact ⟨i, fun j => hi j (Finset.mem_univ j)⟩
  Classical.choose h_exists

/-- All minimizers of a finite family of estimated radial distances. -/
noncomputable def radialMinimizers {n : Nat} (hn : n > 0)
    (rhat : Fin n → Real) : Finset (Fin n) :=
  Finset.univ.filter fun i => IsArgmin rhat i

/-- Average the reference scores over all tied radial-distance minimizers. -/
noncomputable def radialTieAverage {n : Nat} (hn : n > 0)
    (rhat : Fin n → Real) (yref : Fin n → Real) : Real :=
  let S := radialMinimizers hn rhat
  (∑ i ∈ S, yref i) / (S.card : Real)

/-- Stage-indexed radial nearest-neighbor regression.  At stage zero there are
no references, so the value is set to zero; every asymptotic theorem operates
after positive stages. -/
noncomputable def radialTieAverageNN
    (rhat : ∀ n, Ω → Model Q X → Fin n → Real)
    (f_ref : ∀ n, Ω → Fin n → Model Q X)
    (y : Model Q X → Real)
    (n : Nat) (ω : Ω) (f : Model Q X) : Real := by
  by_cases hn : n > 0
  · exact radialTieAverage hn (rhat n ω f) (fun i => y (f_ref n ω i))
  · exact 0

@[simp] theorem radialTieAverageNN_of_pos
    (rhat : ∀ n, Ω → Model Q X → Fin n → Real)
    (f_ref : ∀ n, Ω → Fin n → Model Q X)
    (y : Model Q X → Real)
    (n : Nat) (ω : Ω) (f : Model Q X) (hn : n > 0) :
    radialTieAverageNN rhat f_ref y n ω f =
      radialTieAverage hn (rhat n ω f) (fun i => y (f_ref n ω i)) := by
  simp [radialTieAverageNN, hn]

lemma radialIndex_isArgmin {n : Nat} (hn : n > 0) (rhat : Fin n → Real) :
    IsArgmin rhat (radialIndex hn rhat) := by
  unfold radialIndex
  apply Classical.choose_spec

@[simp] lemma mem_radialMinimizers_iff {n : Nat} (hn : n > 0)
    (rhat : Fin n → Real) (i : Fin n) :
    i ∈ radialMinimizers hn rhat ↔ IsArgmin rhat i := by
  simp [radialMinimizers]

lemma radialMinimizers_nonempty {n : Nat} (hn : n > 0)
    (rhat : Fin n → Real) : (radialMinimizers hn rhat).Nonempty := by
  refine ⟨radialIndex hn rhat, ?_⟩
  rw [mem_radialMinimizers_iff]
  exact radialIndex_isArgmin hn rhat

/-- An average over all radial minimizers inherits a common absolute error
bound satisfied by every minimizer. -/
lemma abs_radialTieAverage_sub_le {n : Nat} (hn : n > 0)
    (rhat : Fin n → Real) (yref : Fin n → Real)
    (ytarget B : Real) (hB : 0 ≤ B)
    (hbound : ∀ i ∈ radialMinimizers hn rhat,
      |yref i - ytarget| ≤ B) :
    |radialTieAverage hn rhat yref - ytarget| ≤ B := by
  let S := radialMinimizers hn rhat
  have hS : S.Nonempty := by
    simpa [S] using radialMinimizers_nonempty hn rhat
  have hcardNat : 0 < S.card := Finset.card_pos.mpr hS
  have hcard : 0 < (S.card : Real) := by exact_mod_cast hcardNat
  have hsum :
      |∑ i ∈ S, (yref i - ytarget)| ≤ (S.card : Real) * B := by
    calc
      |∑ i ∈ S, (yref i - ytarget)|
          ≤ ∑ i ∈ S, |yref i - ytarget| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ S, B :=
        Finset.sum_le_sum fun i hi => hbound i (by simpa [S] using hi)
      _ = (S.card : Real) * B := by simp [mul_comm]
  have havg :
      (∑ i ∈ S, yref i) / (S.card : Real) - ytarget =
        (∑ i ∈ S, (yref i - ytarget)) / (S.card : Real) := by
    field_simp [ne_of_gt hcard]
    simp [Finset.sum_sub_distrib]
  rw [radialTieAverage]
  change |(∑ i ∈ S, yref i) / (S.card : Real) - ytarget| ≤ B
  rw [havg, abs_div, abs_of_pos hcard]
  exact (div_le_iff₀ hcard).2 (by simpa [mul_comm] using hsum)

/-- A minimizer of estimated radial distance is close in true radial distance
when every radial estimate is uniformly accurate and one reference covers the
target. -/
lemma trueDistance_radialMinimizer_le
    {n : Nat} (hn : n > 0)
    (rtrue rhat : Fin n → Real) (c ρ : Real)
    (hc : 0 ≤ c)
    (herr : ∀ i, |rhat i - rtrue i| ≤ c)
    (hcover : ∃ j, rtrue j ≤ ρ)
    {i : Fin n} (hi : i ∈ radialMinimizers hn rhat) :
    rtrue i ≤ ρ + 2 * c := by
  obtain ⟨j, hj⟩ := hcover
  have hmin : rhat i ≤ rhat j :=
    (mem_radialMinimizers_iff hn rhat i).1 hi j
  have hiLower : -c ≤ rhat i - rtrue i := (abs_le.mp (herr i)).1
  have hjUpper : rhat j - rtrue j ≤ c := (abs_le.mp (herr j)).2
  linarith

/-- Pointwise score error for the literal radial tie average.  Direct radial
concentration incurs `2c`, rather than the `4c` coordinate-concentration loss
in the original proof. -/
lemma radialTieAverage_pointwise_error
    {n : Nat} (hn : n > 0)
    (rtrue rhat : Fin n → Real)
    (c ρ γ : Real)
    (hc : 0 ≤ c) (hρ : 0 ≤ ρ) (hγ : 0 ≤ γ)
    (herr : ∀ i, |rhat i - rtrue i| ≤ c)
    (hcover : ∃ j, rtrue j ≤ ρ)
    (yref : Fin n → Real) (ytarget : Real)
    (hlip : ∀ i, |yref i - ytarget| ≤ γ * rtrue i) :
    |radialTieAverage hn rhat yref - ytarget| ≤ γ * (ρ + 2 * c) := by
  apply abs_radialTieAverage_sub_le hn rhat yref ytarget
    (γ * (ρ + 2 * c))
  · positivity
  · intro i hi
    exact (hlip i).trans (mul_le_mul_of_nonneg_left
      (trueDistance_radialMinimizer_le hn rtrue rhat c ρ hc herr hcover hi) hγ)

/-- Parameter choice for the radial engine.  This is the existing coordinate
parameter lemma applied to `c / 2`, since `4 · (c / 2) = 2c`. -/
lemma radial_parameter_choice
    (ε γ c : Real) (hε : 0 < ε) (hγ : 0 < γ)
    (hc : 0 ≤ c) (hcBound : c ≤ Real.sqrt ε / (4 * γ)) :
    (γ * (Real.sqrt ε / (2 * γ) + 2 * c)) ^ 2 ≤ ε := by
  have hcHalf : 0 ≤ c / 2 := by positivity
  have hcHalfBound : c / 2 ≤ Real.sqrt ε / (8 * γ) := by
    calc
      c / 2 ≤ (Real.sqrt ε / (4 * γ)) / 2 :=
        div_le_div_of_nonneg_right hcBound (by norm_num)
      _ = Real.sqrt ε / (8 * γ) := by
        field_simp [ne_of_gt hγ]
        ring
  have h := step6_parameter_choice ε γ hε hγ (c / 2) hcHalf hcHalfBound
  convert h using 1 <;> ring

/-- Radial-distance concentration and coverage imply tie-averaged MSE
convergence.  This theorem has no estimated global coordinate map. -/
theorem highProb_mse_radialTieAverage_of_subevents
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (μ : Nat → Measure Ω) (hμ : ∀ n, IsProbabilityMeasure (μ n))
    (ψ : Model Q X → Vec d)
    (rhat : ∀ n, Ω → Model Q X → Fin n → Real)
    (f_ref : ∀ n, Ω → Fin n → Model Q X)
    (y : Model Q X → Real)
    (γ : Real)
    (hlip : ∀ f f', |y f - y f'| ≤ γ * ‖ψ f - ψ f'‖)
    (hγ : 0 < γ)
    (c : Nat → Real) (hcZero : Tendsto c atTop (nhds 0))
    (hcNonneg : ∀ n, 0 ≤ c n)
    (E : Nat → Set Ω)
    (hEmeas : ∀ n, MeasurableSet (E n))
    (hEsub : ∀ n, E n ⊆ {ω | ∀ f i,
      |rhat n ω f i - ‖ψ (f_ref n ω i) - ψ f‖| ≤ c n})
    (hE : HighProbAtTop μ hμ E)
    (C : CoverageSubevents μ hμ ψ f_ref) :
    ∀ ε : Real, 0 < ε →
      HighProbAtTop μ hμ (fun n => {ω |
        MSE Pf y (fun f => radialTieAverageNN rhat f_ref y n ω f) ≤ ε}) := by
  intro ε hε
  let ρ : Real := Real.sqrt ε / (2 * γ)
  let cmax : Real := Real.sqrt ε / (4 * γ)
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hcmax : 0 < cmax := by dsimp [cmax]; positivity
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hcZero cmax hcmax
  have hinter : HighProbAtTop μ hμ (fun n => E n ∩ C.event ρ n) :=
    HighProbAtTop.inter hE (C.highProb ρ hρ) hEmeas (C.measurable ρ hρ)
  refine hinter.mono_eventually ?_
  filter_upwards [eventually_atTop.2 ⟨N + 1, fun n hn => hn⟩] with n hn
  intro ω hω
  have hnpos : n > 0 := by omega
  have hcLt : |c n| < cmax := by
    simpa [Real.dist_eq] using hN n (by omega)
  have hcLe : c n ≤ cmax := (le_abs_self (c n)).trans hcLt.le
  apply mse_le_of_pointwise_sq_error_le Pf y
    (fun f => radialTieAverageNN rhat f_ref y n ω f) ε hε.le
  intro f
  have herr := hEsub n hω.1 f
  have hcover := C.subset ρ hρ n hω.2 f
  have hpoint :
      |radialTieAverageNN rhat f_ref y n ω f - y f| ≤
        γ * (ρ + 2 * c n) := by
    rw [radialTieAverageNN_of_pos rhat f_ref y n ω f hnpos]
    exact radialTieAverage_pointwise_error hnpos
      (fun i => ‖ψ (f_ref n ω i) - ψ f‖) (rhat n ω f)
      (c n) ρ γ (hcNonneg n) hρ.le hγ.le herr hcover
      (fun i => y (f_ref n ω i)) (y f)
      (fun i => hlip (f_ref n ω i) f)
  have hsq :
      (radialTieAverageNN rhat f_ref y n ω f - y f) ^ 2 ≤
        (γ * (ρ + 2 * c n)) ^ 2 := by
    simpa using pow_le_pow_left₀ (abs_nonneg _) hpoint 2
  have hparam : (γ * (ρ + 2 * c n)) ^ 2 ≤ ε := by
    simpa [ρ, cmax] using radial_parameter_choice ε γ (c n)
      hε hγ (hcNonneg n) hcLe
  exact hsq.trans hparam

/-- Fixed-subset eventual query efficiency from radial concentration and
explicit coverage subevents. -/
theorem highProbQQueryEfficient_radialTieAverage_of_subevents
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (μ : Nat → Measure Ω) (hμ : ∀ n, IsProbabilityMeasure (μ n))
    (ψ : Model Q X → Vec d)
    (rhat : ∀ n, Ω → Model Q X → Fin n → Real)
    (f_ref : ∀ n, Ω → Fin n → Model Q X)
    (score : Model Q X → Finset Q → Real)
    (Qstar Qsub : Finset Q)
    (γ : Real)
    (hlip : ∀ f f',
      |score f Qstar - score f' Qstar| ≤ γ * ‖ψ f - ψ f'‖)
    (hγ : 0 < γ)
    (c : Nat → Real) (hcZero : Tendsto c atTop (nhds 0))
    (hcNonneg : ∀ n, 0 ≤ c n)
    (E : Nat → Set Ω)
    (hEmeas : ∀ n, MeasurableSet (E n))
    (hEsub : ∀ n, E n ⊆ {ω | ∀ f i,
      |rhat n ω f i - ‖ψ (f_ref n ω i) - ψ f‖| ≤ c n})
    (hE : HighProbAtTop μ hμ E)
    (C : CoverageSubevents μ hμ ψ f_ref)
    (hbase : 0 < MSE Pf (yFull score Qstar) (yQ score Qsub)) :
    HighProbQQueryEfficient (Q := Q) (X := X) μ hμ Pf sqLoss
      (yFull score Qstar)
      (fun n ω f => radialTieAverageNN rhat f_ref
        (yFull score Qstar) n ω f)
      (fun _ _ f => yQ score Qsub f) := by
  apply highProbQQueryEfficient_of_mse_atTop Pf μ hμ
    (yFull score Qstar) (yQ score Qsub)
    (fun n ω f => radialTieAverageNN rhat f_ref (yFull score Qstar) n ω f)
  · exact highProb_mse_radialTieAverage_of_subevents Pf μ hμ ψ rhat f_ref
      (yFull score Qstar) γ hlip hγ c hcZero hcNonneg
      E hEmeas hEsub hE C
  · exact hbase

/-- Compact perspective image, full support, and iid sampling discharge coverage
for the radial theorem. -/
theorem highProbQQueryEfficient_radialTieAverage_of_compact_iid_fullSupport
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (μ : Nat → Measure Ω) (hμ : ∀ n, IsProbabilityMeasure (μ n))
    (ψ : Model Q X → Vec d) (hψ : Measurable ψ)
    (hcompact : IsCompact (Set.range ψ))
    (hfull : PerspectiveFullSupport Pf ψ)
    (rhat : ∀ n, Ω → Model Q X → Fin n → Real)
    (f_ref : ∀ n, Ω → Fin n → Model Q X)
    (hiid : IIDReferenceSampler Pf μ f_ref)
    (score : Model Q X → Finset Q → Real)
    (Qstar Qsub : Finset Q)
    (γ : Real)
    (hlip : ∀ f f',
      |score f Qstar - score f' Qstar| ≤ γ * ‖ψ f - ψ f'‖)
    (hγ : 0 < γ)
    (c : Nat → Real) (hcZero : Tendsto c atTop (nhds 0))
    (hcNonneg : ∀ n, 0 ≤ c n)
    (E : Nat → Set Ω)
    (hEmeas : ∀ n, MeasurableSet (E n))
    (hEsub : ∀ n, E n ⊆ {ω | ∀ f i,
      |rhat n ω f i - ‖ψ (f_ref n ω i) - ψ f‖| ≤ c n})
    (hE : HighProbAtTop μ hμ E)
    (hbase : 0 < MSE Pf (yFull score Qstar) (yQ score Qsub)) :
    HighProbQQueryEfficient (Q := Q) (X := X) μ hμ Pf sqLoss
      (yFull score Qstar)
      (fun n ω f => radialTieAverageNN rhat f_ref
        (yFull score Qstar) n ω f)
      (fun _ _ f => yQ score Qsub f) := by
  let C := coverageSubevents_of_compact_iid_fullSupport
    Pf μ hμ ψ hψ hcompact hfull f_ref hiid
  exact highProbQQueryEfficient_radialTieAverage_of_subevents
    Pf μ hμ ψ rhat f_ref score Qstar Qsub γ hlip hγ
    c hcZero hcNonneg E hEmeas hEsub hE C hbase

end
