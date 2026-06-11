/-
Deterministic core of the Trosset–Priebe raw-stress MDS stability result.

This file proves the fully deterministic / geometric content underlying the
2024 paper's reliance on continuous multidimensional scaling:

* (a) the square root of raw stress is `1`-Lipschitz in the dissimilarity matrix
  (Minkowski inequality on `ℓ²` over the index set of pairs);
* (b) raw stress is translation invariant;
* (c) raw-stress minimizers exist (`MDS n d Δ` is nonempty), via coercivity on
  centered configurations and compactness in finite dimensions;
* (d) deterministic stability: if `frobSub (D k) Δ → 0` and each `z k` minimizes
  raw stress for `D k` (and is centered), a subsequence of `z` converges to a
  raw-stress minimizer for `Δ`, hence all pairwise distances converge.

These replace all of the ε–δ continuity-in-`Δ` bookkeeping behind the cited
Trosset–Priebe seam with self-contained Lean proofs.

Mathematical sources / citations:
- Trosset and Priebe, "Continuous multidimensional scaling" (cited as [23] /
  Theorem 2 in Acharyya et al., arXiv:2409.17308, Appendix A.1–A.2).
- Borg and Groenen, *Modern Multidimensional Scaling*, 2nd ed., Ch. 3 (raw
  stress).

Formalized by Claude Fable 5, per user-observed model label (claude-fable-5[1m]).
-/

import Acharyya2024.Common

open scoped BigOperators Topology RealInnerProductSpace InnerProductSpace
open Filter

namespace Acharyya2024.RawStress

open Acharyya2024

variable {n d : Nat}

/-! ## Basic structural lemmas -/

/--
Raw stress is a sum of squares, hence nonnegative.

Formalized by Claude Fable 5, per user-observed model label (claude-fable-5[1m]).
-/
theorem rawStress_nonneg (Δ : DisMat n) (z : Config n d) :
    0 ≤ rawStress n d Δ z := by
  unfold rawStress
  exact Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => sq_nonneg _

/--
Raw stress packaged as the squared `ℓ²` norm of the residual family over the set
of index pairs `Fin n × Fin n`.

Formalized by Claude Fable 5, per user-observed model label (claude-fable-5[1m]).
-/
theorem sqrt_rawStress_eq_norm (Δ : DisMat n) (z : Config n d) :
    Real.sqrt (rawStress n d Δ z)
      = ‖(WithLp.toLp 2
          (fun p : Fin n × Fin n => ‖z p.1 - z p.2‖ - Δ p.1 p.2) :
          EuclideanSpace ℝ (Fin n × Fin n))‖ := by
  rw [EuclideanSpace.norm_eq]
  unfold rawStress
  congr 1
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  simp [Real.norm_eq_abs, sq_abs]

/-! ## (a) √-stress is 1-Lipschitz in the dissimilarity -/

/--
The square root of raw stress is `1`-Lipschitz in the dissimilarity matrix:
`|√(rawStress Δ z) − √(rawStress Δ' z)| ≤ frobSub Δ Δ'`.

Viewing raw stress as a squared distance in `ℓ²(Fin n × Fin n)`, this is the
reverse triangle inequality `abs_norm_sub_norm_le`.

Formalized by Claude Fable 5, per user-observed model label (claude-fable-5[1m]).
-/
theorem abs_sqrt_rawStress_sub_le (Δ Δ' : DisMat n) (z : Config n d) :
    |Real.sqrt (rawStress n d Δ z) - Real.sqrt (rawStress n d Δ' z)|
      ≤ frobSub Δ Δ' := by
  set a : EuclideanSpace ℝ (Fin n × Fin n) :=
    WithLp.toLp 2 (fun p : Fin n × Fin n => ‖z p.1 - z p.2‖ - Δ p.1 p.2) with ha
  set b : EuclideanSpace ℝ (Fin n × Fin n) :=
    WithLp.toLp 2 (fun p : Fin n × Fin n => ‖z p.1 - z p.2‖ - Δ' p.1 p.2) with hb
  have hnorm_eq :
      |Real.sqrt (rawStress n d Δ z) - Real.sqrt (rawStress n d Δ' z)|
        = |‖a‖ - ‖b‖| := by
    rw [sqrt_rawStress_eq_norm Δ z, sqrt_rawStress_eq_norm Δ' z]
  rw [hnorm_eq]
  refine (abs_norm_sub_norm_le a b).trans ?_
  -- `a - b` has coordinates `Δ' p − Δ p`; its norm is `frobSub Δ Δ'`.
  have hab :
      ‖a - b‖ = frobSub Δ Δ' := by
    rw [EuclideanSpace.norm_eq, frobSub, frob, frobSq]
    congr 1
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    have hcoord : (a - b) (i, j) = Δ' i j - Δ i j := by
      simp only [ha, hb]
      show (WithLp.toLp 2 (fun p : Fin n × Fin n => ‖z p.1 - z p.2‖ - Δ p.1 p.2)
              - WithLp.toLp 2 (fun p : Fin n × Fin n => ‖z p.1 - z p.2‖ - Δ' p.1 p.2))
            (i, j) = _
      simp
    rw [hcoord, Real.norm_eq_abs, sq_abs]
    ring_nf
  rw [hab]

/-- The Frobenius distance between dissimilarity matrices is symmetric. -/
theorem frobSub_comm (A B : DisMat n) : frobSub A B = frobSub B A := by
  unfold frobSub frob frobSq
  congr 1
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  ring

/-! ## (b) Translation invariance -/

/--
Raw stress depends only on the pairwise differences of a configuration, so it is
invariant under translating every point by a constant vector.

Formalized by Claude Fable 5, per user-observed model label (claude-fable-5[1m]).
-/
theorem rawStress_translate (Δ : DisMat n) (z : Config n d)
    (c : EuclideanSpace ℝ (Fin d)) :
    rawStress n d Δ (fun i => z i - c) = rawStress n d Δ z := by
  unfold rawStress
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  have : (z i - c) - (z j - c) = z i - z j := by abel
  rw [this]

/-! ## (c) Existence of minimizers -/

/-- Each squared residual term is bounded by the whole raw-stress sum. -/
private theorem term_le_rawStress (Δ : DisMat n) (z : Config n d) (i j : Fin n) :
    (‖z i - z j‖ - Δ i j)^2 ≤ rawStress n d Δ z := by
  unfold rawStress
  refine (Finset.single_le_sum (f := fun j' => (‖z i - z j'‖ - Δ i j')^2)
    (fun j' _ => sq_nonneg _) (Finset.mem_univ j)).trans ?_
  exact Finset.single_le_sum (f := fun i' => ∑ j', (‖z i' - z j'‖ - Δ i' j')^2)
    (fun i' _ => Finset.sum_nonneg (fun j' _ => sq_nonneg _)) (Finset.mem_univ i)

/-- Continuity of raw stress in the configuration (a finite sum of continuous
maps in the Pi type `Config n d`). -/
theorem continuous_rawStress (Δ : DisMat n) :
    Continuous (rawStress n d Δ) := by
  unfold rawStress
  refine continuous_finset_sum _ (fun i _ =>
    continuous_finset_sum _ (fun j _ => ?_))
  exact (((continuous_apply i).sub (continuous_apply j)).norm.sub continuous_const).pow 2

/-- The coercivity radius `R₀ := √(rawStress Δ z₀) + ∑ᵢⱼ |Δ i j|` (with `z₀` the
zero configuration), which bounds the pairwise distances on the sublevel set
`{z | rawStress Δ z ≤ rawStress Δ z₀}`. -/
private noncomputable def coRadius (Δ : DisMat n) : ℝ :=
  Real.sqrt (rawStress n d Δ (fun _ : Fin n => (0 : Rvec d)))
    + ∑ i : Fin n, ∑ j : Fin n, |Δ i j|

private theorem coRadius_nonneg (Δ : DisMat n) : 0 ≤ coRadius (d := d) Δ := by
  unfold coRadius
  have h1 : 0 ≤ Real.sqrt (rawStress n d Δ (fun _ : Fin n => (0 : Rvec d))) :=
    Real.sqrt_nonneg _
  have h2 : 0 ≤ ∑ i : Fin n, ∑ j : Fin n, |Δ i j| :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  linarith

/-- A general sublevel pairwise-distance bound: if `rawStress Δ z ≤ s`, then every
pairwise distance is bounded by `√s + ∑ᵢⱼ |Δ i j|`. -/
private theorem pairDist_le_of_rawStress_le (Δ : DisMat n) (z : Config n d)
    {s : ℝ} (hz : rawStress n d Δ z ≤ s) (i j : Fin n) :
    ‖z i - z j‖ ≤ Real.sqrt s + ∑ i' : Fin n, ∑ j' : Fin n, |Δ i' j'| := by
  have hterm : (‖z i - z j‖ - Δ i j)^2 ≤ s :=
    (term_le_rawStress Δ z i j).trans hz
  have habs : |‖z i - z j‖ - Δ i j| ≤ Real.sqrt s := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt hterm
  have hΔ_le : |Δ i j| ≤ ∑ i' : Fin n, ∑ j' : Fin n, |Δ i' j'| := by
    refine (Finset.single_le_sum (f := fun j' => |Δ i j'|)
      (fun j' _ => abs_nonneg _) (Finset.mem_univ j)).trans ?_
    exact Finset.single_le_sum (f := fun i' => ∑ j', |Δ i' j'|)
      (fun i' _ => Finset.sum_nonneg (fun j' _ => abs_nonneg _)) (Finset.mem_univ i)
  have hsplit : ‖z i - z j‖ - Δ i j ≤ Real.sqrt s := (le_abs_self _).trans habs
  have hΔ_self : Δ i j ≤ |Δ i j| := le_abs_self _
  linarith

/-- On the sublevel set, every pairwise distance is bounded by `coRadius`. -/
private theorem pairDist_le_coRadius (Δ : DisMat n) (z : Config n d)
    (hz : rawStress n d Δ z
        ≤ rawStress n d Δ (fun _ : Fin n => (0 : Rvec d)))
    (i j : Fin n) :
    ‖z i - z j‖ ≤ coRadius (d := d) Δ :=
  pairDist_le_of_rawStress_le Δ z hz i j

/-- Centering map: subtract the mean. -/
private noncomputable def center (z : Config n d) : Config n d :=
  fun i => z i - (n : ℝ)⁻¹ • ∑ j : Fin n, z j

/-- Centering does not change raw stress. -/
private theorem rawStress_center (Δ : DisMat n) (z : Config n d) :
    rawStress n d Δ (center z) = rawStress n d Δ z :=
  rawStress_translate Δ z _

/-- The centered configuration has zero coordinate sum (for `n ≠ 0`). -/
private theorem sum_center_eq_zero (hn : n ≠ 0) (z : Config n d) :
    ∑ i : Fin n, center z i = 0 := by
  unfold center
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hn),
    one_smul, sub_self]

/-- A centered configuration whose pairwise distances are bounded by `R` has each
point bounded by `R` (for `n ≠ 0`). -/
private theorem norm_le_of_centered (hn : n ≠ 0) (w : Config n d) {R : ℝ}
    (hcent : ∑ i : Fin n, w i = 0)
    (hpair : ∀ i j, ‖w i - w j‖ ≤ R) (i : Fin n) :
    ‖w i‖ ≤ R := by
  have hrep : w i = (n : ℝ)⁻¹ • ∑ j : Fin n, (w i - w j) := by
    rw [Finset.sum_sub_distrib, hcent, sub_zero, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
      inv_mul_cancel₀ (by exact_mod_cast hn), one_smul]
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := Nat.pos_of_ne_zero hn
    exact_mod_cast this
  rw [hrep, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hsum_le : ‖∑ j : Fin n, (w i - w j)‖ ≤ (n : ℝ) * R := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ j : Fin n, ‖w i - w j‖
        ≤ ∑ _j : Fin n, R := Finset.sum_le_sum fun j _ => hpair i j
      _ = (n : ℝ) * R := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc (n : ℝ)⁻¹ * ‖∑ j : Fin n, (w i - w j)‖
      ≤ (n : ℝ)⁻¹ * ((n : ℝ) * R) :=
        mul_le_mul_of_nonneg_left hsum_le (by positivity)
    _ = R := by rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hnpos), one_mul]

/--
Raw-stress minimizers exist: `MDS n d Δ` is nonempty for every dissimilarity
matrix `Δ`.

Strategy: minimize over the compact box `K = {w | ∀ i, ‖w i‖ ≤ R₀}` of centered
configurations (`R₀ = coRadius Δ`), where raw stress is continuous; translation
invariance and coercivity upgrade the local minimizer over `K` to a global one.

Formalized by Claude Fable 5, per user-observed model label (claude-fable-5[1m]).
-/
theorem mds_nonempty : ∀ Δ : DisMat n, (MDS n d Δ).Nonempty := by
  intro Δ
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · -- `n = 0`: raw stress is the empty sum, identically zero; every config wins.
    subst hn0
    refine ⟨fun i => i.elim0, fun z' => ?_⟩
    simp [rawStress]
  have hn : n ≠ 0 := hnpos.ne'
  set z₀ : Config n d := fun _ : Fin n => (0 : Rvec d) with hz₀
  set R₀ : ℝ := coRadius (d := d) Δ with hR₀
  have hR₀_nonneg : 0 ≤ R₀ := coRadius_nonneg Δ
  -- The compact candidate set.
  set K : Set (Config n d) :=
    Set.pi Set.univ (fun _ : Fin n => Metric.closedBall (0 : Rvec d) R₀) with hK
  have hK_compact : IsCompact K := by
    rw [hK]
    exact isCompact_univ_pi (fun _ => isCompact_closedBall _ _)
  have hK_ne : K.Nonempty := by
    refine ⟨z₀, ?_⟩
    intro i _
    simp only [hz₀, Metric.mem_closedBall, dist_zero_right, norm_zero]
    exact hR₀_nonneg
  -- A minimizer of raw stress over `K`.
  obtain ⟨w, hwK, hwmin⟩ :=
    hK_compact.exists_isMinOn hK_ne (continuous_rawStress Δ).continuousOn
  rw [isMinOn_iff] at hwmin
  -- `z₀ ∈ K`, so `rawStress Δ w ≤ rawStress Δ z₀`.
  have hz₀K : z₀ ∈ K := by
    intro i _
    simp only [hz₀, Metric.mem_closedBall, dist_zero_right, norm_zero]
    exact hR₀_nonneg
  have hw_le_z₀ : rawStress n d Δ w ≤ rawStress n d Δ z₀ := hwmin z₀ hz₀K
  -- `w` is a global minimizer.
  refine ⟨w, fun z' => ?_⟩
  by_cases hz' : rawStress n d Δ z₀ ≤ rawStress n d Δ z'
  · exact hw_le_z₀.trans hz'
  · -- Then `rawStress Δ z' < rawStress Δ z₀`, so `center z' ∈ K`.
    push_neg at hz'
    have hcz'_le : rawStress n d Δ (center z') ≤ rawStress n d Δ z₀ := by
      rw [rawStress_center]; exact hz'.le
    have hcent : ∑ i : Fin n, center z' i = 0 := sum_center_eq_zero hn z'
    have hpair : ∀ i j, ‖center z' i - center z' j‖ ≤ R₀ := fun i j =>
      pairDist_le_coRadius Δ (center z') hcz'_le i j
    have hcz'K : center z' ∈ K := by
      intro i _
      simp only [Metric.mem_closedBall, dist_zero_right]
      exact norm_le_of_centered hn (center z') hcent hpair i
    calc rawStress n d Δ w
        ≤ rawStress n d Δ (center z') := hwmin (center z') hcz'K
      _ = rawStress n d Δ z' := rawStress_center Δ z'

/-! ## (d) Deterministic stability -/

/--
The square root of raw stress, evaluated at a fixed configuration `z`, is
`1`-Lipschitz in the dissimilarity matrix, in the directed form used for the
stability chain.

Formalized by Claude Fable 5, per user-observed model label (claude-fable-5[1m]).
-/
private theorem sqrt_rawStress_le_add (Δ Δ' : DisMat n) (z : Config n d) :
    Real.sqrt (rawStress n d Δ z)
      ≤ Real.sqrt (rawStress n d Δ' z) + frobSub Δ Δ' := by
  have h := abs_sqrt_rawStress_sub_le Δ Δ' z
  have h2 :
      Real.sqrt (rawStress n d Δ z) - Real.sqrt (rawStress n d Δ' z)
        ≤ frobSub Δ Δ' := (le_abs_self _).trans h
  linarith

/--
Deterministic stability of raw-stress MDS under convergence of the dissimilarity
matrices.

If `frobSub (D k) Δ → 0`, each `z k` minimizes raw stress for `D k`, and each
`z k` is centered (`∑ i, z k i = 0`), then a subsequence of `z` converges to some
configuration `ψ` that minimizes raw stress for the limiting matrix `Δ`.

Hypothesis choice: we take the honest centering normalization `hcent`
(`∑ i, z k i = 0`) — this matches the paper's freedom to center MDS output — and
derive the boundedness needed for compactness internally from minimality plus the
`√`-stress Lipschitz bound (a). (The alternative honest hypothesis would be a bare
uniform bound `∃ R, ∀ k i, ‖z k i‖ ≤ R`; centering supplies exactly such an `R`.)

Mathematical source/citation: Trosset & Priebe, "Continuous multidimensional
scaling" (cited as Theorem 2 in Acharyya et al., arXiv:2409.17308, Appendix
A.1–A.2).

Formalized by Claude Fable 5, per user-observed model label (claude-fable-5[1m]).
-/
theorem exists_subseq_tendsto_mds
    (D : Nat → DisMat n) (Δ : DisMat n)
    (z : Nat → Config n d)
    (hz : ∀ k, z k ∈ MDS n d (D k))
    (hcent : ∀ k, ∑ i : Fin n, z k i = 0)
    (hD : Tendsto (fun k => frobSub (D k) Δ) atTop (𝓝 0)) :
    ∃ u : Nat → Nat, StrictMono u ∧ ∃ ψ : Config n d, ψ ∈ MDS n d Δ ∧
      Tendsto (fun t => z (u t)) atTop (𝓝 ψ) := by
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · -- `n = 0`: every configuration minimizes the empty-sum raw stress.
    subst hn0
    refine ⟨id, strictMono_id, z 0, ?_, ?_⟩
    · intro z'; simp [rawStress]
    · -- in `Config 0 d` everything is equal to `z 0`.
      have hconst : (fun t => z (id t)) = fun _ : Nat => z 0 := by
        funext t; funext i; exact i.elim0
      rw [hconst]; exact tendsto_const_nhds
  have hn : n ≠ 0 := hnpos.ne'
  set z₀ : Config n d := fun _ : Fin n => (0 : Rvec d) with hz₀
  -- The uniform stress bound `C` and the box radius `R`.
  set sBase : ℝ := Real.sqrt (rawStress n d Δ z₀) + 2 with hsBase
  set C : ℝ := sBase ^ 2 with hC
  set sumAbsΔ : ℝ := ∑ i : Fin n, ∑ j : Fin n, |Δ i j| with hsumAbsΔ
  set R : ℝ := Real.sqrt C + sumAbsΔ with hR
  have hR_nonneg : 0 ≤ R := by
    have h1 : 0 ≤ Real.sqrt C := Real.sqrt_nonneg _
    have h2 : 0 ≤ sumAbsΔ :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
    rw [hR]; linarith
  -- From `frobSub (D k) Δ → 0`, eventually `frobSub (D k) Δ ≤ 1`, giving `≤ C`.
  obtain ⟨N, hN⟩ : ∃ N, ∀ k ≥ N, frobSub (D k) Δ ≤ 1 := by
    have hev : ∀ᶠ k in atTop, frobSub (D k) Δ < 1 :=
      hD.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))
    rw [eventually_atTop] at hev
    obtain ⟨N, hNlt⟩ := hev
    exact ⟨N, fun k hk => (hNlt k hk).le⟩
  -- Each `z k` (k ≥ N) lies in the compact box `K`.
  have hstress_le : ∀ k ≥ N, rawStress n d Δ (z k) ≤ C := by
    intro k hk
    have hmin : rawStress n d (D k) (z k) ≤ rawStress n d (D k) z₀ := hz k z₀
    -- `√(rawStress Δ (z k)) ≤ √(rawStress (D k) (z k)) + frobSub (D k) Δ`
    have h1 : Real.sqrt (rawStress n d Δ (z k))
        ≤ Real.sqrt (rawStress n d (D k) (z k)) + frobSub (D k) Δ := by
      rw [frobSub_comm (D k) Δ]; exact sqrt_rawStress_le_add Δ (D k) (z k)
    -- `√(rawStress (D k) (z k)) ≤ √(rawStress (D k) z₀)`
    have h2 : Real.sqrt (rawStress n d (D k) (z k))
        ≤ Real.sqrt (rawStress n d (D k) z₀) :=
      Real.sqrt_le_sqrt hmin
    -- `√(rawStress (D k) z₀) ≤ √(rawStress Δ z₀) + frobSub (D k) Δ`
    have h3 : Real.sqrt (rawStress n d (D k) z₀)
        ≤ Real.sqrt (rawStress n d Δ z₀) + frobSub (D k) Δ :=
      sqrt_rawStress_le_add (D k) Δ z₀
    have hfb : frobSub (D k) Δ ≤ 1 := hN k hk
    have hchain : Real.sqrt (rawStress n d Δ (z k)) ≤ sBase := by
      rw [hsBase]; linarith
    have hsBase_nonneg : 0 ≤ sBase := by
      rw [hsBase]; positivity
    -- square both sides
    calc rawStress n d Δ (z k)
        = (Real.sqrt (rawStress n d Δ (z k)))^2 :=
          (Real.sq_sqrt (rawStress_nonneg Δ (z k))).symm
      _ ≤ sBase ^ 2 := by
          apply sq_le_sq'
          · linarith [Real.sqrt_nonneg (rawStress n d Δ (z k))]
          · exact hchain
      _ = C := hC.symm
  set K : Set (Config n d) :=
    Set.pi Set.univ (fun _ : Fin n => Metric.closedBall (0 : Rvec d) R) with hK
  have hK_compact : IsCompact K := by
    rw [hK]; exact isCompact_univ_pi (fun _ => isCompact_closedBall _ _)
  -- The reindexed sequence `y t := z (t + N)` lives in `K`.
  set y : Nat → Config n d := fun t => z (t + N) with hy
  have hyK : ∀ t, y t ∈ K := by
    intro t i _
    simp only [Metric.mem_closedBall, dist_zero_right]
    have hk : t + N ≥ N := Nat.le_add_left N t
    have hsl : rawStress n d Δ (y t) ≤ C := hstress_le (t + N) hk
    have hcentk : ∑ i : Fin n, y t i = 0 := hcent (t + N)
    have hpair : ∀ a b, ‖y t a - y t b‖ ≤ R := by
      intro a b
      have := pairDist_le_of_rawStress_le Δ (y t) hsl a b
      rw [hR, ← hsumAbsΔ] at *
      exact this
    exact norm_le_of_centered hn (y t) hcentk hpair i
  -- Extract a convergent subsequence of `y` inside `K`.
  obtain ⟨ψ, hψK, φ, hφ_mono, hφ_tendsto⟩ := hK_compact.tendsto_subseq hyK
  refine ⟨fun t => φ t + N, ?_, ψ, ?_, ?_⟩
  · exact fun a b hab => by simpa using Nat.add_lt_add_right (hφ_mono hab) N
  · -- `ψ` minimizes raw stress for `Δ`.
    intro z'
    -- `rawStress Δ ψ = lim rawStress Δ (y (φ t))` by continuity.
    have hcont_tendsto :
        Tendsto (fun t => rawStress n d Δ (y (φ t))) atTop
          (𝓝 (rawStress n d Δ ψ)) :=
      ((continuous_rawStress Δ).tendsto ψ).comp hφ_tendsto
    -- The squared upper bound, tending to `rawStress Δ z'`.
    set g : Nat → ℝ := fun t =>
      (Real.sqrt (rawStress n d Δ z') + 2 * frobSub (D (φ t + N)) Δ)^2 with hg
    have hg_tendsto : Tendsto g atTop (𝓝 (rawStress n d Δ z')) := by
      have hfrob_tendsto :
          Tendsto (fun t => frobSub (D (φ t + N)) Δ) atTop (𝓝 0) := by
        have hmono : StrictMono (fun t => φ t + N) :=
          fun a b hab => by simpa using Nat.add_lt_add_right (hφ_mono hab) N
        exact hD.comp hmono.tendsto_atTop
      have hlim :
          Tendsto (fun t => Real.sqrt (rawStress n d Δ z') + 2 * frobSub (D (φ t + N)) Δ)
            atTop (𝓝 (Real.sqrt (rawStress n d Δ z') + 2 * 0)) :=
        tendsto_const_nhds.add ((tendsto_const_nhds.mul hfrob_tendsto))
      have hsq := hlim.pow 2
      simpa [hg, mul_zero, add_zero, Real.sq_sqrt (rawStress_nonneg Δ z')] using hsq
    -- Pointwise: `rawStress Δ (y (φ t)) ≤ g t`.
    have hpt : ∀ t, rawStress n d Δ (y (φ t)) ≤ g t := by
      intro t
      have hmin : rawStress n d (D (φ t + N)) (y (φ t))
          ≤ rawStress n d (D (φ t + N)) z' := hz (φ t + N) z'
      have h1 : Real.sqrt (rawStress n d Δ (y (φ t)))
          ≤ Real.sqrt (rawStress n d (D (φ t + N)) (y (φ t)))
            + frobSub (D (φ t + N)) Δ := by
        rw [frobSub_comm (D (φ t + N)) Δ]
        exact sqrt_rawStress_le_add Δ (D (φ t + N)) (y (φ t))
      have h2 : Real.sqrt (rawStress n d (D (φ t + N)) (y (φ t)))
          ≤ Real.sqrt (rawStress n d (D (φ t + N)) z') :=
        Real.sqrt_le_sqrt hmin
      have h3 : Real.sqrt (rawStress n d (D (φ t + N)) z')
          ≤ Real.sqrt (rawStress n d Δ z') + frobSub (D (φ t + N)) Δ :=
        sqrt_rawStress_le_add (D (φ t + N)) Δ z'
      have hchain : Real.sqrt (rawStress n d Δ (y (φ t)))
          ≤ Real.sqrt (rawStress n d Δ z') + 2 * frobSub (D (φ t + N)) Δ := by
        linarith
      have hbase_nonneg :
          0 ≤ Real.sqrt (rawStress n d Δ z') + 2 * frobSub (D (φ t + N)) Δ := by
        have hfrob_nonneg : 0 ≤ frobSub (D (φ t + N)) Δ := by
          rw [frobSub, frob]; exact Real.sqrt_nonneg _
        have := Real.sqrt_nonneg (rawStress n d Δ z'); linarith
      calc rawStress n d Δ (y (φ t))
          = (Real.sqrt (rawStress n d Δ (y (φ t))))^2 :=
            (Real.sq_sqrt (rawStress_nonneg Δ (y (φ t)))).symm
        _ ≤ g t := by
            rw [hg]
            apply sq_le_sq'
            · linarith [Real.sqrt_nonneg (rawStress n d Δ (y (φ t)))]
            · exact hchain
    -- Pass to the limit.
    exact le_of_tendsto_of_tendsto hcont_tendsto hg_tendsto
      (Eventually.of_forall hpt)
  · -- The subsequence converges to `ψ`.
    have : (fun t => z (φ t + N)) = (fun t => y (φ t)) := by funext t; rfl
    rw [this]; exact hφ_tendsto

/--
Pairwise distances of the stable subsequence converge to those of the limiting
configuration.

This is the direct geometric consequence of `exists_subseq_tendsto_mds`: the
paper works with pairwise dissimilarities, and these converge along the extracted
subsequence.

Formalized by Claude Fable 5, per user-observed model label (claude-fable-5[1m]).
-/
theorem pairDist_tendsto
    (D : Nat → DisMat n) (Δ : DisMat n)
    (z : Nat → Config n d)
    (hz : ∀ k, z k ∈ MDS n d (D k))
    (hcent : ∀ k, ∑ i : Fin n, z k i = 0)
    (hD : Tendsto (fun k => frobSub (D k) Δ) atTop (𝓝 0)) :
    ∃ u : Nat → Nat, StrictMono u ∧ ∃ ψ : Config n d, ψ ∈ MDS n d Δ ∧
      ∀ i j : Fin n,
        Tendsto (fun t => pairDist (z (u t)) i j) atTop (𝓝 (pairDist ψ i j)) := by
  obtain ⟨u, hu_mono, ψ, hψ_mds, hψ_tendsto⟩ :=
    exists_subseq_tendsto_mds D Δ z hz hcent hD
  refine ⟨u, hu_mono, ψ, hψ_mds, fun i j => ?_⟩
  -- Per-coordinate convergence from the Pi-type convergence.
  rw [tendsto_pi_nhds] at hψ_tendsto
  have hi : Tendsto (fun t => z (u t) i) atTop (𝓝 (ψ i)) := hψ_tendsto i
  have hj : Tendsto (fun t => z (u t) j) atTop (𝓝 (ψ j)) := hψ_tendsto j
  have hsub : Tendsto (fun t => z (u t) i - z (u t) j) atTop (𝓝 (ψ i - ψ j)) :=
    hi.sub hj
  simpa [pairDist] using hsub.norm

end Acharyya2024.RawStress
