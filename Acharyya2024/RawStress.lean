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

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/

import Acharyya2024.Common
import ForMathlib.Topology.ApproxMinimizer

open scoped BigOperators Topology RealInnerProductSpace InnerProductSpace
open Filter

namespace Acharyya2024.RawStress

open Acharyya2024

variable {n d : Nat}

/-! ## Basic structural lemmas -/

/--
Raw stress is a sum of squares, hence nonnegative.

Internal helper / structural step: raw stress is the objective in Eq. (1) of the
paper (the sum over pairs of squared mismatches between embedded distances and
target dissimilarities); this records that that objective is `≥ 0`.

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
theorem rawStress_nonneg (Δ : DisMat n) (z : Config n d) :
    -- Δ : target dissimilarity matrix; z : candidate configuration of n points in ℝ^d
    -- Conclusion: the raw-stress objective of `z` against `Δ` is nonnegative.
    0 ≤ rawStress n d Δ z := by
  unfold rawStress
  exact Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => sq_nonneg _

/--
Raw stress packaged as the squared `ℓ²` norm of the residual family over the set
of index pairs `Fin n × Fin n`.

Internal helper / structural step: rewrites `√(raw stress)` as a genuine Euclidean
norm so that triangle inequalities apply. The residual at pair `(i, i')` is
`‖z i − z i'‖ − Δ i i'`, the per-pair mismatch from Eq. (1).

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
theorem sqrt_rawStress_eq_norm (Δ : DisMat n) (z : Config n d) :
    -- Conclusion: √(rawStress) equals the ℓ²-norm of the residual family indexed by pairs.
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

Internal helper / step of the proof: this Lipschitz-in-`Δ` bound is the engine
behind the stability arguments (it transfers minimality for one dissimilarity
matrix to a near-minimality for a nearby one). Compare Remark 2 / Theorem 2 of
[23], where stress is controlled via the Frobenius distance of distance matrices.

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
theorem abs_sqrt_rawStress_sub_le (Δ Δ' : DisMat n) (z : Config n d) :
    -- Δ, Δ' : two target dissimilarity matrices; z : a fixed configuration
    -- Conclusion: √(stress) at fixed `z` changes by at most the Frobenius distance ‖Δ − Δ'‖_F.
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

/-- The Frobenius distance between dissimilarity matrices is symmetric:
`‖A − B‖_F = ‖B − A‖_F`. Internal helper / bookkeeping step. -/
theorem frobSub_comm (A B : DisMat n) :
    -- Conclusion: the Frobenius distance is symmetric in its two arguments.
    frobSub A B = frobSub B A := by
  unfold frobSub frob frobSq
  congr 1
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  ring

/-! ## (b) Translation invariance -/

/--
Raw stress depends only on the pairwise differences of a configuration, so it is
invariant under translating every point by a constant vector.

Paper correspondence: this is the translation part of the affine invariance of
the raw-stress minimizer noted in Remark 1 ("an affine transformation upon a
minimizer gives another minimizer"); here only translations `z ↦ z − c` are
treated (orthogonal/affine invariance is not formalized in this lemma).

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
theorem rawStress_translate (Δ : DisMat n) (z : Config n d)
    (c : EuclideanSpace ℝ (Fin d)) :  -- c : the constant translation vector
    -- Conclusion: translating every point of `z` by `c` leaves raw stress unchanged.
    rawStress n d Δ (fun i => z i - c) = rawStress n d Δ z := by
  unfold rawStress
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  have : (z i - c) - (z j - c) = z i - z j := by abel
  rw [this]

/-! ## (c) Existence of minimizers -/

/-- Each squared residual term is bounded by the whole raw-stress sum.
Internal helper / step toward the existence-of-minimizers proof (used to bound
pairwise distances on sublevel sets). -/
private theorem term_le_rawStress (Δ : DisMat n) (z : Config n d) (i j : Fin n) :
    -- Conclusion: a single pair's squared residual is ≤ the total raw stress.
    (‖z i - z j‖ - Δ i j)^2 ≤ rawStress n d Δ z := by
  unfold rawStress
  refine (Finset.single_le_sum (f := fun j' => (‖z i - z j'‖ - Δ i j')^2)
    (fun j' _ => sq_nonneg _) (Finset.mem_univ j)).trans ?_
  exact Finset.single_le_sum (f := fun i' => ∑ j', (‖z i' - z j'‖ - Δ i' j')^2)
    (fun i' _ => Finset.sum_nonneg (fun j' _ => sq_nonneg _)) (Finset.mem_univ i)

/-- An exact realization has zero raw stress. -/
theorem rawStress_eq_zero_of_realizes {Δ : DisMat n} {z : Config n d}
    (hz : RealizesDissimilarity z Δ) :
    rawStress n d Δ z = 0 := by
  unfold rawStress
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  rw [← hz i j]
  simp [pairDist]

/-- Every exact realization is a raw-stress minimizer. -/
theorem mem_MDS_of_realizes {Δ : DisMat n} {z : Config n d}
    (hz : RealizesDissimilarity z Δ) :
    z ∈ MDS n d Δ := by
  intro z'
  rw [rawStress_eq_zero_of_realizes hz]
  exact rawStress_nonneg Δ z'

/--
If the target dissimilarities admit one exact realization, every raw-stress
minimizer exactly realizes the same dissimilarities.
-/
theorem realizes_of_mem_MDS_of_exists_realizes {Δ : DisMat n} {z : Config n d}
    (hexact : ∃ z₀ : Config n d, RealizesDissimilarity z₀ Δ)
    (hz : z ∈ MDS n d Δ) :
    RealizesDissimilarity z Δ := by
  obtain ⟨z₀, hz₀⟩ := hexact
  have hz_le_zero : rawStress n d Δ z ≤ 0 := by
    calc
      rawStress n d Δ z ≤ rawStress n d Δ z₀ := hz z₀
      _ = 0 := rawStress_eq_zero_of_realizes hz₀
  have hz_zero : rawStress n d Δ z = 0 :=
    le_antisymm hz_le_zero (rawStress_nonneg Δ z)
  intro i j
  have hterm : (‖z i - z j‖ - Δ i j) ^ 2 ≤ 0 := by
    simpa [hz_zero] using term_le_rawStress Δ z i j
  have hresidual : ‖z i - z j‖ - Δ i j = 0 := by
    nlinarith [sq_nonneg (‖z i - z j‖ - Δ i j)]
  change ‖z i - z j‖ = Δ i j
  linarith

/-- Continuity of raw stress in the configuration (a finite sum of continuous
maps in the Pi type `Config n d`). Internal helper / step of the proof: supplies
the continuity needed to extract minimizers from compact sets.

Note: this continuity is over the configuration `z`, holding `Δ` fixed; it is an
analytic ingredient (not an explicit hypothesis of the paper). -/
theorem continuous_rawStress (Δ : DisMat n) :
    -- Conclusion: `z ↦ rawStress Δ z` is continuous on the space of configurations.
    Continuous (rawStress n d Δ) := by
  unfold rawStress
  refine continuous_finsetSum _ (fun i _ =>
    continuous_finsetSum _ (fun j _ => ?_))
  exact (((continuous_apply i).sub (continuous_apply j)).norm.sub continuous_const).pow 2

/-- The coercivity radius `R₀ := √(rawStress Δ z₀) + ∑ᵢⱼ |Δ i j|` (with `z₀` the
zero configuration), which bounds the pairwise distances on the sublevel set
`{z | rawStress Δ z ≤ rawStress Δ z₀}`.

Internal helper / construction: this is an explicit, computable radius used to
confine the search for a minimizer to a compact box (coercivity). It plays the
role of the bounded set `Yₙ` from Remark 2 / Theorem 2 of [23], here phrased
directly in terms of configurations rather than distance matrices. -/
private noncomputable def coRadius (Δ : DisMat n) : ℝ :=
  Real.sqrt (rawStress n d Δ (fun _ : Fin n => (0 : Rvec d)))
    + ∑ i : Fin n, ∑ j : Fin n, |Δ i j|

/-- The coercivity radius is nonnegative. Internal helper / bookkeeping. -/
private theorem coRadius_nonneg (Δ : DisMat n) :
    -- Conclusion: the coercivity radius is `≥ 0`.
    0 ≤ coRadius (d := d) Δ := by
  unfold coRadius
  have h1 : 0 ≤ Real.sqrt (rawStress n d Δ (fun _ : Fin n => (0 : Rvec d))) :=
    Real.sqrt_nonneg _
  have h2 : 0 ≤ ∑ i : Fin n, ∑ j : Fin n, |Δ i j| :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  linarith

/-- A general sublevel pairwise-distance bound: if `rawStress Δ z ≤ s`, then every
pairwise distance is bounded by `√s + ∑ᵢⱼ |Δ i j|`.

Internal helper / step of the proof: this is the coercivity estimate — small
stress forces bounded pairwise distances — used both for minimizer existence and
for compactness in the stability arguments. -/
private theorem pairDist_le_of_rawStress_le (Δ : DisMat n) (z : Config n d)
    {s : ℝ} (hz : rawStress n d Δ z ≤ s) (i j : Fin n) :  -- hz : `z` lies in the sublevel set {stress ≤ s}
    -- Conclusion: each pairwise distance is bounded by `√s` plus the total of `|Δ|` entries.
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

/-- On the sublevel set, every pairwise distance is bounded by `coRadius`.
Internal helper / specialization of `pairDist_le_of_rawStress_le` to the level of
the zero configuration. -/
private theorem pairDist_le_coRadius (Δ : DisMat n) (z : Config n d)
    -- hz : `z` does no worse than the all-zero configuration
    (hz : rawStress n d Δ z
        ≤ rawStress n d Δ (fun _ : Fin n => (0 : Rvec d)))
    (i j : Fin n) :
    -- Conclusion: each pairwise distance of `z` is bounded by the coercivity radius.
    ‖z i - z j‖ ≤ coRadius (d := d) Δ :=
  pairDist_le_of_rawStress_le Δ z hz i j

/-- Centering map: subtract the mean (translate so that the configuration's
centroid is at the origin). Internal helper / normalization: a particular
translation, used to fix the translation freedom of Remark 1. -/
private noncomputable def center (z : Config n d) : Config n d :=
  fun i => z i - (n : ℝ)⁻¹ • ∑ j : Fin n, z j

/-- Centering does not change raw stress (it is a translation, see
`rawStress_translate`). Internal helper / step of the proof. -/
private theorem rawStress_center (Δ : DisMat n) (z : Config n d) :
    -- Conclusion: centering `z` leaves its raw stress unchanged.
    rawStress n d Δ (center z) = rawStress n d Δ z :=
  rawStress_translate Δ z _

/-- The centered configuration has zero coordinate sum (for `n ≠ 0`), i.e. its
centroid is the origin. Internal helper / normalization step. -/
private theorem sum_center_eq_zero (hn : n ≠ 0) (z : Config n d) :  -- hn : at least one object
    -- Conclusion: the centered configuration sums to the zero vector.
    ∑ i : Fin n, center z i = 0 := by
  unfold center
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hn),
    one_smul, sub_self]

/-- A centered configuration whose pairwise distances are bounded by `R` has each
point bounded by `R` (for `n ≠ 0`).

Internal helper / step of the proof: converts a bound on pairwise distances into
a bound on individual points, which is what compactness (a box `‖w i‖ ≤ R`)
requires. Centering is exactly what makes this passage possible. -/
private theorem norm_le_of_centered (hn : n ≠ 0) (w : Config n d) {R : ℝ}
    (hcent : ∑ i : Fin n, w i = 0)        -- hcent : `w` is centered at the origin
    (hpair : ∀ i j, ‖w i - w j‖ ≤ R) (i : Fin n) :  -- hpair : all pairwise distances ≤ R
    -- Conclusion: each point of a centered configuration has norm ≤ R.
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

Paper correspondence: this is the existence of a raw-stress minimizer asserted
around Eq. (1) and Remark 2 ("This guarantees the existence of a solution to
Eq. (1)"), i.e. `MDS(Δ)` is nonempty. The compactness/coercivity argument here
mirrors restricting to the bounded set `Yₙ` in Remark 2 / Theorem 2 of [23].

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
theorem mds_nonempty :
    -- Conclusion: for every dissimilarity matrix, the set of raw-stress minimizers is nonempty.
    ∀ Δ : DisMat n, (MDS n d Δ).Nonempty := by
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
    push Not at hz'
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

/-- A canonical raw-stress minimizer, selected from `mds_nonempty`.

This packages the unavoidable nonconstructive choice once, so downstream
paper-facing theorems can name an MDS estimator without carrying a separate
configuration and membership proof through every layer. -/
noncomputable def mdsConfig (Δ : DisMat n) : Config n d :=
  Classical.choose (mds_nonempty (n := n) (d := d) Δ)

/-- The canonical raw-stress configuration is a global minimizer. -/
theorem mdsConfig_mem (Δ : DisMat n) :
    mdsConfig (n := n) (d := d) Δ ∈ MDS n d Δ :=
  Classical.choose_spec (mds_nonempty (n := n) (d := d) Δ)

/-! ## (d) Deterministic stability -/

/--
The square root of raw stress, evaluated at a fixed configuration `z`, is
`1`-Lipschitz in the dissimilarity matrix, in the directed form used for the
stability chain.

Internal helper / step of the proof: the one-sided (directed) form of
`abs_sqrt_rawStress_sub_le`, convenient for chaining stress inequalities across
`Δ` and `Δ'`.

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
private theorem sqrt_rawStress_le_add (Δ Δ' : DisMat n) (z : Config n d) :
    -- Conclusion: √(stress at Δ) ≤ √(stress at Δ') + Frobenius distance ‖Δ − Δ'‖_F.
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

Paper correspondence: this is the deterministic skeleton of Lemma 1 / Theorem 1
of the paper — convergence (in Frobenius norm) of the dissimilarity matrices
forces a subsequence of MDS minimizers to converge to a minimizer of the limit.
The paper states convergence "up to an affine transformation" (Remark 1); here the
affine freedom is pinned down by the centering hypothesis `hcent`, and convergence
is in the actual configuration space (stronger, given centering).

Extra (implicit) assumption beyond the paper: `hcent` (every `z k` is centered,
`∑ i, z k i = 0`). The paper's minimizers are only defined up to affine
transformations; centering is a specific normalization chosen here to obtain
boundedness/compactness, as the docstring notes. (No measurability hypothesis is
needed because this is a purely deterministic statement.)

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
theorem exists_subseq_tendsto_mds
    (D : Nat → DisMat n) (Δ : DisMat n)         -- D : sequence of (random-data) dissimilarity matrices; Δ : limit matrix
    (z : Nat → Config n d)                       -- z : a chosen MDS configuration for each `D k`
    (hz : ∀ k, z k ∈ MDS n d (D k))              -- hz : each `z k` minimizes raw stress for `D k`
    (hcent : ∀ k, ∑ i : Fin n, z k i = 0)        -- hcent : centering normalization (extra vs. paper)
    (hD : Tendsto (fun k => frobSub (D k) Δ) atTop (𝓝 0)) :  -- hD : `D k → Δ` in Frobenius norm
    -- Conclusion: along a subsequence `u`, `z (u t)` converges to some minimizer `ψ` of stress for `Δ`.
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
  -- Per-point approximate-minimizer bound for `y` against the limit `Δ`:
  -- minimality of `y t` for `D (t+N)` plus the √-stress Lipschitz bound give
  -- `rawStress Δ (y t) ≤ (√(rawStress Δ x') + 2·frobSub (D (t+N)) Δ)²`.
  have happrox : ∀ (x' : Config n d) (t : ℕ),
      rawStress n d Δ (y t) ≤ rawStress n d Δ x'
        + ((Real.sqrt (rawStress n d Δ x') + 2 * frobSub (D (t + N)) Δ) ^ 2
            - rawStress n d Δ x') := by
    intro x' t
    have hmin : rawStress n d (D (t + N)) (y t) ≤ rawStress n d (D (t + N)) x' :=
      hz (t + N) x'
    have h1 : Real.sqrt (rawStress n d Δ (y t))
        ≤ Real.sqrt (rawStress n d (D (t + N)) (y t)) + frobSub (D (t + N)) Δ := by
      rw [frobSub_comm (D (t + N)) Δ]
      exact sqrt_rawStress_le_add Δ (D (t + N)) (y t)
    have h2 : Real.sqrt (rawStress n d (D (t + N)) (y t))
        ≤ Real.sqrt (rawStress n d (D (t + N)) x') := Real.sqrt_le_sqrt hmin
    have h3 : Real.sqrt (rawStress n d (D (t + N)) x')
        ≤ Real.sqrt (rawStress n d Δ x') + frobSub (D (t + N)) Δ :=
      sqrt_rawStress_le_add (D (t + N)) Δ x'
    have hchain : Real.sqrt (rawStress n d Δ (y t))
        ≤ Real.sqrt (rawStress n d Δ x') + 2 * frobSub (D (t + N)) Δ := by linarith
    have hsq : rawStress n d Δ (y t)
        ≤ (Real.sqrt (rawStress n d Δ x') + 2 * frobSub (D (t + N)) Δ) ^ 2 := by
      calc rawStress n d Δ (y t)
          = (Real.sqrt (rawStress n d Δ (y t))) ^ 2 :=
            (Real.sq_sqrt (rawStress_nonneg Δ (y t))).symm
        _ ≤ _ := by
            apply sq_le_sq'
            · linarith [Real.sqrt_nonneg (rawStress n d Δ (y t))]
            · exact hchain
    linarith [hsq]
  -- The per-point error vanishes as `frobSub (D (t+N)) Δ → 0`.
  have hε : ∀ x' : Config n d,
      Tendsto (fun t => (Real.sqrt (rawStress n d Δ x') + 2 * frobSub (D (t + N)) Δ) ^ 2
          - rawStress n d Δ x') atTop (𝓝 0) := by
    intro x'
    have hfrob : Tendsto (fun t => frobSub (D (t + N)) Δ) atTop (𝓝 0) :=
      hD.comp (Filter.tendsto_add_atTop_nat N)
    have hlim : Tendsto
        (fun t => (Real.sqrt (rawStress n d Δ x') + 2 * frobSub (D (t + N)) Δ) ^ 2)
        atTop (𝓝 ((Real.sqrt (rawStress n d Δ x') + 2 * 0) ^ 2)) :=
      (tendsto_const_nhds.add (tendsto_const_nhds.mul hfrob)).pow 2
    have hval : (Real.sqrt (rawStress n d Δ x') + 2 * 0) ^ 2 = rawStress n d Δ x' := by
      rw [mul_zero, add_zero, Real.sq_sqrt (rawStress_nonneg Δ x')]
    rw [hval] at hlim
    simpa using hlim.sub_const (rawStress n d Δ x')
  -- Apply the Mathlib-staged approximate-minimizer stability lemma.
  obtain ⟨φ, hφ_mono, ψ, hψK, hψmin, hψtendsto⟩ :=
    ForMathlib.exists_subseq_tendsto_forall_le_of_approxMin hK_compact
      (continuous_rawStress Δ) hyK hε happrox
  refine ⟨fun t => φ t + N, ?_, ψ, hψmin, ?_⟩
  · exact fun a b hab => by simpa using Nat.add_lt_add_right (hφ_mono hab) N
  · have hreidx : (fun t => z (φ t + N)) = (fun t => y (φ t)) := by funext t; rfl
    rw [hreidx]; exact hψtendsto

/--
Pairwise distances of the stable subsequence converge to those of the limiting
configuration.

This is the direct geometric consequence of `exists_subseq_tendsto_mds`: the
paper works with pairwise dissimilarities, and these converge along the extracted
subsequence.

Paper correspondence: this is the deterministic form of the pairwise-distance
convergence in Lemma 1 / Theorem 1 — the embedded pairwise distances
`‖ψ̂_i − ψ̂_i'‖` of the MDS output approach `‖ψ_i − ψ_i'‖` of a limit minimizer.
Distances are the affine-invariant quantities the paper compares (Remark 1).

Extra (implicit) assumption beyond the paper: same centering hypothesis `hcent`
as in `exists_subseq_tendsto_mds`.

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
theorem pairDist_tendsto
    (D : Nat → DisMat n) (Δ : DisMat n)         -- D : dissimilarity matrices; Δ : limit matrix
    (z : Nat → Config n d)                       -- z : an MDS configuration for each `D k`
    (hz : ∀ k, z k ∈ MDS n d (D k))              -- hz : each `z k` is a raw-stress minimizer
    (hcent : ∀ k, ∑ i : Fin n, z k i = 0)        -- hcent : centering normalization (extra vs. paper)
    (hD : Tendsto (fun k => frobSub (D k) Δ) atTop (𝓝 0)) :  -- hD : `D k → Δ` in Frobenius norm
    -- Conclusion: along a subsequence, every pairwise distance converges to that of a minimizer `ψ` of `Δ`.
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

/-! ## Closing the measurable-selection gap

The remaining seam between the deterministic subsequence stability (d) and the
paper's probabilistic Theorem-1 statement is usually bridged by a measurable
selection of minimizers.  We avoid measurable selection entirely:

* a contradiction/compactness argument upgrades the subsequence stability to a
  uniform modulus of continuity (`exists_modulus_pairDist`);
* the probabilistic statements then follow from event inclusion plus
  monotonicity of outer measure (`measure_mono` holds for *arbitrary* sets), so
  no measurability hypotheses on the events are ever needed. -/

open MeasureTheory

/--
Centering preserves all pairwise distances: `center` subtracts the same mean
vector from every point of a configuration, so differences of points — and
hence their norms — are unchanged.

Internal helper / step of the proof: lets us replace any minimizer by its
centered version without altering the distance profile the paper compares.

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
theorem pairDist_center (z : Config n d) (i j : Fin n) :
    -- Conclusion: centering leaves each pairwise distance unchanged.
    pairDist (center z) i j = pairDist z i j := by
  unfold pairDist center
  congr 1
  abel

/--
Centering a raw-stress minimizer yields a raw-stress minimizer: raw stress is
translation invariant (`rawStress_center`), so subtracting the mean does not
change the objective value, and global minimality is preserved.

Internal helper / step of the proof: concretely realizes a fragment of Remark 1
(a translate of a minimizer is again a minimizer) and lets us assume minimizers
are centered when needed.

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
theorem center_mem_mds {Δ : DisMat n} {z : Config n d} (hz : z ∈ MDS n d Δ) :  -- hz : `z` is a raw-stress minimizer for `Δ`
    -- Conclusion: the centered version of `z` is also a raw-stress minimizer for `Δ`.
    center z ∈ MDS n d Δ := by
  intro z'
  rw [rawStress_center]
  exact hz z'

/-- A canonical centered raw-stress minimizer.

Centering removes translation ambiguity while preserving both raw stress and
all pairwise distances.  This is the most convenient deterministic witness for
compactness and rigidity arguments that need a normalized representative. -/
noncomputable def centeredMDSConfig (Δ : DisMat n) : Config n d :=
  center (mdsConfig (n := n) (d := d) Δ)

/-- The canonical centered configuration remains a raw-stress minimizer. -/
theorem centeredMDSConfig_mem (Δ : DisMat n) :
    centeredMDSConfig (n := n) (d := d) Δ ∈ MDS n d Δ := by
  exact center_mem_mds (mdsConfig_mem (n := n) (d := d) Δ)

/-- The canonical centered minimizer has zero coordinate sum when the model
index type is nonempty. -/
theorem sum_centeredMDSConfig_eq_zero (hn : n ≠ 0) (Δ : DisMat n) :
    ∑ i : Fin n, centeredMDSConfig (n := n) (d := d) Δ i = 0 := by
  exact sum_center_eq_zero hn (mdsConfig (n := n) (d := d) Δ)

/-- Centering the canonical minimizer does not change its pairwise-distance
profile. -/
theorem pairDist_centeredMDSConfig (Δ : DisMat n) (i j : Fin n) :
    pairDist (centeredMDSConfig (n := n) (d := d) Δ) i j =
      pairDist (mdsConfig (n := n) (d := d) Δ) i j := by
  exact pairDist_center (mdsConfig (n := n) (d := d) Δ) i j

/--
**Uniform modulus of continuity for raw-stress MDS** (the key to closing the
probabilistic Trosset–Priebe gap WITHOUT measurable selection).

For every tolerance `ε > 0` there is a `δ > 0` such that *any* raw-stress
minimizer `z` for *any* dissimilarity matrix `D'` within Frobenius distance `δ`
of `Δ` has all its pairwise distances within `ε` of those of *some* raw-stress
minimizer `ψ` for `Δ`.

Crucially, `δ` depends only on `(Δ, ε)` — not on `D'`, not on which minimizer
`z` was chosen.  This uniformity is exactly what lets the probabilistic
stability theorems below proceed by event inclusion, with no need to select a
minimizer measurably in `ω`.

Proof: by contradiction.  A failing sequence at `δ = 1/(k+1)` may be centered
(`center_mem_mds`, `pairDist_center` keep it a counterexample), after which the
deterministic compactness result `pairDist_tendsto` extracts a subsequence whose
pairwise distances converge to those of some `ψ ∈ MDS n d Δ` — eventually
violating the assumed failure at `ψ` for the finitely many index pairs.

Mathematical source/citation: Trosset & Priebe, "Continuous multidimensional
scaling" (cited as Theorem 2 in Acharyya et al., arXiv:2409.17308, Appendix
A.1–A.2).

Paper correspondence: this is a deterministic, quantitative strengthening of the
stability behind Lemma 1 / Theorem 1. The paper extracts a subsequence; here the
uniform modulus `δ(Δ, ε)` is what lets the probabilistic statements below proceed
without measurable selection of minimizers (a gap the paper does not address
explicitly). Distances are compared, matching the affine-invariant viewpoint of
Remark 1.

Relation to the abstract Berge modulus (`ForMathlib.Topology.Berge`,
`exists_modulus_isMinOn_family`): the abstract upper-hemicontinuity modulus over a
*fixed compact* feasible set, with closeness measured by a finite family of
continuous invariants, captures the metric side of this statement exactly — the
`pairDistErr` family is such a family of continuous invariants (a deliberate
generalization away from the ambient metric, since MDS minimizers differ by rigid
motions). It does NOT, however, subsume this theorem outright: here the feasible
set is the *non-compact* full configuration space, and compactness is recovered
only after centering minimizers into a `Δ`-dependent box (coercivity, via
`center_mem_mds` / `pairDist_center` / `norm_le_of_centered`). That coercive,
parameter-dependent compactification is the genuinely MDS-specific ingredient the
fixed-`K` Berge theorem leaves to the caller; hence this proof is kept bespoke.

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
theorem exists_modulus_pairDist (Δ : DisMat n) {ε : ℝ} (hε : 0 < ε) :  -- Δ : limit matrix; ε : target distance tolerance
    -- Conclusion: a single δ>0 (depending only on Δ, ε) makes ANY minimizer for ANY Δ'-within-δ
    -- pairwise ε-close to SOME minimizer ψ for Δ.
    ∃ δ : ℝ, 0 < δ ∧ ∀ (D' : DisMat n) (z : Config n d),
      z ∈ MDS n d D' → frobSub D' Δ ≤ δ →
      ∃ ψ ∈ MDS n d Δ, ∀ i j : Fin n, pairDistErr z ψ i j ≤ ε := by
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · -- `n = 0`: `Fin 0` is empty, so any minimizer `ψ` works; take `δ = 1`.
    subst hn0
    obtain ⟨ψ, hψ⟩ := mds_nonempty (d := d) Δ
    exact ⟨1, one_pos, fun D' z _ _ => ⟨ψ, hψ, fun i => i.elim0⟩⟩
  have hn : n ≠ 0 := hnpos.ne'
  by_contra hcon
  push Not at hcon
  -- Counterexamples at `δ = 1/(k+1)` for every `k`.
  have hex := fun k : Nat => hcon (1 / ((k : ℝ) + 1)) (by positivity)
  choose D zc hzmem hfrob hbad using hex
  -- The counterexample matrices converge to `Δ` (squeeze `0 ≤ frobSub ≤ 1/(k+1)`).
  have hfrob_nonneg : ∀ k, 0 ≤ frobSub (D k) Δ := by
    intro k; rw [frobSub, frob]; exact Real.sqrt_nonneg _
  have hD : Tendsto (fun k => frobSub (D k) Δ) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      tendsto_one_div_add_atTop_nhds_zero_nat hfrob_nonneg hfrob
  -- Center the counterexample configurations and apply deterministic stability.
  obtain ⟨u, hu_mono, ψ, hψ_mds, hpd⟩ :=
    pairDist_tendsto D Δ (fun k => center (zc k))
      (fun k => center_mem_mds (hzmem k))
      (fun k => sum_center_eq_zero hn (zc k)) hD
  -- Centering does not change pairwise distances.
  have hpd' : ∀ i j : Fin n,
      Tendsto (fun t => pairDist (zc (u t)) i j) atTop (𝓝 (pairDist ψ i j)) := by
    intro i j
    simpa [pairDist_center] using hpd i j
  -- For each index pair, the distance error to `ψ` is eventually `≤ ε`.
  have hev : ∀ p : Fin n × Fin n,
      ∀ᶠ t in atTop, pairDistErr (zc (u t)) ψ p.1 p.2 ≤ ε := by
    intro p
    have hconst : Tendsto (fun _ : Nat => pairDist ψ p.1 p.2) atTop
        (𝓝 (pairDist ψ p.1 p.2)) := tendsto_const_nhds
    have h2 : Tendsto (fun t => pairDistErr (zc (u t)) ψ p.1 p.2) atTop (𝓝 0) := by
      simpa [pairDistErr, sub_self] using ((hpd' p.1 p.2).sub hconst).abs
    exact h2.eventually (eventually_le_nhds hε)
  -- Combine over the finitely many pairs and pick a concrete time `t`.
  obtain ⟨t, ht⟩ := (eventually_all.mpr hev).exists
  -- The assumed failure at `ψ` produces a pair violating the bound.
  obtain ⟨i, j, hij⟩ := hbad (u t) ψ hψ_mds
  exact absurd (ht (i, j)) (not_le.mpr hij)

/--
**Probabilistic raw-stress MDS stability, set version** (no measurability
anywhere).

If the random dissimilarity matrices `Dseq r` converge in probability to
`DeltaInf` in Frobenius norm, and `ψhat r ω` is *any* raw-stress minimizer for
`Dseq r ω`, then the (outer) probability that `ψhat r ω` fails to be pairwise
`ε`-close to some minimizer for `DeltaInf` tends to `0`.

This closes the probabilistic Trosset–Priebe gap WITHOUT measurable selection:
the modulus of continuity `exists_modulus_pairDist` gives the deterministic
event inclusion `{bad} ⊆ {frobSub > δ}`, and `MeasureTheory.measure_mono` holds
for *arbitrary* sets (Mathlib measures are outer measures), so no measurability
of the bad event — and no measurable choice of minimizer — is required.

Paper correspondence: this is the probabilistic conclusion of Theorem 1 / Lemma 1
in set (outer-probability) form: the MDS output `ψ̂` becomes pairwise ε-close (in
probability) to the set of true minimizers `MDS(Δ)`. It compares pairwise
distances (`pairDistErr`), matching the affine-invariant statement of the paper.

Extra (implicit) assumptions / departures from the paper's exact shape:
* The bad event is measured by the OUTER measure; no measurability of that event
  is assumed (the docstring explains this deliberately replaces measurable
  selection, a step the paper leaves implicit).
* `hψhat` allows `ψ̂ r ω` to be ANY minimizer (not a measurably-selected one).
* Convergence is stated for the whole sequence in probability; the paper phrases
  Theorem 1 along a subsequence.

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
theorem mds_stability_inProbability_set
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)   -- (Ω, P) : probability/measure space
    (Dseq : Nat → Ω → DisMat n) (DeltaInf : DisMat n)  -- Dseq : random dissimilarity matrices; DeltaInf : limit Δ
    (ψhat : Nat → Ω → Config n d)                     -- ψhat : a chosen MDS output per replicate `r`, outcome `ω`
    (hψhat : ∀ r ω, ψhat r ω ∈ MDS n d (Dseq r ω))    -- hψhat : `ψhat` is always a raw-stress minimizer (any one)
    (hD : ConvergesInProbabilityZero P (fun r ω => frobSub (Dseq r ω) DeltaInf))  -- hD : `Dseq → DeltaInf` in probability (Frobenius)
    {ε : ℝ} (hε : 0 < ε) :                            -- ε : distance tolerance
    -- Conclusion: the (outer) probability that `ψhat r` fails to be pairwise ε-close to some
    -- minimizer of `DeltaInf` tends to 0.
    Tendsto (fun r => P {ω | ¬ ∃ ψ ∈ MDS n d DeltaInf,
      ∀ i j : Fin n, pairDistErr (ψhat r ω) ψ i j ≤ ε}) atTop (𝓝 0) := by
  obtain ⟨δ, hδ, hmod⟩ := exists_modulus_pairDist (n := n) (d := d) DeltaInf hε
  -- Event inclusion: bad MDS output forces `frobSub > δ`.
  have hsub : ∀ r, {ω | ¬ ∃ ψ ∈ MDS n d DeltaInf,
        ∀ i j : Fin n, pairDistErr (ψhat r ω) ψ i j ≤ ε}
      ⊆ {ω | dist (frobSub (Dseq r ω) DeltaInf) 0 > δ} := by
    intro r ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    by_contra hle
    push Not at hle
    have hfrob_nonneg : 0 ≤ frobSub (Dseq r ω) DeltaInf := by
      rw [frobSub, frob]; exact Real.sqrt_nonneg _
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hfrob_nonneg] at hle
    exact hω (hmod (Dseq r ω) (ψhat r ω) (hψhat r ω) hle)
  -- Squeeze in `ℝ≥0∞` using outer-measure monotonicity.
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hD δ hδ)
    (fun r => zero_le) (fun r => measure_mono (hsub r))

/--
The limiting dissimilarity matrix has a **unique pairwise-distance profile**:
all raw-stress minimizers induce the same pairwise distances.  This is the
hypothesis the paper's Theorem 1 implicitly needs in order to speak of "the"
embedding distances of the limit; without it only the set version
(`mds_stability_inProbability_set`) is true.

Note (relation to the paper): Remark 1 explicitly warns that minimizers need not
be affine images of one another, so `UniquePairProfile` is a genuine EXTRA
hypothesis, not something the paper proves. It is exactly the additional
assumption needed to upgrade the set-version conclusion to a fixed-limit one.

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
def UniquePairProfile (n d : Nat) (Δ : DisMat n) : Prop :=
  ∀ ψ₁ ∈ MDS n d Δ, ∀ ψ₂ ∈ MDS n d Δ, ∀ i j : Fin n, pairDist ψ₁ i j = pairDist ψ₂ i j

/--
Exact realizability dispatches the distance-profile uniqueness assumption:
when one configuration realizes every target dissimilarity, every minimizer has
zero stress and therefore realizes that same pairwise-distance profile.
-/
theorem uniquePairProfile_of_exists_realizes {Δ : DisMat n}
    (hexact : ∃ z : Config n d, RealizesDissimilarity z Δ) :
    UniquePairProfile n d Δ := by
  intro ψ₁ hψ₁ ψ₂ hψ₂ i j
  have h₁ := realizes_of_mem_MDS_of_exists_realizes hexact hψ₁
  have h₂ := realizes_of_mem_MDS_of_exists_realizes hexact hψ₂
  exact (h₁ i j).trans (h₂ i j).symm

/--
**Probabilistic raw-stress MDS stability with a fixed limit configuration**
(full sequence, no subsequence) — the repaired Theorem-1 shape of Acharyya et
al. under the profile-uniqueness hypothesis the paper implicitly needs.

If additionally all minimizers for `DeltaInf` share the same pairwise-distance
profile (`UniquePairProfile`), then there is a single fixed minimizer `ψ` such
that every pairwise-distance error of the random MDS output `ψhat r ω` against
`ψ` converges to `0` in probability — along the full sequence.

Like `mds_stability_inProbability_set`, this closes the probabilistic
Trosset–Priebe gap WITHOUT measurable selection: the proof is pure event
inclusion (any witness `ψ'` from the modulus event has the same distance
profile as `ψ`, by uniqueness) followed by outer-measure monotonicity, so no
measurability of events or of a minimizer selection is required.

Paper correspondence: this is the closest match to the literal statement of
Theorem 1 — a SINGLE fixed limit `ψ ∈ MDS(Δ)` against which the pairwise-distance
errors of `ψ̂` go to 0 in probability — but obtained for the FULL sequence
(stronger than the paper's subsequence) and under the EXTRA `UniquePairProfile`
hypothesis (see note on `UniquePairProfile`), which Remark 1 indicates the paper
does not establish in general.

Extra (implicit) assumptions beyond the paper:
* `huniq : UniquePairProfile …` — distance-profile uniqueness of the limit
  minimizers (the paper's Remark 1 explicitly does not guarantee this).
* As in the set version, the bad events are handled by outer measure; no
  measurability of events or measurable selection of `ψ̂` is assumed.

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
theorem mds_stability_inProbability_of_uniqueProfile
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)   -- (Ω, P) : probability/measure space
    (Dseq : Nat → Ω → DisMat n) (DeltaInf : DisMat n)  -- Dseq : random dissimilarity matrices; DeltaInf : limit Δ
    (ψhat : Nat → Ω → Config n d)                     -- ψhat : a chosen MDS output per replicate/outcome (any minimizer)
    (hψhat : ∀ r ω, ψhat r ω ∈ MDS n d (Dseq r ω))    -- hψhat : `ψhat` is always a raw-stress minimizer
    (huniq : UniquePairProfile n d DeltaInf)          -- huniq : EXTRA — all limit minimizers share one distance profile
    (hD : ConvergesInProbabilityZero P (fun r ω => frobSub (Dseq r ω) DeltaInf)) :  -- hD : `Dseq → DeltaInf` in probability
    -- Conclusion: there is ONE fixed minimizer ψ for DeltaInf such that every pairwise-distance
    -- error `pairDistErr (ψhat r) ψ` converges to 0 in probability, along the full sequence.
    ∃ ψ ∈ MDS n d DeltaInf, ∀ i j : Fin n,
      ConvergesInProbability P (fun r ω => pairDistErr (ψhat r ω) ψ i j) 0 := by
  obtain ⟨ψ, hψ⟩ := mds_nonempty (n := n) (d := d) DeltaInf
  refine ⟨ψ, hψ, fun i j => ?_⟩
  intro ε hε
  -- Event inclusion into the set-version bad event.
  have hsub : ∀ r, {ω | dist (pairDistErr (ψhat r ω) ψ i j) 0 > ε}
      ⊆ {ω | ¬ ∃ ψ' ∈ MDS n d DeltaInf,
          ∀ i' j' : Fin n, pairDistErr (ψhat r ω) ψ' i' j' ≤ ε} := by
    intro r ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    rintro ⟨ψ', hψ', hclose⟩
    -- `ψ'` and `ψ` share the same distance profile, so the bound transfers.
    have heq : pairDist ψ' i j = pairDist ψ i j := huniq ψ' hψ' ψ hψ i j
    have herr_eq : pairDistErr (ψhat r ω) ψ i j = pairDistErr (ψhat r ω) ψ' i j := by
      unfold pairDistErr
      rw [heq]
    have hle : pairDistErr (ψhat r ω) ψ i j ≤ ε := by
      rw [herr_eq]; exact hclose i j
    have hpe_nonneg : 0 ≤ pairDistErr (ψhat r ω) ψ i j := by
      unfold pairDistErr; exact abs_nonneg _
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hpe_nonneg] at hω
    exact absurd hle (not_le.mpr hω)
  have hset := mds_stability_inProbability_set P Dseq DeltaInf ψhat hψhat hD hε
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hset
    (fun r => zero_le) (fun r => measure_mono (hsub r))

end Acharyya2024.RawStress
