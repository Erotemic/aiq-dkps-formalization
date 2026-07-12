/-
Growing-dimension foundations for the Acharyya2025 spectral pipeline.

The fixed-population aligned pipeline controls coordinates after choosing an
aligning isometry.  Downstream nearest-neighbor arguments need only pairwise
distances.  Pairwise distances are invariant under the aligning isometry, so a
finite CMDS perturbation bound immediately yields a choice-free distance
perturbation bound.  This file packages that reduction and the deterministic
rate certificate needed when the matrix size varies with the asymptotic stage.
-/

import Acharyya2025.AlignedPipeline

open scoped BigOperators RealInnerProductSpace InnerProductSpace Matrix Topology
open Filter

namespace Acharyya2025.GrowingPipeline

open Acharyya2024
open Acharyya2025.Deterministic
open Acharyya2025.MathlibBridge
open Acharyya2025.ConfigPerturbation
open Acharyya2025.MatrixPerturbation
open Acharyya2025.GramRealization
open Acharyya2025.AlignedPipeline

/-- Pairwise distances of two configurations differ by at most twice their
`ConfigError`.  The first configuration may first be transported by an
inner-product-preserving linear map; this does not change its distances. -/
theorem abs_pairwiseDistance_sub_le_two_configError
    {n d : Nat}
    (W : EuclideanSpace Real (Fin d) →ₗ[Real] EuclideanSpace Real (Fin d))
    (hW : ∀ x y, ⟪W x, W y⟫_ℝ = ⟪x, y⟫_ℝ)
    (zhat z : Config n d) (i j : Fin n) :
    |‖zhat i - zhat j‖ - ‖z i - z j‖| ≤
      2 * ConfigError (fun k => W (zhat k)) z := by
  have hnorm : ∀ x, ‖W x‖ = ‖x‖ := by
    intro x
    have hsq : ‖W x‖ ^ 2 = ‖x‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, hW x x]
    nlinarith [norm_nonneg (W x), norm_nonneg x]
  have hdist : ‖zhat i - zhat j‖ = ‖W (zhat i) - W (zhat j)‖ := by
    rw [← map_sub, hnorm]
  rw [hdist]
  calc
    |‖W (zhat i) - W (zhat j)‖ - ‖z i - z j‖|
        ≤ ‖(W (zhat i) - W (zhat j)) - (z i - z j)‖ :=
          abs_norm_sub_norm_le _ _
    _ = ‖(W (zhat i) - z i) - (W (zhat j) - z j)‖ := by
          congr 1
          abel
    _ ≤ ‖W (zhat i) - z i‖ + ‖W (zhat j) - z j‖ := norm_sub_le _ _
    _ ≤ 2 * ConfigError (fun k => W (zhat k)) z := by
      have hi := norm_config_le_ConfigError (fun k => W (zhat k)) z i
      have hj := norm_config_le_ConfigError (fun k => W (zhat k)) z j
      linarith

/-- Entrywise CMDS closeness controls every pairwise distance in the raw sample
spectral configuration.  No aligning map appears in the conclusion because
pairwise distances are invariant under the map supplied by the deterministic
spectral theorem. -/
theorem abs_pairwiseDistance_spectralConfig_sub_le_two_configBound
    {n d : Nat} (hd : d ≤ n)
    (B Bhat : Matrix (Fin n) (Fin n) Real)
    (hB : B.PosSemidef) (hBhat : Bhat.IsHermitian)
    (hrank : B.rank ≤ d)
    {α Λ η : Real} (hα_pos : 0 < α) (hη_nonneg : 0 ≤ η)
    (hfloor : ∀ i : Fin n, (i : Nat) < d →
      α ≤ sortedEigenvalues hB.isHermitian i)
    (hΛ : ∀ i : Fin n, sortedEigenvalues hB.isHermitian i ≤ Λ)
    (hentry : ∀ i j, |Bhat i j - B i j| ≤ η)
    (hsmall : (n : Real) * η ≤ α / 2)
    (hpolar : (d : Real) * (4 * (n : Real) * ((n : Real) * η)^2 / α^2) ≤ 1 / 2)
    (z : Config n d)
    (hz : ∀ i j, (∑ k, z i k * z j k) = B i j)
    (i j : Fin n) :
    |‖spectralConfig (Matrix.toEuclideanLin Bhat) (opSym hBhat) hd i -
          spectralConfig (Matrix.toEuclideanLin Bhat) (opSym hBhat) hd j‖ -
        ‖z i - z j‖| ≤
      2 * configBound n d α Λ ((n : Real) * η) := by
  obtain ⟨W, hW, hconfig⟩ :=
    exists_isometry_configError_le_of_entrywise_close hd B Bhat hB hBhat
      hrank hα_pos hη_nonneg hfloor hΛ hentry hsmall hpolar z hz
  exact (abs_pairwiseDistance_sub_le_two_configError W hW
    (spectralConfig (Matrix.toEuclideanLin Bhat) (opSym hBhat) hd) z i j).trans
      (mul_le_mul_of_nonneg_left hconfig (by norm_num))

/-- Canonical-ceiling version of the pairwise-distance perturbation theorem. -/
theorem abs_pairwiseDistance_spectralConfig_sub_le_two_configBound_topEigenvalue
    {n d : Nat} (hn : 0 < n) (hd : d ≤ n)
    (B Bhat : Matrix (Fin n) (Fin n) Real)
    (hB : B.PosSemidef) (hBhat : Bhat.IsHermitian)
    (hrank : B.rank ≤ d)
    {α η : Real} (hα_pos : 0 < α) (hη_nonneg : 0 ≤ η)
    (hfloor : ∀ i : Fin n, (i : Nat) < d →
      α ≤ sortedEigenvalues hB.isHermitian i)
    (hentry : ∀ i j, |Bhat i j - B i j| ≤ η)
    (hsmall : (n : Real) * η ≤ α / 2)
    (hpolar : (d : Real) * (4 * (n : Real) * ((n : Real) * η)^2 / α^2) ≤ 1 / 2)
    (z : Config n d)
    (hz : ∀ i j, (∑ k, z i k * z j k) = B i j)
    (i j : Fin n) :
    |‖spectralConfig (Matrix.toEuclideanLin Bhat) (opSym hBhat) hd i -
          spectralConfig (Matrix.toEuclideanLin Bhat) (opSym hBhat) hd j‖ -
        ‖z i - z j‖| ≤
      2 * configBound n d α (topEigenvalue hn hB) ((n : Real) * η) := by
  exact abs_pairwiseDistance_spectralConfig_sub_le_two_configBound hd B Bhat
    hB hBhat hrank hα_pos hη_nonneg hfloor
    (sortedEigenvalues_le_topEigenvalue hn hB) hentry hsmall hpolar z hz i j

/-- Canonical population-realization version. -/
theorem abs_pairwiseDistance_spectralConfig_sub_le_two_configBound_canonical
    {n d : Nat} (hn : 0 < n) (hd : d ≤ n)
    (Dhat D : DisMat n)
    (hBhat : (disMatToMatrix (classicalMDSMatrix Dhat)).IsHermitian)
    (hB : (disMatToMatrix (classicalMDSMatrix D)).PosSemidef)
    (hrank : (disMatToMatrix (classicalMDSMatrix D)).rank ≤ d)
    {α η : Real} (hα_pos : 0 < α) (hη_nonneg : 0 ≤ η)
    (hfloor : ∀ i : Fin n, (i : Nat) < d →
      α ≤ sortedEigenvalues hB.isHermitian i)
    (hentry : Acharyya2025.Bridge.EntrywiseClose
      (classicalMDSMatrix Dhat) (classicalMDSMatrix D) η)
    (hsmall : (n : Real) * η ≤ α / 2)
    (hpolar : (d : Real) * (4 * (n : Real) * ((n : Real) * η)^2 / α^2) ≤ 1 / 2)
    (i j : Fin n) :
    |‖spectralConfig
          (Matrix.toEuclideanLin (disMatToMatrix (classicalMDSMatrix Dhat)))
          (opSym hBhat) hd i -
        spectralConfig
          (Matrix.toEuclideanLin (disMatToMatrix (classicalMDSMatrix Dhat)))
          (opSym hBhat) hd j‖ -
        ‖canonicalCMDSConfig D hB hrank i - canonicalCMDSConfig D hB hrank j‖| ≤
      2 * configBound n d α (topEigenvalue hn hB) ((n : Real) * η) := by
  apply abs_pairwiseDistance_spectralConfig_sub_le_two_configBound_topEigenvalue
    hn hd
    (disMatToMatrix (classicalMDSMatrix D))
    (disMatToMatrix (classicalMDSMatrix Dhat))
    hB hBhat hrank hα_pos hη_nonneg hfloor hentry hsmall hpolar
    (canonicalCMDSConfig D hB hrank)
    (canonicalCMDSConfig_gram_eq D hB hrank)

/-- A deterministic certificate for a varying matrix size.  It separates the
three asymptotic requirements actually consumed by the finite spectral theorem:
entrywise nonnegativity, eventual local side conditions, and a vanishing
deterministic envelope for the resulting `configBound`.

This is the correct interface for a joint model-count/response-budget schedule.
In particular, merely knowing `(count u) * entryRate u → 0` is not enough when
`count u` itself grows, because the polar term and the final `√count` factor
must also vanish. -/
structure GrowingConfigControl
    (count : Nat → Nat) (d : Nat) (α : Real)
    (ceiling entryRate : Nat → Real) where
  entry_nonneg : ∀ u, 0 ≤ entryRate u
  small_eventually : ∀ᶠ u in atTop,
    (count u : Real) * entryRate u ≤ α / 2
  polar_eventually : ∀ᶠ u in atTop,
    (d : Real) *
      (4 * (count u : Real) *
        (((count u : Real) * entryRate u)^2) / α^2) ≤ 1 / 2
  bound : Nat → Real
  bound_nonneg : ∀ u, 0 ≤ bound u
  bound_zero : Tendsto bound atTop (𝓝 0)
  configBound_le : ∀ᶠ u in atTop,
    configBound (count u) d α (ceiling u)
      ((count u : Real) * entryRate u) ≤ bound u


/-- Build a growing control certificate directly from the three vanishing
quantities exposed by a joint asymptotic calculation.  The final envelope is
taken to be the exact `configBound`. -/
noncomputable def GrowingConfigControl.of_tendsto
    {count : Nat → Nat} {d : Nat} {α : Real}
    {ceiling entryRate : Nat → Real}
    (hα : 0 < α)
    (hentry : ∀ u, 0 ≤ entryRate u)
    (hscaled : Tendsto
      (fun u => (count u : Real) * entryRate u) atTop (𝓝 0))
    (hpolar : Tendsto
      (fun u => (d : Real) *
        (4 * (count u : Real) *
          (((count u : Real) * entryRate u)^2) / α^2)) atTop (𝓝 0))
    (hbound : Tendsto
      (fun u => configBound (count u) d α (ceiling u)
        ((count u : Real) * entryRate u)) atTop (𝓝 0)) :
    GrowingConfigControl count d α ceiling entryRate where
  entry_nonneg := hentry
  small_eventually := by
    have hhalf : 0 < α / 2 := by positivity
    exact (hscaled.eventually (Iio_mem_nhds hhalf)).mono fun _ hu => hu.le
  polar_eventually := by
    have hhalf : (0 : Real) < 1 / 2 := by norm_num
    exact (hpolar.eventually (Iio_mem_nhds hhalf)).mono fun _ hu => hu.le
  bound := fun u => configBound (count u) d α (ceiling u)
    ((count u : Real) * entryRate u)
  bound_nonneg := by
    intro u
    unfold configBound
    positivity
  bound_zero := hbound
  configBound_le := Filter.Eventually.of_forall fun _ => le_rfl

/-- All finite spectral side conditions and the final error domination hold
simultaneously eventually. -/
theorem GrowingConfigControl.eventually_all
    {count : Nat → Nat} {d : Nat} {α : Real}
    {ceiling entryRate : Nat → Real}
    (H : GrowingConfigControl count d α ceiling entryRate) :
    ∀ᶠ u in atTop,
      (count u : Real) * entryRate u ≤ α / 2 ∧
      (d : Real) *
        (4 * (count u : Real) *
          (((count u : Real) * entryRate u)^2) / α^2) ≤ 1 / 2 ∧
      configBound (count u) d α (ceiling u)
        ((count u : Real) * entryRate u) ≤ H.bound u := by
  filter_upwards [H.small_eventually, H.polar_eventually, H.configBound_le]
    with u hsmall hpolar hbound
  exact ⟨hsmall, hpolar, hbound⟩

/-- The augmented batch size `u + 1` eventually dominates every fixed embedding
dimension. -/
theorem eventually_dimension_le_succ (d : Nat) :
    ∀ᶠ u in atTop, d ≤ u + 1 := by
  exact eventually_atTop.2 ⟨d, fun u hu => by omega⟩

end Acharyya2025.GrowingPipeline
