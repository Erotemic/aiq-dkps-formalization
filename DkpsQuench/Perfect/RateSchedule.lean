/-
Explicit conservative schedules for Perfect Quench.

The current public bridge accepts abstract limit certificates.  This module
provides one deliberately loose polynomial schedule that discharges those
limits automatically.  The constants are not intended to be optimal; the goal
is a theorem whose users choose a response budget, not a collection of
asymptotic side proofs.
-/

import DkpsQuench.Perfect.UniformConcentration

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

namespace DkpsQuench.Perfect

open Acharyya2025.Bridge
open Acharyya2025.GrowingPipeline
open Acharyya2025.GrowingResponse
open Acharyya2025.ConfigPerturbation

/-- Conservative response-mean tolerance.  The fifth power is chosen to beat
the intentionally loose growing CMDS bound, including its final
configuration-error factor. -/
noncomputable def safeResponseTolerance (n : Nat) : Real :=
  ((((n + 1 : Nat) : Real) ^ 5))⁻¹

/-- Conservative finite-model replicate budget. -/
def safeFiniteReplicates (n : Nat) : Nat :=
  (n + 1) ^ 13

/-- Replicate budget allowing a stage net with polynomial cardinality
`O((n+1)^entropyPower)`. -/
def safeEntropyReplicates (entropyPower n : Nat) : Nat :=
  (n + 1) ^ (13 + entropyPower)

/-- Canonical shrinking perspective-net radius for a common raw-response
Lipschitz constant `L`.  The denominator reserves half of the response error
budget for extension from net centers to arbitrary models. -/
noncomputable def safePerspectiveRadius (L : Real) (n : Nat) : Real :=
  safeResponseTolerance n / (4 * (L + 1))

/-- Half of the final response tolerance is reserved for concentration on the
finite net; the other half is reserved for deterministic net extension. -/
noncomputable def safeNetTolerance (n : Nat) : Real :=
  safeResponseTolerance n / 2

theorem safeResponseTolerance_pos (n : Nat) :
    0 < safeResponseTolerance n := by
  unfold safeResponseTolerance
  positivity

theorem safeFiniteReplicates_pos (n : Nat) :
    0 < safeFiniteReplicates n := by
  unfold safeFiniteReplicates
  positivity

theorem safeEntropyReplicates_pos (entropyPower n : Nat) :
    0 < safeEntropyReplicates entropyPower n := by
  unfold safeEntropyReplicates
  positivity

theorem safePerspectiveRadius_pos
    (L : Real) (hL : 0 ≤ L) (n : Nat) :
    0 < safePerspectiveRadius L n := by
  unfold safePerspectiveRadius
  have hden : 0 < 4 * (L + 1) := by linarith
  exact div_pos (safeResponseTolerance_pos n) hden

/-- The canonical perspective-net radius vanishes for every nonnegative fixed
Lipschitz constant.

Implementation recipe (execute in this order):
1. Unfold `safePerspectiveRadius`; set the positive constant
   `c := (4 * (L + 1))⁻¹` and prove it is finite using `hL`.
2. Rewrite the function as `fun n => c * safeResponseTolerance n`.
3. Apply `safeResponseTolerance_zero.const_mul c` after that theorem is
   available; if declaration order prevents this, prove directly from
   `tendsto_natCast_atTop_atTop`, `tendsto_pow_atTop_atTop_of_one_lt`, and
   `tendsto_inv_atTop_zero` for power five.
4. Close scalar normalization with `ring`/`field_simp`; no epsilon proof is
   necessary.
-/
theorem safePerspectiveRadius_zero
    (L : Real) (hL : 0 ≤ L) :
    Tendsto (safePerspectiveRadius L) atTop (𝓝 0) := by
  sorry

/-- Compact finite-dimensional perspective ranges admit canonical safe nets
with polynomial stage cardinality.

Proof plan:

1. apply `exists_growingPerspectiveNet_with_polynomial_card` to
   `safePerspectiveRadius L`;
2. rewrite the inverse radius as a fixed constant times `(n+1)^5`;
3. raise that estimate to dimension `d`;
4. absorb every fixed factor and all `max 1` early-stage slack into `C`.

This result removes the net, radius, entropy exponent, and covering-number
certificate from the final infinite-model theorem.

Implementation recipe (execute in this order):
1. Apply `exists_growingPerspectiveNet_with_polynomial_card` with radius
   `safePerspectiveRadius L`, positivity
   `safePerspectiveRadius_pos L hL`, and limit `safePerspectiveRadius_zero`.
2. Obtain `net`, a cover constant `C0`, its polynomial inverse-radius bound, and
   the radius identity.
3. Prove a fixed constant `K` such that
   `max 1 (safePerspectiveRadius L n)⁻¹ ≤ K * (n+1)^5` for every `n`; unfold the
   radius and use `safeResponseTolerance` plus `hL`.
4. Raise this inequality to power `d` using `pow_le_pow_left₀`; combine with the
   existing card bound.
5. Choose `C := C0 * K^d` (or a larger nonnegative max) and normalize
   `((n+1)^5)^d = (n+1)^(5*d)` with `pow_mul`.
6. Return the original `net` and exact radius equality; absorb all small-stage
   slack into `C`, never by adding a lower bound on `n`.
-/
theorem exists_safeGrowingPerspectiveNet
    {Q : Type*} [DecidableEq Q]
    {X : Type*} [MeasurableSpace X]
    {d : Nat}
    (ψ : Model Q X → Vec d)
    (hcompact : IsCompact (Set.range ψ))
    (L : Real) (hL : 0 ≤ L) :
    ∃ net : GrowingPerspectiveNet ψ, ∃ C : Real,
      0 ≤ C ∧
      (∀ n, ((net.centers n).card : Real) ≤
        C * (((n + 1 : Nat) : Real) ^ (5 * d))) ∧
      (∀ n, net.radius n = safePerspectiveRadius L n) := by
  sorry

/-- The conservative response tolerance vanishes.

Implementation recipe (execute in this order):
1. Unfold `safeResponseTolerance`.
2. Prove `((n+1 : Nat) : Real) → ∞` with `tendsto_natCast_atTop_atTop` composed
   with `tendsto_add_atTop_nat`.
3. Raise to the fifth power using `tendsto_pow_atTop_atTop_of_one_lt` or the
   monotone polynomial API.
4. Apply `tendsto_inv_atTop_zero`.
5. Use `simpa` to match the exact coercion and power syntax.  Avoid manual
   epsilon estimates.
-/
theorem safeResponseTolerance_zero :
    Tendsto safeResponseTolerance atTop (𝓝 0) := by
  sorry

/-- The finite-model Chebyshev/union-bound ratio vanishes under the safe
replicate schedule.

Suggested proof route: rewrite every term as a power of `n+1`; after cancelling
powers, dominate the expression by a constant times `(n+1)⁻²`.  Use the
existing `tendsto_pow_atTop_nhds_zero_of_lt_one` or polynomial-at-infinity API
rather than epsilon arithmetic.

Implementation recipe (execute in this order):
1. Unfold `safeFiniteReplicates`, `safeResponseTolerance`, and division; rewrite
   natural powers after coercion with `Nat.cast_pow`.
2. On all stages, normalize the expression algebraically to
   `(targetCount * varianceBound) * (((n+1 : Nat) : Real)⁻¹)^2` (or an even
   smaller inverse power); use `field_simp` only after proving `n+1 ≠ 0`.
3. Prove `(((n+1 : Nat) : Real)⁻¹)^2 → 0` from the inverse-at-infinity theorem
   and `Tendsto.pow`.
4. Multiply by the fixed constant with `Tendsto.const_mul`.
5. The theorem is valid even when `varianceBound` is negative, so avoid order
   arguments; use exact algebra and limits.
-/
theorem safeFinite_concentration_ratio_zero
    (targetCount : Nat) (varianceBound : Real) :
    Tendsto (fun n =>
      (targetCount : Real) * ((n + 1 : Nat) : Real) *
        (varianceBound / safeFiniteReplicates n) /
        (safeResponseTolerance n) ^ 2) atTop (𝓝 0) := by
  sorry

/-- Entropy-aware concentration ratio for polynomial-size shrinking nets.

The theorem is stated with an upper bound on net cardinality so applications do
not need an exact covering number formula.  The extra exponent in
`safeEntropyReplicates` leaves polynomial slack after the tolerance is squared.

Implementation recipe (execute in this order):
1. Let `a n` be the nonnegative target expression and replace
   `centersCard n` with its upper bound from `hcard`; if constants may be
   negative, first enlarge `coverConstant` and `varianceBound` by `max 0` or
   prove the target by exact algebra when possible.
2. Unfold `safeEntropyReplicates` and `safeNetTolerance`; rewrite all casts and
   powers of `n+1`.
3. Show the resulting upper bound is a fixed constant times at most
   `((n+1 : Nat) : Real)⁻²`; the exponent calculation is
   `entropyPower + 10 - (13 + entropyPower) = -3`, with one spare power.
4. Apply squeeze with nonnegativity of the original ratio and the inverse-power
   limit.
5. If sign assumptions make squeeze awkward, split on `varianceBound ≤ 0`; in
   that branch the second-moment application is trivial, and in the positive
   branch all factors are nonnegative.
6. Keep this theorem independent of any particular net structure.
-/
theorem safeEntropy_concentration_ratio_zero
    (entropyPower : Nat) (varianceBound coverConstant : Real)
    (centersCard : Nat → Nat)
    (hcard : ∀ n,
      (centersCard n : Real) ≤
        coverConstant * (((n + 1 : Nat) : Real) ^ entropyPower)) :
    Tendsto (fun n =>
      (centersCard n : Real) *
        (varianceBound / safeEntropyReplicates entropyPower n) /
        (safeNetTolerance n) ^ 2) atTop (𝓝 0) := by
  sorry

/-- A small enough shrinking-net radius fits inside the half-tolerance budget
when sample and population response maps have a common Lipschitz envelope.

This is elementary scalar bookkeeping.  It is separated because the infinite-
model capstone should ask for one radius inequality, not repeat a triangle-
inequality calculation in every application.

Implementation recipe (execute in this order):
1. Fix `n`; abbreviate `η := safeResponseTolerance n` and note `0 < η`.
2. Use `hsampleNonneg n`, `hpopulationNonneg n`, `hsample n`, and
   `hpopulation n` to obtain
   `0 ≤ Lsample n + Lpopulation n ≤ 2 * L`.
3. Use `hradiusNonneg n` and `hradius n` with
   `mul_le_mul_of_nonneg_left` to bound the extension term by
   `(2 * L) * (η / (4 * (L + 1)))`.
4. Substitute `safeNetTolerance n = η/2` and the definition of
   `safePerspectiveRadius`.
5. Show `2 * L / (4 * (L + 1)) ≤ 1/2` from `hL`; multiply by `η ≥ 0` and finish
   by `nlinarith` or `field_simp` followed by `nlinarith`.
6. The explicit nonnegativity premises are essential for the multiplication
   steps; do not remove them or infer them from upper bounds alone.
-/
theorem safe_net_extension_budget
    (Lsample Lpopulation radius : Nat → Real)
    (L : Real)
    (hL : 0 ≤ L)
    (hsampleNonneg : ∀ n, 0 ≤ Lsample n)
    (hpopulationNonneg : ∀ n, 0 ≤ Lpopulation n)
    (hradiusNonneg : ∀ n, 0 ≤ radius n)
    (hsample : ∀ n, Lsample n ≤ L)
    (hpopulation : ∀ n, Lpopulation n ≤ L)
    (hradius : ∀ n,
      radius n ≤ safeResponseTolerance n / (4 * (L + 1))) :
    ∀ n,
      safeNetTolerance n +
          (Lsample n + Lpopulation n) * radius n ≤
        safeResponseTolerance n := by
  sorry

/-- The batch-size-scaled CMDS entry rate vanishes under the safe
tolerance.

Unfold the response and CMDS rates, use `hm` to simplify the inverse query
count safely, and compare powers of `n+1`.  This is the exact limit used by the
local spectral-smallness field of `GrowingConfigControl`.

Implementation recipe (execute in this order):
1. Unfold `cmdsEntrywiseRate`, `responseFrobRate`, `responseDistBound`, and
   `safeResponseTolerance`; rewrite the inverse of `(m : Real)` using `hm` only
   to establish it is a fixed finite constant.
2. Expand the expression and collect every fixed factor into one constant.
3. Count powers of `N := ((n+1 : Nat) : Real)`: the scaled rate is bounded by a
   constant times `N^3 * N⁻5`, hence `O(N⁻2)`; the extra term containing
   `safeResponseTolerance` decays faster.
4. Prove the inverse-power limits and combine them with `Tendsto.add`,
   `Tendsto.mul`, and constant multiplication.
5. Use exact ring normalization in a local equality before applying limits; do
   not attempt to make `simp` discover the exponent arithmetic automatically.
-/
theorem safe_scaled_cmdsEntrywiseRate_zero
    (m : Nat) (hm : 0 < m) (populationResponseBound : Real) :
    Tendsto (fun n =>
      ((n + 1 : Nat) : Real) *
        cmdsEntrywiseRate (n + 1) m
          (responseDistBound m
            (populationResponseBound + safeResponseTolerance n))
          (safeResponseTolerance n)) atTop (𝓝 0) := by
  sorry

/-- The polar-factor side expression vanishes under the safe tolerance.

This proof should consume `safe_scaled_cmdsEntrywiseRate_zero`, square the
scaled rate, multiply by the remaining linear batch factor, and use `hκ` to
show division by the fixed positive spectral floor is harmless.

Implementation recipe (execute in this order):
1. Define `s n := ((n+1 : Nat) : Real) * cmdsEntrywiseRate ...`; obtain
   `hs : Tendsto s atTop (𝓝 0)` from
   `safe_scaled_cmdsEntrywiseRate_zero`.
2. Prove the stronger weighted limit
   `((n+1 : Real) * (s n)^2) → 0` by unfolding the safe rate once and comparing
   powers; `hs` alone is not sufficient without a rate.
3. Multiply by fixed constants `d`, `4`, and `((κ/2)^2)⁻¹`; prove the denominator
   nonzero from `hκ`.
4. Normalize the target expression to that product with `field_simp` and `ring`.
5. Conclude by `Tendsto.const_mul`; keep this separate from `configBound` so any
   exponent correction is localized here.
-/
theorem safe_polar_expression_zero
    (m d : Nat) (hm : 0 < m)
    (populationResponseBound κ : Real) (hκ : 0 < κ) :
    Tendsto (fun n =>
      (d : Real) *
        (4 * ((n + 1 : Nat) : Real) *
          ((((n + 1 : Nat) : Real) *
            cmdsEntrywiseRate (n + 1) m
              (responseDistBound m
                (populationResponseBound + safeResponseTolerance n))
              (safeResponseTolerance n)) ^ 2) / (κ / 2) ^ 2))
      atTop (𝓝 0) := by
  sorry

/-- The complete deterministic configuration envelope vanishes under the safe
schedule and linear population spectral ceiling.

Treat the summands in `configBound` separately.  Use the preceding scaled-rate
limit, the ceiling `4(n+1)B²`, and positivity of `κ/2`.  Loose domination is
preferred; this theorem exists so the final constructor does not contain a
single monolithic asymptotic calculation.

Implementation recipe (execute in this order):
1. Inspect the exact definition of `configBound` and name its three summands
   `t1`, `t2`, and `t3` in local `let`s.
2. Use `safe_scaled_cmdsEntrywiseRate_zero` for the scaled perturbation `e n` and
   the explicit ceiling `4*(n+1)*perspectiveBound^2`.
3. For every square-root term, prove the radicand tends to zero by explicit power
   comparison under `safeResponseTolerance`; then apply continuity of `Real.sqrt`
   at zero.
4. Handle division by `κ/2` using `hκ`, and fixed factors with constant
   multiplication.
5. Combine the three limits with `Tendsto.add` and normalize back to
   `configBound` by `simpa [configBound, t1, t2, t3]`.
6. Do not appeal only to continuity in `e`; the ceiling grows with `n`, so each
   weighted product must be shown to vanish explicitly.
-/
theorem safe_configBound_zero
    (m d : Nat) (hm : 0 < m)
    (populationResponseBound perspectiveBound κ : Real)
    (hκ : 0 < κ) :
    Tendsto (fun n =>
      configBound (n + 1) d (κ / 2)
        (4 * ((n + 1 : Nat) : Real) * perspectiveBound ^ 2)
        (((n + 1 : Nat) : Real) *
          cmdsEntrywiseRate (n + 1) m
            (responseDistBound m
              (populationResponseBound + safeResponseTolerance n))
            (safeResponseTolerance n))) atTop (𝓝 0) := by
  sorry

/-- The conservative tolerance and linear spectral ceiling satisfy every field
of `GrowingConfigControl` for the current proved CMDS perturbation bound.

Completing this theorem removes `Hrate`, entrywise nonnegativity, the local
smallness inequality, the polar inequality, and the vanishing configuration
bound from the final public theorem.  This is intentionally a safe-rate result;
a later sharp Davis--Kahan theorem may improve the exponent without changing
the Perfect Quench interface.

Proof plan:
1. unfold `cmdsEntrywiseRate`, `responseFrobRate`, `responseDistBound`, and the
   safe tolerance;
2. prove the scaled entry rate is `O((n+1)⁻²)`;
3. prove the polar term is `O((n+1)⁻³)`;
4. bound each of the three square-root summands in `configBound` separately
   using the linear ceiling;
5. invoke `GrowingConfigControl.of_tendsto`.
Mark any future replacement by sharper spectral theory here, but retain the
proved bespoke finite theorem until the replacement removes a public premise.

Implementation recipe (execute in this order):
1. Set `entryRate n` to the displayed `cmdsEntrywiseRate` and `ceiling n` to the
   displayed linear ceiling.
2. Prove `entry_nonneg` by unfolding the response/CMDS rates and using
   `hresponse`, `safeResponseTolerance_pos`, `hm`, and positivity.
3. Supply `hscaled` with `safe_scaled_cmdsEntrywiseRate_zero`.
4. Supply `hpolar` with `safe_polar_expression_zero`.
5. Supply `hbound` with `safe_configBound_zero`.
6. Apply `GrowingConfigControl.of_tendsto` with `α := κ/2`; discharge positivity
   from `hκ`.
7. Use named arguments so `count := fun n => n+1` and the exact ceiling/entry
   functions are not inferred incorrectly.
8. No new asymptotic algebra belongs in this theorem; all failures should be
   repaired in the three preceding limit lemmas.
-/
noncomputable def safe_growingConfigControl
    (m d : Nat) (hm : 0 < m)
    (populationResponseBound perspectiveBound κ : Real)
    (hresponse : 0 ≤ populationResponseBound)
    (hperspective : 0 ≤ perspectiveBound)
    (hκ : 0 < κ) :
    GrowingConfigControl (fun n => n + 1) d (κ / 2)
      (fun n => 4 * ((n + 1 : Nat) : Real) * perspectiveBound ^ 2)
      (fun n => cmdsEntrywiseRate (n + 1) m
        (responseDistBound m
          (populationResponseBound + safeResponseTolerance n))
        (safeResponseTolerance n)) := by
  sorry

end DkpsQuench.Perfect
