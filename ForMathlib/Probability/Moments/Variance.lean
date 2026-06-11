/-
Staged for Mathlib: additions to `Mathlib/Probability/Moments/Variance.lean`.

Formalized by Claude Fable 5, per user-observed model label (claude-fable-5[1m]);
to be re-authored per Mathlib's AI-contribution policy at PR time.
-/

import Mathlib.Probability.Moments.Variance

/-! # Uncentered second-moment Chebyshev inequality

`P {ω | η < Y ω} ≤ ENNReal.ofReal (v / η ^ 2)` from `∫ Y² ≤ v`, for a real
random variable `Y` that need not be centered, nonnegative, or measurable
(integrability of `Y ^ 2` suffices).

Mathlib's `meas_ge_le_variance_div_sq` is the centered version and requires
`MemLp Y 2`; concentration arguments routinely need the raw second-moment form
below, applied to error norms `Y = ‖Xᵢ - μᵢ‖`.
-/

namespace ForMathlib

open MeasureTheory

/--
**Uncentered second-moment Chebyshev.**  If `∫ Y² ≤ v` and `0 < η`, then
`P {ω | η < Y ω} ≤ ENNReal.ofReal (v / η ^ 2)`.  No measurability of `Y` is
required beyond integrability of `Y ^ 2`.
-/
theorem meas_gt_le_ofReal_integral_sq_div_sq {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {Y : Ω → ℝ}
    (hY_int : Integrable (fun ω => Y ω ^ 2) P)
    {v η : ℝ} (hη : 0 < η) (hmoment : ∫ ω, Y ω ^ 2 ∂P ≤ v) :
    P {ω | η < Y ω} ≤ ENNReal.ofReal (v / η ^ 2) := by
  -- Markov on `Y ^ 2` at level `η ^ 2`.
  have hsq_nonneg : 0 ≤ᵐ[P] fun ω => Y ω ^ 2 :=
    Filter.Eventually.of_forall fun ω => sq_nonneg (Y ω)
  have hmarkov :
      η ^ 2 * P.real {ω | η ^ 2 ≤ Y ω ^ 2} ≤ ∫ ω, Y ω ^ 2 ∂P :=
    mul_meas_ge_le_integral_of_nonneg hsq_nonneg hY_int (η ^ 2)
  -- The bad set is contained in the squared-threshold set.
  have hsubset : {ω | η < Y ω} ⊆ {ω | η ^ 2 ≤ Y ω ^ 2} := fun ω hω =>
    pow_le_pow_left₀ hη.le (le_of_lt hω) 2
  have hηsq_pos : 0 < η ^ 2 := by positivity
  -- Real-valued bound on `P.real` of the bad set.
  have hbad_real : P.real {ω | η < Y ω} ≤ v / η ^ 2 := by
    have hmono : P.real {ω | η < Y ω} ≤ P.real {ω | η ^ 2 ≤ Y ω ^ 2} :=
      measureReal_mono hsubset
    have h2 : η ^ 2 * P.real {ω | η < Y ω} ≤ v :=
      ((mul_le_mul_of_nonneg_left hmono hηsq_pos.le).trans hmarkov).trans hmoment
    rw [le_div_iff₀ hηsq_pos]
    linarith
  -- Convert to `ENNReal`.
  have hne_top : P {ω | η < Y ω} ≠ ⊤ := measure_ne_top P _
  calc P {ω | η < Y ω}
      = ENNReal.ofReal (P.real {ω | η < Y ω}) := by
        rw [measureReal_def, ENNReal.ofReal_toReal hne_top]
    _ ≤ ENNReal.ofReal (v / η ^ 2) := ENNReal.ofReal_le_ofReal hbad_real

end ForMathlib
