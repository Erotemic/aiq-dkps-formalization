/-
Measurability of the sample CMDS matrix and the CMDS-entrywise-closeness event,
from measurability of the sample dissimilarity matrix alone.

These are the measurability facts the DkpsQuench / Helm bridges use to discharge
the `hmeas_spec` seam: the sample CMDS matrix is a measurable function of the
sample (every entry is algebraic in the `Dhat` entries), so the
CMDS-entrywise-closeness event is Borel — and that event is *deterministically*
contained in the alignment-existence event
(`AlignedPipeline.alignExists_of_entrywiseClose`), so it serves directly as the
measurable high-probability sub-event, with no eigenvector measurability ever
needed.  See `docs/planning/hmeas-spec-discharge.md`.

The genuinely-general measurability fact used along the way — that a continuous
spectral function `Σₖ h(λₖ) uₖuₖᵀ` of a measurable Hermitian-matrix family is
measurable (no functional calculus, no eigenbasis selection) — is staged
independently as a Mathlib candidate in
`ForMathlib/Analysis/Matrix/SpectralFunctionMeasurable.lean`
(`ForMathlib.Matrix.measurable_specTransform`).

Formalized by Claude Fable 5 (claude-fable-5[1m]) and Claude Opus 4.8
(claude-opus-4-8[1m]).
-/

import Acharyya2025.MatrixPerturbation
import Acharyya2025.AlignedPipeline

open scoped BigOperators Matrix
open MeasureTheory

namespace Acharyya2025.SpectralMeasurability

open Acharyya2024

variable {n : ℕ}

/-- `Matrix` is a type-level def, so the pi `MeasurableSpace` instance does not
fire on it; register it (entrywise σ-algebra, matching the pi topology). -/
instance : MeasurableSpace (Matrix (Fin n) (Fin n) ℝ) :=
  inferInstanceAs (MeasurableSpace (Fin n → Fin n → ℝ))

instance : BorelSpace (Matrix (Fin n) (Fin n) ℝ) :=
  inferInstanceAs (BorelSpace (Fin n → Fin n → ℝ))

open Acharyya2025.AlignedPipeline Acharyya2025.MathlibBridge Acharyya2025.Deterministic in
/-- Glue: the sample CMDS matrix is a measurable function of the sample whenever
the dissimilarity matrix is — every entry is a finite algebraic expression in
the entries of `Dhat`. -/
theorem measurable_cmds_matrix {Ω : Type} [MeasurableSpace Ω]
    (Dhat : Nat → Ω → DisMat n) (u : Nat)
    (hD : Measurable fun ω => Dhat u ω) :
    Measurable fun ω => disMatToMatrix (classicalMDSMatrix (Dhat u ω)) := by
  have hentry : ∀ a b : Fin n, Measurable fun ω => Dhat u ω a b := fun a b =>
    (measurable_pi_apply b).comp ((measurable_pi_apply a).comp hD)
  have hsq : ∀ a b : Fin n, Measurable fun ω => (Dhat u ω a b) ^ 2 := fun a b =>
    (hentry a b).pow_const 2
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  show Measurable fun ω =>
    -(1 / 2 : ℝ) * doubleCenter (fun a b => (Dhat u ω a b) ^ 2) i j
  refine Measurable.const_mul ?_ _
  rw [show (fun ω => doubleCenter (fun a b => (Dhat u ω a b) ^ 2) i j)
      = fun ω => (Dhat u ω i j) ^ 2
          - rowMean (fun a b => (Dhat u ω a b) ^ 2) i
          - colMean (fun a b => (Dhat u ω a b) ^ 2) j
          + grandMean (fun a b => (Dhat u ω a b) ^ 2) from rfl]
  refine Measurable.add (Measurable.sub (Measurable.sub (hsq i j) ?_) ?_) ?_
  · -- rowMean
    rw [show (fun ω => rowMean (fun a b => (Dhat u ω a b) ^ 2) i)
        = fun ω => ((n : ℝ)⁻¹) * ∑ b : Fin n, (Dhat u ω i b) ^ 2 from rfl]
    exact (Finset.measurable_sum _ fun b _ => hsq i b).const_mul _
  · -- colMean
    rw [show (fun ω => colMean (fun a b => (Dhat u ω a b) ^ 2) j)
        = fun ω => ((n : ℝ)⁻¹) * ∑ a : Fin n, (Dhat u ω a j) ^ 2 from rfl]
    exact (Finset.measurable_sum _ fun a _ => hsq a j).const_mul _
  · -- grandMean
    rw [show (fun ω => grandMean (fun a b => (Dhat u ω a b) ^ 2))
        = fun ω => ((n : ℝ)⁻¹) ^ 2 * ∑ a : Fin n, ∑ b : Fin n, (Dhat u ω a b) ^ 2 from rfl]
    exact (Finset.measurable_sum _ fun a _ =>
      Finset.measurable_sum _ fun b _ => hsq a b).const_mul _

open Acharyya2025.MathlibBridge Acharyya2025.Deterministic in
/-- **The CMDS-entrywise-closeness event is Borel**, from measurability of the
sample dissimilarity matrix alone — every CMDS entry is a finite algebraic
expression in the `Dhat` entries.  This is the measurable high-probability
sub-event the Quench bridge uses in place of `hmeas_spec`. -/
theorem measurableSet_entrywiseClose_event {Ω : Type} [MeasurableSpace Ω]
    (Dhat : Nat → Ω → DisMat n) (D : DisMat n) (rate : Nat → ℝ) (u : Nat)
    (hD : Measurable fun ω => Dhat u ω) :
    MeasurableSet {ω | Acharyya2025.Bridge.EntrywiseClose
      (classicalMDSMatrix (Dhat u ω)) (classicalMDSMatrix D) (rate u)} := by
  have hcmds : Measurable fun ω => disMatToMatrix (classicalMDSMatrix (Dhat u ω)) :=
    measurable_cmds_matrix Dhat u hD
  have hset : {ω | Acharyya2025.Bridge.EntrywiseClose
        (classicalMDSMatrix (Dhat u ω)) (classicalMDSMatrix D) (rate u)}
      = ⋂ (i : Fin n), ⋂ (j : Fin n),
          {ω | |classicalMDSMatrix (Dhat u ω) i j - classicalMDSMatrix D i j| ≤ rate u} := by
    ext ω; simp [Acharyya2025.Bridge.EntrywiseClose, Set.mem_iInter]
  rw [hset]
  refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_
  have hentry : Measurable fun ω => classicalMDSMatrix (Dhat u ω) i j :=
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hcmds)
  exact (hentry.sub measurable_const).abs measurableSet_Iic

end Acharyya2025.SpectralMeasurability
