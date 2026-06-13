/-
# AIQ DKPS ForMathlib inventory solution: Probability, moments, and concentration

Imports the corresponding project `ForMathlib` staging files. The declarations
named in the comparator config are provided by those imports.
-/
import ForMathlib.MeasureTheory.Measure.Typeclasses.Probability
import ForMathlib.Probability.Moments.Variance
import ForMathlib.Probability.Moments.SampleMean
import ForMathlib.MeasureTheory.Function.ConvergenceInMeasure
import ForMathlib.Probability.Moments.MatrixConcentration
import ForMathlib.Probability.Moments.SampleCovariance

/-! Axiom audit commands for this inventory group. -/
#print axioms ForMathlib.one_sub_measure_compl_le
#print axioms ForMathlib.meas_gt_le_ofReal_integral_sq_div_sq
#print axioms ForMathlib.integral_sq_scaledSum_sub_of_pairwise_indep
#print axioms ForMathlib.integral_norm_sq_average_sub_eq_sum
#print axioms ForMathlib.integral_norm_sq_average_sub_of_iid
#print axioms ForMathlib.integral_norm_sq_average_sub_le_of_bound
#print axioms ForMathlib.tendstoInMeasure_of_tendsto_measure_rate_lt_edist
#print axioms ForMathlib.tendstoInMeasure_of_tendsto_measure_rate_lt_dist
#print axioms ForMathlib.tendstoInMeasure_of_tendsto_measure_dist_le_rate
#print axioms ForMathlib.measure_exists_entry_gt_le
#print axioms ForMathlib.measure_forall_abs_sortedEig_sub_le_ge
#print axioms ForMathlib.measure_forall_sortedEig_ge_ge
#print axioms ForMathlib.integral_sq_sampleCovariance_entry_le
