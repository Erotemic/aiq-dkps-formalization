/-
# AIQ DKPS ForMathlib inventory solution: Matrix spectral functions and entrywise eigenvalue bounds

Imports the corresponding project `ForMathlib` staging files. The declarations
named in the comparator config are provided by those imports.
-/
import ForMathlib.Analysis.Matrix.EntrywiseOpNorm
import ForMathlib.Analysis.Matrix.SpectralFunctionMeasurable
import ForMathlib.Analysis.Matrix.EntrywiseEigenvalue

/-! Axiom audit commands for this inventory group. -/
#print axioms ForMathlib.sum_norm_le_sqrt_card_mul_norm
#print axioms ForMathlib.norm_toEuclideanLin_le_of_entry_le
#print axioms ForMathlib.Matrix.exists_polynomial_uniform_close
#print axioms ForMathlib.Matrix.abs_coord_le_norm
#print axioms ForMathlib.Matrix.abs_sortedEig_le_of_entry_le
#print axioms ForMathlib.Matrix.pow_mulVec_eigenvector
#print axioms ForMathlib.Matrix.aeval_mulVec_eigenvector
#print axioms ForMathlib.Matrix.mulVec_eigenvectorBasis
#print axioms ForMathlib.Matrix.aeval_entry_eq_sum
#print axioms ForMathlib.Matrix.abs_specTransform_sub_aeval_le
#print axioms ForMathlib.Matrix.abs_sortedEig_sub_le_of_entry_le
