/-
# AIQ DKPS ForMathlib inventory solution: Gram geometry and near-isometry

Imports the corresponding project `ForMathlib` staging files. The declarations
named in the comparator config are provided by those imports.
-/
import ForMathlib.Analysis.InnerProductSpace.GramMatrix
import ForMathlib.Analysis.InnerProductSpace.NearIsometry

/-! Axiom audit commands for this inventory group. -/
#print axioms ForMathlib.inner_linearCombination_linearCombination
#print axioms ForMathlib.exists_linearIsometry_span_map_eq_of_inner_eq
#print axioms ForMathlib.exists_linearIsometry_map_eq_of_inner_eq
#print axioms ForMathlib.exists_linearIsometryEquiv_map_eq_of_inner_eq
#print axioms ForMathlib.Matrix.gram_eq_gram_iff_exists_linearIsometryEquiv_map_eq
#print axioms ForMathlib.Real.abs_one_sub_inv_sqrt_le
#print axioms ForMathlib.LinearMap.exists_linearIsometryEquiv_norm_sub_le
#print axioms ForMathlib.ContinuousLinearMap.exists_linearIsometryEquiv_norm_sub_le
