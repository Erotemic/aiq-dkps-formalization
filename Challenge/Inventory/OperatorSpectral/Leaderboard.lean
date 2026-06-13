/-
# AIQ DKPS ForMathlib inventory solution: Operator spectral perturbation and projections

Imports the corresponding project `ForMathlib` staging files. The declarations
named in the comparator config are provided by those imports.
-/
import ForMathlib.Analysis.InnerProductSpace.Spectrum
import ForMathlib.Analysis.InnerProductSpace.CourantFischer
import ForMathlib.Analysis.InnerProductSpace.DavisKahan

/-! Axiom audit commands for this inventory group. -/
#print axioms ForMathlib.inner_eigenvectorBasis_map_sub_eigenvectorBasis
#print axioms ForMathlib.finrank_specSubspace
#print axioms ForMathlib.repr_eq_zero_of_mem_specSubspace
#print axioms ForMathlib.re_inner_map_self_eq_sum_eigenvalues_mul_sq
#print axioms ForMathlib.exists_unit_vector_re_inner_le_eigenvalue
#print axioms ForMathlib.forall_unit_vector_eigenvalue_le_re_inner
#print axioms ForMathlib.abs_eigenvalues_sub_le
#print axioms ForMathlib.abs_eigenvalues_sub_le_opNorm
#print axioms ForMathlib.sum_norm_inner_eigenvectorBasis_map_sub_sq_le
#print axioms ForMathlib.sum_cross_norm_inner_eigenvectorBasis_sq_le
#print axioms ForMathlib.gap_of_rank_floor
#print axioms ForMathlib.sum_cross_norm_inner_eigenvectorBasis_sq_le_of_rank_floor
#print axioms ForMathlib.Orthonormal.starProjection_span_image_apply
#print axioms ForMathlib.Orthonormal.starProjection_span_image_apply_self
#print axioms ForMathlib.Orthonormal.norm_sq_starProjection_span_image
#print axioms ForMathlib.sum_norm_sub_starProjection_span_sq_eq
#print axioms ForMathlib.sum_norm_sub_starProjection_span_sq_le
