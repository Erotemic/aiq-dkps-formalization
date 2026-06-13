/-
# AIQ DKPS ForMathlib inventory solution: Rank factorization and PSD Gram realization

Imports the corresponding project `ForMathlib` staging files. The declarations
named in the comparator config are provided by those imports.
-/
import ForMathlib.Analysis.Matrix.Spectrum
import ForMathlib.LinearAlgebra.Matrix.PosDef
import ForMathlib.LinearAlgebra.Matrix.RankFactorization

/-! Axiom audit commands for this inventory group. -/
#print axioms ForMathlib.Matrix.PosSemidef.eigenvalues₀_eq_zero_of_le
#print axioms ForMathlib.Matrix.isHermitian_entry_eq_sum_eigenvalues
#print axioms ForMathlib.Matrix.PosSemidef.exists_eq_conjTranspose_mul_self
#print axioms ForMathlib.Matrix.PosSemidef.exists_conjTranspose_mul_self_of_rank_le
#print axioms ForMathlib.Matrix.posSemidef_and_rank_le_iff_exists_conjTranspose_mul_self
#print axioms ForMathlib.Matrix.exists_eq_mul_rank
#print axioms ForMathlib.Matrix.exists_eq_mul_of_rank_le
#print axioms ForMathlib.Matrix.rank_le_iff_exists_eq_mul
