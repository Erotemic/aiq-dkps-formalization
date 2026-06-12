/-
# Gram / Procrustes rigidity challenge solution file

This file imports the staged AIQ `ForMathlib` module that proves the claims
stated in `Challenge/Gram/Conformance.lean`.
-/

import ForMathlib.Analysis.InnerProductSpace.GramMatrix

#print axioms ForMathlib.exists_linearIsometryEquiv_map_eq_of_inner_eq
#print axioms ForMathlib.Matrix.gram_eq_gram_iff_exists_linearIsometryEquiv_map_eq
