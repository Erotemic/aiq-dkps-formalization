/-
# Gram / Procrustes rigidity challenge solution file

This file imports the staged AIQ `ForMathlib` module that proves the headline
claim stated in `Challenge/Gram/Conformance.lean`. The supporting lemmas it is
built from are tracked in the `Challenge/Inventory/GramGeometry` challenge.
-/

import ForMathlib.Analysis.InnerProductSpace.GramMatrix

#print axioms ForMathlib.Matrix.gram_eq_gram_iff_exists_linearIsometryEquiv_map_eq
