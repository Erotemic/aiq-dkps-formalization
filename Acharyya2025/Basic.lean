/-
Entry point for the Acharyya et al. 2025 DKPS concentration scaffold.

This library is intentionally separate from `Acharyya2024`: the 2024 paper is
asymptotic consistency of DKPS/raw-stress MDS, while the 2025 paper is finite-
sample concentration. This file depends on `Acharyya2024.Common` for shared finite
matrix/configuration definitions only.
-/

import Acharyya2025.Deterministic
import Acharyya2025.Concentration
