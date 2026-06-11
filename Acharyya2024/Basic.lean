/-
Entry point for the Acharyya et al. 2024 DKPS consistency scaffold.

This library is intentionally separate from `Acharyya2025`: the 2024 paper is
asymptotic consistency of DKPS/raw-stress MDS, while the 2025 paper is finite-
sample concentration. Keeping them separate makes dependency direction and audit
status clearer.
-/

import Acharyya2024.WellKnown
import Acharyya2024.Common
import Acharyya2024.Consistency

import Acharyya2024.Probability
import Acharyya2024.SecondMoment
import Acharyya2024.RawStress
