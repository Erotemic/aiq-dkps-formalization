/-
Compatibility entry point for older `AcharyyaMDS` imports.

The paper-specific scaffolds now live in separate libraries:
- `Acharyya2024` for asymptotic DKPS/raw-stress MDS consistency.
- `Acharyya2025` for finite-sample DKPS concentration.

This file intentionally contains no declaration-level assumptions.
-/

import Acharyya2024.Basic
import Acharyya2025.Basic
