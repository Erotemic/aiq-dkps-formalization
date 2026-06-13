# PR-oriented inventory challenge groups

The monolithic inventory challenge is split here into smaller theorem-family
modules that better match plausible Mathlib PR tracks. Each group has its own
`Conformance.lean`, `Leaderboard.lean`, and `comparator/aiq-inventory-*.json`
config.

These groups are audit and planning artifacts. They are not commitments that a
Mathlib PR should contain exactly this set of declarations.

| Group | Comparator config | Theorems | Intended review axis |
|---|---:|---:|---|
| `Probability` | `comparator/aiq-inventory-probability.json` | 13 | Probability, moments, and concentration |
| `OperatorSpectral` | `comparator/aiq-inventory-operator-spectral.json` | 17 | Operator spectral perturbation and projections |
| `GramGeometry` | `comparator/aiq-inventory-gram-geometry.json` | 9 | Gram geometry and near-isometry |
| `RankPsd` | `comparator/aiq-inventory-rank-psd.json` | 8 | Rank factorization and PSD Gram realization |
| `MatrixSpectral` | `comparator/aiq-inventory-matrix-spectral.json` | 11 | Matrix spectral functions and entrywise eigenvalue bounds |
| `Measurability` | `comparator/aiq-inventory-measurability.json` | 3 | Measurability and compact-existential infrastructure |
| `Berge` | `comparator/aiq-inventory-berge.json` | 8 | Approximate minimizers and Berge-style continuity |

The legacy aggregate files remain at `Challenge/Inventory/Conformance.lean` and
`Challenge/Inventory/Leaderboard.lean`; use them only when an all-inventory audit
is desired.
