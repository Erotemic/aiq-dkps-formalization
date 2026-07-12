# Perfect Quench completion scaffold

This directory is the proof plan for the smallest honest end-to-end Quench
interface.  It is intentionally executable Lean source rather than a prose-only
roadmap: every remaining mathematical seam is represented by a theorem with an
open proof body, and every final result is already stated in the form that the
completed lower layers should support.

The production theorems outside this directory remain unchanged and proved.
Nothing in this scaffold should replace a working bespoke argument merely for
style.  A replacement is valuable only when it removes or weakens a hypothesis
visible to callers.

## Target theorem

The final fixed-subset theorems are:

- `perfectQuench_finite_fixedSubset` for finite model classes;
- `perfectQuench_infinite_fixedSubset` for compact infinite model classes.

The final all-budget theorems are:

- `perfectQuench_finite_allQueries`;
- `perfectQuench_infinite_allQueries`.

The finite theorem starts from raw iid response replicates, a population
response map, exact response-distance realization of the perspective, one
population covariance nondegeneracy condition, full support, and score
Lipschitzness.  The infinite theorem adds exactly the finite-net entropy and
response-regularity assumptions required to derive uniform concentration.

## Dependency graph

```text
Definitions
├── PopulationGeometry
├── SpectralRegularity
│   └── RawResponses
│       └── Compactness
│           └── UniformConcentration
│               └── RateSchedule
│                   └── SpectralCapstone
│                       └── Capstone
└───────────────────────────────────────┘
```

The import order is linear to keep elaboration predictable, but the mathematical
work is more parallel than the import graph suggests:

1. Population geometry is independent of probability.
2. Spectral regularity depends only on population geometry and iid references.
3. Raw responses depends on the product probability space and sample-mean
   algebra, not on spectral perturbation.
4. Compactness derives response envelopes, raw-to-mean regularity, and
   polynomial finite nets.
5. Infinite-class uniform concentration builds on those finite nets.
6. Rate schedules are elementary asymptotic arithmetic and choose the canonical
   net radius and entropy-aware replicate budget.
7. Spectral capstones are event-intersection and theorem-composition work.
8. Final capstones assemble the preceding certificates and lift across query
   subsets.

## Open-proof inventory

| Module | Open proofs | Main mathematical work | Current hypotheses removed when complete |
|---|---:|---|---|
| `PopulationGeometry.lean` | 4 | finite centering and double-centering algebra | explicit configuration, Gram identity, radial identity, PSD, rank |
| `SpectralRegularity.lean` | 15 | covariance measurability/weak law, quadratic-form transfer, augmented scatter | global samplewise eigenvalue floor and ceiling |
| `RawResponses.lean` | 9 | product-space iid lifting, replicate means, finite union bound | abstract response means, per-index moment events, manual measurability |
| `Compactness.lean` | 8 | finite/compact response envelopes, raw-to-mean Lipschitz bridges, polynomial Euclidean covers | explicit population bounds, nets, entropy certificates, separate regularity proofs |
| `UniformConcentration.lean` | 8 | finite-net concentration and deterministic extension | finite model-class restriction or assumed uniform concentration |
| `RateSchedule.lean` | 10 | polynomial limit arithmetic, canonical shrinking net and entropy schedule | caller-built nets, entry rates, and `GrowingConfigControl` |
| `SpectralCapstone.lean` | 3 | high-probability event intersections and reuse of the proved CMDS bound | global spectral hypotheses in the response bridge |
| `Capstone.lean` | 4 | final assembly and query-subset quantifier lift | all remaining intermediate certificates |
| **Total** | **61** | | |

The count is meant to track real proof debt.  Small algebraic or measurability
facts have their own obligations; the probability-heavy covariance and
finite-net results remain larger because they represent genuinely larger pieces
of mathematics.  The four final proofs should be short compositions once the
lower modules are complete.

## Module guidance

### PopulationGeometry

Prove the finite Euclidean double-centering identity directly.  Do not invoke an
eigendecomposition.  The intended public assumption is
`ModelResponseRealization`; all configuration-level data must be derived from
it.  This track should be completed first because several later theorem types
mention its Gram witness.

### SpectralRegularity

The goal is not a sharp random-matrix theorem.  A fixed-dimensional entrywise
weak law plus a finite union bound is sufficient.  The essential public
assumption is `PerspectiveNondegeneracy`, a population covariance floor.  Do not
reintroduce a stagewise spectral floor as a field of a final assumptions
structure.

The production CMDS proof currently uses a bespoke cross-energy and polar-factor
argument.  Retain it.  New Davis--Kahan machinery should enter only if it removes
`polar_eventually` or another caller-visible condition.

### RawResponses

Keep reference randomness and response randomness on independent factors of a
product probability space.  This prevents selection bias when a random
reference chooses which cached response array is averaged.  Reuse the existing
matrix-valued replicate-mean second-moment theorem rather than reproving sample
mean algebra.

### Compactness

Derive every finite-dimensional auxiliary object rather than exposing it in the
final theorem.  Finite model classes supply response norm envelopes by a finite
maximum.  Compact infinite classes use one pathwise raw-response Lipschitz
constant to derive sample-mean and population-mean regularity, a population
response envelope, and polynomial finite covers.  The exact constants are not
important; eliminating coupled caller certificates is.

### UniformConcentration

Never ask for measurability of an uncountable universal event.  Concentrate on a
finite stage net, prove that finite event measurable, and use regularity only in
the deterministic event-inclusion field.  The finite-model route should remain
a direct union bound and should not depend on this module's entropy machinery.

### RateSchedule

The polynomial exponents are deliberately conservative.  Finish the theorem by
power comparison; do not optimize constants.  A later rate-sharpening patch may
change the schedule without changing either final theorem signature.

### SpectralCapstone

Copy the event construction in
`highProbQQueryEfficient_tieAverage_of_growing_augmented_cmds`.  The substantive
change is that floor and ceiling facts come from `GrowingSpectralSubevents` only
after entering its event.  The existing pairwise-distance perturbation theorem
should be used unchanged.

### Capstone

Do not add new mathematics here.  Each fixed-subset proof should construct the
geometry, response, spectral, and rate certificates and pass them to the
spectral capstone.  Each all-query proof should unfold the corresponding
predicate and apply the fixed-subset theorem.

## Suggested parallel assignment

- Agent A: `PopulationGeometry.lean`.
- Agent B: first seven obligations in `SpectralRegularity.lean`.
- Agent C: `RawResponses.lean`.
- Agent D: `Compactness.lean`, especially raw-to-population Lipschitzness and
  finite-dimensional covering numbers.
- Agent E: `UniformConcentration.lean` after the compactness interfaces settle.
- Agent F: `RateSchedule.lean`.
- Agent G: `SpectralCapstone.lean` after population geometry is stable.
- Final integrator: the last constructor in `SpectralRegularity.lean` and all of
  `Capstone.lean`.

Agents should preserve theorem signatures unless a signature is false or cannot
express the intended dependency.  When a change is necessary, update this file,
the relevant theorem docstring, and
`papers/DKPS-formalized-vs-literature.tex` in the same patch.

## Validation commands

During scaffold development, open proof bodies are expected.  The important
checks are that every declaration elaborates and no accidental placeholders are
introduced outside this directory.

```bash
lake build DkpsQuench.Perfect
lake build Acharyya2024 Acharyya2025 DkpsQuench Helm2025

grep -RIn '\bsorry\b' DkpsQuench/Perfect
grep -RIn '\baxiom\b' DkpsQuench/Perfect
```

The first grep should report exactly the inventory above until the program is
complete.  The second should report no declarations.
