# Davis–Kahan gap-closure plan

Plan for closing the gaps between the Lean formalization and the literature, as
catalogued in `papers/DavisKahan-formalized-vs-literature.tex` §"What is not
formalized". Written for an Opus-level agent; every step names its target file,
statement shape, proof route, Mathlib/ForMathlib assets, pitfalls, and a
difficulty grade.

## Revision log

- **v1 (2026-07-07, Fable):** initial plan.
- **v2 (2026-07-07, Opus review):** added `## Opus review notes` R1–R8;
  rerated W2.4 to 4/5; added statement-first gate to Definition of done.
- **v4 (2026-07-07, Opus — implementation sweep):** executed a large portion of
  the plan. **Closed: G5** (W1.1, W1.2), **G4** (W4.1, W4.2, W4.3), and the full
  **YWS/Hoffman–Wielandt core** (W2.1–W2.4, both branches). **G3 foundations
  complete:** W3.1 (unitary polar decomposition), W0.1(a) Frobenius=∑σ², W0.1(b)
  σ≤1, W0.1(c) tr|A|=∑σ, unitary-invariance of the Frobenius sum, and the W3.4
  core inequality ∑σ²≤∑σ. Every item build-green (8712 jobs) and axiom-clean,
  committed separately. **Remaining:** W3.4 final assembly (connective plumbing,
  all ingredients ready), W0.1(d)+W0.2 (principal-angle API), W5.2 (op-norm
  sin-Θ), W6 (sin2Θ/tan2Θ), W7 (UI norms — deferred by design). Env note: a
  shared-machine sandbox FD ceiling blocks `lake` unless run with the sandbox
  disabled; the Mathlib olean cache needed `lake exe cache get!` recovery once.
- **v3 (2026-07-07, Fable):** every R-note folded into the step text it
  concerns (see per-note status markers in the review section). Major change:
  **W5.1 rerouted from the spectral-integral argument to a purely algebraic
  contraction argument** — no Bochner integrals, no measurability, no
  operator-valued `∫`; rerated 5/5 → 3/5, which dissolves Opus's R6 descope
  concern. Division of labor: **Fable implements W5.1** (hardest item,
  route-discovery-sensitive) and the W2.4 statement-first stubs (the R1 design
  content); **everything else is for Opus**, now unblocked by the corrected
  routes below. Follow the house rules in `dev/mathlib-quality-adapter.md`
(provenance headers, golf gates, `lake build` green after every step, axiom
check `propext, Classical.choice, Quot.sound` on headline declarations).
- **v5 (2026-07-08, Fable — remaining-work detail pass):** verified the v4
  status sweep against source (all ✅ claims confirmed; no sorries anywhere).
  Three route corrections/simplifications for the remaining items, each folded
  into its step below:
  1. **W6.1 needs no ℂ phase alignment** — taking real parts of the subtracted
     eigenvector equations directly gives the key identity with `re ⟪q, H p⟫`;
     the rotation trick then uses only *real* coefficients. The "phase
     alignment" pitfall in the v1 text is dissolved. W6.1 stays 4/5 (the √
     half-angle algebra and degenerate cases remain fiddly) and is **assigned
     to Fable**; with its scaffolding in place W6.2 drops 3/5 → 2/5.
  2. **W0.1(d) only needs the square case** (`E = F`): both W0.2 overlap-map
     spaces are `EuclideanSpace 𝕜 (Fin d)`. There, `A ∘ A† = U ∘ (A† ∘ A) ∘ U†`
     with `U = polarUnitary A` (already in `PolarDecomposition.lean`), so the
     multiplicity-counting route is replaced by "unitary conjugation preserves
     sorted eigenvalues" (Courant–Fischer, both directions already local).
     Rerated 3/5 → 2.5/5.
  3. **W5.2 is decoupled from W0.2**: state the headline as `‖Q̂ ∘L P‖ ≤ ε/g`
     directly (that operator norm *is* `‖sinΘ‖_op`); the principal-angle
     identification becomes an optional bridge lemma after W0.2. With the
     concrete compression recipe below, rerated 3.5/5 → 3/5.
  Updated division of labor: **Fable = W6.1**; **Opus = W0.1(d), W0.2, W5.2,
  W6.2**, then optionally attempt W6.3-Frobenius. W7 stays deferred. Paper
  `papers/DavisKahan-formalized-vs-literature.tex` synced to this state
  (extensions section + remaining-work ranking).

- **v6 (2026-07-08, Opus — remaining-work sweep):** executed every item
  assigned to Opus in the v5 plan, each committed separately, all axiom-clean,
  full library build green (8716 jobs). **Closed: W6.2** (tan2θ), **W0.1(d)**
  (`singularValues_adjoint` + reusable `eigenvalues_conj_unitary`), **W0.2**
  (canonical principal-angle API, new `PrincipalAngles.lean`), **W5.2**
  (operator-norm sin-Θ, new `SinThetaOpNorm.lean` — closing the op-norm half of
  G1). W6.1 (sin2θ) had already been landed by Fable. Two route improvements
  vs the v5 text, both recorded in-step: W5.2 uses a full-space scalar-extension
  argument (no subtype compressions, no CourantFischer un-privatizing), and
  W0.1(d)'s reverse eigenvalue direction reuses the forward `_le` helper via
  `eigenvalues_congr`. **Everything the DKPS pipeline consumes is now
  formalized; only W6.3 (subspace sin2Θ) and W7 (UI norms) remain, both
  deferred by design.**

## The five gaps (from the paper)

| # | Gap | Workstream | Status (2026-07-07) |
|---|-----|------------|---------------------|
| G1 | Operator-norm `‖sinΘ‖_op ≤ ‖S−T‖_op/g` and general unitarily-invariant-norm sinΘ | W5, W7 | ◑ W5.1 ✅ + W5.2 ✅ (op-norm half **closed**); W7 (UI norms) deferred |
| G2 | tanΘ, sin2Θ, tan2Θ theorems | W6 | ◑ W6.1 ✅ (Fable) + W6.2 ✅ (Opus) done in `RotationSharp.lean`; W6.3 defer |
| G3 | YWS aligned-basis bound | W3 | ✅ **closed** (W3.1–W3.4) |
| G4 | YWS singular-vector extension (rectangular `A, Â`) | W4 | ✅ **closed** (W4.1–W4.3) |
| G5 | General-interval spectral subspaces (two-sided gap) | W1 | ✅ **closed** (W1.1, W1.2) |

Plus two enabling workstreams the paper implies but does not list: a canonical
principal-angle API (W0) and Hoffman–Wielandt (W2 — required for the *exact*
YWS constant-2 Frobenius branch, which the current Weyl bridge cannot deliver;
see W2.4 for why).

## Existing assets (verified 2026-07-07, all sorry-free)

In `ForMathlib/Analysis/InnerProductSpace/` (namespace `ForMathlib` unless noted):

- **DavisKahan.lean** — the engine. Overlap encoded as
  `∑_{i∈s} ∑_{j∉s} ‖⟪uᵢ, v̂ⱼ⟫‖²` with `u = hT.eigenvectorBasis hn`,
  `v̂ = hS.eigenvectorBasis hn`; ladder rungs `…_le_offDiag`, `…_le_residual`,
  `…_le_hilbertSchmidt`, `…_le_opNorm`; Weyl bridges `gap_of_eigengap`,
  `gap_of_rank_floor`; projector identity
  `sum_norm_sub_starProjection_span_sq_eq` (`‖P̂−P‖²_F = 2·overlap`, already
  stated for an **arbitrary** `s : Finset (Fin m)`).
- **Spectrum.lean** — cross-term identity
  `inner_eigenvectorBasis_map_sub_eigenvectorBasis`:
  `⟪uᵢ,(S−T)v̂ⱼ⟫ = (μⱼ−λᵢ)⟪uᵢ,v̂ⱼ⟫`.
- **CourantFischer.lean** — Courant–Fischer both directions; Weyl
  `abs_eigenvalues_sub_le` (`|λₖ(T)−λₖ(S)| ≤ ε`).
- **SchurHorn.lean** — `schurWeight hT hn e i k = ‖⟪vᵢ, e k⟫‖²`, doubly
  stochastic (`schurWeight_row_sum`, `schurWeight_col_sum`); Karamata
  majorization `convexOn_sum_re_inner_orthonormalBasis_self_le`.
- **EigenvalueChange.lean** — Birkhoff bridge
  `diag_mem_convexHull_perm_spectrum` (uses
  `doublyStochastic_eq_convexHull_permMatrix`); Davis Thm 4.1.
- **PositiveSqrt.lean** (`namespace LinearMap.IsPositive`) — spectral PSD
  `sqrt` with uniqueness, `ker_sqrt`, `range_sqrt`, `sq_norm_sqrt_apply`.
- **PartialIsometry.lean** — `IsPartialIsometry` predicate + operator
  characterizations, constructor `isPartialIsometry_of_isometryOn`.
- **PolarDecomposition.lean** — `abs A`, `polarFactor A`,
  `polar_decomposition : A = polarFactor A ∘ₗ abs A`, `ker/range_polarFactor`,
  unitary case `polarUnitaryEquiv`, CFC bridge.
- **IntertwiningUnitary.lean** — `spectralProjection b S` (rank-one sums),
  `OrthoProjFamily`, Davis §2 `intertwiningUnitary`, `sqSinAngle`.
- **RotationBound.lean** — Davis Thm 3.2 + `rotation_le_two_mul_offDiag`.
- **NearIsometry.lean** — quantitative polar factor over ℝ (pattern for
  eigenbasis-defined operator functions; has a `TODO(RCLike)`).

Mathlib (pinned master `308db4b`, toolchain v4.32.0-rc1) **has**:
`LinearMap.singularValues : ℕ →₀ ℝ` (descending, `singularValues_antitone`,
`sq_singularValues_fin`, `card_support_singularValues`) in
`Analysis/InnerProductSpace/SingularValues.lean`; matrix Frobenius norm
(scoped `Matrix.Norms.Frobenius`); CFC `sqrt`/`abs`; Rayleigh quotients;
`LinearMap.IsSymmetric.eigenvalues/eigenvectorBasis` (sorted);
`Submodule.starProjection` API; `doublyStochastic_eq_convexHull_permMatrix`;
rearrangement inequality (`Algebra/Order/Rearrangement.lean`,
`MonovaryOn.sum_smul_comp_perm_le_sum_smul` family); Bochner integration.

Mathlib **lacks** (do not search for these upstream): matrix SVD
factorization, Schatten/Ky Fan/unitarily invariant norms, symmetric gauge
functions, principal angles, Hoffman–Wielandt, polar decomposition
(ForMathlib supplies it), Weyl eigenvalue perturbation (ForMathlib supplies
it), operator Hilbert–Schmidt norm as a bundled norm (the project encodes
`‖B‖²_F` as `∑ₖ ‖B(bₖ)‖²` over an orthonormal basis — keep that convention).

## Statement-shape conventions (apply to every step)

- Variables: `{𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] {n : ℕ}`,
  hypotheses `hT : T.IsSymmetric`, `hn : finrank 𝕜 E = n`, eigendata via
  Mathlib's `hT.eigenvalues hn` / `hT.eigenvectorBasis hn`.
- Frobenius quantities as explicit finite sums (`∑ⱼ ‖(S−T)v̂ⱼ‖²`), never a
  bundled HS norm; operator-norm hypotheses in the elementwise form
  `hε : ∀ x, ‖(S−T) x‖ ≤ ε * ‖x‖` (matches `gap_of_eigengap`).
- Gap hypotheses as explicit `∀ i j, … → … → g ≤ |…|` quantifications.
- **Boundary eigenvalue conventions (per Opus R2):** never encode YWS's
  `λ₀ = ∞`, `λ_{p+1} = −∞` sentinels. State edge-touching gaps as two guarded
  hypotheses — `hlow : r ≠ 0 → Δ ≤ λ_{r-1}(T) − λ_r(T)` and
  `hhigh : s + 1 ≠ n → Δ ≤ λ_s(T) − λ_{s+1}(T)` (vacuous at the spectrum
  edges) — and phrase complement sums over the actual `sᶜ`, so no fictitious
  index is ever referenced. Applies to W1.2, W2.4, W4.3.
- Names follow the existing `sum_cross_norm_inner_eigenvectorBasis_sq_le_*`
  pattern; `theorem` over `lemma` except for definitional glue; every public
  declaration gets a docstring citing the paper result it formalizes.
- Each new file: staging provenance header (`/- Staged for Mathlib: … -/`),
  added to `ForMathlib.lean` only when sorry-free.

---

## W0 — Canonical principal-angle API (foundation)

New file `ForMathlib/Analysis/InnerProductSpace/PrincipalAngles.lean`.
This is the "full canonical-angle API" the paper names as missing, and it is
the shared substrate for G1, G2, G3. Build it on Mathlib's
`LinearMap.singularValues`.

**W0.1 — Singular-value glue lemmas. Difficulty 3/5. ◑ MOSTLY DONE 2026-07-07
(Opus).** In `SingularSubspace.lean`: (a) `sum_sq_singularValues`
(`∑ᵢ σᵢ(A)² = ∑ₖ ‖A bₖ‖²`); (b) `singularValues_le_one_of_contraction`
(`‖Ax‖≤‖x‖ ⇒ σᵢ ≤ 1`); (c) `sum_re_inner_abs_self_eq_sum_singularValues`
(`∑ₖ re⟪|A|bₖ, bₖ⟫ = ∑ᵢ σᵢ(A)` — trace of the modulus). Also
`sum_sq_norm_apply_unitary_comp` (unitary invariance of the Frobenius sum, W3.2
groundwork). (d) `singularValues_adjoint` [`σ(A⋆)=σ(A)`] remains — the hard
piece (relates eigenvalues of `AA⋆` and `A⋆A` across different-dim spaces),
needed only for W0.2's symmetry. All build green, axiom-clean.
For `A : E →ₗ[𝕜] F` between finite-dim spaces, prove:
(a) `∑ i, singularValues A i ^ 2 = ∑ₖ ‖A bₖ‖²` for any orthonormal basis `b`
    (Frobenius² = sum of squared singular values; route: diagonalize
    `A.adjoint ∘ₗ A`, use `sq_singularValues_fin` + Parseval);
(b) `singularValues A i ≤ ‖A‖` pointwise, and if `∀ x, ‖A x‖ ≤ ‖x‖`
    (contraction) then `singularValues A i ≤ 1`
    (route: `hasEigenvalue_adjoint_comp_self_sq_singularValues` + Rayleigh);
(c) `∑ i ∈ range d, singularValues A i = re (∑ₖ ⟪bₖ, (abs A) bₖ⟫)` — trace of
    `PolarDecomposition.abs A` equals the sum of singular values (route:
    `abs A` is diagonal in the eigenbasis of `A†A` with entries
    `√λᵢ = σᵢ` by `sqrt_apply_eigenvectorBasis` + `sqrt_unique`);
(d) **`singularValues_adjoint : (A.adjoint).singularValues = A.singularValues`
    — ✅ DONE 2026-07-08 (Opus), `SingularSubspace.lean` (square case),
    axiom-clean.** Delivered `isSymmetric_conj_unitary`, `eigenvalues_congr`,
    `eigenvalues_conj_unitary` (the reusable Courant–Fischer conjugation-invariance
    lemma — independently Mathlib-attractive), `comp_adjoint_eq_conj_adjoint_comp`
    (`A A⋆ = U (A⋆A) U⁻¹`), `eigenvalues_gram_adjoint`, and the headline
    `singularValues_adjoint`. Followed the v5 route exactly; the reverse
    eigenvalue direction reused the forward `_le` helper via
    `eigenvalues_congr` on `U⁻¹ (U S U⁻¹) U = S`.
    **v5 reroute (Fable) — do the SQUARE case only (`A : E →ₗ[𝕜] E`), which is
    all W0.2 consumes** (both overlap-map spaces are `EuclideanSpace 𝕜 (Fin d)`).
    Two lemmas:
    - *(d-i) Unitary conjugation preserves sorted eigenvalues.* For
      `hS : S.IsSymmetric`, `U : E ≃ₗᵢ[𝕜] E`, the conjugate
      `S' = U.toLinearMap ∘ₗ S ∘ₗ U.symm.toLinearMap` is symmetric with
      `hS'.eigenvalues hn = hS.eigenvalues hn`. Route: Courant–Fischer — both
      minimax directions are already in `CourantFischer.lean`, and the
      sup/inf over subspaces is invariant because `Submodule.map U` is a
      dimension-preserving bijection of the subspace lattice that preserves
      Rayleigh quotients (`⟪S'(Ux), Ux⟫ = ⟪S x, x⟫`, `‖Ux‖ = ‖x‖`). Sorted
      lists that satisfy the same minimax characterization are equal
      index-by-index — no multiset/char-poly uniqueness needed.
      Independently Mathlib-attractive.
    - *(d-ii) The conjugation identity.* With `U := polarUnitary A` (already in
      `PolarDecomposition.lean`): `A = U ∘ |A|` and `|A|` self-adjoint give
      `A† = |A| ∘ U†`, hence
      `A ∘ A† = U ∘ |A|² ∘ U† = U ∘ (A† ∘ A) ∘ U†`.
      Then `σᵢ(A†)² = λᵢ(A ∘ A†) = λᵢ(A† ∘ A) = σᵢ(A)²` by (d-i) and Mathlib's
      `sq_singularValues_fin`, and `σ ≥ 0` upgrades squares to values.
    The original cross-space multiplicity-counting route is *superseded*; only
    revive it if some later consumer genuinely needs `E ≠ F` (none currently
    does). This is independently Mathlib-attractive — file a
    `comparator/candidate-*.json`. **Rerated 3/5 → 2.5/5.**
Pitfall: `singularValues` is a `ℕ →₀ ℝ` (finsupp) — write index bookkeeping
lemmas once (`singularValues_fin` mediates `Fin (finrank) → ℕ`).

**W0.2 — Principal angles between equal-dimensional subspaces. Difficulty 3/5.
✅ DONE 2026-07-08 (Opus) — new file `PrincipalAngles.lean`, registered,
library build green (8715 jobs), all headlines axiom-clean.** Delivered:
`cosPrincipalAngles hu hv := (overlapOp hu hv).singularValues`,
`cosPrincipalAngles_{nonneg,le_one,antitone}` (range/order via the existing
contraction lemmas), `overlapOp_adjoint` (`(overlapOp hu hv)⋆ = overlapOp hv hu`,
one line from `adjoint_comp`), the symmetry `cosPrincipalAngles_comm` (the
W0.1(d) payoff — `singularValues_adjoint`), `sinThetaSq hu hv := ∑ (1 − cos²)`,
the bridge `sinThetaSq_eq_sub_overlap` (`‖sinΘ‖²_F = d − overlap`),
`sinThetaSq_{nonneg,comm}`, and `sum_sq_norm_aligned_le_sinThetaSq` (the YWS
aligned-basis bound restated as `∑‖wⱼ−uⱼ‖² ≤ 2‖sinΘ‖²_F`). Deferred as optional
follow-ups (not on any consumer's critical path): the DavisKahan cross-block
bridge (c)/(d) tying `sinThetaSq` of eigenvector blocks to the
`sum_cross_…`/`sum_norm_sub_starProjection_span_sq_eq` encodings, the
`sqSinAngle` rank-one bridge (e), and the op-norm identification (f) — W5.2 no
longer needs (f).
*(historical route notes below.)*
*(Rewritten per Opus R3 — the original mixed a subspace-compression definition
with flat-encoding lemmas; the flat encoding is now the definition itself.)*
**v5 status note (Fable): do NOT redefine the flat operator — it already
exists as `overlapOp hu hv` in `AlignedBasis.lean`** (defined as
`(familyIsometry hu).adjoint ∘ₗ (familyIsometry hv)`, with
`overlapOp_apply` giving the matrix entries `⟪uᵢ, vⱼ⟫`). Already proved there:
contraction (`overlapOp_contraction`), `∑σ² = ∑ᵢⱼ‖⟪uᵢ,vⱼ⟫‖²`
(`sum_sq_singularValues_overlapOp`), σ ≤ 1
(`singularValues_le_one_of_contraction` in `SingularSubspace.lean`), and
`∑σ² ≤ ∑σ`. So W0.2 reduces to: the definition line, symmetry via W0.1(d)
plus `adjoint (overlapOp hu hv) = overlapOp hv hu` (immediate from the
`adjoint` of a composition — `(P⋆ ∘ Q)⋆ = Q⋆ ∘ P`), and bridges (c)–(e) below.
Item (f) is **no longer on W5.2's critical path** (see W5.2 v5 note) — keep it
as an optional bridge lemma.
Given orthonormal families `u : Fin d → E` and `v : Fin d' → E` (chosen bases
of the two subspaces), the **flat overlap operator** is
`overlapOp hu hv : EuclideanSpace 𝕜 (Fin d') →ₗ[𝕜] EuclideanSpace 𝕜 (Fin d)`
with matrix entries `⟪u i, v j⟫`; set
`cosPrincipalAngles hu hv := LinearMap.singularValues (overlapOp hu hv)`.
Do **not** introduce `↥U →ₗ ↥V` compressions anywhere — all three consumers
(W3.3, W5.2 identification, W6 angle forms) want the flat operator. Prove
basis-independence at the level of singular values (conjugating `overlapMap`
by the unitary change-of-basis matrices of `u` and of `v` fixes
`singularValues`), so the notion descends to the subspace pair; a thin
`Submodule`-level wrapper choosing `stdOrthonormalBasis` bases comes last, if
at all. Prove:
(a) antitone, values in `[0,1]` (contraction, W0.1(b): `‖(overlapMap u v) x‖
    ≤ ‖x‖` is Bessel/Parseval);
(b) symmetry `cosPrincipalAngles u v = cosPrincipalAngles v u` via
    `singularValues_adjoint` (W0.1(d) — a required build, not an existing
    lemma; Opus R4) plus `adjoint (overlapMap u v) = overlapMap v u`;
(c) `∑ i, (1 - cosPrincipalAngles u v i ^ 2) = ∑ᵢ∑_{j∉block} ‖⟪uᵢ,wⱼ⟫‖²` when
    `u, v` are orthonormal-basis blocks (`v = w` restricted to the block) —
    the bridge to the DavisKahan.lean overlap encoding (route: W0.1(a) on
    `overlapMap` gives `∑cos² = ∑ᵢⱼ‖⟪uᵢ,vⱼ⟫‖²`; the complementary Parseval
    lemma `OrthonormalBasis.norm_sq_sub_starProjection_span_image` converts
    `d − ∑ᵢⱼ` into the cross-block sum);
(d) `∑ₖ ‖(P_U − P_V) bₖ‖² = 2 ∑ i, sin²θᵢ` (compose (c) with the existing
    projector identity `sum_norm_sub_starProjection_span_sq_eq`);
(e) bridge to `OrthoProjFamily.sqSinAngle` in the rank-one case (compose with
    `sqSinAngle_ofOrthonormalBasis`);
(f) *(for W5.2)* `‖Q̂ ∘ P‖ = max i, sin θᵢ`-form identification, or at minimum
    the inequality `sinθ_max ≤ ‖Q̂ ∘ P‖` needed there.
Define `sinThetaSq u v : ℝ := ∑ i, (1 - cos² …)` as the canonical `‖sinΘ‖²_F`
and restate the sharp DK rung as a thin wrapper over
`sum_cross_…_le_hilbertSchmidt`.

---

## W1 — General-interval spectral subspaces (G5)

Extend `DavisKahan.lean` (or new sibling `DavisKahanInterval.lean` if the file
would pass ~900 lines).

**W1.1 — Engine over an arbitrary index block. Difficulty 2/5. ✅ DONE
2026-07-07 (Opus).** Added `sum_cross_norm_inner_eigenvectorBasis_sq_le_{offDiag,residual,hilbertSchmidt}_block`
taking independent row/column finsets `s t : Finset (Fin n)` with membership gap
hypothesis `∀ i ∈ s, ∀ j ∈ t, gap ≤ |λᵢ(T) − λⱼ(S)|`; the three `d`-block
lemmas are now one-line corollaries (signatures unchanged, external Acharyya
consumer intact). Library build green.
The cross-term engine never uses that the block is `{i | i < d}`; the
projector section already takes `s : Finset (Fin m)`. Generalize
`sum_cross_norm_inner_eigenvectorBasis_sq_le_offDiag/_residual/_hilbertSchmidt`
from the `(·<d)/(d≤·)` split to `s : Finset (Fin n)` with gap hypothesis
`∀ i j, i ∈ s → j ∉ s → g ≤ |hT.eigenvalues hn i − hS.eigenvalues hn j|`.
Keep the current `d`-block statements as one-line corollaries
(`s := univ.filter (·<d)`) so no downstream statement drifts. Mechanical:
re-run the same proofs with `Finset.sum_filter`-style bookkeeping replaced by
`∈ s` / `∉ s`.

**W1.2 — Interval-selected subspaces and two-sided gap. Difficulty 2/5. ✅ DONE
2026-07-07 (Opus).** Added `sum_cross_interval_sq_le_hilbertSchmidt` (rows =
`{i | λᵢ(T) ∈ [a,b]}`, any column block avoiding the `g`-enlarged interval),
the two-sided Weyl bridge `notMem_Ioo_eigenvalues_of_notMem_Ioo`, and the
composed `sum_cross_interval_sq_le_hilbertSchmidt_of_eigengap` (population
interval gap `δ`, `ε`-close ⇒ sharp bound with gap `δ − ε`). Uses the W1.1
block engine with independent row/column finsets exactly as the pitfall note
anticipated. G5 closed.
Define the selected block by spectral membership:
`s := univ.filter (fun i => hT.eigenvalues hn i ∈ Set.Icc a b)` and state:
if every eigenvalue of `S` outside the enlarged interval
`Set.Icc (a−g) (b+g)`… — concretely, hypothesis
`∀ j, j ∉ s' → hS.eigenvalues hn j ∉ Set.Ioo (a−g) (b+g)` where `s'` is the
matching `S`-block — then the W1.1 gap hypothesis holds and the full ladder
applies to the interval subspaces. Also provide the Weyl bridge: a two-sided
population gap (`spec T ∩ (a−δ, a) = ∅ = spec T ∩ (b, b+δ)`) plus
`‖S−T‖_op ≤ ε < δ` yields `g = δ − ε` (same proof pattern as
`gap_of_eigengap`, done on both sides). Deliverable: the paper's
"general-interval subspaces" bullet closes with statements about
`span (eigenvectors with λ ∈ [a,b])`.
Pitfall: the two `Finset`s (`T`-selected and `S`-selected) may have different
cardinalities without extra hypotheses; state the ladder with independent
`s s' : Finset (Fin n)` and a cross-gap hypothesis `i ∈ s → j ∉ s' → …` —
the engine is already asymmetric, so this is free — and only tie the
cardinalities in the interval corollary where Weyl forces them equal.

---

## W2 — Hoffman–Wielandt and the exact YWS theorem

New file `ForMathlib/Analysis/InnerProductSpace/HoffmanWielandt.lean`, then
`YuWangSamworth.lean`.

Why needed: the current formalization recovers YWS only through the Weyl
bridge, which needs an *operator-norm* smallness case-split. For the
Frobenius branch of `‖sinΘ‖_F ≤ 2·min{√d‖E‖_op, ‖E‖_F}/Δ` the case
`‖E‖_op ≤ Δ/2 < ‖E‖_F` is fine (hybrid gap `Δ/2` + sharp rung), but when
`‖E‖_op > Δ/2` the Frobenius branch is not recoverable from the hybrid bound
(`2‖E‖_F/Δ` can be far below the trivial bound `√d`). YWS's own residual
sandwich with Hoffman–Wielandt closes it uniformly.

**W2.1 — Sorted rearrangement lemma. Difficulty 2/5. ✅ DONE 2026-07-07
(Opus).** `HoffmanWielandt.lean` (new file):
`sum_mul_comp_perm_le_sum_mul_of_antitone` —
`∑ i, f (σ i) * g i ≤ ∑ i, f i * g i` for antitone `f g : Fin n → ℝ`. One line
via `Antitone.monovary` + `Monovary.sum_comp_perm_smul_le_sum_smul`. Registered,
build green, axiom-clean. (Note: needs `import Mathlib.Data.Real.Basic` — the
abstract Rearrangement file does not pull in ℝ's order instances.)

**W2.2 — Trace inequality `tr(TS) ≤ ∑ λᵢ(T)·λᵢ(S)`. Difficulty 3/5. ✅ DONE
2026-07-07 (Opus).** `HoffmanWielandt.lean`:
`sum_mul_sum_mul_le_sum_mul_of_antitone` (abstract Birkhoff bilinear bound:
`∑ₖ aₖ ∑ⱼ Mₖⱼ bⱼ ≤ ∑ᵢ aᵢbᵢ` for antitone `a,b`, doubly-stochastic `M`, via
`doublyStochastic_eq_convexHull_permMatrix` + `permMatrix_mulVec` + W2.1 at each
vertex) and `sum_eigenvalues_mul_re_inner_self_le` (von Neumann trace
inequality, discharged from the bilinear bound with `M = schurWeight`). Axiom-clean.
Statement (basis-free trace avoided): `∑ₖ re ⟪T (vₖ), S? …⟫` — cleanest form:
`∑ k, hT.eigenvalues hn k * re ⟪uₖ, S uₖ⟫ ≤ ∑ i, λᵢ(T) * λᵢ(S)` where
`uₖ = hT.eigenvectorBasis`. Route: `re⟪uₖ, S uₖ⟫ = ∑ⱼ wⱼₖ λⱼ(S)` with
`w = schurWeight hS hn (hT.eigenvectorBasis hn)` (exists:
`re_inner_orthonormalBasis_self_eq_sum_eigenvalues_mul`); the double sum is a
doubly-stochastic image, bounded via Birkhoff
(`doublyStochastic_eq_convexHull_permMatrix`, pattern already worked out in
`diag_mem_convexHull_perm_spectrum`) + W2.1 on each permutation vertex.
The convex-combination argument: a linear functional on a convex hull is
maximized at a vertex — use `Finset.inner_le` style or just expand the convex
combination directly.

**W2.3 — Hoffman–Wielandt. Difficulty 3/5. ✅ DONE 2026-07-07 (Opus).**
`HoffmanWielandt.lean`: `sum_sq_eigenvalues_sub_le_sum_sq_norm_apply` —
`∑ᵢ(λᵢ(T)−λᵢ(S))² ≤ ∑ₖ‖(S−T)uₖ‖²`. Route exactly as planned: per-column
`norm_sub_sq` expansion, the helper `sum_sq_norm_apply_eq_sum_sq_eigenvalues`
(basis-independence `∑ₖ‖S eₖ‖² = ∑ᵢλᵢ(S)²`, double-Parseval swap), and W2.2 for
the cross term; `linarith` closes. Axiom-clean. **W2 (Hoffman–Wielandt) complete
— unblocks W2.4/W4.**
`∑ i, (hT.eigenvalues hn i − hS.eigenvalues hn i)² ≤ ∑ₖ ‖(S−T)(bₖ)‖²`
(any orthonormal basis `b`; instantiate at `hT.eigenvectorBasis`).
Route: expand `‖S−T‖²_F = ∑λᵢ(T)² + ∑λᵢ(S)² − 2·"tr(TS)"` where the trace
term is `∑ₖ re⟪T(bₖ),S(bₖ)⟫` evaluated in the `T`-eigenbasis
(`= ∑ₖ λₖ(T)·re⟪uₖ,S uₖ⟫`), then W2.2. The `‖·‖²_F` expansion needs a small
lemma `∑ₖ‖(S−T)bₖ‖² = ∑ₖ(‖T bₖ‖² + ‖S bₖ‖² − 2 re⟪T bₖ, S bₖ⟫)` plus
basis-independence of each trace-like sum (pattern:
`sum_re_inner_orthonormalBasis_self_eq_sum_eigenvalues` in SchurHorn.lean and
the Parseval lemmas in DavisKahan.lean).
Pitfall: keep everything real-part-explicit; `⟪T bₖ, S bₖ⟫` is not real
termwise-symmetric until summed — prove the summed symmetrization.

**W2.4 — YWS theorem, exact form. Difficulty 4/5 (rerated per Opus R1). ✅ DONE
2026-07-07 (Opus).** `YuWangSamworth.lean`: `residualColumn` +
`inner_eigenvectorBasis_residualColumn` (the R1 T-only cross-term identity),
`residualColumn_eq` (perturbation-column form), lower bound
`sq_gap_mul_sum_cross_le_sum_sq_norm_residualColumn` (population gap, Bessel),
upper bound `sum_sq_norm_residualColumn_le` (Hoffman–Wielandt + basis
independence), and the headline `sq_gap_mul_sum_cross_le_of_population_gap`
(`Δ²·overlap ≤ 4‖S−T‖²_F`) with the `‖sinΘ‖_F` form
`sqrt_sum_cross_le_of_population_gap` (`‖sinΘ‖_F ≤ 2‖S−T‖_F/Δ`). Verified via
`lake env lean` + axiom-clean. **Simplification vs plan:** the `(a+b)²≤2a²+2b²`
bound replaces the Minkowski step and preserves YWS's exact constant 2 (√ of 4).
**Frobenius branch; the √d operator-norm branch and d=1 corollary remain.**
*(Route rewritten per Opus R1 — the original text second-guessed the residual;
this version is re-derived against `prose/Yu-Wang-Samworth-2014…` and is the
committed design. Statement-first gate applies: land the `sorry` stubs below
before proving anything.)*

In `YuWangSamworth.lean`. Headline (commit to this statement first):
`‖sinΘ‖_F ≤ 2·min{√d·‖E‖_op, ‖E‖_F}/Δ` with `Δ` population-only, in the
squared sum-encoded form `Δ² · overlap ≤ (2·min{√d·ε_op, ε_F})²`, with the
gap given by the two guarded hypotheses of the R2 convention
(`hlow : r ≠ 0 → …`, `hhigh : s + 1 ≠ n → …`).

**Residual (the R1 correction).** Never form an operator `R`; work with the
columns
`Rⱼ := (λⱼ(T) : 𝕜) • v̂ⱼ − T v̂ⱼ` for `j` in the block — the **population
eigenvalue at the matched sorted index `j`** times the **sample eigenvector**.
The quantity `‖R‖²_F` is `∑_{j∈block} ‖Rⱼ‖²`.

**Stub 1 — T-only cross-term identity** (new lemma, trivial, goes next to
`Spectrum.lean`'s mixed identity):
`⟪uₖ, Rⱼ⟫ = ((λⱼ(T) − λₖ(T)) : 𝕜) * ⟪uₖ, v̂ⱼ⟫` — both multipliers are
`T`-eigenvalues; proof is `hT.apply_eigenvectorBasis` + `IsSymmetric`, and it
does **not** factor through `inner_eigenvectorBasis_map_sub_eigenvectorBasis`.

**Stub 2 — lower bound (population-gap engine):**
`Δ² · ∑_{j∈block}∑_{k∉block} ‖⟪uₖ, v̂ⱼ⟫‖² ≤ ∑_{j∈block} ‖Rⱼ‖²`.
Proof shape = the existing `offDiag → residual` enlargement: Stub 1 turns each
cross pair into `(λⱼ(T)−λₖ(T))²‖⟪uₖ,v̂ⱼ⟫‖² `, sortedness
(`eigenvalues_antitone`) plus the guarded `Δ`-hypotheses give
`|λⱼ(T)−λₖ(T)| ≥ Δ` for `j ∈ block ∌ k` (`k < r` uses `hlow`, `k > s` uses
`hhigh`), and row Parseval (`sum_sq_norm_inner_…_eq_row` pattern) enlarges
`∑_{k∉block}` to `‖Rⱼ‖²`.

**Stub 3 — upper bound, both branches.** Column identity (uses
`S v̂ⱼ = λⱼ(S)v̂ⱼ`):
`Rⱼ = (S−T) v̂ⱼ − ((λⱼ(S) − λⱼ(T)) : 𝕜) • v̂ⱼ`. Then
- Frobenius: `√(∑‖Rⱼ‖²) ≤ √(∑_{block}‖(S−T)v̂ⱼ‖²) + √(∑_{block}(λⱼ(S)−λⱼ(T))²)
  ≤ ‖E‖_F + ‖E‖_F` — first term by enlarging the block to all `j` (the
  existing residual→hilbertSchmidt enlargement), second by
  **Hoffman–Wielandt (W2.3)**;
- operator: `≤ √d·ε_op + √d·ε_op` — per-column `‖(S−T)v̂ⱼ‖ ≤ ε_op` and
  per-index Weyl `|λⱼ(S)−λⱼ(T)| ≤ ε_op` (`abs_eigenvalues_sub_le`).
*Pitfall:* the `√(∑‖aⱼ+bⱼ‖²)` triangle step is the `L²`-family Minkowski
inequality — do **not** expand squares and Cauchy–Schwarz by hand; package
the families as elements of `EuclideanSpace ℝ (Fin d)` (of norms) or
`PiLp 2 (fun _ : Fin d => E)` and use `norm_add_le`. State Stubs 2–3 squared
to keep `Real.sqrt` out of everything except the final assembly.

**Assembly:** `Δ·√overlap ≤ √(∑‖Rⱼ‖²) ≤ 2·min{√d ε_op, ε_F}`. Also derive the
`d = 1` eigenvector corollary (YWS Corollary 1, with sign-alignment
`re⟪v̂,v⟫ ≥ 0 → ‖v̂−v‖ ≤ √2 sinθ`).
Depends on: W1.1 (block-general engine vocabulary), W2.3.

---

## W3 — YWS aligned-basis bound (G3)

Same file `YuWangSamworth.lean` (or `AlignedBasis.lean` if it grows).
Operator-native statement of `∃ orthogonal O, ‖V̂O − V‖_F ≤ 2^{3/2}·min{…}/Δ`:

> There is an orthonormal family `w : Fin d → E` with
> `span w = span (v̂-block)` and
> `∑ i, ‖w i − u i‖² ≤ 2 · overlap(u-block, v̂-block)`,
> hence `√(∑‖wᵢ−uᵢ‖²) ≤ 2^{3/2}·min{√d ε_op, ε_F}/Δ`.

(`w = V̂O` in matrix language; spanning + orthonormality is the faithful
operator rendering of right-multiplication by orthogonal `O`.)

**W3.1 — Unitary polar decomposition in finite dimension. Difficulty 3/5. ✅ DONE
2026-07-07 (Opus).** `PolarDecomposition.lean`: `polarUnitary A : E ≃ₗᵢ[𝕜] E`
(the kernel-completed unitary — restrict `polarFactor A` to its initial space
`(ker A)ᗮ` where it is isometric, extend via Mathlib's `LinearIsometry.extend`,
upgrade to an equiv by `injective_iff_surjective`) and `polar_decomposition_unitary`
(`A = U ∘ₗ |A|`, `U` unitary for every `A`, singular or not). This is the R5
load-bearing prerequisite for W3.4. Build green, axiom-clean.
Extend `polarFactor` to a genuine unitary when `E = F` (square case):
`∃ U : E ≃ₗᵢ[𝕜] E, ∀ x, A x = U ((abs A) x)`. Route: `polarFactor A` is a
partial isometry with `ker = ker A`, `range = range A`;
`finrank (ker A) = finrank (range A)ᗮ` (rank-nullity + orthogonal complement
dims), so pick any linear isometry equiv between them
(`LinearIsometryEquiv` from two orthonormal bases of equal-dim subspaces —
`stdOrthonormalBasis`-based, or reuse the extension idiom from
`GramMatrix.lean`'s `LinearIsometry.extend`) and glue along
`(ker A) ⊕ (ker A)ᗮ`. This is an independently Mathlib-worthy lemma; put it
in `PolarDecomposition.lean`.
Pitfall: gluing two maps along an internal direct sum with isometry — use
`Submodule.isCompl_orthogonal` + `LinearMap.ofIsCompl`, prove isometry via
Pythagoras on the orthogonal decomposition, then
`LinearIsometryEquiv.ofSurjective` (pattern in `NearIsometry.lean`).

**W3.2 — `|tr(U A)| ≤ tr A` for positive `A`, unitary `U`. Difficulty 2/5.**
Statement: `hA : A.IsPositive` → `‖∑ₖ ⟪bₖ, (U ∘ₗ A) bₖ⟫‖ ≤ ∑ₖ re⟪bₖ, A bₖ⟫`.
Route: `tr(UA) = ⟨(√A)U†, √A⟩_HS`-style Cauchy–Schwarz:
`∑ₖ ⟪bₖ, U(A bₖ)⟫ = ∑ₖ ⟪√A(U† bₖ), √A bₖ⟫`, then Cauchy–Schwarz on the sum
and `∑ₖ‖√A(U†bₖ)‖² = ∑ₖ‖√A bₖ‖² = tr A` (unitary invariance of the basis
sum — a small lemma worth stating separately:
`∑ₖ ‖B (U bₖ)‖² = ∑ₖ ‖B bₖ‖²`, i.e. Frobenius sums are unitarily invariant
in the vector argument; also needed by W5/W7). Uses `sq_norm_sqrt_apply`.

**W3.3 — Trace–singular-value–angle chain. Difficulty 3/5.**
For the overlap compression `M : ↥(span v̂-block) →ₗ ↥(span u-block)` (or its
flat `d×d` matrix `Mᵢⱼ = ⟪uᵢ, v̂ⱼ⟫` — prefer the flat matrix on
`EuclideanSpace 𝕜 (Fin d)` to dodge subspace coercions):
(a) `tr (abs M) = ∑ σᵢ(M)` (W0.1(c));
(b) `σᵢ(M) ≤ 1` (W0.1(b): `M` is a compression of the identity);
(c) `∑ᵢ σᵢ(M) ≥ ∑ᵢ σᵢ(M)² = ∑ᵢⱼ ‖Mᵢⱼ‖² = d − overlap` (W0.1(a) +
    complementary Parseval).

**W3.4 — Assemble the aligned-basis theorem. Difficulty 4/5. ✅ DONE 2026-07-07
(Opus) — closes G3.** `sum_sq_norm_aligned_le` in `AlignedBasis.lean`:
`∑ⱼ‖wⱼ−uⱼ‖² ≤ 2(d − ∑ⱼᵢ‖⟪uᵢ,vⱼ⟫‖²) = 2‖sinΘ‖²_F` for the Procrustes-rotated
basis `wⱼ = (familyIsometry hv)(O⁻¹ eⱼ)`, `O = polarUnitary (overlapOp hu hv)`.
Assembled from `sum_re_inner_u_aligned` (cross-term sum = ∑cos θ), the norm
expansion (`‖wⱼ−uⱼ‖² = 2 − 2 re⟪uⱼ,wⱼ⟫`), and the analytic core
`sum_overlap_le_sum_singularValues`. The finrank/`d` friction was resolved by
generalizing W0.1(c) + the core lemma to `(hn : finrank = n)` via `subst`.
Full build green, axiom-clean.

Historical detail (superseded by the ✅ above): Substantial progress in
`AlignedBasis.lean` (new file) + `SingularSubspace.lean`:
- `sum_sq_norm_le_sum_re_inner_abs_of_contraction` (`∑σ² ≤ ∑σ` for a contraction).
- `familyMap`/`familyIsometry` — the coordinate isometry `EuclideanSpace 𝕜 (Fin d)
  →ₗᵢ E` of an orthonormal family (built via `Fintype.linearCombination` +
  `WithLp.linearEquiv`; the `Basis.constr` route is absent in this Mathlib).
- `overlapOp` + `overlapOp_contraction` — the `d×d` overlap operator
  `(familyIsometry hu)⋆ ∘ (familyIsometry hv)`, matrix `⟪uᵢ,vⱼ⟫`, a contraction.
- `sum_sq_singularValues_overlapOp` (`∑σ² = ∑ᵢⱼ‖⟪uᵢ,vⱼ⟫‖²`) and
  `sum_overlap_le_sum_singularValues` (**`d − ‖sinΘ‖²_F ≤ ∑ cos θ`** — the
  analytic heart), handling the `finrank(EuclideanSpace (Fin d)) = d` reindex.
**Remaining:** the geometric Procrustes identity `∑‖wⱼ−uⱼ‖² = 2d − 2∑cos θ` for
the explicit rotated basis `wⱼ = familyIsometry hv (O⁻¹ eⱼ)` (`O = polarUnitary
overlapOp`), via `polar_decomposition_unitary` (W3.1) + W0.1(c) on the
`O⁻¹`-image basis; then combine with the analytic core. All ingredients proved
and verified; this is bookkeeping (polar computation + one more finrank reindex).
*(Corrected per Opus R5, load-bearing:)* `O` **must** be the genuine
*kernel-completed unitary* from W3.1, **never** the bare `polarFactor M`
partial isometry. When a principal angle hits `π/2`, `M` is singular; with the
bare partial isometry `w` fails orthonormality and `tr(O†M) = tr|M|` breaks.
With W3.1's unitary, `O† ∘ M = |M|` holds as an **equality regardless of
`M`'s rank** — this equality (not an inequality via W3.2) is what the cross
term reduces to, and is the whole reason W3 avoids the SVD Mathlib lacks. Do
W3.1 first; W3.2 stays as the general von-Neumann-lite lemma (used to show the
chosen `O` is *optimal*, an optional remark, not on the critical path).

Set `w j := ∑ᵢ (O)ᵢⱼ • v̂ᵢ` where `O = ` the unitary polar factor of `M†`
(W3.1 at the `d`-dimensional level). Compute
`∑ⱼ ‖wⱼ − uⱼ‖² = 2d − 2 re tr(O† M) = 2d − 2 tr(abs M)` (polar decomposition
makes the cross term the trace of `abs M` exactly — no inequality needed on
this step), then by W3.3(c): `≤ 2d − 2(d − overlap) = 2·overlap`. Chain with
W2.4 for the `2^{3/2}` headline, and with the hybrid sharp rung for a
gap-hypothesis version (`√2·‖E‖_F·√2/g` form) so the theorem is usable
without the YWS `Δ` packaging.
Pitfalls: (i) orthonormality and spanning of `w` come from `O` unitary —
prove `Orthonormal 𝕜 w` via `∑ᵢ conj Oᵢⱼ Oᵢₖ = δⱼₖ`; (ii) mind conjugation
conventions in `⟪·,·⟫` (Mathlib inner is conjugate-linear in the *first*
argument) when identifying the cross term with `tr(O†M)`; over ℝ this
disappears — do **not** take the ℝ-only shortcut, state over `RCLike`
(YWS is real, but the proof is field-agnostic and the DK core is `RCLike`).
Depends on: W0.1, W3.1–W3.3; the headline constant additionally on W2.4.

---

## W4 — YWS singular-vector extension (G4)

New file `ForMathlib/Analysis/InnerProductSpace/SingularSubspace.lean`.
Setting: `A Â : E →ₗ[𝕜] F`, right-singular subspaces = spectral subspaces of
`A.adjoint ∘ₗ A` (self-adjoint, positive).

**W4.1 — Gram perturbation bound. Difficulty 2/5. ✅ DONE 2026-07-07 (Opus).**
`SingularSubspace.lean` (new file): `norm_adjoint_apply_le` (`‖A⋆‖ ≤ ‖A‖`
elementwise, via `‖A⋆y‖² = re⟪y, A(A⋆y)⟫`) and `norm_gram_sub_gram_apply_le`
(`‖(Â⋆Â − A⋆A)x‖ ≤ (a+â)ε‖x‖` from `Â⋆Â − A⋆A = Â⋆(Â−A) + (Â−A)⋆A`). Build green,
axiom-clean. (W4.2/W4.3 — singular-value Weyl dictionary + main theorem —
remain.)
`∀ x, ‖(Â†Â − A†A) x‖ ≤ (‖A‖ + ‖Â‖)·‖Â−A‖·‖x‖`, in the elementwise-ε form
used by the DK gap bridges. Route:
`Â†Â − A†A = Â†(Â−A) + (Â†−A†)A`, triangle inequality + `‖A†‖ = ‖A‖`
(Mathlib `LinearMap.adjoint` + opNorm lemmas; if the flat `∀ x` form is used
throughout, prove the adjoint step via
`‖A† y‖² = re⟪A A† y, y⟫ ≤ ‖A‖‖A†y‖‖y‖`).

**W4.2 — Singular-value Weyl + eigen/singular dictionary. Difficulty 3/5. ✅ DONE
2026-07-07 (Opus).** `SingularSubspace.lean`: `abs_sq_singularValues_sub_le`
(`|σₖ(Â)² − σₖ(A)²| ≤ (a+â)ε`). The dictionary `σₖ² = λₖ(·⋆·)` is Mathlib's
`sq_singularValues_fin` directly, composed with `abs_eigenvalues_sub_le` (Weyl)
on the Gram operators via W4.1. Build green, axiom-clean. (W4.3 main
singular-subspace theorem remains.)
(a) `λᵢ(A†A) = σᵢ(A)²` sorted-form dictionary between
    `(isSymmetric_adjoint_mul_self).eigenvalues hn` and
    `LinearMap.singularValues` (Mathlib's `sq_singularValues_fin` is close;
    align the sorting/indexing conventions once, as lemmas);
(b) Weyl for squared singular values:
    `|σᵢ(Â)² − σᵢ(A)²| ≤ ε_gram` via `abs_eigenvalues_sub_le` applied to the
    Gram operators with W4.1.

**W4.3 — YWS Theorem 3 (singular-subspace bound). Difficulty 3/5. ✅ DONE
2026-07-07 (Opus).** `SingularSubspace.lean`:
`sq_gap_mul_sum_cross_singularVectors_le` — the right singular vectors are the
eigenvectors of the Gram operators `A⋆A, Â⋆Â`, so the YWS operator-norm branch
(W2.4) applied to them, with the perturbation from W4.1, gives
`Γ²·overlap ≤ 4·d·((a+â)ε)²`. A clean instantiation. Build green, axiom-clean.
**G4 (singular-vector extension) closed** (operator branch; Frobenius branch and
left-singular mirror are one-line variants).
Apply W2.4 (or, for the hybrid-gap version, the W1.1 ladder) to
`T := A†A`, `S := Â†Â`, gap `Γ = min(σ²_{r−1} − σ²_r, σ²_s − σ²_{s+1})`.
The right-hand side unfolds to
`2·min{√d·(‖A‖+‖Â‖)‖Â−A‖, …_F}/Γ`; for the Frobenius branch of the numerator
YWS state `‖Â†Â−A†A‖_F` directly — provide both forms and a corollary
substituting the W4.1 product bound. Left-singular subspaces: state the
mirror via `A A†` (one-line corollary swapping `A ↔ A†`).
Depends on: W1.1/W2.4, W4.1, W4.2.

---

## W5 — Operator-norm sinΘ theorem (G1, op-norm case)

New files `ForMathlib/Analysis/InnerProductSpace/SylvesterBound.lean` and
extension of `DavisKahan.lean`.

**W5.1 — The Sylvester-solution bound. Difficulty 3/5 (was 5/5) — REROUTED
(v3, Fable). ✅ DONE 2026-07-07:** `SylvesterBound.lean` (helper
`norm_le_of_abs_re_inner_map_self_le` + coercive `opNorm_le_div_of_comp_add_comp_eq`
+ separated `opNorm_le_div_of_comp_sub_comp_eq`), registered in
`ForMathlib.lean`, `lake build` green (8709 jobs), all three headline
declarations axiom-clean. Bonus generality over the plan: **no
finite-dimensionality and no completeness** — the Rayleigh-quotient helper
made the eigenbasis unnecessary, so the bound holds for bounded symmetric
operators on arbitrary inner product spaces. The spectral-integral route and its
Bochner-integral risks (Opus R6) are **abandoned**. The replacement is a
purely algebraic one-inequality argument; no integrals, no measurability, no
fixed-point theorem, works verbatim over `RCLike` between two different
spaces.

*Headline lemma (coercive/Lyapunov form).* `A : E →L[𝕜] E`, `B : F →L[𝕜] F`
self-adjoint with `δ > 0` and
`hA : ∀ x, δ‖x‖² ≤ re⟪A x, x⟫`, `hB : ∀ v, δ‖v‖² ≤ re⟪B v, v⟫`.
If `A ∘L X + X ∘L B = Y` then `‖X‖ ≤ ‖Y‖ / (2δ)`.

*Proof (verified on paper, v3).* WLOG `X ≠ 0` (else trivial); then `E, F`
are nontrivial and evaluating the coercivity at a nonzero vector against
Cauchy–Schwarz gives `δ ≤ a := ‖A‖` and `δ ≤ b := ‖B‖`. Pure algebra from
the hypothesis:
`(a+b) • X = Y + (a•1 − A) ∘L X + X ∘L (b•1 − B)`.
The helper lemma below gives `‖(a•1−A)w‖ ≤ (a−δ)‖w‖` (the symmetric operator
`a•1−A` has quadratic form in `[0, (a−δ)‖·‖²]`) and likewise for `b•1−B`.
Pointwise for any `v`:
`(a+b)‖Xv‖ ≤ ‖Y‖‖v‖ + (a−δ)‖Xv‖ + (b−δ)‖X‖‖v‖`,
so `(b+δ)‖Xv‖ ≤ (‖Y‖ + (b−δ)‖X‖)‖v‖`; by `opNorm_le_bound`,
`(b+δ)‖X‖ ≤ ‖Y‖ + (b−δ)‖X‖`, i.e. `2δ‖X‖ ≤ ‖Y‖`. ∎
Note the asymmetry is harmless: the `(a−δ)‖Xv‖` term is absorbed pointwise,
the `(b−δ)` term after taking the sup — only one scalar solve.

*Helper lemma* (independently useful; symmetric-operator norm from the
quadratic form): `C.IsSymmetric`, `∀ x, |re⟪C x, x⟫| ≤ κ‖x‖²` ⟹
`∀ x, ‖C x‖ ≤ κ‖x‖`. Proof: eigen-expansion — each eigenvalue satisfies
`|λᵢ| ≤ κ` (plug the eigenvector), then
`‖Cx‖² = ∑ λᵢ²‖⟪bᵢ,x⟫‖² ≤ κ²‖x‖²` by Parseval; exactly the
`CourantFischer.lean` expansion pattern. Check first whether Mathlib's
Rayleigh file already has a usable form (`norm_eq_iSup_rayleighQuotient`
vicinity); if yes, use it, else stage this.

*DK-facing corollary (separated form).* `hA : ∀ x, (c+g)‖x‖² ≤ re⟪A x, x⟫`,
`hB : ∀ v, re⟪B v, v⟫ ≤ c‖v‖²`, `A ∘L X − X ∘L B = Y` ⟹ `‖X‖ ≤ ‖Y‖ / g`.
Shift `A' := A − (c+g/2)•1`, `B' := (c+g/2)•1 − B`, `δ := g/2`; then
`A'∘X + X∘B' = A∘X − X∘B = Y` and both coercivity hypotheses hold. Mind the
scalar casts: the shift is `((c+g/2 : ℝ) : 𝕜) • 1`, self-adjoint by
`RCLike.conj_ofReal`, with `re⟪(r:𝕜)•x, x⟫ = r‖x‖²`.

*Why quadratic-form hypotheses (not spectra):* they are exactly what the
compressions in W5.2 can discharge — the quadratic form of `S` on the
trailing span is `≤ c‖·‖²` by the (currently `private`) CourantFischer lemma
`re_inner_map_self_le_of_mem_specSubspace`; no compression-spectrum lemma
needed at all. Statements stay eigenvalue-index-free, the most
Mathlib-idiomatic form.
Do NOT attempt the general two-interval separation (constant π/2 territory);
half-line is what the DK hybrid gap needs.

**W5.2 — Operator-norm sinΘ. Difficulty 3/5. ✅ DONE 2026-07-08 (Opus) — new
file `SinThetaOpNorm.lean`, registered, full library build green (8716 jobs),
both headlines axiom-clean.** Delivered `norm_starProjection_comp_starProjection_le`
(`‖Q̂ ∘L P‖ ≤ ε/g`, abstract invariant-subspace + quadratic-form hypotheses) and
the reusable commutation helper `starProjection_comp_toContinuousLinearMap_comm`
(a symmetric operator commutes with the projection onto an invariant subspace).
**Route improvement vs the plan's subtype recipe:** rather than compress to
`↥U →L ↥V` subtypes (heavy coercion plumbing), the proof stays on the full
space `E` with the *scalar-extended* operators `A = T P + (c+g)(1−P)` and
`B = S Q + c(1−Q)`, which are globally `(c+g)`-coercive / `c`-bounded by the
block decomposition (T-invariance of `U, Uᗮ`; S-invariance of `V, Vᗮ`), and the
projection algebra gives the exact Sylvester relation
`A ∘L X − X ∘L B = P ∘L (T − S) ∘L Q` with `X = P ∘L Q`; the existing
`opNorm_le_div_of_comp_sub_comp_eq` finishes, and `‖Q̂ P‖ = ‖P Q̂‖` by
self-adjointness. This needed **no un-privatizing of CourantFischer** (the
form hypotheses are taken abstractly) — the eigenvector-block corollary using
those private lemmas is an optional follow-up. One extra hypothesis `0 ≤ ε`
(vacuous in the intended `ε = ‖S−T‖_op` application) makes the trivial-space
edge case go through.
*(historical subtype recipe retained below for reference.)*
`‖Q̂ ∘L P‖ ≤ ε/g` where `P` = starProjection onto the `T`-leading block span
`U`, `Q̂` = onto the `S`-trailing block span `V`. **State the headline in
exactly this vocabulary — `‖Q̂ ∘L P‖` *is* `‖sinΘ‖_op`**; the principal-angle
identification (`‖Q̂P‖ = max sinθᵢ`) is an optional bridge lemma to add after
W0.2, *not* a dependency. Use the **one-sided (half-line) gap shape** the
Sylvester corollary consumes: `hU : ∀ i ∈ s, c + g ≤ λᵢ(T)` and
`hV : ∀ j ∉ s', λⱼ(S) ≤ c` (the standard sin-θ setting; do not try to consume
the symmetric hybrid `|λᵢ−λⱼ| ≥ g`, which also allows the blocks to sit on
the other side).

v5 concrete recipe (verified on paper):
1. **Un-`private`** in `CourantFischer.lean`: `specSubspace`,
   `re_inner_map_self_le_of_mem_specSubspace`,
   `le_re_inner_map_self_of_mem_specSubspace` (update the file-header note —
   they now have an external consumer, which is exactly the criterion the
   header gives for un-privatizing).
2. **Commutation helper** (new, independently useful — also wanted by W6's
   spectral corollary): if `hT : T.IsSymmetric` and `U` is `T`-invariant
   (`∀ u ∈ U, T u ∈ U`, finite-dim so `Uᗮ` is invariant by symmetry), then
   `T ∘ₗ U.starProjection = U.starProjection ∘ₗ T`. Proof: split
   `x = Px + (x − Px)`, apply invariance to each summand. Instantiate at
   `U = span (eigenvectors in s)` (invariance is `apply_eigenvectorBasis`).
3. **Compression.** `X : ↥V →L[𝕜] ↥U`, `X v := U.orthogonalProjection v`
   (the `↥U`-valued projection; `starProjection = subtypeL ∘ orthogonalProjection`).
   With `T_U : ↥U →L ↥U`, `S_V : ↥V →L ↥V` the restrictions (well-defined by
   invariance; symmetric — restriction of symmetric to invariant is symmetric),
   compute for `v : ↥V`:
   `(T_U ∘L X − X ∘L S_V) v = U.orthogonalProjection ((T − S) v)`
   using step 2 on the `T` term and `S`-invariance of `V` on the `S` term.
   So `Y := X ∘L (T−S 	compressed)` — more precisely the map
   `v ↦ U.orthogonalProjection ((T − S) v)` — has `‖Y‖ ≤ ε` (inclusion is an
   isometry, projection is a contraction, `‖(T−S)z‖ ≤ ε‖z‖`).
4. **Quadratic forms.** Coercivity of `T_U`: for `u ∈ U`,
   `(c+g)‖u‖² ≤ re⟪T u, u⟫` — this is `le_re_inner_map_self_of_mem_specSubspace`
   with `p := (· ∈ s)` and `hU`. Upper bound for `S_V`: the dual lemma with
   `hV`. Apply `opNorm_le_div_of_comp_sub_comp_eq` (SylvesterBound.lean) ⇒
   `‖X‖ ≤ ε/g`.
5. **Un-compress.** `‖P ∘L Q̂‖ ≤ ‖X‖`: for any `z`,
   `P (Q̂ z) = ↑(X ⟨Q̂ z, _⟩)` and `‖⟨Q̂ z, _⟩‖ ≤ ‖z‖`. Finally
   `‖Q̂ ∘L P‖ = ‖P ∘L Q̂‖` because the two are adjoint to each other
   (starProjections are self-adjoint) and `‖B⋆‖ = ‖B‖`
   (`ContinuousLinearMap.opNorm_adjoint` or the elementwise route via
   `norm_adjoint_apply_le` in SingularSubspace.lean).
Optional extras, rank separately: the projector corollary
`‖P̂−P‖ = max(‖Q̂P‖, ‖P̂Q‖)` (stretch), the W0.2 bridge `‖Q̂P‖ = max sinθᵢ`.
Depends on: W5.1 (done), W1.1 (done). **No W0.2 dependency.**

---

## W6 — sin2Θ / tan2Θ (G2)

New file `ForMathlib/Analysis/InnerProductSpace/RotationSharp.lean`.
Davis's 2×2-compression results (digest: `prose/Davis-1963-core-arguments.tex`
§"The sharp two-subspace estimate").

**W6.1 — Per-eigenvector sin2θ bound. Difficulty 4/5. ✅ DONE 2026-07-08
(Fable) — `RotationSharp.lean` (new file, registered, library build green
8714 jobs, all four public declarations axiom-clean).**
Implemented exactly along the v5 route below, with one further simplification
found during implementation: **the half-angle square roots disappear
entirely** — since `1 − 2cs = (c − s)²` and `1 + 2cs = (c + s)²`, the two
rotation test vectors can be taken with *polynomial* coefficients
`s(c−s)•y + c(c+s)•z` and `−s(c+s)•y + c(c−s)•z` (unnormalized `y = Px`,
`z = x − Px`; each has squared norm `2c²s²`), so the proof has **no
`Real.sqrt`, no inverses, no normalization of `p, q`, and no case split on
`s ≤ c`** — pure `linear_combination`/`linarith` algebra. Bonus generality:
the primary statement `sin_two_theta_le_of_mem` is in orthogonal-decomposition
form (`y ∈ U`, `z ∈ Uᗮ`, `‖y+z‖ = 1`) and needs **no orthogonal projection,
no completeness, no finite dimension**; `sin_two_theta_le`
(`Submodule.starProjection` product form, `[U.HasOrthogonalProjection]`) and
`sin_two_arccos_le` (literature-facing `(b−a)·sin 2θ ≤ 2ε`) are thin
corollaries. The shared engine `key_identity` (μ-free real identity) and the
expansion lemmas `re_inner_smul_add_smul_map` / `norm_smul_add_smul_sq` are
factored exactly as W6.2 needs; the invariance helper
`map_mem_orthogonal_of_forall_map_mem` is public (also wanted by W5.2 step 2).
*(v5 full reroute — the route below eliminates the ℂ phase alignment the v1
text warned about, and needs no location assumption on the perturbed
eigenvalue. Verified on paper end-to-end, Fable 2026-07-08.)*

**Statement (abstract subspace form — no spectral projections, no rescaling).**
In `RotationSharp.lean` (new file). Context: `T H : E →ₗ[𝕜] E`,
`hT : T.IsSymmetric`, `hH : H.IsSymmetric`, a subspace `U` with
`hUinv : ∀ u ∈ U, T u ∈ U`, form bounds
`hb : ∀ u ∈ U, b * ‖u‖^2 ≤ re ⟪T u, u⟫` and
`ha : ∀ w ∈ Uᗮ, re ⟪T w, w⟫ ≤ a * ‖w‖^2`, perturbation
`hε : ∀ z, ‖H z‖ ≤ ε * ‖z‖`, and a unit eigenvector
`hx : ‖x‖ = 1`, `hμ : (T + H) x = (μ:𝕜) • x` with `μ : ℝ` **unconstrained**
(the sin2θ theorem's whole point: no smallness/location assumption).
Conclusion, product form (θ never appears):
`(b − a) * (‖P x‖ * ‖x − P x‖) ≤ ε`, `P := U.starProjection`.
This is Davis's `sin 2θ ≤ 2‖H‖/(b−a)` since `sin 2θ = 2·‖Px‖·‖x−Px‖`.
The literature-facing spectral instantiation (`U` = span of eigenvectors with
`λᵢ ≥ b`, rest `≤ a`) is a corollary via the W5.2 step-1/2 assets
(`specSubspace` form lemmas + invariance of eigen-spans) — leave it to the
W5.2/W6.2 executor if not done in the first pass.

**Proof (all real-part arithmetic; no phases).** Write `c := ‖Px‖`,
`s := ‖x − Px‖`, so `c² + s² = 1`.
1. *Degenerate cases* `c = 0` or `s = 0`: LHS `= 0 ≤ ε` (from `hε x`).
2. Otherwise set `p := (c⁻¹:𝕜) • P x ∈ U`, `q := (s⁻¹:𝕜) • (x − Px) ∈ Uᗮ`;
   unit, orthogonal, `x = (c:𝕜)•p + (s:𝕜)•q`.
3. *Eigen-equations.* Pair `hμ` with `p` and `q`; `⟪p, T q⟫ = 0 = ⟪q, T p⟫`
   (invariance of `U` and — via symmetry — of `Uᗮ`). With
   `α := re ⟪T p, p⟫`, `β := re ⟪T q, q⟫`, `w := ⟪q, H p⟫`, and the real
   diagonal entries `Hpp := re ⟪H p, p⟫`, `Hqq := re ⟪H q, q⟫`:
   `(1) c·α + c·⟪H p,p⟫-term + s·⟪p, H q⟫ = μ·c` and
   `(2) s·β + c·⟪q, H p⟫ + s·⟪H q,q⟫-term = μ·s` (scalar equations in 𝕜).
4. *Key identity (the phase-alignment killer).* Compute `s·(1) − c·(2)` and
   take `re`. Since `re ⟪p, H q⟫ = re (conj w) = re w`, the mixed terms
   combine to `(s² − c²)·re w` — **`re(c²w − s²·conj w) = (c²−s²)·re w`
   identically**, so no unimodular phase multiplication is ever needed:
   `c·s·(α − β) = c·s·(Hqq − Hpp) + (c² − s²)·re w`. (μ cancels.)
5. *Rotation bound.* For any real `γ σ` with `γ² + σ² = 1`, the vectors
   `u := (γ:𝕜)•p + (σ:𝕜)•q` and `u' := (−σ:𝕜)•p + (γ:𝕜)•q` are unit, and
   `re⟪H u, u⟫ − re⟪H u', u'⟫ = (γ²−σ²)(Hpp − Hqq) + 4γσ·re w`,
   bounded by `2ε` in absolute value (`|re⟪H u, u⟫| ≤ ‖H u‖·‖u‖ ≤ ε`).
6. *Half-angle choice.* Take `γ := √((1 − 2cs)/2)` and
   `σ := (if s ≤ c then 1 else −1) · √((1 + 2cs)/2)`. Then `γ² + σ² = 1`
   (needs `2cs ≤ 1`, i.e. AM–GM `2cs ≤ c²+s²`), `γ² − σ² = −2cs`, and
   `2γσ = ±√(1 − 4c²s²) = ±|c² − s²| = c² − s²` (sign matches the `if`;
   `1 − 4c²s² = (c²−s²)²` because `c²+s² = 1`). Substituting into step 5:
   `|2·(cs(Hqq − Hpp) + (c²−s²)·re w)| ≤ 2ε`, i.e. by step 4
   `cs·(α − β) ≤ ε`.
7. *Conclusion.* `α ≥ b` (`hb` at `p`), `β ≤ a` (`ha` at `q`), `cs ≥ 0`:
   `(b−a)·cs ≤ (α−β)·cs ≤ ε`. ∎

Lean pitfalls that remain (why this is still 4/5): the `c⁻¹`/`s⁻¹` scalar-cast
bookkeeping in steps 2–3 (`RCLike.ofReal` everywhere, conjugate-linearity in
the *first* slot); extracting the two scalar equations from `hμ` cleanly
(`inner (T x + H x) …` expansion against the `p,q` decomposition of `x`); the
`Real.sqrt` algebra in step 6 (keep it in the two lemmas
`γ² = (1−2cs)/2`, `σ² = (1+2cs)/2` and derive `2γσ` via
`(2γσ)² = (c²−s²)²` + sign analysis, never expand `sqrt` products directly);
and the sign split `s ≤ c` vs `c < s`. Provide the `Real.arccos` corollary
(`Real.sin (2 * Real.arccos c) * (b − a) ≤ 2ε`) only as a thin optional
wrapper — the product form is the API.

**W6.2 — Per-eigenvector tan2θ bound under vanishing pinch. Difficulty 2/5.
✅ DONE 2026-07-08 (Opus) — `RotationSharp.lean`, `tan_two_theta_le_of_mem`
(orthogonal-decomposition form) + `tan_two_theta_le` (`starProjection` form),
both axiom-clean, module build green.** Implemented exactly along the route
below: the vanishing-pinch hypotheses are stated subspace-wise
(`hHU : ∀ u ∈ U, ∀ u' ∈ U, ⟪u, H u'⟫ = 0` and the `Uᗮ` analogue), they kill the
two diagonal `H`-terms of the private `key_identity`, and the single mixed term
`re⟪y,Hz⟫` is bounded by `‖y‖‖z‖ε` directly (Cauchy–Schwarz, no rotation trick).
Conclusion `(b−a)·(‖y‖·‖z‖) ≤ |‖y‖²−‖z‖²|·ε` (= `tan 2θ ≤ 2ε/(b−a)`, product
form, no `θ ≠ π/4` side condition). The engine `key_identity`, `re_inner_map_symm`
etc. were already factored by W6.1, so this was pure assembly as planned.
Encode the vanishing diagonal blocks subspace-wise:
`hUU : ∀ u ∈ U, ∀ u' ∈ U, ⟪H u, u'⟫ = 0` and the same on `Uᗮ` (never form
`P H P` as an operator). Then W6.1's step-4 identity collapses to
`c·s·(α − β) = (c² − s²)·re w`, and `|re w| ≤ |⟪q, H p⟫| ≤ ‖H p‖ ≤ ε`
directly — steps 5–6 (the rotation and half-angle) are not used. Product-form
conclusion: `(b − a)·(‖Px‖·‖x − Px‖) ≤ |‖Px‖² − ‖x − Px‖²|·ε`, which is
`tan 2θ ≤ 2ε/(b−a)` (both sides divided by `cos 2θ = c² − s²`; the θ-form
corollary needs `c² ≠ s²`, i.e. `θ ≠ π/4`, exactly Davis's implicit
condition — in the product form no side condition is needed). Reuses W6.1's
steps 1–4 verbatim; factor them as standalone lemmas when implementing W6.1
so this step is pure assembly.

**W6.3 — (Stretch) subspace-level sin2Θ theorem. Difficulty 5/5. DEFER with W7
unless a cheap route appears.**
*(v5 warning, Fable: the v1 suggestion "sum the per-vector squares — same
pattern as the existing ladder" does NOT go through.* W6.1's per-vector proof
tests `H` against rotated vectors `u ∈ span{p, q}` — the bound it yields is
`cs(b−a) ≤ max over that 2-plane of |re⟪Hu,u⟫|`, which is controlled by the
**operator** norm `ε`, not by the column norm `‖H xⱼ‖`. Summing over an
eigenbasis of `S` therefore gives `∑ⱼ sin²2θⱼ ≤ 4n·ε²/(b−a)²`, a dimension-
carrying bound, not the part-III `‖sin 2Θ‖_F ≤ 2‖H‖_F/(b−a)`. The genuine
subspace-level sin2Θ needs Davis–Kahan part-III technology (or at least a
2×2-block operator argument at the subspace level), which is W7-adjacent.)*
If attempted anyway, the honest reachable deliverables are: (i) the summed
dimension-carrying corollary above (trivial once W6.1 lands — acceptable as a
documented-weaker form), and (ii) the op-norm per-subspace `sin 2Θ` for the
**largest** angle only, via W6.1 applied to a worst eigenvector. Mark both as
explicitly weaker than part III in docstrings and the paper.

---

## W7 — Unitarily invariant norms (G1, general case) — OPTIONAL / DEFER

A self-contained mini-library (symmetric gauge functions, Ky Fan k-norms,
majorization ⇒ norm domination, von Neumann trace inequality), prerequisite
for the *full* part-III statement and W6.3-op. Recommendation: **defer to a
separate project** — it is a Mathlib-sized contribution on its own
(`Analysis/UnitarilyInvariantNorm/…`), and the Frobenius + operator-norm pair
(W1–W6) already covers every application downstream in this repo (DKPS
pipeline consumes Frobenius bounds only). If undertaken:
W7.1 Ky Fan k-norms via `singularValues` partial sums + Ky Fan variational
principle (difficulty 4/5); W7.2 majorization ⇒ all-Ky-Fan domination ⇒
unitarily invariant norm domination (Fan dominance, 5/5); W7.3 extend the
Sylvester bound to any UI norm (note: W5.1's v3 algebraic route is op-norm
native; the UI-norm extension re-runs the same one-inequality argument using
submultiplicativity `|||CX||| ≤ ‖C‖·|||X|||` of UI norms against op-norm
factors, which W7.1–2 provide — no integrals needed here either; 3/5 given
W7.1–2); W7.4 part-III sinΘ for all UI norms (4/5).

---

## Execution order and dependency graph

```
W0.1 ──→ W0.2 ──→ (W3.3, W5.2 identification, W6 angle forms)
W1.1 ──→ W1.2                               [independent start]
W1.1 ──→ W2.4 ←── W2.1 → W2.2 → W2.3        [W2.1 independent start]
W2.4 ──→ W3.4 ←── W3.1, W3.2, W3.3 (←W0.1)
W2.4/W1.1 ──→ W4.3 ←── W4.1, W4.2
W5.1 ──→ W5.2 (←W0.2, W1.1)
W6.1 ──→ W6.2 → (W6.3 stretch)
W7: deferred
```

Recommended batches (each ends with `lake build` green, axiom check, golf
pass per `dev/mathlib-quality-adapter.md`, and a `papers/…-vs-literature.tex`
update including the permalink line):

1. **Batch A (warm-up, high leverage):** W1.1, W1.2, W2.1 — closes G5.
2. **Batch B (YWS exact):** W2.2, W2.3, W2.4 — Hoffman–Wielandt + YWS
   headline. Independently Mathlib-attractive (HW has repeatedly been
   requested upstream).
3. **Batch C (angles + alignment):** W0.1, W0.2, W3.1, W3.2, W3.3, W3.4 —
   closes G3, delivers the canonical-angle API.
4. **Batch D (singular vectors):** W4.1, W4.2, W4.3 — closes G4.
5. **Batch E (operator norm):** W5.1, W5.2 — closes the op-norm half of G1.
   **W5.1 is Fable's (in progress, v3 algebraic route); W5.2 is Opus's**, and
   with the reroute it no longer sits behind any integration machinery.
6. **Batch F (sharp rotations):** W6.1, W6.2 (+ W6.3 stretch) — closes G2's
   tractable core.
7. **Batch G (deferred):** W7 — full G1. Separate project decision.

## Remaining work — v5 ranking (hardest first) and order for Opus

Everything not listed here is ✅ done and verified (v4 sweep + v5 re-check).

| Rank | Step | What | Difficulty | Assignee | Notes |
|------|------|------|-----------|----------|-------|
| 1 | W6.3 | Subspace-level sin2Θ | 5/5 | **defer** (with W7) | v5 warning: per-vector summation does *not* recover part III; only weaker forms reachable |
| 2 | W7.1–7.4 | Unitarily invariant norms | 4–5/5 | **defer** (separate project) | unchanged |
| 3 | W6.1 | Per-vector sin2θ, product form | 4/5 | **✅ DONE** (Fable, 2026-07-08) | `RotationSharp.lean`; polynomial-coefficient rotation, no `sqrt`/inverses; axiom-clean |
| — | W5.2 | Op-norm sinΘ via Sylvester | 3/5 | **✅ DONE** (Opus, 2026-07-08) | `SinThetaOpNorm.lean`; full-space scalar-extension route (no subtypes), axiom-clean |
| — | W0.2 | Principal-angle API | 3/5 | **✅ DONE** (Opus, 2026-07-08) | `PrincipalAngles.lean`; cos/sin defs + symmetry + overlap bridge, axiom-clean |
| — | W0.1(d) | `singularValues_adjoint` (square case) | 2.5/5 | **✅ DONE** (Opus, 2026-07-08) | `SingularSubspace.lean`; `eigenvalues_conj_unitary` + polar identity, axiom-clean |
| — | W6.2 | tan2θ under vanishing pinch | 2/5 | **✅ DONE** (Opus, 2026-07-08) | `RotationSharp.lean`; pure assembly on `key_identity`, axiom-clean |

Suggested order for Opus: **W6.2** (done first, closes G2), then **W0.1(d) →
W0.2** (closes the canonical-angle API), then **W5.2** (closes G1's op-norm
half). After each: `lake build` green, axiom check on headlines, paper sync per
Definition of done.

## Difficulty ranking (all steps, hardest first) — historical (v3)

*(v3: rows for W5.1/W5.2 rerated after the algebraic reroute; W2.4 rerated
per Opus R1. Historical ranks kept so the deltas are visible. Superseded by
the v5 remaining-work table above.)*

| Rank | Step | What | Difficulty | Why |
|------|------|------|-----------|-----|
| 1 | W6.3 | Subspace-level sin2Θ (stretch) | 5/5 | Needs W7 for op-norm form; Frobenius form still a heavy summation argument |
| 2 | W7.2 | Fan dominance theorem | 5/5 | Majorization theory from scratch (deferred) |
| 3 | W7.1 | Ky Fan norms + variational principle | 4/5 | New norm family + duality (deferred) |
| 4 | W7.4 | Part-III UI-norm sinΘ | 4/5 | Assembly over W7.1–3 (deferred) |
| 5 | W5.2 | Operator-norm sinΘ from Sylvester bound | **3.5/5 (was 4/5)** | Quadratic-form hypotheses kill the compression-spectrum lemma; remaining cost is subtype/restriction plumbing |
| — | W5.1 | Sylvester solution bound | **✅ DONE (was 5/5; rerouted v3, Fable)** | Landed in `SylvesterBound.lean`, axiom-clean, infinite-dim generality |
| 7 | W6.1 | Per-eigenvector sin2θ (Davis compression) | 4/5 | Delicate scalar geometry, degenerate cases, ℂ phase alignment |
| 8 | W3.4 | Aligned-basis theorem assembly | 4/5 | Long chain; conjugation bookkeeping; orthonormality of rotated family |
| 9 | W0.2 | Principal-angle definitions + bridges | 3.5/5 | Design-heavy (right def matters for three consumers); subspace coercions |
| 10 | W4.3 | YWS singular-subspace theorem | 3.5/5 | Mostly instantiation, but index/sorting bookkeeping across Gram dictionary |
| 11 | W2.2 | Trace inequality via Birkhoff | 3/5 | Machinery exists (schurWeight, Birkhoff); vertex-maximization plumbing |
| 12 | W2.3 | Hoffman–Wielandt | 3/5 | Frobenius expansion + basis-independence lemmas; W2.2 does the work |
| 13 | W2.4 | YWS exact theorem | **4/5 (was 3/5, per Opus R1)** | Residual is T-only + needs a new cross-term lemma; design content, not just assembly |
| 14 | W3.1 | Unitary polar decomposition (square case) | 3/5 | Direct-sum gluing of isometries; standard but fiddly |
| 15 | W3.3 | Trace/singular-value/angle chain | 3/5 | Three short lemmas over W0.1 |
| 16 | W0.1 | Singular-value glue (Frobenius², contraction, trace of abs) | 3/5 | Finsupp indexing friction; otherwise Parseval-level |
| 17 | W4.2 | Singular-value Weyl + dictionary | 3/5 | Sorting/indexing alignment, Weyl already local |
| 18 | W6.2 | tan2θ under vanishing pinch | 3/5 | Marginal cost over W6.1 |
| 19 | W3.2 | `|tr(UA)| ≤ tr A` for positive A | 2/5 | One Cauchy–Schwarz + existing `sq_norm_sqrt_apply` |
| 20 | W1.2 | Interval subspaces + two-sided Weyl bridge | 2/5 | Predicate plumbing over W1.1 |
| 21 | W4.1 | Gram perturbation bound | 2/5 | Triangle inequality + adjoint norm |
| 22 | W2.1 | Sorted rearrangement lemma | 2/5 | Mathlib rearrangement API plumbing |
| 23 | W1.1 | Engine over arbitrary Finset block | 2/5 | Mechanical generalization; projector section already does it |

## Opus review notes (2026-07-07)

**v3 disposition (Fable):** every note below is now folded into the plan body;
this section is kept as review history. Per-note status —
R1 → W2.4 rewritten with the corrected T-only residual + three statement-first
stubs (rerated 4/5). R2 → guarded-hypotheses convention added to the
statement-shape list. R3 → W0.2 redefined on the flat `overlapMap`
(compressions banned). R4 → `singularValues_adjoint` is now W0.1(d) with a
proof route. R5 → W3.4 rewritten around W3.1's kernel-completed unitary;
`tr(O†M)=tr|M|` recorded as an equality via `O†∘M = |M|`. R6 → **moot**: W5.1
rerouted to an integral-free algebraic argument (see W5.1 v3), so the Bochner
uncertainty and the descope path disappear; Fable is implementing W5.1
directly. R7 → division of labor set accordingly (W7, W6.3 stay deferred;
W5.2 now within Opus reach at 3.5/5). R8 → gate added to Definition of done.

Review by the executing (Opus) agent. I verified the load-bearing structural
claims against source: the ladder engine (`sum_cross_…` in `DavisKahan.lean`)
does extract the block only via `Finset.mem_filter.mp`, and the projector
section (`sum_norm_sub_starProjection_span_sq_eq` etc.) is already stated for
an arbitrary `s : Finset ι` — so **W1.1 is genuinely 2/5 as claimed**. Below
are the places that are underspecified, subtly wrong, or (for me) at the edge
of feasibility. Ordered by how much they'd cost if discovered mid-proof.

**R1 — W2.4 is the weakest-specified step; its residual is stated wrong.**
Fable's prose second-guesses which eigenvalues appear, and the version that
survives is not the one the current engine gives. The faithful YWS argument
(checked against `prose/Yu-Wang-Samworth-2014…` §"Lower/Upper bound"):
- *Residual:* `R` has columns `R v̂ⱼ = λⱼ(T-block)·v̂ⱼ − T v̂ⱼ`, `j` in the
  S-block. Here `λⱼ(T-block)` is a **T (population)** eigenvalue, *not* an
  `S`/sample one. This is **not** `(S−T)v̂ⱼ`, so the existing
  `…_le_residual` rung does **not** apply directly.
- *Lower bound (population gap, constant 1):* for `k` outside the T-block,
  `⟪uₖ, R v̂ⱼ⟫ = (λⱼ(T) − λₖ(T))·⟪uₖ, v̂ⱼ⟫`, and `|λⱼ(T) − λₖ(T)| ≥ Δ`.
  **Both multipliers are T-eigenvalues** ⇒ this needs a *new, simpler*
  cross-term identity `⟪uₖ, T v̂ⱼ⟫ = λₖ(T)·⟪uₖ, v̂ⱼ⟫` (just
  `hT.apply_eigenvectorBasis`), **not** `Spectrum.lean`'s mixed
  `inner_eigenvectorBasis_map_sub_eigenvectorBasis`. Then reuse the
  Parseval/`V₁ᵀV̂` counting to get `Δ‖sinΘ‖_F ≤ ‖R‖_F`. This is effectively a
  *second copy* of the engine specialized to `S = T` — plan for a small new
  lemma, do not expect to reuse the ladder verbatim.
- *Upper bound:* `R = E V̂ − V̂(Λ̂−Λ)` from `S v̂ⱼ = λ̂ⱼ v̂ⱼ` (this direction
  *is* the sample eigenvalues), giving `‖R‖_F ≤ ‖E‖_F + ‖Λ̂−Λ‖_F ≤ 2‖E‖_F`
  (HW, W2.3) and `≤ 2√d‖E‖_op` (Weyl, per-column).
- Fable's claim that the constant-2 population branch is *not* recoverable from
  the existing hybrid bound when `‖E‖_op > Δ/2` is **correct** — I checked:
  `gap_of_eigengap` yields hybrid gap `Δ − ‖E‖_op`, which degenerates exactly
  in that regime. So W2/W2.4 is genuinely necessary, not redundant.
- **Action for executor:** write the final `theorem` signature (population `Δ`,
  constant 2, both `min` branches) and the T-only cross-term lemma as `sorry`
  stubs *first*, confirm the constant on paper, then fill. Budget W2.4 at
  effectively 4/5, not 3/5, because of this design content.

**R2 — Boundary eigenvalue conventions (`λ₀=∞`, `λ_{p+1}=−∞`) are unspecified**
across W1.2, W2.4, W4.3. The cleanest faithful encoding I can commit to: state
the gap as **two hypotheses**
`hlow : r ≠ 0 → Δ ≤ λ_{r-1}(T) − λ_r(T)` and
`hhigh : s+1 ≠ n → Δ ≤ λ_s(T) − λ_{s+1}(T)` (vacuous at the spectrum edges),
and phrase the lower-bound counting over the *actual* complement `sᶜ` so no
fictitious `±∞` index is ever referenced. Add this as an explicit statement
convention to the header list. Without it, W2.4/W4.3 will churn on off-by-one
`Fin` boundary cases.

**R3 — W0.2's definition is self-contradictory as written.** It says define
`cosPrincipalAngles` via a subspace-compression map `↥U →ₗ ↥V` but "prove all
lemmas against the flat overlap-sum encoding." Those are different objects with
no stated bridge. Decision (unifying with W3.3, which already prefers the flat
matrix): **define `cosPrincipalAngles` as `LinearMap.singularValues` of the
flat overlap operator** `M : EuclideanSpace 𝕜 (Fin d') → EuclideanSpace 𝕜 (Fin d)`,
`M eⱼ = ∑ᵢ ⟪uᵢ, vⱼ⟫ • eᵢ`, and never introduce `↥U →ₗ ↥V`. All three
consumers (W3.3, W5.2, W6 angle-forms) want the flat matrix anyway. Rewrite
W0.2 to drop the compression-map phrasing.

**R4 — Missing dependency: `singularValues_adjoint` does not exist in Mathlib**
(I grepped — confirmed absent). W0.2(b) symmetry `cosPA U V = cosPA V U` rests
on `σ(M) = σ(M†)`, which must be built. It's a clean lemma
(`(M†M)` and `(MM†)` have equal nonzero spectra ⇒ equal singular values) and
independently Mathlib-attractive — **add it to W0.1 as an explicit sub-item**,
difficulty 3/5, and add a `comparator/candidate` entry. Do not assume it.

**R5 — W3.4 is subtly wrong about `O`, and the fix makes it depend hard on
W3.1.** Using `polarFactor M` (a *partial* isometry) fails when `M` is singular
(some `cosθ = 0`, i.e. a right angle): `w` is then not orthonormal and
`tr(O†M) = tr|M|` breaks. The correct `O` is the **kernel-completed unitary**
from W3.1, for which `O†M = |M|` holds with `O` unitary regardless of `M`'s
rank. So (i) W3.1 must produce a genuine `E ≃ₗᵢ E`, not just a partial
isometry (its current spec does — keep it); (ii) apply W3.1 at the flat
`d`-dimensional level to `M` (or `M†` — fix the side once and stay consistent);
(iii) `tr(O†M) = ∑σᵢ` becomes an *equality*, no SVD needed, sidestepping
Mathlib's missing matrix SVD. This is the crux that lets W3 avoid SVD at all —
call it out so no one reaches for `polarFactor` directly.

**R6 — W5.1 is at the edge of what I can land cleanly; timebox it.** I concur
with 5/5. Two specific under-specifications that will bite:
- The "commute inner product past the Bochner integral" step needs an
  operator-valued integral into `E₂ →L[𝕜] E₁` and a lemma of the shape
  `⟪u, (∫ f) v⟫ = ∫ ⟪u, f·v⟫`. Mathlib has `ContinuousLinearMap.integral_comp_comm`
  / `integral_clm` style lemmas but I am **not certain the exact form needed
  exists**; verify before committing, else the fallback (entrywise
  Schur-multiplier + Minkowski integral inequality, scalar integrals only) is
  safer and I'd start there.
- The spectrally-defined `expScaled(t)` needs measurability in `t` and
  integrability from the exponential bound; each is a small but real lemma.
- **Recommendation:** attempt W5.1 on a timebox. If the operator-integral
  infrastructure resists, deliver only the Frobenius operator-norm corollary
  the repo actually consumes and **defer the dimension-free op-norm sinΘ**,
  documenting the descope. Nothing downstream in the DKPS pipeline needs W5.2.

**R7 — Too difficult for me to commit to (flagging per instructions):**
- **W5.1 / W5.2 (op-norm sinΘ):** feasible but genuinely research-grade; treat
  as "attempt with descope option," not "will land." See R6.
- **W7 (unitarily invariant norms) in full:** agree with Fable — this is a
  standalone Mathlib-sized library (symmetric gauge functions + Fan dominance +
  von Neumann trace inequality). I would **not** take it on inside this effort;
  it deserves its own project. W7.1/W7.2 especially.
- **W6.3 (subspace-level op-norm sin2Θ):** defer; its op-norm form is downstream
  of W7. The Frobenius-summed W6.1/W6.2 are fine.
Everything else (W0, W1, W2.1–2.3, W3.1–3.3, W4) I assess as within reach at
Fable's stated difficulties, with W2.4 rerated up to 4/5 per R1.

**R8 — Process gap: no "statement-first" gate.** For every step whose *content*
is a derivation rather than a generalization (W2.4, W3.4, W4.3, W5.1, W6.1),
the plan should require writing the final `theorem … := sorry` with the exact
literature constant and a one-paragraph paper cross-check *before* proving, so a
wrong constant is caught in minutes not hours. Add this to Definition of done.

## Definition of done (per batch and overall)

- **Statement-first gate (per R8):** for every derivation-content step (W2.4,
  W3.4, W4.3, W5.1, W6.1) write the final `theorem … := sorry` with the exact
  literature constant and a one-paragraph paper cross-check *before* proving.
- `lake build` green (all ~8.6k jobs), zero `sorry`, `#print axioms` on each
  headline = `propext, Classical.choice, Quot.sound`.
- Every new file: staging provenance header, docstrings on public decls,
  registered in `ForMathlib.lean`.
- Golf pass per `dev/mathlib-quality-adapter.md` (`mathlib-quality:cleanup`
  with the provenance carve-out; decompose any proof > ~60 lines, > ~15 for
  headlines); statements never drift during golf.
- `papers/DavisKahan-formalized-vs-literature.tex`: move each closed item out
  of §"What is not formalized", extend the dictionary table, update the
  companion permalink, add the authoring model to the author list per the
  file's NOTE.
- Consider a `comparator/candidate-*.json` entry for independently
  Mathlib-attractive pieces (Hoffman–Wielandt W2.3, unitary polar W3.1,
  principal angles W0.2, Sylvester bound W5.1).
