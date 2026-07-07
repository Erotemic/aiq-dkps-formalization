# Decomposition — Operator polar decomposition `A = U|A|` + the intertwining unitary

> **STATUS (2026-07-07): COMPLETE.** All milestones (M1: PD-01..PD-12, M2: PD-13..PD-17,
> M3: PD-18) are proven, sorry-free, and axiom-clean; Davis Result B (BL1–BL6) is discharged
> in `ForMathlib/Analysis/InnerProductSpace/RotationBound.lean`. See `tickets.md` for
> per-ticket implementation notes. Route deviation from this plan worth recording: `blockPolar`
> (M2.2) is obtained by *restricting the assembled intertwining unitary* — block surjectivity
> follows from `U Pⱼ = P'ⱼ U`, so the rank-equality/dimension-count argument sketched below was
> never needed.

Spun off from the Davis Result-B **API gap BL3** (`.mathlib-quality/decomposition-B.md`): Davis's
sharper total-rotation estimate needs the canonical matching unitary `U`, whose construction is the
operator polar decomposition. Mathlib has **no** polar decomposition and **no** partial-isometry API
(grep-confirmed, all of Mathlib, rev 476fb97).

**Scope decision (user, 2026-07-04):** *hybrid carrier* — build the general `A=U|A|` in `E →L[ℂ] E`
via `CFC.abs` (the "via CFC" headline) **and** a `LinearMap`/RCLike route for Davis; *full chain* —
polar decomposition → invertible/unitary case → intertwining unitary → wire into Davis BL3.

## Skeleton location & build status
Milestone-1 skeleton (every declaration `:= sorry`/`by sorry`) written and **`lake build`
green** (only `sorry` warnings), verified 2026-07-04:
- `ForMathlib/Analysis/InnerProductSpace/PositiveSqrt.lean`      (Sub-dev I)
- `ForMathlib/Analysis/InnerProductSpace/PartialIsometry.lean`   (Sub-dev II)
- `ForMathlib/Analysis/InnerProductSpace/PolarDecomposition.lean` (Sub-dev III + CFC bridge)
- `ForMathlib/Analysis/InnerProductSpace/IntertwiningUnitary.lean` (Milestone 2 + spectral proj) —
  authored 2026-07-04 at user request; `lake build` green (sorries only).

Milestone 3 (Davis wiring) is decomposed below at ticket level; it consumes the parent Result-B
board (`decomposition-B.md`). REVIEW note: the M1 skeleton *compiling* is the physical proof that the ℂ-CLM ↔ RCLike
bridge type-checks — in particular `(abs A).toContinuousLinearMap = CFC.abs A.toContinuousLinearMap`
and the headline `A = U ∘L CFC.abs A` elaborate.

---

## ★ Proof-route pivot (binding, read first) ★

Horn & Johnson prove the polar decomposition (Thm 7.3.1) **via the SVD factorization `A = VΣW*`**
(their Thm 2.6.3). **Mathlib has no SVD factorization** — `Mathlib/Analysis/InnerProductSpace/
SingularValues.lean` defines the singular *values* (numbers) only, not the factorization. So HJ's
proof route is NOT formalizable without first building SVD (a large detour we avoid).

We instead use the **operator/isometry route (ii)**, the standard functional-analysis proof:
`|A| = (A⋆A)^{1/2}`; the identity `‖A x‖ = ‖|A| x‖`; the isometry `|A|x ↦ Ax` on `range|A|`;
extension by `0` on `ker|A|`. Source of this route: **Conway, *A Course in Functional Analysis*,
2nd ed., VI.3.9**; **Reed–Simon I, Thm VI.10**; **Riesz–Sz.-Nagy §110/§136** (cited by Davis).

Consequence for source-faithfulness: HJ supplies the *statements* (7.3.1, 7.2.6, 7.2.7b) verbatim;
the route-(ii) *mechanics* (norm identity, isometry extension) are elementary consequences we
expand ourselves, cited to Conway VI.3. Every such leaf is one paragraph of standard linear algebra.

## Prior-B2 log consultation (Step 4.6)
`.mathlib-quality/b2_log.jsonl` is **absent/empty** (checked 2026-07-04). No name- or shape-match to
any prior B2 for any leaf below. Step 4.6 is vacuously satisfied for the whole tree.

---

# Milestone 1 — General polar decomposition `A = U|A|`

## Sub-dev I — Positive-operator square root (`PositiveSqrt.lean`)

### Plain-English proof (HJ §7.2)
`T ≥ 0` symmetric on finite-dim `E` (over `𝕜 : RCLike`). By the spectral theorem `T = ∑ᵢ λᵢ Pᵢ`
with `λᵢ ≥ 0` and `Pᵢ` the rank-one projections onto an orthonormal eigenbasis `eᵢ`. Define
`sqrt T := ∑ᵢ √λᵢ Pᵢ`. Then `sqrt T ≥ 0` symmetric, `(sqrt T)² = ∑ᵢ λᵢ Pᵢ = T`, and (spectral)
`ker(sqrt T) = ker T`, `range(sqrt T) = range T`. Uniqueness: any PSD `S` with `S²=T` commutes with
`T`, is simultaneously diagonalizable, and equals `sqrt T` by uniqueness of nonneg real roots.

### Leaves
- **I.1** (leaf): `LinearMap.IsPositive.sqrt` (def) — `PositiveSqrt.lean:33`
  - `noncomputable def sqrt {T : E →ₗ[𝕜] E} (_hT : T.IsPositive) : E →ₗ[𝕜] E := sorry`
    (intended body `∑ i : Fin (finrank 𝕜 E), (√(eigenvalues i):𝕜) • (rankOne 𝕜 eᵢ eᵢ).toLinearMap`)
  - Source: HJ Thm 7.2.6, p. 440 (verbatim): *"We denote the unique positive (semi)definite square
    root of a positive (semi)definite matrix A by A^{1/2}."* Construction mirrors HJ's proof
    (`B = UΣ^{1/2}U*`).
  - Discharge: project code — the exact eigenbasis-sqrt pattern is already proven in
    `ForMathlib/LinearAlgebra/Matrix/PosDef.lean` (`PosSemidef.exists_eq_conjTranspose_mul_self`
    builds `√λ • eigenvector`); mathlib `Positive.lean:544` uses the identical inline term.
    Building blocks verified: `IsSymmetric.eigenvalues/eigenvectorBasis` (Spectrum.lean:279/300),
    `rankOne`/`rankOne_apply` (LinearMap.lean:303/322), `OrthonormalBasis.sum_repr` (PiL2.lean:492),
    `IsPositive.nonneg_eigenvalues` (Positive.lean:155).
  - Attacks attempted:
    1. Counterexample: is `∑√λᵢPᵢ` really `≥0`? `√λᵢ≥0` since `λᵢ≥0` (`nonneg_eigenvalues`), sum of
       PSD rank-ones is PSD (`isPositive_sum`, `isPositive_rankOne_self`). No counterexample.
    2. Edge cases: `T=0` → all `λᵢ=0` → `sqrt 0 = 0` ✓ (`sq_norm` etc. hold). `T=1` → `λᵢ=1` →
       `sqrt 1 = ∑Pᵢ = 1` ✓. `dim E = 0` → empty sum = 0 ✓ (vacuous).
    3. Hypothesis test: `IsPositive` (symmetric + nonneg form) is exactly what's needed for `λᵢ`
       real (`IsSymmetric.eigenvalues : Fin n → ℝ`) and `≥0`. Dropping symmetry: eigenvalues not
       even real → `√` undefined. Necessary, not over-specified. `FiniteDimensional` necessary for
       eigenbasis to span. No hidden assumption.
    - Verdict: SURVIVED. This is the one genuinely-new construction leaf; ~40 LOC (mathlib's inline
      version is ~6 lines; the named def + `sum_repr` bookkeeping adds overhead).
- **I.2** (leaf): `sqrt_mul_self : hT.sqrt ∘ₗ hT.sqrt = T` — `PositiveSqrt.lean:47`
  - Source: HJ 7.2.6 (`Bᵏ = A`; here k=2). Discharge: from I.1's def, `(∑√λPᵢ)² = ∑λPᵢ = T` via
    orthonormality (`Pᵢ Pⱼ = δᵢⱼ Pᵢ`) and `T = ∑λᵢPᵢ` (`apply_eigenvectorBasis` + `sum_repr`).
  - Attacks: (1) counterexample: cross terms `PᵢPⱼ (i≠j)` must vanish — they do, eigenbasis
    orthonormal. (2) edge `dim0`: 0=0 ✓. (3) hypothesis: needs orthonormality of eigvecs — supplied
    by `eigenvectorBasis : OrthonormalBasis`. SURVIVED. ~30 LOC.
- **I.3** (leaf): `sq_norm_sqrt_apply : ‖hT.sqrt x‖² = re⟪T x,x⟫` — `PositiveSqrt.lean:63`
  - Source: consequence of I.2 (`‖Sx‖² = re⟪Sx,Sx⟫ = re⟪S²x,x⟫` for `S` symmetric). Discharge:
    `real_inner_self_eq_norm_sq`, `IsSymmetric` adjoint move, I.2. Attacks: (1) sign — `re⟪Tx,x⟫≥0`
    by `IsPositive`, matches `‖·‖²≥0` ✓. (2) `x=0` → 0=0 ✓. (3) needs `sqrt` symmetric (I, via
    `sqrt_isPositive`). SURVIVED. ~15 LOC.
- **I.4** (leaf): `ker_sqrt : ker hT.sqrt = ker T` — `PositiveSqrt.lean:69`
  - Source: HJ 7.2.7(b), p.440 (verbatim): *"if x ∈ Cⁿ, then Ax = 0 if and only if Bx = 0"* (for
    `A=B*B`; here `T = (sqrt T)² = (sqrt T)⋆(sqrt T)` since sqrt symmetric). Discharge: I.3
    (`sqrt T x = 0 ↔ ‖sqrt T x‖=0 ↔ re⟪Tx,x⟫=0 ↔ Tx=0` for `T≥0`). Attacks: (1) `⊇`: `Tx=0 ⟹
    re⟪Tx,x⟫=0 ⟹ ‖sqrtT x‖=0`✓; `⊆`: `sqrtT x=0 ⟹ Tx=(sqrtT)²x=0`✓. (2) edge trivial. (3)
    positivity of `T` needed for the `re⟪Tx,x⟫=0 ⟹ Tx=0` step (`inner_map_self_eq_zero` for PSD).
    SURVIVED. ~15 LOC.
- **I.5** (leaf): `range_sqrt : range hT.sqrt = range T` — `PositiveSqrt.lean:75`
  - Source: HJ 7.2.6(c), p.440 (verbatim): *"range A = range B, so rank A = rankB."* Discharge:
    finite-dim rank-nullity + I.4 (`ker` equal ⟹ `range` equal dims; and `range(sqrt) ⊇ range T`
    since `T = sqrt·sqrt`). Attacks: (1) `range T ⊆ range sqrt`: `Tx = sqrt(sqrt x)` ✓. reverse via
    dims from I.4 + symmetric self-orthogonality. (2) trivial edges. (3) finite-dim essential
    (rank-nullity). SURVIVED. ~15 LOC.
- **I.6** (leaf): `sqrt_unique` — `PositiveSqrt.lean:57`
  - Source: HJ 7.2.6(a) verbatim: *"There is a **unique** Hermitian positive semidefinite matrix B
    such that B² = A."* Discharge: `S²=T=sqrt²`, both PSD; on each `T`-eigenspace both act as `√λ`
    (commute with T, simultaneously diagonalize). Attacks: (1) two distinct PSD sqrts? impossible by
    nonneg-root uniqueness. (2) `T=0`: only `S=0` PSD with `S²=0` ✓. (3) needs PSD on `S` (else
    `-sqrt` is another root) — hypothesis necessary. SURVIVED. ~40 LOC (uses commutant/simul-diag).
- **I.7** (leaf): `isUnit_sqrt_of_isUnit` — `PositiveSqrt.lean:81`
  - Source: HJ 7.2.6 proof (`Σ^{1/2}` invertible iff `Σ` invertible). Discharge: `T` invertible ⟺
    all `λᵢ>0` ⟺ all `√λᵢ>0` ⟺ `sqrt T` invertible. Attacks: (1) `λᵢ=0` somewhere → not a unit,
    consistent. (2) `det`-style. (3) needs strict positivity ⟺ IsUnit for symmetric. SURVIVED. ~20 LOC.

## Sub-dev II — Partial isometry API (`PartialIsometry.lean`)

### Plain-English (Conway VI.3)
`u` is a **partial isometry** iff `u⋆u` is a projection, iff `u` is isometric on `(ker u)ᗮ` and
zero on `ker u`. `(ker u)ᗮ` is the *initial space*, `range u` the *final space*.

### Leaves
- **II.1** (def): `IsPartialIsometry u := u * star u * u = u` — `PartialIsometry.lean:33`
  - Source: Conway VI.3.1 (standard; the algebraic characterization `uu*u=u`). Stated abstractly for
    `[Monoid R] [StarMul R]` (max generality — works for both `→ₗ` and `→L` and any C⋆-algebra).
  - Attacks: (1) is `uu*u=u` the right defn (vs `u*u` projection)? equivalent in any *-monoid; both
    standard. (2) unitary `u` (`u*u=1`): `uu*u = u·1 = u` ✓. (3) `u=0`: `0=0` ✓ partial isometry.
    SURVIVED.
- **II.2** (leaf): `isStarProjection_star_mul_self` — `PartialIsometry.lean:41`. Source Conway VI.3.2.
  Discharge: `(u*u)² = u*(uu*u) = u*u` from II.1; `star(u*u)=u*u`. `IsStarProjection` (StarProjection.lean:27).
  Attacks: (1) idempotent from `uu*u=u`✓ (2) self-adjoint `star(u*u)=u*u`✓ (3) n/a-abstract. SURVIVED. ~8 LOC.
- **II.3** (leaf): `star_star`, **II.4** `of_star_mul_self_eq_one` — algebraic, Conway VI.3.
  Discharge: star-monoid algebra. SURVIVED (unitary ⟹ PI; star of PI is PI — standard *-identities). ~6 LOC each.
- **II.5** (leaf): `isPartialIsometry_iff_norm_map : IsPartialIsometry u ↔ ∀ x∈(ker u)ᗮ, ‖u x‖=‖x‖`
  — `PartialIsometry.lean:56`. Source Conway VI.3.2 (verbatim standard): *"a partial isometry is an
  operator that is isometric on the orthogonal complement of its kernel."* Discharge: `u*u` =
  orthogonal projection onto `(ker u)ᗮ` iff isometric there; `IsStarProjection`+`orthogonal_ker`
  (Adjoint.lean:607). Attacks: (1) `x∈ker u`: `‖ux‖=0` but excluded from `(ker u)ᗮ` ✓. (2) unitary:
  isometric everywhere, `(ker u)ᗮ=⊤` ✓. (3) needs finite-dim for `(ker u)ᗮ` decomposition. SURVIVED. ~40 LOC.
- **II.6** (leaf): `star_mul_self_eq_starProjection` — `PartialIsometry.lean:62`. `u*u =
  starProjection (ker u)ᗮ`. Building block `Submodule.starProjection` (Projection/Basic.lean:124).
  SURVIVED (companion to II.5). ~25 LOC.
- **II.7** (leaf): `isPartialIsometry_of_isometryOn` — `PartialIsometry.lean:71`. The **constructor**
  for Sub-dev III: isometric on `K`, `ker u = Kᗮ` ⟹ PI. Discharge: II.5 (`K = (ker u)ᗮ`).
  Attacks: (1) `K` vs `(ker u)ᗮ` must coincide — hypothesis `ker u = Kᗮ` gives `(ker u)ᗮ = Kᗮᗮ = K`
  (finite-dim, `Submodule.orthogonal_orthogonal`). (2) `K=⊤`: unitary. (3) `K=⊥`: `u=0`. SURVIVED. ~20 LOC.

## Sub-dev III — Polar decomposition (`PolarDecomposition.lean`)

### Plain-English proof (route ii; Conway VI.3.9)
Let `P := |A| = (A⋆A)^{1/2}` (Sub-dev I sqrt of the positive `A⋆A`). (★) `‖P x‖ = ‖A x‖` (from
`P² = A⋆A`, i.e. `‖Px‖² = re⟪A⋆A x,x⟫ = ‖Ax‖²`). Hence `ker P = ker A`, and by (★) the assignment
`V₀ : P x ↦ A x` is a well-defined linear **isometry** `range P → range A` (well-def: `Px=Py ⟹
P(x−y)=0 ⟹ A(x−y)=0`). Extend to `U := V₀ ∘ (orthogonal projection onto range P)`, i.e. `U=0` on
`(range P)ᗮ = ker P = ker A`. Then `U` is a partial isometry and `U(Px)=Ax`, i.e. `A = U P`. When
`A` is invertible, `P` is invertible, `U = A P⁻¹` is unitary (a `LinearIsometryEquiv`).

### Leaves
- **III.1** (def): `ForMathlib.abs A := (isPositive_adjoint_comp_self A).sqrt` — `PolarDecomposition.lean:37`
  - Source: HJ 7.3.1 (verbatim, p.449): *"Q = (A∗A)^{1/2} … uniquely determined; it is a polynomial
    in A∗A."* (task's `|A|` = HJ's right factor `Q`.) Discharge: `isPositive_adjoint_comp_self`
    (Positive.lean, verified: `(A.adjoint ∘ₗ A).IsPositive`) + Sub-dev I sqrt. Attacks: (1) `A⋆A≥0`
    always ✓. (2) `A=0`→`|0|=0`. (3) `star A * A = adjoint A ∘ₗ A` (star=adjoint, Adjoint.lean:699).
    SURVIVED.
- **III.2** (leaf): `abs_mul_self : abs A ∘ₗ abs A = A.adjoint ∘ₗ A` — `:47`. Discharge: I.2 directly.
  Cross-checks with mathlib `CFC.abs_mul_abs` (Abs.lean:64, verbatim `abs a * abs a = star a * a`).
  SURVIVED. ~2 LOC.
- **III.3** (leaf): `norm_abs_apply : ‖abs A x‖ = ‖A x‖` — `:52`. **The key (★).** Source: NOT in HJ
  (route-ii lemma, Conway VI.3.9); one line from I.3 (`‖abs A x‖² = re⟪A⋆A x,x⟫ = ‖Ax‖²`) +
  `re_inner_adjoint_comp_self` / `‖Ax‖²=re⟪A⋆Ax,x⟫`. Attacks: (1) sign/sqrt: both sides `≥0`,
  squares equal ⟹ equal. (2) `x∈ker A`: `0=0`. (3) needs `A⋆A` = `star A * A` (Adjoint). SURVIVED. ~10 LOC.
- **III.4** (leaf): `ker_abs : ker (abs A) = ker A` — `:57`. Discharge: III.3 (or I.4 +
  `ker_adjoint_comp_self` Adjoint.lean:620 `(A.adjoint∘ₗA).ker = A.ker`). SURVIVED. ~10 LOC.
- **III.5** (leaf): `range_abs : range (abs A) = (ker A)ᗮ` — `:62`. Discharge: `abs A` symmetric
  (`sqrt_isSymmetric`) ⟹ `range(abs A) = (ker (abs A))ᗮ` (`LinearMap.orthogonal_ker`/normal
  `orthogonal_range`, Adjoint.lean:607/416) `= (ker A)ᗮ` (III.4). Attacks: (1) symmetric needed for
  range=ker^perp ✓ (abs is PSD). (2) finite-dim (double perp). (3) `A=0`: `range 0 = ⊥ = ⊤ᗮ`,
  `ker 0 = ⊤` ✓. SURVIVED. ~10 LOC.
- **III.6** (def): `polarUnitary A` — `:68` (`:= sorry`, construction is a ticket).
  - Construction (Conway VI.3.9): `V₀ : range(abs A) → E` well-defined by `abs A x ↦ A x`, extended
    by `0` on `(range abs A)ᗮ`. Building blocks verified: `Submodule.isCompl_orthogonal`
    (Projection/Basic.lean:89), `Submodule.linearProjOfIsCompl`/`prodEquivOfIsCompl`
    (Projection.lean:76/338), `starProjection` (Projection/Basic.lean:124), III.3 for well-def.
  - Source: Conway VI.3.9 (partial-isometry factor). Attacks: (1) well-defined? `Px=Py ⟹ Ax=Ay` by
    III.3/III.4 (the crux; `ker P=ker A`). (2) linear? `V₀` linear since `A`,`P` linear and `P`
    surjects `range P`. (3) `A=0`: `U=0`, a (trivial) partial isometry. SURVIVED — construction
    feasible from verified primitives.
- **III.7** (leaf): `polar_decomposition : A = polarUnitary A ∘ₗ abs A` — `:73`.
  - Source: HJ 7.3.1(b) verbatim: *"A = PU = UQ … P=(AA*)^{1/2}, Q=(A*A)^{1/2} … U unitary"* +
    Conway VI.3.9. Discharge: `U(abs A x) = V₀(abs A x) = A x` by construction. Attacks: (1) does
    `U∘ₗabs A` agree with `A` on all `x`? on `range(absA)` by def; `absA x ∈ range(absA)` always ✓.
    (2) `A=0`: `0 = 0∘ₗ0` ✓. (3) uniqueness NOT claimed here (separate). SURVIVED. ~15 LOC.
- **III.8** (leaf): `polarUnitary_isPartialIsometry` — `:78`. Discharge: II.7 (`isometryOn` with
  `K=range(absA)`, `ker U = (range absA)ᗮ = ker A` [III.5], isometric via III.3). SURVIVED. ~15 LOC.
- **III.9** (leaf): `ker_polarUnitary : ker U = ker A` — `:83`. Source Conway VI.3.9 (`ker W = ker A`).
  Discharge: construction (`U=0` on `ker A`, injective on `(ker A)ᗮ`). SURVIVED. ~10 LOC.
- **III.10** (leaf): `norm_polarUnitary_apply_of_mem` — `:88`. Isometric on `(ker A)ᗮ`. Discharge:
  III.3 + construction. SURVIVED. ~10 LOC.

### Invertible case (unitary factor)
- **III.11** (def): `polarUnitaryEquiv (hA : IsUnit A) : E ≃ₗᵢ[𝕜] E` — `:97` (`:= sorry`).
  - Source: HJ 7.3.1(b) verbatim: *"The factor U is uniquely determined **if A is nonsingular**"*,
    with explicit `U = P⁻¹A = AQ⁻¹`. Discharge: `A` unit ⟹ `abs A` unit (I.7) ⟹ `U = A ∘ₗ (absA)⁻¹`
    is a bijective isometry ⟹ `LinearIsometryEquiv`. Building blocks: `LinearIsometryEquiv`,
    `Unitary.linearIsometryEquiv` (Adjoint.lean:944). Attacks: (1) isometry: III.10 with
    `(ker A)ᗮ=⊤` (A injective). (2) surjective: `A` surjective ⟹ `U` surjective. (3) `abs A`
    invertible needs `A` invertible (I.7) ✓. SURVIVED. ~30 LOC.
- **III.12** (leaf): `coe_polarUnitaryEquiv`, **III.13** `polar_decomposition_of_isUnit` — `:102/107`.
  Bridge the equiv to `polarUnitary`/`polar_decomposition`. SURVIVED. ~10 LOC each.

### CFC bridge — ℂ / ContinuousLinearMap headline
- **III.14** (leaf): `abs_toContinuousLinearMap_eq_cfcAbs` — `:116`.
  `(abs A).toContinuousLinearMap = CFC.abs A.toContinuousLinearMap` for `A : H →ₗ[ℂ] H`.
  - Source: both are the unique PSD sqrt of `A⋆A` (HJ 7.2.6 uniqueness = I.6). Discharge: `CFC.abs`
    = `CFC.sqrt (star·)`; `CFC.sqrt` is PSD with square `A⋆A` (`abs_mul_abs`, Abs.lean:64);
    `(abs A).toCLM` is PSD with square `A⋆A` (III.2, via the **`rfl` adjoint bridge**
    `adjoint_toContinuousLinearMap`, Adjoint.lean:541); apply I.6/CFC sqrt-uniqueness.
  - Attacks: (1) do the two `A⋆A`s coincide across the bridge? YES — `star=adjoint` both worlds and
    `adjoint_toContinuousLinearMap` is `rfl` (verified). (2) is `CFC.abs` output PSD symmetric to
    match? `abs_nonneg` (Abs.lean:53). (3) uniqueness needs both PSD — both are (`abs_nonneg`,
    `sqrt_isPositive`). SURVIVED — **this leaf is why the M1 skeleton compiling matters**; the types
    align only because the bridge is definitional. ~35 LOC.
- **III.15** (leaf): `continuousLinearMap_polar_decomposition` — `:122`. The literal "via CFC"
  headline: `∃ U, IsPartialIsometry U ∧ A = U ∘L CFC.abs A` for `A : H →L[ℂ] H`. Discharge: transport
  III.7 + III.14 through `toContinuousLinearMap` (a *-algebra/ring equiv on finite-dim). SURVIVED. ~25 LOC.

---

# Milestone 2 — Intertwining (canonical matching) unitary (`IntertwiningUnitary.lean`)

Source: **Davis (1963) §2**, lines 217–312 (`.tex` present) + digest §2. Skeleton deferred (consumes
M1 API). Internal-node structure mirrors Davis's own construction (source proof structure preserved).

### Source (Davis §2, verbatim lines 218–230)
> "Define U=U({P_j},{P'_j}) by requiring for all j that  U P_j=(P'_j P_j P'_j)^{-1/2} P'_j P_j …
> This makes sense, and determines a unitary U, at least under the hypothesis that, for all j,
> x=P_j x≠0 implies P'_j x≠0. … Clearly U P_j = P'_j U = P'_j(P_j P'_j P_j)^{-1/2} P_j."

### Prerequisite (Sub-dev I.5): spectral projections
Mathlib has no spectral/eigenspace projection *operator*. Build `Pⱼ` = orthogonal projection onto
an eigenspace (from `eigenvectorBasis` + `Submodule.starProjection`). Small file/section; ~1 def +
`IsStarProjection Pⱼ`, `∑Pⱼ = 1`, `Pⱼ Pₖ = 0 (j≠k)`. **This is an API gap with its own mini-tree.**

### Decomposition (mirrors Davis §2)
- **M2.1** (leaf): non-degeneracy `Pⱼx≠0 ⟹ P'ⱼPⱼx≠0` ⟹ `P'ⱼPⱼP'ⱼ` strictly positive on `range P'ⱼ`
  (so `(P'ⱼPⱼP'ⱼ)^{-1/2}` exists via I.7 + inverse sqrt). Davis line 224.
- **M2.2** (internal): block polar factor `Wⱼ = (P'ⱼPⱼP'ⱼ)^{-1/2} P'ⱼPⱼ : range Pⱼ ≃ₗᵢ range P'ⱼ` is
  **unitary** — this is the invertible-case polar decomposition (III.11) applied to `Mⱼ=P'ⱼPⱼ`
  restricted to the block. Davis line 221. Sub-leaves: M2.2a `Mⱼ` bijective block→block (from M2.1 +
  equal ranks); M2.2b `Wⱼ = polarUnitaryEquiv` of `Mⱼ|block`.
- **M2.3** (def+leaf): `intertwiningUnitary : E ≃ₗᵢ[𝕜] E := ∑ⱼ Wⱼ ∘ Pⱼ`; `WPⱼ = P'ⱼW` (Davis
  line 229); `W` unitary. Internal node — assembles M2.2 over the complete family.
- **M2.4** (leaf): angle interpretation `‖𝒞⊥W‖²_F = ∑ᵢ sin²θᵢ`, `θᵢ = arccos⟨Wxᵢ,xᵢ⟩` (Davis §2,
  lines 280–312, which Davis proves in full — the `‖Off U‖₂² = ‖W‖₂² − ‖𝒞W‖₂²` computation). Needed
  by parent BL4.
- **DEFERRED (not on BL3 path):** Davis Thm 2.1/2.3 *minimality* (`‖1−W‖₂` minimal). Davis line 249:
  *"The proof need not be duplicated here"* — it lives in **Davis (1958) §7, which we do NOT have**.
  Per the source-gap fallback chain this is REVIEW-PENDING/deferred; Result B (BL1–BL6) does not use
  minimality (it uses the *canonical* `W` + the angle interpretation, both available). Flag to user.

# Milestone 3 — Wire into Davis Result B (BL3/BL4)
Instantiate M2 with the spectral projection families of `T` and `S` (parent's symmetric operators);
supply `W`, `WPⱼ=P'ⱼW`, angles `θᵢ`, `‖𝒞⊥W‖²=∑sin²θᵢ` to the parent's BL3/BL4. Then parent BL1, BL2,
BL5, BL6 (already decomposed in `decomposition-B.md`) execute. **This project's deliverable = unblock
BL3+BL4.** M3 is one bridging file/section referencing `EigenvalueChange.lean` + `decomposition-B.md`.

---

# Confidence gate (Step 5)
- **M1 (Sub-devs I, II, III + CFC bridge): PASSES.** Every leaf discharged from mathlib
  (verified names/lines) or project code, or is the one new construction leaf (I.1, III.6, III.11)
  with feasibility established from verified primitives. Skeleton compiles (`lake build` green).
  Verbatim source quotes present (HJ 7.2.6/7.2.7b/7.3.1; Conway VI.3.9). Adversarial pass ≥3 attacks
  per leaf, all SURVIVED. Prior-B2 log empty. Route-(ii) pivot documented.
- **M2: PASSES for M2.1–M2.4** (feasible from M1 + verified spectral-projection primitives), with the
  **spectral-projection prerequisite (I.5) an explicit API gap** getting its own mini-tree at ticket
  time. Davis §2 quotes present. Minimality is **DEFERRED/REVIEW-PENDING** (source Davis1958 §7
  unavailable; off the BL3 critical path) — its tickets are NOT created; flagged to user.
- **M3: PASSES** (consumes parent's existing decomposition-B.md).

# Feasibility assessment
Feasible and bounded. `|A|=√(A⋆A)` "via CFC" is *already in mathlib* (`CFC.abs`) — the genuine work
is the factorization `A=U|A|` and the intertwining unitary, both absent from mathlib. The hybrid
carrier is validated: the ℂ-CLM headline (`CFC.abs`) and the RCLike route (spectral `sqrt`) coexist,
joined by the **definitional** `LinearMap↔CLM` adjoint bridge — the M1 skeleton compiling is the
proof. The only from-scratch pieces are three constructions (spectral `sqrt`, the polar factor `U`,
the invertible unitary) plus the intertwining-unitary assembly — all standard, all with verified
building blocks. No SVD is needed (route ii avoids HJ's SVD proof). No multi-week gap. The single
genuine source-availability gap (Davis1958 §7 minimality) is off the critical path and deferred.
