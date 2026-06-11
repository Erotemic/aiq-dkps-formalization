# Acharyya DKPS formalization plan

Active planning document. Companion: `acharyya-graveyard.md` (approaches tried and
abandoned, so we and other agents don't re-visit them).

Last updated: 2026-06-11 (Claude Fable 5 session, model id claude-fable-5[1m]).

## Goal

Complete the `Acharyya2024` (asymptotic consistency, arXiv:2409.17308) and
`Acharyya2025` (finite-sample concentration, arXiv:2511.08307) scaffolds to the
point where:

1. Every `sorry` that remains is a *faithful* statement of a citable external
   theorem (ideally exactly one: Davis–Kahan), with real — not placeholder —
   hypotheses.
2. Every statement that is currently **false as written** is repaired (see
   inventory below). This is the highest-priority debt: a `sorry` on a false
   statement is worse than no theorem, because downstream code type-checks
   against a lie.
3. The deterministic + probabilistic reduction chains are fully proved, and the
   downstream consumers (`DkpsQuench/AcharyyaBridge`, `Helm2025/AcharyyaBridge`)
   are re-wired to the hardened statements.
4. Paper-agnostic lemmas land in `WellKnown.lean`-style files, Mathlib-ready.

## Ground rules

- No `axiom` declarations. `sorry` only for cited seams with faithful statements.
- A statement is "hardened" when its hypotheses are sufficient to make it true
  and are satisfiable in the paper's setting (no vacuous `Prop` struct fields,
  no `1/(u+1)` placeholder rates).
- One logical commit per work package (WP). Do not commit unrelated dirty files
  (`DkpsQuench/Basic.lean`, `DrsbBridge/V1.lean`, `Helm2025/Basic.lean` are
  dirty from other work — leave them out).
- Failed proof strategies get a dated entry in the graveyard, not silence.
- Provenance lines in docstrings (`Formalized by <model>`).
- Verify per-file with `~/.elan/bin/lake env lean <file>`; full
  `lake build Acharyya2024 Acharyya2025` before each commit;
  `grep -RIn 'axiom\|sorry'` in the commit message footer.

## Sorry inventory and truth status

| # | Location | Statement | Status |
|---|----------|-----------|--------|
| 1 | `Acharyya2024/Consistency.lean:41` `rawStress_mds_stability` | Trosset–Priebe raw-stress MDS stability | Plausibly true as stated; HARD (WP9) |
| 2 | `Acharyya2024/Consistency.lean:91` `growing_queries_dissimilarity_converges` | dissimilarity → Δ in probability | **FALSE as stated** (no hypotheses at all). Repair = WP2 |
| 3 | `Acharyya2024/Consistency.lean:134` `growing_models_growing_queries_consistency` | triangular-array regime | **FALSE as stated** (same disease). WP8 |
| 4 | `Acharyya2025/Concentration.lean:58` `dissimilarity_matrix_concentrates` | matrix concentration, Thm 1/Cor 1 | **FALSE as stated** (vacuous `ResponseRegularity`, placeholder rate, arbitrary `proc.sample`). WP6 |
| 5 | `Acharyya2025/Concentration.lean:86` `classical_mds_embedding_perturbation` | Thm 2 one-step form | **FALSE as stated** (no orthogonal alignment in `ConfigError`, vacuous stability). WP6 |
| 6 | `Acharyya2025/Bridge.lean:270` `cited_cmds_embedding_perturbation_from_centered_entrywise` | centered-matrix → config error | **FALSE as stated** (same: no alignment, vacuous `MDSStabilityAssumptions`). WP6 |
| 7 | `Acharyya2025/SpectralPipeline.lean` `cited_entrywise_to_operatorNormClose` | entrywise ε → operator nε | ✅ **PROVED** (WP1, this session) |
| 8 | `Acharyya2025/SpectralPipeline.lean` `cited_population_cmds_realization` | CMDS Gram realization | Unprovable as stated (vacuous `CMDSpectralAssumptions`); true core = WP3 |
| 9 | `Acharyya2025/SpectralPipeline.lean` `cited_cmds_spectral_to_config_perturbation` | Davis–Kahan/Weyl/Procrustes | The boss fight. Decomposed into WP4/WP5/WP7 |

Key structural defect shared by #4–#6: `ResponseRegularity`,
`MDSStabilityAssumptions`, and (partially) `CMDSpectralAssumptions` carry bare
`Prop` *fields* rather than actual mathematical content, so they constrain
nothing; and `ConfigError ψ̂ ψ = Σᵢ ‖ψ̂ᵢ − ψᵢ‖` with no alignment cannot be small
(CMDS output is only defined up to O(d)). Both papers' Thm-2-type results are
"up to W ∈ O(d)".

## Strategy decision (2026-06-11, user directive)

**Hard bridge layers first.** WP4 (Procrustes rigidity) → WP5 (Weyl) → WP7
(Davis–Kahan) are the priority, plus WP3 (Gram realization) which feeds them.
Downstream false statements (#2–#6) are NOT repaired now — they get an explicit
`TODO(false-statement)` marker in their docstrings and are fixed *after* the
hard theorems exist, when the right hypothesis shapes will be evident (WP6/WP8
deferred). WP2 (probability step) continues since it is already in flight and
is independent.

**Commit discipline:** every unit of progress gets a commit — including failed
directions (commit, then revert-with-message, or commit the graveyard entry).
The git history is the lab notebook for a case study on model formalization
ability.

## Work packages

Ordering ≈ (value × tractability). Each WP ends in one commit.

### WP0 — Planning docs (this commit)
`planning/acharyya-plan.md`, `planning/acharyya-graveyard.md`.

### WP1 — entrywise → operator norm  ✅ proved, ready to commit
`cited_entrywise_to_operatorNormClose`: per-coordinate `|xⱼ| ≤ ‖x‖₂` then sum;
constant `n·ε` (loose but as stated; tightening to `n^{1/2}·ε` via
Cauchy–Schwarz is optional later).

### WP2 — 2024 Theorem 2 probability step (agent in flight)
New `Acharyya2024/Probability.lean`:
`dissimilarity_convergesInProbability_of_secondMoment`:
hypotheses = measurability + `∫ ‖X̄ᵢ(r) − μᵢ‖² ≤ v(r)`, `v → 0`;
conclusion = `ConvergesInProbabilityZero P (frobSub (responseDist X̄) (responseDist μ))`.
Proof = Chebyshev/Markov + union bound over `Fin n` + the already-proved
deterministic `frobSub_responseDist_le_of_uniform_errors`.
Then: replace the false `growing_queries_dissimilarity_converges` with a
hardened wrapper (responseDist structure + moment hypotheses) and re-derive
`fixed_models_growing_queries_consistency` from it.

### WP3 — PSD rank-≤d Gram realization (agent in flight)
New `Acharyya2025/GramRealization.lean`:
`B.PosSemidef → B.rank ≤ d → ∃ ψ : Config n d, ∀ i j, ⟨ψᵢ,ψⱼ⟩ = B i j`
via Mathlib spectral theorem + injection of nonzero-eigenvalue indices into
`Fin d`. Then harden `CMDSpectralAssumptions` (replace `positive_rank_d : Prop`
etc. with `PosSemidef` + `rank ≤ d` + a real eigengap field) and prove
`cited_population_cmds_realization` from it.

### WP4 — Procrustes rigidity (exact case)
Equal Gram matrices ⇒ configurations related by a linear isometry:
`(∀ i j, ⟨ψᵢ,ψⱼ⟩ = ⟨φᵢ,φⱼ⟩) → ∃ W ∈ O(d), ∀ i, ψᵢ = W φᵢ`.
Math: the map `span{φᵢ} → span{ψᵢ}`, `φᵢ ↦ ψᵢ` is well-defined and inner-product
preserving; extend to O(d) on orthogonal complements
(`LinearIsometry.extend...` / orthonormal basis extension in Mathlib).
This is required to even *state* the perturbation theorems faithfully.
Deliverable also: `AlignedConfigError` definition
(`⨅ W : O(d), ConfigError (W ∘ ψ̂) ψ` or the ∃-form used in statements).

### WP5 — Weyl eigenvalue perturbation
`|λₖ(Â) − λₖ(A)| ≤ ‖Â − A‖op` for symmetric operators, eigenvalues sorted.

API survey results (2026-06-11): Mathlib HAS sorted eigenvalues for symmetric
operators — `LinearMap.IsSymmetric.eigenvalues hn : Fin n → ℝ` (decreasing,
`eigenvalues_antitone`) with orthonormal `eigenvectorBasis` and
`apply_eigenvectorBasis`, in `Mathlib/Analysis/InnerProductSpace/Spectrum.lean`.
No Courant–Fischer, no Weyl, no Davis–Kahan anywhere in Mathlib. Also found:
`LinearIsometry.extend` (PiL2.lean, finite-dim — the WP4 extension step) and
`Matrix.gram` + `Matrix.posSemidef_gram` (GramMatrix.lean).

DESIGN DECISIONS:
- Work in the OPERATOR world (`T : E →ₗ[ℝ] E`, `IsSymmetric`, finrank = n),
  where the sorted spectral API lives; bridge to `Matrix` later via
  `Matrix.toEuclideanLin`.
- DISCRETE Courant–Fischer: avoid `sSup`/`iInf` over subspaces entirely.
  Two inequality lemmas suffice for Weyl:
  (a) ∀ V with finrank V = k+1, ∃ unit x ∈ V, ⟪Tx,x⟫ ≤ λₖ   (dim counting
      against span{bᵢ : i ≥ k}, finrank V + finrank W = n+1 > n);
  (b) ∃ V (= span{bᵢ : i ≤ k}) with finrank = k+1, ∀ unit x ∈ V, λₖ ≤ ⟪Tx,x⟫.
  Weyl then: take V from (b) for S, x from (a) for T on that V:
  λₖ(S) − λₖ(T) ≤ ⟪Sx,x⟫ − ⟪Tx,x⟫ = ⟪(S−T)x,x⟫ ≤ ε by Cauchy–Schwarz.
- Operator-closeness hypothesis as `∀ x, ‖(T−S)x‖ ≤ ε‖x‖` (matches
  `MatrixOperatorNormClose` shape; no bundled norm instance commitments).
Prerequisite: quadratic form formula ⟪Tx,x⟫ = Σ λᵢ (repr x i)² + Parseval.
File: `Acharyya2025/Weyl.lean`.

### WP6 — Statement hardening pass (Concentration.lean, Bridge.lean)
- Replace vacuous structures with contentful ones (keep old names where
  possible; document the change in READMEs).
- Restate #4 with the paper's actual shape: entrywise event with failure prob
  `16·Σγᵢⱼ/(rmε²)` (Thm 1), parameterized rates instead of `1/(u+1)`.
- Restate #5/#6 with `∃ W ∈ O(d)` alignment.
- Re-derive `quench_style_uniform_embedding_error` and the
  `dkps_config_concentration_from_response_mean_hp` chain from hardened
  versions; update `DkpsQuench/AcharyyaBridge` + `Helm2025/AcharyyaBridge`
  call-sites if shapes shift.

### WP7(c) — Configuration assembly: ELEMENTARY DESIGN (2026-06-11)

The literature proofs (ALA 2022 / Tu et al.) use SVD + von Neumann trace
inequality — heavy to formalize. The following fully elementary route avoids
both. Setting: population `B` symmetric PSD rank `d`, sorted eigenvalues
`λ₁ ≥ ... ≥ λ_d ≥ α > 0 = λ_{d+1} = ...`, `λ₁ ≤ Λ`; sample `B̂` symmetric,
`‖B̂−B‖op ≤ ε ≤ α/2`. Spectral factors: `ψ̂ = Û Λ̂^{1/2}` (top-d of B̂, eigenvalues
clamped at 0), `ψ = U Λ^{1/2}` (canonical; a general Gram realization reduces to
this by WP4 rigidity). Let `Q := ÛᵀU : Matrix (Fin d) (Fin d) ℝ` (overlap
matrix), `W := polar(Q)`. Decompose:

  `ψ̂W − ψ = ÛΛ̂^{1/2}(W − Q) + Û(Λ̂^{1/2}Q − QΛ^{1/2}) + (ÛQ − U)Λ^{1/2}`

* **Term 3** (`ÛQ − U`): columns are `P̂u_l − u_l`; Frobenius² = the DK cross
  sum ≤ `4nε²/α²` (RankGap, DONE). Multiplied by `‖Λ^{1/2}‖ ≤ √Λ`.
* **Term 2** (the commutator — THE TRAP, see graveyard): entrywise
  `(√λ̂_k − √λ_l)Q_{kl} = (λ̂_k − λ_l)Q_{kl}/(√λ̂_k + √λ_l)`, and the KEY identity
  `Λ̂Q − QΛ = Ûᵀ(B̂−B)U` (from `B̂Û = ÛΛ̂`, `BU = UΛ`), so each entry is
  `⟪û_k, (B̂−B)u_l⟫/(√λ̂_k + √λ_l)`, bounded by `ε/(√(α/2) + √α)`.
  No naive splitting — the naive `‖Λ̂^{1/2}W − WΛ^{1/2}‖` bound is FALSE without
  per-eigenvalue gaps.
* **Term 1** (`W − Q`): `(QᵀQ − I)_{kl} = −Σ_{j≥d}⟪û_j,u_k⟫⟪û_j,u_l⟫` (bilinear
  Parseval), entrywise ≤ DK cross sum by Cauchy–Schwarz/AM-GM. Polar factor:
  `W := Q(QᵀQ)^{-1/2}` (spectral inverse-square-root via our eigenbasis
  machinery on `EuclideanSpace ℝ (Fin d)`); `‖Q − W‖op = max_k |1 − μ_k^{-1/2}|
  ≤ δ` for `‖QᵀQ−I‖op ≤ δ ≤ 1/2`. Multiplied by `‖Λ̂^{1/2}‖ ≤ √(Λ+ε)`.

Sub-deliverables:
* (c2) overlap-matrix lemmas: bilinear Parseval `⟪x,y⟫ = Σⱼ⟪bⱼ,x⟫⟪bⱼ,y⟫`,
  `QᵀQ − I` entrywise bound, `Λ̂Q − QΛ = Ûᵀ(B̂−B)U` identity.
* (c3) polar factor: PSD `G` with spectrum in `[1−δ, 1+δ]`, `δ ≤ 1/2` ⇒
  `G^{-1/2}` exists with `‖id − G^{-1/2}‖op ≤ δ`-ish; `W := Q∘G^{-1/2}`
  orthogonal. All via sorted-eigenbasis sums (no Mathlib CFC needed).
* (c4) assembly: the three-term decomposition above + `ConfigError ≤ √n·‖·‖F`
  + clamped-eigenvalue handling (`√λ̂_k` for `λ̂_k` possibly negative beyond
  `d`: top-d only, Weyl gives `λ̂_k ≥ α − ε ≥ α/2 > 0` for `k < d`, so no
  clamping needed in the top block).

### WP7 — Davis–Kahan (finite-dimensional, elementary route)
Target: spectral-projector perturbation. For symmetric A, Â with top-d
eigengap γ: `‖P̂ − P‖F ≤ c·‖Â − A‖F/γ`.
Elementary finite-dim proof to formalize (no resolvents): expand in the two
eigenbases; for eigenvectors `uᵢ` (A, λᵢ), `ûⱼ` (Â, λ̂ⱼ):
`⟨uᵢ, (Â−A)ûⱼ⟩ = (λ̂ⱼ − λᵢ)⟨uᵢ, ûⱼ⟩`; with Weyl (WP5) the cross terms
(i ≤ d < j or j ≤ d < i) have `|λ̂ⱼ − λᵢ| ≥ γ/2`, giving
`Σ_cross ⟨uᵢ,ûⱼ⟩² ≤ 4‖Â−A‖F²/γ²`, which is exactly `‖P̂−P‖F²/2`.
Then sin-Θ → Procrustes for the scaled embedding (needs WP4 + eigenvalue
square-root scaling + `λ_d` lower bound). This is the long pole; sub-commits:
(a) projector defs + cross-term identity, (b) the bound, (c) configuration
version. Acceptable intermediate outcome: (a)+(b) proved, (c) remains the
single cited seam with a faithful statement.

### WP8 — 2024 remaining regimes
Triangular-array Thm 4/5 statement repair (probability hypotheses per stage k);
derive from WP2 machinery + diagonal subsequence extraction. The continuous-MDS
(Lemma 2/[23] Thm 3) part stays a cited seam.

### WP9 — Trosset–Priebe raw-stress stability assessment
Likely outcome: keep as cited seam. Partial targets that are honest progress:
existence of raw-stress minimizers over centered configurations (coercivity +
compactness), and lower semicontinuity of the stress. Decide after WP2–WP7.

### WP10 — iid second-moment lemma (connects WP2's `v(r)` to the paper's γ/r)
`E‖(1/r)Σₖ Xₖ − μ‖² = trace(Σ)/r` for iid square-integrable vector RVs,
componentwise via `ProbabilityTheory.variance` + independence. Paper-agnostic →
`WellKnown`-style file.

## Milestone definition of done

- [x] WP1 committed
- [x] WP2 committed (honest content proved in Probability.lean; legacy false
      statement still carries its TODO marker pending WP6 rewiring)
- [x] WP3 committed (Gram realization proved; CMDSpectralAssumptions hardening
      pending WP6)
- [x] WP4 committed (alignment statable — and USED in WP7c4)
- [ ] WP6 committed (no false statements remain anywhere) — NEXT SESSION
- [x] WP5, WP7(a,b) committed
- [x] WP7(c) committed IN FULL (c2 Overlap, c3 PolarFactor, c4
      ConfigPerturbation) — the Davis–Kahan seam is not merely "reduced", it is
      PROVED end-to-end: exists_isometry_configError_spectralConfig_le with the
      explicit configBound constant
- [x] WP10 committed (iid second-moment algebra)
- [ ] READMEs updated to reflect non-scaffold status of finished layers
- [ ] Mathlib-candidate list extracted (WellKnown + WP5 + WP7 + WP10)

## Remaining work (next sessions)

1. WP6 statement-repair pass: re-derive / replace the 8 legacy sorries
   (Consistency.lean ×3, Concentration.lean ×2, Bridge.lean ×1,
   SpectralPipeline.lean ×2) from the new proved bridge. The matrix-world
   plumbing needed: classicalMDSMatrix → toEuclideanLin symmetric operator
   (OperatorBridge has the transport), spectralConfig as the formal CMDS
   estimator definition for the paper-facing statements, Procrustes rigidity
   (WP4) to pass from spectralConfig T to an arbitrary Gram realization ψ.
2. WP8 triangular-array regimes (2024 Thm 4/5).
3. WP9 Trosset–Priebe raw-stress stability — the one genuinely external cited
   seam that remains.
4. Paper-faithful rate bookkeeping: chain WP10 (γ/r) → WP2 → entrywise →
   cmdsEntrywiseRate → operator (n·ε) → configBound to extract the
   end-to-end Poly((n³/r)^…)-style rate and compare with the paper's.

## Progress ledger

- 2026-06-11: WP0 docs created. WP1 proof complete (uncommitted). WP2/WP3
  agents launched (new files only; pending review).
- 2026-06-11: WP0/WP1 committed; 5 false statements marked TODO(false-statement)
  (committed). Strategy pivot per user: hard bridge first, downstream repair
  deferred. Mathlib API survey done (see WP5 notes). WP4 agent launched
  (Procrustes via Finsupp.linearCombination factorization + LinearIsometry.extend,
  file Acharyya2025/Procrustes.lean). WP5 agent launched (discrete
  Courant–Fischer + Weyl, file Acharyya2025/Weyl.lean). Four agents in flight:
  WP2, WP3, WP4, WP5 — all in disjoint new files, review-then-commit
  individually on completion.
- 2026-06-11 (later): WP2 ✅ COMMITTED (Probability.lean; WP2/WP3 agents were
  killed mid-proof by a session interrupt — union-bound/squeeze half finished by
  main session). WP3 ✅ COMMITTED (GramRealization.lean; final sum-extension,
  WithLp packaging, Unitary namespace fixed by main session — note: `set`-bound
  subtype broke unification, had to inline the subtype literally; recorded in
  graveyard). WP4 ✅ COMMITTED (Procrustes.lean, agent-clean). WP5 ✅ COMMITTED
  (Weyl.lean, agent-clean on first review). OperatorBridge.lean ✅ COMMITTED
  (MatrixL2OperatorClose honest l2 operator predicate + entrywise→l2 n·ε +
  symmetry transport; resolves the sup/l2 watch-list item). WP7(a,b) agent in
  flight (DavisKahan.lean: cross-term identity + sin-Θ cross-energy bound).
  WP10 agent in flight (SecondMoment.lean: iid variance algebra).
  Hard-bridge status: 6 of 9 sorry-inventory items now have their honest core
  proved; remaining: #9 final configuration-perturbation step (WP7c), #1
  Trosset–Priebe (WP9), and the statement-repair pass (WP6/WP8).
- 2026-06-11 (later still): RankGap.lean ✅ COMMITTED (Weyl→DK-gap composition,
  4nε²/α² cross bound under rank-d + floor). WP7(c2) Overlap.lean ✅ COMMITTED
  (bilinear Parseval, overlap matrix Q, QᵀQ−I deviation, Sylvester identity
  (λ̂_k−λ_l)Q_kl = ⟪v_k,(S−T)u_l⟫, entrywise ≤ ε). WP7(c3) PolarFactor.lean ✅
  COMMITTED (near-isometry ⇒ exact isometry within 2δ; inverse-sqrt via
  eigenbasis, no CFC/SVD). WP7(c4) ConfigPerturbation agent in flight (final
  assembly: spectralConfig def + three-term telescoping split + the proven
  toolkit ⇒ ∃ isometry W, ConfigError(W∘ψ̂, ψ) ≤ explicit bound).
