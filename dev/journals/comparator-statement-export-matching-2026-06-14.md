# `statement do not match`: conformances that build green but fail the comparator's export check

**Date:** 2026-06-14. **Context:** restructured the whole `Challenge/` layer into
`MathlibCandidate/` + `MathlibPending/`, regenerating ~13 Mathlib-only
`Conformance.lean` stubs (each restates a `ForMathlib` theorem as `sorry`) plus
their `Leaderboard.lean` proofs. Everything built; every leaf's `#print axioms`
was clean. Then the real comparator (real `landrun`) rejected statements.

## Symptom

```
uncaught exception: Challenge and solution theorem statement do not match:
'ForMathlib.Matrix.gram_eq_gram_iff_exists_linearIsometryEquiv_map_eq'
```

…for a conformance that (a) `lake build`s green, (b) has clean `#print axioms`,
and (c) whose `set_option pp.all true in #check @…` *looked* identical to the
solution's. Same failure later on `continuous_iInf_of_isCompact` (Berge).

## What it was NOT (and a diagnostic that lied)

- **NOT a type-body difference** — the propositions were genuinely equal.
- A first diagnostic *said* "IDENTICAL" and was **wrong**: it diffed two `lake env
  lean … #check` outputs captured to temp files, but both captures were empty
  (the `#check` output wasn't where I grepped), and **two empty files diff as
  identical**. Lesson inside the lesson: a comparison over possibly-empty output
  is a false pass; assert the captured output is non-empty first.

## Root cause

The comparator exports both declarations with `lean4export` and compares them
**without alpha-normalizing universe parameters or the instance telescope.** Two
classes of mismatch, both from *not mirroring the source's `variable` context*:

1. **Universe slot (Gram).** The source section is
   `variable {𝕜 E F ι : Type*} …` where `F` is unused by this theorem. The
   "tidy" conformance wrote `variable {𝕜 E ι}` — dropping `F`. But universe
   params are positional over *declared* type variables, so the source numbers
   `ι` as `u_4` (F reserves `u_3`) while the slimmed conformance numbers `ι` as
   `u_3`:

   ```
   solution:     …map_eq.{u_1, u_2, u_4}
   conformance:  …map_eq.{u_1, u_2, u_3}
   ```

   `#print <name>` (not `#check`) shows this leading `.{…}` signature plainly.

2. **Instance slot (Berge).** `continuous_iInf_of_isCompact`'s solution carries
   an accumulated section instance `[FirstCountableTopology X]` (added by a
   `variable` line before the theorem, used by the proof). The conformance, with
   a `sorry` proof, did *not* auto-include it, so its instance telescope was
   missing one entry. `pp.all #check` diff showed the extra
   `[@FirstCountableTopology X inst_1]` on the solution side.

Two adjacent slips surfaced in the same pass (not export-matching, but same
"didn't mirror the source" family):

3. **`failed to synthesize` (SampleMeanMSE).** Dropped `[MeasurableSpace E]
   [BorelSpace E]` from the source's E-variable line → the Bochner integral
   couldn't elaborate.
4. **`Unknown constant` (RankPsd leaderboard).** `eigenvalues₀_eq_zero_of_le`
   lives in `ForMathlib/Analysis/Matrix/Spectrum.lean`, not `…/PosDef.lean`; the
   leaderboard imported the wrong module for that declaration.

## Fix

Mirror the source's variable context **exactly** in each conformance:
- Gram: restore the unused `F` (with its instances) → universe sig becomes
  `.{u_1,u_2,u_4}`, matches. Comparator **PASS** (confirmed, real landrun).
- Berge: add `[FirstCountableTopology X]` explicitly, *before*
  `[FirstCountableTopology P]`, matching declaration order.
- SampleMeanMSE: restore `[MeasurableSpace E] [BorelSpace E]`.
- RankPsd leaderboard: also `import ForMathlib.Analysis.Matrix.Spectrum`.

Then verify *before* paying for the comparator: for every leaf, diff (a) the
`#print` universe signature and (b) the `pp.all #check` full type, conformance
vs solution. All 21 leaves matched after the fixes.

## Takeaway

- **The comparator/export is a trust boundary *below* `lake build`.** "Builds +
  axiom-clean + pp.all-looks-right" is not "matches." A Mathlib-only conformance
  must reproduce the source's *entire binder telescope* — type variables
  (including unused ones that reserve universe slots) and the full instance list
  in declaration order — because the exporter is name/position-sensitive and does
  not alpha-normalize. Treat "slim the conformance" as "copy the source's
  `variable` lines verbatim, then delete only the *other theorems*," never the
  context.
- **`#print <name>` shows the universe `.{…}` signature; `#check` buries it.**
  When chasing `statement do not match`, `#print` both sides and compare the
  leading universe list first — it's the cheapest discriminator.
- **Verify with the precise tool, and guard the diagnostic.** `#print axioms`
  decides sorry/axiom-freeness; a `pp.all` type diff (with a non-empty-output
  assertion) is a good local proxy for the comparator; the comparator is ground
  truth. Don't trust a textual grep — including one over `sorry`, which happily
  matches docstring prose like `` no `sorry` remains `` and produced a bogus
  "the papers have sorries" alarm earlier in the same session.

See also: benchmark questions Q1/Q2/Q3 in
[`../benchmark-candidates/lean-questions.md`](../benchmark-candidates/lean-questions.md).
