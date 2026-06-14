# Lessons learned

Effortful-debug postmortems, **newest first**. Each entry is written so its
symptom keywords match what you'd grep for from *inside* the bug. Standalone
per-incident files are preferred for focused lessons (link them from
[`index.md`](index.md)); short or cross-cutting lessons accumulate here.

Canonical entry shape: **Symptom / What it was NOT / Root cause / Fix /
Takeaway**.

---

## 2026-06-14 — Comparator `statement do not match` on conformances that build green + are axiom-clean

Full postmortem:
[`comparator-statement-export-matching-2026-06-14.md`](comparator-statement-export-matching-2026-06-14.md).

**One-line root cause:** the comparator's `lean4export` compares **universe
parameters and the instance telescope without alpha-normalizing**, so a
Mathlib-only conformance must mirror the source's `variable` context *exactly* —
dropping an unused `variable {F}` shifted `ι`'s universe from `u_4` to `u_3`
(`statement do not match`), and omitting an accumulated section instance
(`[FirstCountableTopology X]`) dropped an entry from the instance list.

**Durable rules:**
1. **"Slim a conformance" = delete other *theorems*, never the *context*.** Copy
   the source's `variable` lines verbatim, including unused type vars (they
   reserve universe slots) and every instance in declaration order.
2. **`#print <name>` first when chasing `statement do not match`** — it shows the
   leading `.{u_…}` universe signature; `#check` hides it in the body.
3. **The export is a trust boundary below `lake build`.** Build-green +
   axiom-clean + pp.all-identical is *not* export-match. Verify each leaf with a
   `#print` universe diff + `pp.all #check` type diff before paying for the
   comparator; the comparator is ground truth.
4. **Adjacent slips from the same "didn't mirror the source" family:** a dropped
   `[MeasurableSpace E] [BorelSpace E]` → `failed to synthesize`; a leaderboard
   importing the wrong ForMathlib module for a declaration → `Unknown constant`
   (a decl can live in a different file than its "natural" home —
   `eigenvalues₀_eq_zero_of_le` is in `Analysis/Matrix/Spectrum.lean`, not
   `PosDef.lean`).

### Meta-takeaway (the one that would have saved the most time)
**For any semantic property the Lean toolchain can decide, ask the toolchain —
never a textual grep, and never `lake build` alone.** Three precise tools sit one
keystroke away and each answers a different question crisply:
- `#print axioms <name>` → sorry/axiom-freeness (clean = `[propext,
  Classical.choice, Quot.sound]`). A `grep sorry` over source matched docstring
  prose (`` no `sorry` remains ``) and produced a *false* "the papers have
  sorries" alarm that nearly triggered pointless recovery work.
- `#print <name>` / `pp.all #check @<name>` → exact statement, universes,
  instances. The thing that decides comparator match.
- the comparator itself → the real export comparison.

And guard the diagnostic: a comparison over captured command output is a false
pass if the capture was empty — assert non-empty before trusting "identical."
