# Searching DKPS-formalization engineering memory

Use this when you hit a confusing Lean/comparator failure, plan a challenge or
upstream refactor, or see an error that feels familiar.

## Choose the right corpus

| Situation | Search |
|---|---|
| A check failed that the build did *not* (comparator, `#print axioms`, kernel) | `dev/journals/` first |
| Confusing Lean error / elaboration / instance / universe symptom | `dev/journals/` |
| About to restate a theorem, slim a conformance, pick a leaf, minimize imports | `dev/benchmark-candidates/` |
| About to polish a proof for upstream (fold tactic traces into `simp`-friendly lemmas) | `dev/mathlib-proof-polishing.md` |
| Choosing/relating a Mathlib lemma, checking a gap, naming | both |
| Module-system (`public import`, `@[expose]`), import direction/cycles | both |
| Provenance / fork↔staging sync / AI-authorship stripping | both |

## Common searches

```bash
# Comparator statement-match / export invariants (the project's signature trap)
rg -n "statement do not match|universe|lean4export|\.\{u_|variable|instance.*order|conformance|leaf|sink" dev/

# Lean elaboration / proof-engineering symptoms
rg -n "motive is not type correct|failed to synthesize|defeq|definitional|sorryAx|#print axioms|sorry" dev/

# Mathlib API / duplication / naming
rg -n "already (exists|in Mathlib)|posSemidef|gram|eigenvalues|rank|duplicat|naming|dot.notation" dev/

# Module system / imports
rg -n "public import|@\[expose\]|import direction|upstream|downstream|cycle|minimal import|shake" dev/

# Process / provenance
rg -n "provenance|claude-|backport|staging|fork|disclosure|grep.*comment|false.positive" dev/
```

## Search protocol

1. Search with the **symptom words** first (the exact error / failure text).
2. Search with the **subsystem** words second (comparator, conformance, axioms,
   instance, universe, Mathlib lemma name).
3. Search with the likely **failure class** third (export-signature match,
   defeq, leaf selection, import direction).
4. Read only the matching entries plus their linked benchmark questions or
   journals. **Do not load the whole corpus** — it is a lookup memory, not a
   cold-start essay.
5. When a lesson becomes durable project *policy*, promote it into the relevant
   `docs/` doc (`docs/challenge/`, `docs/planning/pr-decisions.md`) and leave the
   postmortem here.

## The ground-truth checks (run these, don't guess)

The whole reason this domain makes good benchmarks is that the checks are
crisp. When verifying a fix, prefer these over reasoning:

```bash
# Does the proof tree depend only on permitted axioms (no sorryAx)?
lake env lean Challenge/<Family>/<Name>/Leaderboard.lean   # runs #print axioms

# Do conformance and solution exports actually match? (the comparator is truth)
bash scripts/run_challenge_comparator.sh --config comparator/<config>.json

# Local proxy when the comparator tools aren't installed: compare the exact
# universe signature and full type of conformance vs solution.
#   #print <FullyQualified.name>            -> shows .{u_1,…} universe params
#   set_option pp.all true in #check @<name>  -> full type incl. instances/universes
```
