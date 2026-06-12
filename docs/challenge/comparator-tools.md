# Comparator tool setup

This repository includes challenge packages for AI-authored Mathlib-candidate
lemmas:

- `ChallengeConformance.lean` / `ChallengeLeaderboard.lean` provide a four-claim
  headline sampler.
- `ChallengeInventoryConformance.lean` / `ChallengeInventoryLeaderboard.lean`
  provide a broader inventory of the current `ForMathlib` theorem surface.
- `comparator/*.json` configures comparator runs.
- `formalization.yaml` records provenance and AI usage notes.

The comparator check needs external tools: `landrun`, `comparator`, and
`lean4export`. The working setup used `landrun` from the `main` branch rather
than the latest released tag.

## Install tools

From the repository root:

```bash
bash scripts/install_comparator_tools.sh
```

By default this uses:

```text
~/code/lean-tools/comparator
$(go env GOPATH)/bin/landrun
```

Override the tool root if desired:

```bash
AIQ_COMPARATOR_TOOL_ROOT=/tmp/lean-tools bash scripts/install_comparator_tools.sh
```

## Run checks

From the repository root:

```bash
bash scripts/run_challenge_comparator.sh
```

This performs Lean checks, builds the solution modules, and runs comparator for
both comparator configs:

```text
comparator/aiq-mathlib-candidates.json
comparator/aiq-mathlib-inventory.json
```

Run a single config with:

```bash
bash scripts/run_challenge_comparator.sh --config comparator/aiq-mathlib-candidates.json
bash scripts/run_challenge_comparator.sh --config comparator/aiq-mathlib-inventory.json
```

## Development fallback

If real `landrun` fails locally with a sandbox permission error, the wiring can
be checked with comparator's fake landrun wrapper:

```bash
bash scripts/run_challenge_comparator.sh --fake-landrun
```

A fake-landrun pass is useful for development, but it is not the hardened
sandboxed check. The real check should end with:

```text
Lean default kernel accepts the solution
Your solution is okay!
```
