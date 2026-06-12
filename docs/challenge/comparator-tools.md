# Comparator tool setup

This repository includes a challenge package for the AI-authored Mathlib-candidate
lemmas:

- `ChallengeConformance.lean` imports only Mathlib and states the challenge claims
  with `sorry`.
- `ChallengeLeaderboard.lean` imports this project and fills those claims.
- `comparator/aiq-mathlib-candidates.json` configures the comparator run.
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

This performs:

```bash
lake env lean ChallengeConformance.lean
lake env lean ChallengeLeaderboard.lean
lake build ChallengeLeaderboard
lake env comparator comparator/aiq-mathlib-candidates.json
```

using explicit `COMPARATOR_LANDRUN` and `COMPARATOR_LEAN4EXPORT` paths.

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


## Current challenge layout

The challenge files now live under `Challenge/` rather than at repository root.
The runner reads the module names from each comparator JSON file and derives the
corresponding paths automatically.

Default configs run by `scripts/run_challenge_comparator.sh`:

* `comparator/aiq-gram-rigidity.json`
* `comparator/aiq-psd-gram-realization.json`
* `comparator/aiq-spectral-perturbation.json`
* `comparator/aiq-inventory.json`

## Summary output

`scripts/run_challenge_comparator.sh` runs each requested comparator config and
prints a final summary table with pass/fail status, exit code, elapsed seconds,
and config path. The script exits nonzero if any requested config fails, but it
continues running later configs so failures can be diagnosed independently.
