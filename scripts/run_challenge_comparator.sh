#!/usr/bin/env bash
# Run AIQ challenge conformance / leaderboard checks and comparator.
#
# This expects scripts/install_comparator_tools.sh to have been run first.
# Defaults mirror the setup that worked on Jon's machine.
#
# Usage:
#   bash scripts/run_challenge_comparator.sh
#   bash scripts/run_challenge_comparator.sh --fake-landrun
#   bash scripts/run_challenge_comparator.sh --config comparator/aiq-gram-rigidity.json
#   bash scripts/run_challenge_comparator.sh --config comparator/aiq-inventory.json
#
set -euo pipefail

CONFIGS=()
USE_FAKE_LANDRUN=0
ONLY_COMPARATOR=0

DEFAULT_CONFIGS=(
    "comparator/aiq-gram-rigidity.json"
    "comparator/aiq-psd-gram-realization.json"
    "comparator/aiq-spectral-perturbation.json"
    "comparator/aiq-inventory.json"
)

while [ "$#" -gt 0 ]; do
    case "$1" in
        --config)
            CONFIGS+=("$2")
            shift 2
            ;;
        --fake-landrun)
            USE_FAKE_LANDRUN=1
            shift
            ;;
        --only-comparator)
            ONLY_COMPARATOR=1
            shift
            ;;
        -h|--help)
            sed -n '1,42p' "$0"
            exit 0
            ;;
        *)
            echo "error: unknown argument: $1" >&2
            exit 1
            ;;
    esac
done

if [ "${#CONFIGS[@]}" -eq 0 ]; then
    CONFIGS=("${DEFAULT_CONFIGS[@]}")
fi

if git_root="$(git rev-parse --show-toplevel 2>/dev/null)"; then
    cd "$git_root"
fi

TOOL_ROOT="${AIQ_COMPARATOR_TOOL_ROOT:-$HOME/code/lean-tools}"
COMPARATOR_REPO="${AIQ_COMPARATOR_REPO:-$TOOL_ROOT/comparator}"
GO_BIN="$(go env GOPATH 2>/dev/null)/bin"

COMPARATOR_BIN="${AIQ_COMPARATOR_BIN:-$COMPARATOR_REPO/.lake/build/bin/comparator}"
LEAN4EXPORT_BIN="${COMPARATOR_LEAN4EXPORT:-$COMPARATOR_REPO/.lake/packages/lean4export/.lake/build/bin/lean4export}"

if [ "$USE_FAKE_LANDRUN" -eq 1 ]; then
    LANDRUN_BIN="$COMPARATOR_REPO/scripts/fake-landrun.sh"
else
    LANDRUN_BIN="${COMPARATOR_LANDRUN:-$GO_BIN/landrun}"
fi

export PATH="$GO_BIN:$COMPARATOR_REPO/.lake/build/bin:$PATH"
export COMPARATOR_LANDRUN="$LANDRUN_BIN"
export COMPARATOR_LEAN4EXPORT="$LEAN4EXPORT_BIN"

for exe in "$COMPARATOR_BIN" "$COMPARATOR_LEAN4EXPORT" "$COMPARATOR_LANDRUN"; do
    if [ ! -x "$exe" ]; then
        echo "error: required executable missing: $exe" >&2
        echo "hint: run: bash scripts/install_comparator_tools.sh" >&2
        exit 1
    fi
done

module_to_path() {
    python3 - "$1" <<'PY'
import sys
print(sys.argv[1].replace('.', '/') + '.lean')
PY
}

json_field() {
    python3 - "$1" "$2" <<'PY'
import json
import sys
with open(sys.argv[1], encoding='utf8') as f:
    data = json.load(f)
print(data[sys.argv[2]])
PY
}

run_one_config() {
    local CONFIG="$1"
    if [ ! -f "$CONFIG" ]; then
        echo "error: comparator config not found: $CONFIG" >&2
        exit 1
    fi

    local CHALLENGE_MODULE SOLUTION_MODULE CHALLENGE_PATH SOLUTION_PATH
    CHALLENGE_MODULE="$(json_field "$CONFIG" challenge_module)"
    SOLUTION_MODULE="$(json_field "$CONFIG" solution_module)"
    CHALLENGE_PATH="$(module_to_path "$CHALLENGE_MODULE")"
    SOLUTION_PATH="$(module_to_path "$SOLUTION_MODULE")"

    echo
    echo "======================================================================"
    echo "Comparator config: $CONFIG"
    echo "Challenge module:  $CHALLENGE_MODULE"
    echo "Solution module:   $SOLUTION_MODULE"
    echo "======================================================================"

    if [ "$ONLY_COMPARATOR" -eq 0 ]; then
        echo "Checking $CHALLENGE_PATH"
        lake env lean "$CHALLENGE_PATH"

        echo "Checking $SOLUTION_PATH"
        lake env lean "$SOLUTION_PATH"

        echo "Building $SOLUTION_MODULE"
        lake build "$SOLUTION_MODULE"
    fi

    echo "Running comparator with config: $CONFIG"
    echo "COMPARATOR_LANDRUN=$COMPARATOR_LANDRUN"
    echo "COMPARATOR_LEAN4EXPORT=$COMPARATOR_LEAN4EXPORT"
    lake env "$COMPARATOR_BIN" "$CONFIG"
}

for CONFIG in "${CONFIGS[@]}"; do
    run_one_config "$CONFIG"
done
