#!/usr/bin/env bash
set -euo pipefail

OUTDIR="${1:-build/lean-dep-trace}"
TARGET="${2:-DkpsQuench.AcharyyaBridge.queryEfficient_nn_of_second_moment}"

python tools/lean_dep_trace/trace_deps.py . \
  --outdir "$OUTDIR" \
  --target "$TARGET"

echo "Wrote dependency trace to $OUTDIR"
