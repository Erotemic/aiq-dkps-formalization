#!/usr/bin/env bash
set -euo pipefail

case "${1:-supported}" in
    supported)
        lake build ForMathlib.Analysis.InnerProductSpace.DavisKahan.All
        ;;
    experimental)
        lake build ForMathlib.Analysis.InnerProductSpace.DavisKahan.Experimental.All
        ;;
    compatibility)
        lake build ForMathlib.Analysis.InnerProductSpace.DavisKahanExt.All
        lake build ForMathlib.Analysis.InnerProductSpace.DavisKahanExt.ExperimentalAll
        ;;
    all)
        lake build ForMathlib.Analysis.InnerProductSpace.DavisKahan.All
        lake build ForMathlib.Analysis.InnerProductSpace.DavisKahan.Experimental.All
        ;;
    *)
        echo "usage: $0 [supported|experimental|compatibility|all]" >&2
        exit 2
        ;;
esac
