/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import ForMathlib.Analysis.InnerProductSpace.DavisKahanExt.Basic
import ForMathlib.Analysis.InnerProductSpace.DavisKahanExt.SpectralProjection
import ForMathlib.Analysis.InnerProductSpace.DavisKahanExt.Resolvent
import ForMathlib.Analysis.InnerProductSpace.DavisKahanExt.OperatorAngle
import ForMathlib.Analysis.InnerProductSpace.DavisKahanExt.SymmetricIdeals
import ForMathlib.Analysis.InnerProductSpace.DavisKahanExt.Sylvester
import ForMathlib.Analysis.InnerProductSpace.DavisKahanExt.SinTheta
import ForMathlib.Analysis.InnerProductSpace.DavisKahanExt.ComplexSpectral
import ForMathlib.Analysis.InnerProductSpace.DavisKahanExt.DoubleAngle
import ForMathlib.Analysis.InnerProductSpace.DavisKahanExt.Continuation
import ForMathlib.Analysis.InnerProductSpace.DavisKahanExt.GraphSubspace
import ForMathlib.Analysis.InnerProductSpace.DavisKahanExt.Riccati
import ForMathlib.Analysis.InnerProductSpace.DavisKahanExt.OffDiagonal
import ForMathlib.Analysis.InnerProductSpace.DavisKahanExt.DirectRotation
import ForMathlib.Analysis.InnerProductSpace.DavisKahanExt.Unbounded
import ForMathlib.Analysis.InnerProductSpace.DavisKahanExt.UnboundedRiccati
import ForMathlib.Analysis.InnerProductSpace.DavisKahanExt.Forms
import ForMathlib.Analysis.InnerProductSpace.DavisKahanExt.CompactAndSingular
import ForMathlib.Analysis.InnerProductSpace.DavisKahanExt.Sharpness

/-!
# Infinite-dimensional Davis--Kahan extension scaffold

This umbrella module intentionally lives inside the new `DavisKahanExt`
directory.  The overlay does not modify `ForMathlib.lean` or any existing module.
Build the dependency graph explicitly with:

`lake build ForMathlib.Analysis.InnerProductSpace.DavisKahanExt.All`

A direct `lake env lean .../All.lean` invocation expects the imported local
modules to have already been compiled to `.olean` files; it is not the initial
build command.  See `DavisKahanExt/PROOF_PLAN.md` for the shared-core and
finite-specialization roadmap.
-/
