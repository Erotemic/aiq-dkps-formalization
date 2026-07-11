/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import ForMathlib.Analysis.InnerProductSpace.DavisKahan.Experimental.Foundation.RealSpectralBridge

/-!
# Hilbert-space complexification roadmap

This module is a sequestered foundation seam for a future reusable
complexification API.  The intended development includes:

* a complex Hilbert space associated to a real Hilbert space;
* an isometric real-linear embedding;
* extension of bounded real operators;
* preservation of composition, symmetry, adjoints, and operator norms;
* compatibility with invariant subspaces and orthogonal projections;
* comparison of real spectra with spectra of complexified operators.

The direct Rayleigh-shift route in `RealSpectralBridge` should be attempted
before this larger foundation is made a dependency of Davis--Kahan theory.
-/
