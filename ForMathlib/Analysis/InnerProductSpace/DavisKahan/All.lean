/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import ForMathlib.Analysis.InnerProductSpace.DavisKahan.Basic
import ForMathlib.Analysis.InnerProductSpace.DavisKahan.SinTheta
import ForMathlib.Analysis.InnerProductSpace.DavisKahan.Projector
import ForMathlib.Analysis.InnerProductSpace.DavisKahan.ReflectionDefect
import ForMathlib.Analysis.InnerProductSpace.DavisKahan.Spectral.Complex

/-!
# Supported bounded Davis--Kahan theory

The primary API is scalar-generic over `RCLike`: reducing subspaces, coercive
Sylvester estimates, directed `sin Θ`, sharp projector geometry, and reflection
defects.  The complex spectral module is a leaf specialization that converts
actual restriction spectra into the generic form-bound hypotheses.

Foundational and literature-facing open developments are intentionally absent
from this umbrella; use `DavisKahan.Experimental.All` to compile them.
-/
