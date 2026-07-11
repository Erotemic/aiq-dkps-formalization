/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/

import ForMathlib.Analysis.InnerProductSpace.DavisKahanTheory.Basic
import ForMathlib.Analysis.InnerProductSpace.DavisKahanTheory.RectangularUINorm
import ForMathlib.Analysis.InnerProductSpace.DavisKahanTheory.Residual
import ForMathlib.Analysis.InnerProductSpace.DavisKahanTheory.Sylvester
import ForMathlib.Analysis.InnerProductSpace.DavisKahanTheory.SinTheta
import ForMathlib.Analysis.InnerProductSpace.DavisKahanTheory.TanTheta
import ForMathlib.Analysis.InnerProductSpace.DavisKahanTheory.SinTwoTheta
import ForMathlib.Analysis.InnerProductSpace.DavisKahanTheory.TanTwoTheta
import ForMathlib.Analysis.InnerProductSpace.DavisKahanTheory.Generalized
import ForMathlib.Analysis.InnerProductSpace.DavisKahanTheory.DirectRotation
import ForMathlib.Analysis.InnerProductSpace.DavisKahanTheory.Davis1963
import ForMathlib.Analysis.InnerProductSpace.DavisKahanTheory.Sharpness
import ForMathlib.Analysis.InnerProductSpace.DavisKahanTheory.Statistics
import ForMathlib.Analysis.InnerProductSpace.DavisKahanTheory.SingularSubspace

/-!
# Complete finite-dimensional Davis--Kahan theory scaffold

Umbrella import for the literature-indexed roadmap under
`ForMathlib.Analysis.InnerProductSpace.DavisKahanTheory`.

The declarations intentionally contain `sorry`. Their proof architecture is
recorded in
`ForMathlib/prose/Davis-Kahan-1970-part-III-core-arguments.tex` and
`ForMathlib/prose/Davis-1963-core-arguments.tex`.
-/
