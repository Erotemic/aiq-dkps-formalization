/-
Root module for the `ForMathlib` staging library.

Paper-agnostic results restated in Mathlib idiom, one file per proposed
Mathlib destination path.  See `ForMathlib/README.md` for the contribution
workflow and `planning/mathlib-candidates.md` for the ranked candidate list.
-/

import ForMathlib.Analysis.InnerProductSpace.CourantFischer
import ForMathlib.Analysis.InnerProductSpace.DavisKahan
import ForMathlib.Analysis.InnerProductSpace.GramMatrix
import ForMathlib.Analysis.InnerProductSpace.NearIsometry
import ForMathlib.Analysis.InnerProductSpace.Spectrum
import ForMathlib.Analysis.Matrix.EntrywiseOpNorm
import ForMathlib.Analysis.Matrix.Spectrum
import ForMathlib.LinearAlgebra.Matrix.PosDef
import ForMathlib.MeasureTheory.CfcMeasurable
import ForMathlib.MeasureTheory.CompactExists
import ForMathlib.MeasureTheory.Function.ConvergenceInMeasure
import ForMathlib.MeasureTheory.Measure.Typeclasses.Probability
import ForMathlib.Probability.Moments.SampleMean
import ForMathlib.Probability.Moments.Variance
import ForMathlib.Topology.ApproxMinimizer
