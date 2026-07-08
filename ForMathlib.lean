/-
Root module for the `ForMathlib` staging library.

Paper-agnostic results restated in Mathlib idiom, one file per proposed
Mathlib destination path.  See `ForMathlib/README.md` for the contribution
workflow and `planning/mathlib-candidates.md` for the ranked candidate list.
-/

import ForMathlib.Analysis.InnerProductSpace.AlignedBasis
import ForMathlib.Analysis.InnerProductSpace.CourantFischer
import ForMathlib.Analysis.InnerProductSpace.DavisKahan
import ForMathlib.Analysis.InnerProductSpace.EigenvalueChange
import ForMathlib.Analysis.InnerProductSpace.GramMatrix
import ForMathlib.Analysis.InnerProductSpace.HoffmanWielandt
import ForMathlib.Analysis.InnerProductSpace.IntertwiningUnitary
import ForMathlib.Analysis.InnerProductSpace.NearIsometry
import ForMathlib.Analysis.InnerProductSpace.PartialIsometry
import ForMathlib.Analysis.InnerProductSpace.PolarDecomposition
import ForMathlib.Analysis.InnerProductSpace.PositiveSqrt
import ForMathlib.Analysis.InnerProductSpace.RotationBound
import ForMathlib.Analysis.InnerProductSpace.SchurHorn
import ForMathlib.Analysis.InnerProductSpace.SingularSubspace
import ForMathlib.Analysis.InnerProductSpace.Spectrum
import ForMathlib.Analysis.InnerProductSpace.SylvesterBound
import ForMathlib.Analysis.InnerProductSpace.YuWangSamworth
import ForMathlib.Analysis.Matrix.EntrywiseOpNorm
import ForMathlib.Analysis.Matrix.SpectralFunctionMeasurable
import ForMathlib.Analysis.Matrix.EntrywiseEigenvalue
import ForMathlib.Analysis.Matrix.Spectrum
import ForMathlib.Analysis.Normed.Operator.LinearIsometry
import ForMathlib.LinearAlgebra.Matrix.PosDef
import ForMathlib.LinearAlgebra.Matrix.RankFactorization
import ForMathlib.MeasureTheory.CfcMeasurable
import ForMathlib.MeasureTheory.CompactExists
import ForMathlib.MeasureTheory.Function.ConvergenceInMeasure
import ForMathlib.MeasureTheory.Measure.Typeclasses.Probability
import ForMathlib.Probability.Moments.MatrixConcentration
import ForMathlib.Probability.Moments.SampleCovariance
import ForMathlib.Probability.Moments.SampleMean
import ForMathlib.Probability.Moments.Variance
import ForMathlib.Topology.ApproxMinimizer
import ForMathlib.Topology.Berge
