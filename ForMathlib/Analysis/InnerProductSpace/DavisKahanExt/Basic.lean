/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import ForMathlib.Analysis.InnerProductSpace.DavisKahan.Basic
import ForMathlib.Analysis.InnerProductSpace.DavisKahan.Experimental.Foundation.AbstractSpectrum

/-!
# Compatibility layer for the former `DavisKahanExt.Basic`

Supported declarations now live in general `ForMathlib` modules and in
`ForMathlib.DavisKahan`.  Provisional spectral interfaces live under
`DavisKahan.Experimental.Foundation`.  This module retains the old names so
existing literature scaffolds continue to compile during migration.
-/

namespace ForMathlib
namespace DavisKahanExt

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

abbrev BoundedOperator (𝕜 : Type*) (E : Type*) [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] := E →L[𝕜] E
abbrev IsSelfAdjointOperator (A : E →L[𝕜] E) := DavisKahan.IsSelfAdjointOperator A
abbrev Reduces (A : E →L[𝕜] E) (U : Submodule 𝕜 E) := DavisKahan.Reduces A U
noncomputable abbrev projection (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :=
  DavisKahan.projection U
noncomputable abbrev complementaryProjection (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] := DavisKahan.complementaryProjection U
noncomputable abbrev diagonalPart (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (A : E →L[𝕜] E) := DavisKahan.diagonalPart U A
noncomputable abbrev offDiagonalPart (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (A : E →L[𝕜] E) := DavisKahan.offDiagonalPart U A
abbrev IsOffDiagonal (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (A : E →L[𝕜] E) := U.IsOffDiagonal A
abbrev IsOrthogonalProjection (P : E →L[𝕜] E) :=
  DavisKahan.Experimental.Foundation.IsOrthogonalProjection P
abbrev IsUnitaryOperator (W : E →L[𝕜] E) :=
  DavisKahan.Experimental.Foundation.IsUnitaryOperator W
abbrev IsOffDiagonalRelativeToProjection (P H : E →L[𝕜] E) :=
  DavisKahan.Experimental.Foundation.IsOffDiagonalRelativeToProjection P H
noncomputable abbrev realSpectrum (A : E →L[𝕜] E) :=
  DavisKahan.Experimental.Foundation.realSpectrum A
noncomputable abbrev restrictedSpectrum (A : E →L[𝕜] E) (U : Submodule 𝕜 E) :=
  DavisKahan.Experimental.Foundation.restrictedSpectrum A U
abbrev SpectrumIn (A : E →L[𝕜] E) (U : Submodule 𝕜 E) (s : Set ℝ) :=
  DavisKahan.Experimental.Foundation.SpectrumIn A U s
abbrev BoundedOnSpectrum (A : E →L[𝕜] E) (f : ℝ → ℝ) :=
  DavisKahan.Experimental.Foundation.BoundedOnSpectrum A f
noncomputable abbrev spectralDistance (s t : Set ℝ) :=
  DavisKahan.Experimental.Foundation.spectralDistance s t
abbrev SpectraSeparated (A : E →L[𝕜] E) (U : Submodule 𝕜 E)
    (B : F →L[𝕜] F) (V : Submodule 𝕜 F) (d : ℝ) :=
  DavisKahan.Experimental.Foundation.SpectraSeparated A U B V d
abbrev HybridGap (A B : E →L[𝕜] E) (U V : Submodule 𝕜 E) (d : ℝ) :=
  DavisKahan.Experimental.Foundation.HybridGap A B U V d
abbrev InternalGap (A : E →L[𝕜] E) (U : Submodule 𝕜 E) (d : ℝ) :=
  DavisKahan.Experimental.Foundation.InternalGap A U d
abbrev OrderedSpectraSeparated (A : E →L[𝕜] E) (U : Submodule 𝕜 E)
    (B : F →L[𝕜] F) (V : Submodule 𝕜 F) (d : ℝ) :=
  DavisKahan.Experimental.Foundation.OrderedSpectraSeparated A U B V d
abbrev IntervalExteriorSeparated (A : E →L[𝕜] E) (U : Submodule 𝕜 E)
    (B : F →L[𝕜] F) (V : Submodule 𝕜 F) (left right d : ℝ) :=
  DavisKahan.Experimental.Foundation.IntervalExteriorSeparated A U B V left right d
abbrev FiniteGapConfiguration (A : E →L[𝕜] E) (U : Submodule 𝕜 E) (d : ℝ) :=
  DavisKahan.Experimental.Foundation.FiniteGapConfiguration A U d
abbrev OrderedInternalGap (A : E →L[𝕜] E) (U : Submodule 𝕜 E) (d : ℝ) :=
  DavisKahan.Experimental.Foundation.OrderedInternalGap A U d
noncomputable abbrev subspaceGap (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] := DavisKahan.subspaceGap U V
noncomputable abbrev directedGap (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] := DavisKahan.directedGap U V
abbrev IsAcute (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] := DavisKahan.IsAcute U V
abbrev IsQuarterAcute (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] := DavisKahan.IsQuarterAcute U V
abbrev IsometricEmbedding (X : F →L[𝕜] E) := DavisKahan.IsometricEmbedding X
abbrev residual (A : E →L[𝕜] E) (X : F →L[𝕜] E) (M : F →L[𝕜] F) :=
  DavisKahan.residual A X M
noncomputable abbrev sinThetaEmbedding (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →L[𝕜] E) := DavisKahan.sinThetaEmbedding U X
noncomputable abbrev reflectionOperator (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] := DavisKahan.reflectionOperator U
noncomputable abbrev sinTwoThetaEmbedding (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →L[𝕜] E) :=
  DavisKahan.Experimental.Foundation.sinTwoThetaEmbedding U X

theorem reduces_orthogonalComplement {A : E →L[𝕜] E}
    (hA : IsSelfAdjointOperator A) {U : Submodule 𝕜 E}
    (hU : ∀ x ∈ U, A x ∈ U) : Reduces A U :=
  DavisKahan.reduces_orthogonalComplement hA hU

theorem projection_comp_comm_of_reduces
    (A : E →L[𝕜] E) (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (hU : Reduces A U) :
    projection U ∘L A = A ∘L projection U :=
  DavisKahan.projection_comp_comm_of_reduces A U hU

theorem projection_apply_comm_of_reduces
    (A : E →L[𝕜] E) (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (hU : Reduces A U) (x : E) :
    projection U (A x) = A (projection U x) :=
  DavisKahan.projection_apply_comm_of_reduces A U hU x

theorem reflectionOperator_apply (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (x : E) :
    reflectionOperator U x = (2 : 𝕜) • projection U x - x :=
  U.reflectionOperator_apply x

theorem reflectionOperator_involutive (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] :
    reflectionOperator U ∘L reflectionOperator U = ContinuousLinearMap.id 𝕜 E :=
  DavisKahan.reflectionOperator_involutive U

theorem reflectionOperator_isUnitary (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] : IsUnitaryOperator (reflectionOperator U) :=
  ⟨U.reflectionOperator_norm_map, U.reflectionOperator_surjective⟩

theorem norm_reflectionOperator_le_one (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] : ‖reflectionOperator U‖ ≤ 1 :=
  DavisKahan.norm_reflectionOperator_le_one U

theorem reflectionOperator_comm_of_reduces
    (A : E →L[𝕜] E) (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (hU : Reduces A U) :
    reflectionOperator U ∘L A = A ∘L reflectionOperator U :=
  DavisKahan.reflectionOperator_comm_of_reduces A U hU

theorem complementaryProjection_apply (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (x : E) :
    complementaryProjection U x = x - projection U x :=
  U.starProjection_orthogonal_apply x

theorem two_smul_diagonalPart_eq_add_reflectionConjugate
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] (A : E →L[𝕜] E) :
    (2 : 𝕜) • diagonalPart U A =
      A + reflectionOperator U ∘L A ∘L reflectionOperator U :=
  U.two_smul_diagonalPart_eq_add_reflectionConjugate A

theorem two_smul_offDiagonalPart_eq_sub_reflectionConjugate
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] (A : E →L[𝕜] E) :
    (2 : 𝕜) • offDiagonalPart U A =
      A - reflectionOperator U ∘L A ∘L reflectionOperator U :=
  U.two_smul_offDiagonalPart_eq_sub_reflectionConjugate A

theorem subspaceGap_comm (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    subspaceGap U V = subspaceGap V U := U.projectionGap_comm V

theorem directedGap_le_subspaceGap (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    directedGap U V ≤ subspaceGap U V := U.directedProjectionGap_le_projectionGap V

end DavisKahanExt
end ForMathlib
