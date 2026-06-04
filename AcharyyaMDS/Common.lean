/- Compatibility shim for older `AcharyyaMDS.Common` imports. -/

import Acharyya2024.Common

open Filter MeasureTheory
open scoped BigOperators Topology

namespace AcharyyaMDS

abbrev Rvec (d : Nat) := Acharyya2024.Rvec d
abbrev Mat (m p : Nat) := Acharyya2024.Mat m p
abbrev DisMat (n : Nat) := Acharyya2024.DisMat n
abbrev Config (n d : Nat) := Acharyya2024.Config n d
abbrev Subseq (u : Nat → Nat) : Prop := Acharyya2024.Subseq u

noncomputable abbrev frobSq {n : Nat} (A : DisMat n) : Real := Acharyya2024.frobSq A
noncomputable abbrev frob {n : Nat} (A : DisMat n) : Real := Acharyya2024.frob A
noncomputable abbrev frobSub {n : Nat} (A B : DisMat n) : Real := Acharyya2024.frobSub A B
noncomputable abbrev rawStress (n d : Nat) (Δ : DisMat n) (z : Config n d) : Real :=
  Acharyya2024.rawStress n d Δ z
abbrev MDS (n d : Nat) (Δ : DisMat n) : Set (Config n d) := Acharyya2024.MDS n d Δ
noncomputable abbrev pairDist {n d : Nat} (z : Config n d) (i j : Fin n) : Real :=
  Acharyya2024.pairDist z i j
noncomputable abbrev pairDistErr {n d : Nat} (z z' : Config n d) (i j : Fin n) : Real :=
  Acharyya2024.pairDistErr z z' i j
abbrev ConvergesInProbability {Ω α : Type} [MeasurableSpace Ω] [PseudoMetricSpace α]
    (P : Measure Ω) (X : Nat → Ω → α) (x : α) : Prop :=
  Acharyya2024.ConvergesInProbability P X x
abbrev ConvergesInProbabilityZero {Ω α : Type} [MeasurableSpace Ω] [PseudoMetricSpace α]
    [Zero α] (P : Measure Ω) (X : Nat → Ω → α) : Prop :=
  Acharyya2024.ConvergesInProbabilityZero P X
abbrev HighProbAtTop {Ω : Type} [MeasurableSpace Ω]
    (P : Nat → Measure Ω) (E : Nat → Set Ω) : Prop :=
  Acharyya2024.HighProbAtTop P E
abbrev ConfigError {n d : Nat} (ψhat ψ : Config n d) : Real := Acharyya2024.ConfigError ψhat ψ

end AcharyyaMDS
