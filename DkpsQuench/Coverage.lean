/-
DKPS / Quench reference-sample coverage.

This module derives the paper-facing uniform reference-coverage event from a
finite-net argument.  The true perspective image is assumed totally bounded,
every positive perspective ball has positive model probability, and each
finite reference sample has the iid joint law.  A positive-mass ball is then
missed with geometrically decaying probability; a finite net upgrades those
pointwise hit events to uniform coverage.
-/
import DkpsQuench.Internal
import Mathlib
set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise Topology
open Filter MeasureTheory

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

universe u v w

variable {Q : Type u} [DecidableEq Q]
variable {X : Type v} [MeasurableSpace X]
variable {d : ℕ}
variable {Ω : Type w} [MeasurableSpace Ω]

/-- Models whose true perspectives lie in the open radius-`ρ` ball centered at
`ψ f`. -/
def perspectiveBall (ψ : Model Q X → Vec d) (f : Model Q X) (ρ : ℝ) :
    Set (Model Q X) :=
  {g | ‖ψ g - ψ f‖ < ρ}

/-- A finite collection of model centers whose perspective balls cover every
model perspective. -/
def PerspectiveFiniteCover (ψ : Model Q X → Vec d) (ρ : ℝ)
    (centers : Finset (Model Q X)) : Prop :=
  ∀ f, ∃ g ∈ centers, ‖ψ g - ψ f‖ < ρ

/-- Total boundedness stated directly in the form needed by the coverage
argument: every positive scale admits a finite perspective cover whose centers
are themselves models. -/
def PerspectiveTotallyBounded (ψ : Model Q X → Vec d) : Prop :=
  ∀ ρ > 0, ∃ centers : Finset (Model Q X),
    PerspectiveFiniteCover ψ ρ centers

/-- Compactness of the perspective image supplies finite perspective covers. -/
theorem perspectiveTotallyBounded_of_isCompact_range
    (ψ : Model Q X → Vec d) (hcompact : IsCompact (Set.range ψ)) :
    PerspectiveTotallyBounded ψ := by
  classical
  intro ρ hρ
  have hopen : ∀ f : Model Q X, IsOpen (Metric.ball (ψ f) ρ) :=
    fun _ => Metric.isOpen_ball
  have hcover : Set.range ψ ⊆ ⋃ f : Model Q X, Metric.ball (ψ f) ρ := by
    rintro z ⟨f, rfl⟩
    exact Set.mem_iUnion.2 ⟨f, Metric.mem_ball_self hρ⟩
  obtain ⟨centers, hcenters⟩ :=
    hcompact.elim_finite_subcover
      (fun f : Model Q X => Metric.ball (ψ f) ρ) hopen hcover
  refine ⟨centers, ?_⟩
  intro f
  have hf := hcenters (show ψ f ∈ Set.range ψ from ⟨f, rfl⟩)
  simp only [Set.mem_iUnion] at hf
  obtain ⟨g, hgmem, hball⟩ := hf
  refine ⟨g, hgmem, ?_⟩
  simpa [dist_eq_norm, norm_sub_rev] using (Metric.mem_ball.mp hball)

/-- A perspective map that factors through a finite configuration has compact
range automatically. -/
theorem isCompact_range_of_finite_factor
    {n : ℕ} (indexOf : Model Q X → Fin n) (z : Fin n → Vec d)
    (ψ : Model Q X → Vec d) (hψ : ∀ f, ψ f = z (indexOf f)) :
    IsCompact (Set.range ψ) := by
  have hsubset : Set.range ψ ⊆ Set.range z := by
    rintro _ ⟨f, rfl⟩
    exact ⟨indexOf f, (hψ f).symm⟩
  exact ((Set.finite_range z).subset hsubset).isCompact

/-- Every positive perspective ball centered at a model has positive model
probability.  This is the precise full-support condition needed by the finite
net proof. -/
def PerspectiveFullSupport
    (Pf : Measure (Model Q X)) (ψ : Model Q X → Vec d) : Prop :=
  ∀ f ρ, 0 < ρ → 0 < Pf (perspectiveBall ψ f ρ)

/-- The finite-dimensional joint-law formulation of iid reference sampling.
For every stage and every measurable family of coordinate events, the
probability that all references land in their assigned events is the product
of the common marginal probabilities.  This packages independence and the
common model law in exactly the form consumed below. -/
structure IIDReferenceSampler
    (Pf : Measure (Model Q X))
    (μ : ℕ → Measure Ω)
    (f_ref : ∀ n, Ω → Fin n → Model Q X) : Prop where
  measurable : ∀ n i, Measurable (fun ω => f_ref n ω i)
  joint_law : ∀ n (s : Fin n → Set (Model Q X)),
    (∀ i, MeasurableSet (s i)) →
      μ n {ω | ∀ i, f_ref n ω i ∈ s i} = ∏ i, Pf (s i)

/-- Event that at least one stage-`n` reference model lies in `s`. -/
def referenceHits
    (f_ref : ∀ n, Ω → Fin n → Model Q X)
    (s : Set (Model Q X)) (n : ℕ) : Set Ω :=
  {ω | ∃ i : Fin n, f_ref n ω i ∈ s}

/-- Event that every stage-`n` reference model misses `s`. -/
def referenceMisses
    (f_ref : ∀ n, Ω → Fin n → Model Q X)
    (s : Set (Model Q X)) (n : ℕ) : Set Ω :=
  {ω | ∀ i : Fin n, f_ref n ω i ∉ s}

lemma referenceHits_compl
    (f_ref : ∀ n, Ω → Fin n → Model Q X)
    (s : Set (Model Q X)) (n : ℕ) :
    (referenceHits f_ref s n)ᶜ = referenceMisses f_ref s n := by
  ext ω
  simp [referenceHits, referenceMisses]

lemma referenceMisses_compl
    (f_ref : ∀ n, Ω → Fin n → Model Q X)
    (s : Set (Model Q X)) (n : ℕ) :
    (referenceMisses f_ref s n)ᶜ = referenceHits f_ref s n := by
  ext ω
  simp [referenceHits, referenceMisses]

lemma measurableSet_referenceHits
    {f_ref : ∀ n, Ω → Fin n → Model Q X}
    (href_meas : ∀ n i, Measurable (fun ω => f_ref n ω i))
    {s : Set (Model Q X)} (hs : MeasurableSet s) (n : ℕ) :
    MeasurableSet (referenceHits f_ref s n) := by
  classical
  have heq : referenceHits f_ref s n =
      ⋃ i : Fin n, (fun ω => f_ref n ω i) ⁻¹' s := by
    ext ω
    simp [referenceHits]
  rw [heq]
  exact MeasurableSet.iUnion fun i => (href_meas n i) hs

lemma measurableSet_referenceMisses
    {f_ref : ∀ n, Ω → Fin n → Model Q X}
    (href_meas : ∀ n i, Measurable (fun ω => f_ref n ω i))
    {s : Set (Model Q X)} (hs : MeasurableSet s) (n : ℕ) :
    MeasurableSet (referenceMisses f_ref s n) := by
  rw [← referenceHits_compl f_ref s n]
  exact (measurableSet_referenceHits href_meas hs n).compl

/-- The probability that all `n` iid references miss a measurable set is the
`n`-th power of its complement probability. -/
theorem measure_referenceMisses_eq_pow
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (μ : ℕ → Measure Ω)
    (f_ref : ∀ n, Ω → Fin n → Model Q X)
    (hiid : IIDReferenceSampler Pf μ f_ref)
    (s : Set (Model Q X)) (hs : MeasurableSet s) (n : ℕ) :
    μ n (referenceMisses f_ref s n) = (1 - Pf s) ^ n := by
  have hjoint := hiid.joint_law n (fun _ => sᶜ) (fun _ => hs.compl)
  have hevent : referenceMisses f_ref s n =
      {ω | ∀ i : Fin n, f_ref n ω i ∈ sᶜ} := by
    ext ω
    simp [referenceMisses]
  rw [hevent, hjoint]
  calc
    (∏ _i : Fin n, Pf sᶜ) = (Pf sᶜ) ^ n := by simp
    _ = (1 - Pf s) ^ n := by simp [measure_compl hs]

/-- A fixed measurable positive-mass set is hit by an iid reference sample with
probability tending to one. -/
theorem highProb_referenceHits
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (μ : ℕ → Measure Ω) (hμ : ∀ n, IsProbabilityMeasure (μ n))
    (f_ref : ∀ n, Ω → Fin n → Model Q X)
    (hiid : IIDReferenceSampler Pf μ f_ref)
    (s : Set (Model Q X)) (hs : MeasurableSet s) (hs_pos : 0 < Pf s) :
    HighProbAtTop μ hμ (fun n => referenceHits f_ref s n) := by
  have hq_lt : 1 - Pf s < (1 : ENNReal) :=
    ENNReal.sub_lt_self ENNReal.one_ne_top hs_pos
  have hpow : Tendsto (fun n : ℕ => (1 - Pf s) ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hq_lt
  intro δ hδ
  have hevent : ∀ᶠ n in atTop, (1 - Pf s) ^ n < δ :=
    (tendsto_order.1 hpow).2 δ hδ
  obtain ⟨N, hN⟩ := eventually_atTop.1 hevent
  refine ⟨N, ?_⟩
  intro n hn
  have hmiss_lt : μ n (referenceMisses f_ref s n) < δ := by
    rw [measure_referenceMisses_eq_pow Pf μ f_ref hiid s hs n]
    exact hN n (Nat.le_of_lt hn)
  have hhit_eq : μ n (referenceHits f_ref s n) =
      1 - μ n (referenceMisses f_ref s n) := by
    have hcomp := measure_compl
      (measurableSet_referenceMisses hiid.measurable hs n)
    rw [referenceMisses_compl f_ref s n] at hcomp
    simpa using hcomp
  rw [hhit_eq]
  exact tsub_le_tsub_left (le_of_lt hmiss_lt) 1

/-- Event that every center in a finite perspective net is hit within radius
`ρ` by at least one reference model. -/
def finiteNetHitEvent
    (ψ : Model Q X → Vec d)
    (f_ref : ∀ n, Ω → Fin n → Model Q X)
    (centers : Finset (Model Q X)) (ρ : ℝ) (n : ℕ) : Set Ω :=
  {ω | ∀ g ∈ centers, ω ∈ referenceHits f_ref (perspectiveBall ψ g ρ) n}

lemma measurableSet_perspectiveBall
    (ψ : Model Q X → Vec d) (hψ : Measurable ψ)
    (f : Model Q X) (ρ : ℝ) :
    MeasurableSet (perspectiveBall ψ f ρ) := by
  have hpre : perspectiveBall ψ f ρ = ψ ⁻¹' Metric.ball (ψ f) ρ := by
    ext g
    simp [perspectiveBall, dist_eq_norm]
  rw [hpre]
  exact hψ Metric.isOpen_ball.measurableSet

lemma measurableSet_finiteNetHitEvent
    (ψ : Model Q X → Vec d) (hψ : Measurable ψ)
    (f_ref : ∀ n, Ω → Fin n → Model Q X)
    (href_meas : ∀ n i, Measurable (fun ω => f_ref n ω i))
    (centers : Finset (Model Q X)) (ρ : ℝ) (n : ℕ) :
    MeasurableSet (finiteNetHitEvent ψ f_ref centers ρ n) := by
  classical
  unfold finiteNetHitEvent
  exact measurableSet_finset_all centers
    (fun g => referenceHits f_ref (perspectiveBall ψ g ρ) n)
    (fun g _ => measurableSet_referenceHits href_meas
      (measurableSet_perspectiveBall ψ hψ g ρ) n)

/-- Every center of a fixed finite net is hit with high probability. -/
theorem highProb_finiteNetHitEvent
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (μ : ℕ → Measure Ω) (hμ : ∀ n, IsProbabilityMeasure (μ n))
    (ψ : Model Q X → Vec d) (hψ : Measurable ψ)
    (f_ref : ∀ n, Ω → Fin n → Model Q X)
    (hiid : IIDReferenceSampler Pf μ f_ref)
    (hfull : PerspectiveFullSupport Pf ψ)
    (centers : Finset (Model Q X)) (ρ : ℝ) (hρ : 0 < ρ) :
    HighProbAtTop μ hμ (fun n => finiteNetHitEvent ψ f_ref centers ρ n) := by
  classical
  unfold finiteNetHitEvent
  apply HighProbAtTop.finset_all centers
    (fun g n => referenceHits f_ref (perspectiveBall ψ g ρ) n)
  · intro g hg
    exact highProb_referenceHits Pf μ hμ f_ref hiid
      (perspectiveBall ψ g ρ)
      (measurableSet_perspectiveBall ψ hψ g ρ)
      (hfull g ρ hρ)
  · intro g hg n
    exact measurableSet_referenceHits hiid.measurable
      (measurableSet_perspectiveBall ψ hψ g ρ) n

/-- Hitting every radius-`ρ` center of a radius-`ρ` finite perspective cover
implies uniform radius-`2ρ` coverage of every model. -/
theorem finiteNetHitEvent_subset_coverage
    (ψ : Model Q X → Vec d)
    (f_ref : ∀ n, Ω → Fin n → Model Q X)
    (centers : Finset (Model Q X)) (ρ : ℝ)
    (hcover : PerspectiveFiniteCover ψ ρ centers) (n : ℕ) :
    finiteNetHitEvent ψ f_ref centers ρ n ⊆
      {ω | ∀ f, ∃ i : Fin n, ‖ψ (f_ref n ω i) - ψ f‖ ≤ 2 * ρ} := by
  intro ω hω f
  obtain ⟨g, hg, hgf⟩ := hcover f
  have hhit : ω ∈ referenceHits f_ref (perspectiveBall ψ g ρ) n :=
    hω g hg
  obtain ⟨i, hi⟩ := hhit
  refine ⟨i, ?_⟩
  have hig : ‖ψ (f_ref n ω i) - ψ g‖ < ρ := hi
  calc
    ‖ψ (f_ref n ω i) - ψ f‖
        ≤ ‖ψ (f_ref n ω i) - ψ g‖ + ‖ψ g - ψ f‖ := by
          simpa using norm_sub_le
            (ψ (f_ref n ω i) - ψ g) (ψ f - ψ g)
    _ ≤ ρ + ρ := (add_lt_add hig hgf).le
    _ = 2 * ρ := by ring

/-- A measurable high-probability subevent certificate for uniform reference
coverage.  The certificate avoids requiring measurability of the universal
coverage event itself. -/
structure CoverageSubevents
    (μ : ℕ → Measure Ω) (hμ : ∀ n, IsProbabilityMeasure (μ n))
    (ψ : Model Q X → Vec d)
    (f_ref : ∀ n, Ω → Fin n → Model Q X) where
  event : ℝ → ℕ → Set Ω
  measurable : ∀ ρ > 0, ∀ n, MeasurableSet (event ρ n)
  highProb : ∀ ρ > 0, HighProbAtTop μ hμ (event ρ)
  subset : ∀ ρ > 0, ∀ n,
    event ρ n ⊆ {ω | ∀ f, ∃ i : Fin n,
      ‖ψ (f_ref n ω i) - ψ f‖ ≤ ρ}

/-- Choose one finite radius-`ρ/2` perspective net from total boundedness. -/
noncomputable def chosenPerspectiveNet
    (ψ : Model Q X → Vec d) (htb : PerspectiveTotallyBounded ψ)
    (ρ : ℝ) : Finset (Model Q X) :=
  if hρ : 0 < ρ then Classical.choose (htb (ρ / 2) (by positivity)) else ∅

lemma chosenPerspectiveNet_covers
    (ψ : Model Q X → Vec d) (htb : PerspectiveTotallyBounded ψ)
    (ρ : ℝ) (hρ : 0 < ρ) :
    PerspectiveFiniteCover ψ (ρ / 2) (chosenPerspectiveNet ψ htb ρ) := by
  rw [chosenPerspectiveNet, dif_pos hρ]
  exact Classical.choose_spec (htb (ρ / 2) (by positivity))

/-- Total boundedness, a measurable perspective map, full support, and iid
reference sampling produce the coverage subevents required by the Quench MSE
argument. -/
noncomputable def coverageSubevents_of_totallyBounded_iid_fullSupport
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (μ : ℕ → Measure Ω) (hμ : ∀ n, IsProbabilityMeasure (μ n))
    (ψ : Model Q X → Vec d) (hψ : Measurable ψ)
    (htb : PerspectiveTotallyBounded ψ)
    (hfull : PerspectiveFullSupport Pf ψ)
    (f_ref : ∀ n, Ω → Fin n → Model Q X)
    (hiid : IIDReferenceSampler Pf μ f_ref) :
    CoverageSubevents μ hμ ψ f_ref where
  event ρ n := finiteNetHitEvent ψ f_ref
    (chosenPerspectiveNet ψ htb ρ) (ρ / 2) n
  measurable ρ hρ n := measurableSet_finiteNetHitEvent ψ hψ f_ref
    hiid.measurable (chosenPerspectiveNet ψ htb ρ) (ρ / 2) n
  highProb ρ hρ := highProb_finiteNetHitEvent Pf μ hμ ψ hψ f_ref hiid
    hfull (chosenPerspectiveNet ψ htb ρ) (ρ / 2) (by positivity)
  subset ρ hρ n := by
    have hsub := finiteNetHitEvent_subset_coverage ψ f_ref
      (chosenPerspectiveNet ψ htb ρ) (ρ / 2)
      (chosenPerspectiveNet_covers ψ htb ρ hρ) n
    simpa [show 2 * (ρ / 2) = ρ by ring] using hsub

/-- Compactness is the standard sufficient condition for the preceding
coverage certificate. -/
noncomputable def coverageSubevents_of_compact_iid_fullSupport
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (μ : ℕ → Measure Ω) (hμ : ∀ n, IsProbabilityMeasure (μ n))
    (ψ : Model Q X → Vec d) (hψ : Measurable ψ)
    (hcompact : IsCompact (Set.range ψ))
    (hfull : PerspectiveFullSupport Pf ψ)
    (f_ref : ∀ n, Ω → Fin n → Model Q X)
    (hiid : IIDReferenceSampler Pf μ f_ref) :
    CoverageSubevents μ hμ ψ f_ref :=
  coverageSubevents_of_totallyBounded_iid_fullSupport Pf μ hμ ψ hψ
    (perspectiveTotallyBounded_of_isCompact_range ψ hcompact)
    hfull f_ref hiid

/-- Total boundedness, full support, and iid reference sampling imply the raw
uniform coverage event used by the original Quench theorem.  The proof passes
through measurable finite-net subevents, so the universal coverage event itself
need not be shown measurable. -/
theorem highProb_uniformCoverage_of_totallyBounded_iid_fullSupport
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (μ : ℕ → Measure Ω) (hμ : ∀ n, IsProbabilityMeasure (μ n))
    (ψ : Model Q X → Vec d) (hψ : Measurable ψ)
    (htb : PerspectiveTotallyBounded ψ)
    (hfull : PerspectiveFullSupport Pf ψ)
    (f_ref : ∀ n, Ω → Fin n → Model Q X)
    (hiid : IIDReferenceSampler Pf μ f_ref) :
    ∀ ρ > 0, HighProbAtTop μ hμ (fun n => {ω |
      ∀ f, ∃ i : Fin n, ‖ψ (f_ref n ω i) - ψ f‖ ≤ ρ}) := by
  intro ρ hρ
  let C := coverageSubevents_of_totallyBounded_iid_fullSupport
    Pf μ hμ ψ hψ htb hfull f_ref hiid
  exact HighProbAtTop.mono (C.highProb ρ hρ) (C.subset ρ hρ)

/-- Compactness of the perspective image is the standard paper-facing route to
uniform reference coverage under full support and iid sampling. -/
theorem highProb_uniformCoverage_of_compact_iid_fullSupport
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (μ : ℕ → Measure Ω) (hμ : ∀ n, IsProbabilityMeasure (μ n))
    (ψ : Model Q X → Vec d) (hψ : Measurable ψ)
    (hcompact : IsCompact (Set.range ψ))
    (hfull : PerspectiveFullSupport Pf ψ)
    (f_ref : ∀ n, Ω → Fin n → Model Q X)
    (hiid : IIDReferenceSampler Pf μ f_ref) :
    ∀ ρ > 0, HighProbAtTop μ hμ (fun n => {ω |
      ∀ f, ∃ i : Fin n, ‖ψ (f_ref n ω i) - ψ f‖ ≤ ρ}) := by
  exact highProb_uniformCoverage_of_totallyBounded_iid_fullSupport
    Pf μ hμ ψ hψ
      (perspectiveTotallyBounded_of_isCompact_range ψ hcompact)
      hfull f_ref hiid

