/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.Localisation
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Exact chart transport from a partial resolution, and the normalised-indicator partition

The chart data of a partial resolution (the record `PartialResolution` of
`timaeus-research/hironaka`, transcribed here as `ResolutionChart`: a compact chart domain, a chart
map `C¹` on an open neighbourhood, a closed null exceptional set off which the map is injective)
give the **exact transport identity** of the chart: the chart map pushes the domain-restricted
Lebesgue measure weighted by `|det Dφ|` to the Lebesgue measure restricted to the chart image
(`ResolutionChart.map_absDet`; Mathlib's change of variables
`map_withDensity_abs_det_fderiv_eq_addHaar` off the exceptional set, whose image is null because
the map is differentiable on a neighbourhood), and its weighted form
`ResolutionChart.map_absDet_mul` — the measure-theoretic half of grammar's
`ChartPresentation.transport`.  Nondegeneracy of the Jacobian is not needed for this identity.

The **normalised indicators** `ρ_i = 1_{A_i} / ∑_j 1_{A_j}` of a finite measurable cover form a
measurable partition of unity on the union (`coverWeight`), so a finite a.e. cover of the sublevel
set by chart images yields a `FiniteSublevelPartition` (`LocalisationData.partitionOfCover`), and
the weighted transports of the charts assemble to the restricted measure
(`ResolutionCover.sum_map_eq`): finite multiplicity is corrected exactly, without analyticity.

Non-claims: `amplitude_eq` / `NormalMomentPresentation` / `AdaptedStrataData` — these weights are
not analytic in the normal variables (see `LocalisationObstruction.lean`).
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace Grammar

/-! ### Pushforward and density commute -/

theorem map_withDensity_comp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (ν : Measure α)
    {φ : α → β} (hφ : Measurable φ) {g : β → ℝ≥0∞} (hg : Measurable g) :
    (ν.withDensity fun x => g (φ x)).map φ = (ν.map φ).withDensity g := by
  ext t ht
  rw [Measure.map_apply hφ ht, withDensity_apply _ (hφ ht), withDensity_apply _ ht,
    Measure.restrict_map hφ ht, lintegral_map hg hφ]

theorem withDensity_finset_sum {α : Type*} [MeasurableSpace α] (μ : Measure α) {ι : Type*}
    (s : Finset ι) {f : ι → α → ℝ≥0∞} (hf : ∀ i, Measurable (f i)) :
    μ.withDensity (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, μ.withDensity (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [← ih, ← withDensity_add_left (hf a)]
    rfl

/-! ### Resolution charts -/

/-- **A resolution chart** (the chart data of hironaka's `PartialResolution`): a compact domain, a
chart map `C¹` on an open neighbourhood of it, and a closed null exceptional set off which the map
is injective. -/
structure ResolutionChart (d : ℕ) where
  /-- the chart domain -/
  dom : Set (Fin d → ℝ)
  dom_compact : IsCompact dom
  /-- the chart map -/
  φ : (Fin d → ℝ) → (Fin d → ℝ)
  /-- an open neighbourhood of the domain on which the chart map is `C¹` -/
  U : Set (Fin d → ℝ)
  U_open : IsOpen U
  dom_subset : dom ⊆ U
  smooth : ContDiffOn ℝ 1 φ U
  /-- the exceptional set -/
  E : Set (Fin d → ℝ)
  E_subset : E ⊆ dom
  E_closed : IsClosed E
  E_null : volume E = 0
  inj : InjOn φ (dom \ E)

namespace ResolutionChart

variable {d : ℕ} (C : ResolutionChart d)

theorem measurableSet_dom : MeasurableSet C.dom := C.dom_compact.isClosed.measurableSet

theorem measurableSet_E : MeasurableSet C.E := C.E_closed.measurableSet

theorem differentiableOn : DifferentiableOn ℝ C.φ C.U := C.smooth.differentiableOn one_ne_zero

theorem continuousOn : ContinuousOn C.φ C.dom := C.smooth.continuousOn.mono C.dom_subset

theorem hasFDerivWithinAt {x : Fin d → ℝ} (hx : x ∈ C.dom) {s : Set (Fin d → ℝ)} :
    HasFDerivWithinAt C.φ (fderiv ℝ C.φ x) s x :=
  ((C.differentiableOn x (C.dom_subset hx)).differentiableAt
    (C.U_open.mem_nhds (C.dom_subset hx))).hasFDerivAt.hasFDerivWithinAt

open scoped Classical in
/-- The chart map extended measurably by `0` off the domain. -/
noncomputable def Φ : (Fin d → ℝ) → (Fin d → ℝ) := C.dom.piecewise C.φ 0

open scoped Classical in
theorem Φ_eqOn : EqOn C.Φ C.φ C.dom := fun _ hx => by
  unfold Φ
  exact piecewise_eq_of_mem _ _ _ hx

open scoped Classical in
theorem measurable_Φ : Measurable C.Φ := by
  refine measurable_of_restrict_of_restrict_compl C.measurableSet_dom ?_ ?_
  · have h : C.dom.domRestrict C.Φ = C.dom.domRestrict C.φ := funext fun x => C.Φ_eqOn x.2
    rw [h]
    exact (continuousOn_iff_continuous_domRestrict.1 C.continuousOn).measurable
  · have h : C.domᶜ.domRestrict C.Φ = fun _ => (0 : Fin d → ℝ) := by
      funext x
      unfold Φ
      exact piecewise_eq_of_notMem _ _ _ x.2
    rw [h]
    exact measurable_const

/-- The absolute Jacobian density `|det Dφ|`. -/
noncomputable def absDet (x : Fin d → ℝ) : ℝ≥0∞ := ENNReal.ofReal |(fderiv ℝ C.φ x).det|

theorem measurable_absDet : Measurable C.absDet :=
  ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp
    (ContinuousLinearMap.continuous_det.measurable.comp (measurable_fderiv ℝ C.φ)))

theorem image_E_null : volume (C.φ '' C.E) = 0 :=
  addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
    (C.differentiableOn.mono (C.E_subset.trans C.dom_subset)) C.E_null

theorem restrict_dom_eq :
    (volume : Measure (Fin d → ℝ)).restrict C.dom = volume.restrict (C.dom \ C.E) :=
  (Measure.restrict_congr_set
    (sdiff_ae_eq_self.2 (measure_mono_null inter_subset_right C.E_null))).symm

theorem restrict_image_eq :
    (volume : Measure (Fin d → ℝ)).restrict (C.φ '' C.dom) =
      volume.restrict (C.φ '' (C.dom \ C.E)) := by
  refine Measure.restrict_congr_set (ae_eq_set.2 ⟨?_, ?_⟩)
  · refine measure_mono_null (fun y hy => ?_) C.image_E_null
    obtain ⟨⟨x, hx, rfl⟩, hy2⟩ := hy
    by_cases hxE : x ∈ C.E
    · exact ⟨x, hxE, rfl⟩
    · exact absurd ⟨x, ⟨hx, hxE⟩, rfl⟩ hy2
  · rw [sdiff_eq_empty.2 (image_mono sdiff_subset), measure_empty]

/-- **The exact chart transport**: the chart map pushes `|det Dφ| dy` on the domain to Lebesgue
measure on the chart image. -/
theorem map_absDet :
    ((volume.restrict C.dom).withDensity C.absDet).map C.Φ =
      (volume : Measure (Fin d → ℝ)).restrict (C.φ '' C.dom) := by
  rw [C.restrict_dom_eq, C.restrict_image_eq]
  have hmeas : MeasurableSet (C.dom \ C.E) := C.measurableSet_dom.diff C.measurableSet_E
  have hcongr : C.Φ =ᵐ[(volume.restrict (C.dom \ C.E)).withDensity C.absDet] C.φ := by
    refine (withDensity_absolutelyContinuous _ _).ae_eq ?_
    rw [Filter.EventuallyEq, ae_restrict_iff' hmeas]
    exact Eventually.of_forall fun x hx => C.Φ_eqOn hx.1
  rw [Measure.map_congr hcongr]
  exact map_withDensity_abs_det_fderiv_eq_addHaar volume hmeas.nullMeasurableSet
    (fun x hx => C.hasFDerivWithinAt hx.1) C.inj

/-- **The weighted chart transport**: with a measurable weight `g` on the target,
`Φ_* (|det Dφ| · g∘Φ dy|_dom) = g dx|_{φ(dom)}`. -/
theorem map_absDet_mul {g : (Fin d → ℝ) → ℝ≥0∞} (hg : Measurable g) :
    ((volume.restrict C.dom).withDensity fun x => C.absDet x * g (C.Φ x)).map C.Φ =
      ((volume : Measure (Fin d → ℝ)).restrict (C.φ '' C.dom)).withDensity g := by
  rw [← C.map_absDet, ← map_withDensity_comp _ C.measurable_Φ hg]
  exact congrArg (Measure.map C.Φ)
    (withDensity_mul _ C.measurable_absDet (hg.comp C.measurable_Φ))

end ResolutionChart

/-! ### The normalised-indicator partition of a finite cover -/

section CoverWeight

variable {X : Type*} {ι : Type*} [Fintype ι]

/-- The normalised indicator `1_{A_i} / ∑_j 1_{A_j}` (with `0/0 = 0`). -/
noncomputable def coverWeight (A : ι → Set X) (i : ι) (x : X) : ℝ :=
  (A i).indicator (fun _ => (1 : ℝ)) x / ∑ j, (A j).indicator (fun _ => (1 : ℝ)) x

theorem measurable_coverWeight [MeasurableSpace X] {A : ι → Set X}
    (hA : ∀ i, MeasurableSet (A i)) (i : ι) : Measurable (coverWeight A i) :=
  (measurable_const.indicator (hA i)).div
    (Finset.measurable_sum _ fun j _ => measurable_const.indicator (hA j))

theorem coverWeight_nonneg (A : ι → Set X) (i : ι) (x : X) : 0 ≤ coverWeight A i x :=
  div_nonneg (indicator_nonneg (fun _ _ => zero_le_one) _)
    (Finset.sum_nonneg fun _ _ => indicator_nonneg (fun _ _ => zero_le_one) _)

theorem coverWeight_eq_zero_of_notMem {A : ι → Set X} {i : ι} {x : X} (hx : x ∉ A i) :
    coverWeight A i x = 0 := by
  unfold coverWeight
  rw [indicator_of_notMem hx, zero_div]

theorem sum_coverWeight {A : ι → Set X} {x : X} (hx : x ∈ ⋃ i, A i) :
    ∑ i, coverWeight A i x = 1 := by
  obtain ⟨i₀, hi₀⟩ := mem_iUnion.1 hx
  have hpos : 0 < ∑ j, (A j).indicator (fun _ => (1 : ℝ)) x := by
    refine lt_of_lt_of_le zero_lt_one ?_
    calc (1 : ℝ) = (A i₀).indicator (fun _ => (1 : ℝ)) x :=
          (indicator_of_mem hi₀ (fun _ => (1 : ℝ))).symm
      _ ≤ ∑ j, (A j).indicator (fun _ => (1 : ℝ)) x :=
          Finset.single_le_sum (fun j _ => indicator_nonneg (fun _ _ => zero_le_one) _)
            (Finset.mem_univ i₀)
  unfold coverWeight
  rw [← Finset.sum_div, div_self hpos.ne']

theorem coverWeight_le_one (A : ι → Set X) (i : ι) (x : X) : coverWeight A i x ≤ 1 := by
  by_cases hx : x ∈ ⋃ j, A j
  · rw [← sum_coverWeight hx]
    exact Finset.single_le_sum (fun j _ => coverWeight_nonneg A j x) (Finset.mem_univ i)
  · rw [coverWeight_eq_zero_of_notMem fun h => hx (mem_iUnion.2 ⟨i, h⟩)]
    exact zero_le_one

end CoverWeight

namespace LocalisationData

variable {U : Type*} [MeasurableSpace U] (D : LocalisationData U)

/-- **The partition of the sublevel set from a finite a.e. cover** by measurable sets. -/
noncomputable def partitionOfCover {ι : Type*} [Fintype ι] (A : ι → Set U)
    (hA : ∀ i, MeasurableSet (A i)) (hcover : ∀ᵐ z ∂D.μ.restrict D.sublevel, z ∈ ⋃ i, A i) :
    D.FiniteSublevelPartition ι where
  ρ := coverWeight A
  measurable_ρ := measurable_coverWeight hA
  nonneg_ρ := fun i => Eventually.of_forall fun z => coverWeight_nonneg A i z
  sum_eq_one := by
    filter_upwards [hcover] with z hz
    exact sum_coverWeight hz

end LocalisationData

/-! ### A finite cover by resolution charts -/

/-- A finite family of resolution charts. -/
structure ResolutionCover (d : ℕ) (ι : Type*) [Fintype ι] where
  /-- the charts -/
  chart : ι → ResolutionChart d

namespace ResolutionCover

variable {d : ℕ} {ι : Type*} [Fintype ι] (R : ResolutionCover d ι)

/-- The chart images. -/
def image (i : ι) : Set (Fin d → ℝ) := (R.chart i).φ '' (R.chart i).dom

theorem isCompact_image (i : ι) : IsCompact (R.image i) :=
  (R.chart i).dom_compact.image_of_continuousOn (R.chart i).continuousOn

theorem measurableSet_image (i : ι) : MeasurableSet (R.image i) :=
  (R.isCompact_image i).isClosed.measurableSet

/-- The normalised chart weights `ρ_i` on the target. -/
noncomputable def weight (i : ι) : (Fin d → ℝ) → ℝ := coverWeight R.image i

theorem measurable_weight (i : ι) : Measurable (R.weight i) :=
  measurable_coverWeight R.measurableSet_image i

/-- The weighted source measure of chart `i`: `|det Dφ_i| · (ρ_i ∘ Φ_i) dy` on the domain. -/
noncomputable def sourceMeasure (i : ι) : Measure (Fin d → ℝ) :=
  (volume.restrict (R.chart i).dom).withDensity fun x =>
    (R.chart i).absDet x * ENNReal.ofReal (R.weight i ((R.chart i).Φ x))

/-- **The weighted chart transport onto a measurable set containing the chart image**: the chart
map pushes `|det Dφ| · (ρ_i ∘ Φ) dy|_dom` to `ρ_i dx|_S` — the shape of
`ChartPresentation.transport`. -/
theorem map_sourceMeasure (i : ι) {S : Set (Fin d → ℝ)} (hS : MeasurableSet S)
    (hsub : R.image i ⊆ S) :
    (R.sourceMeasure i).map (R.chart i).Φ =
      ((volume : Measure (Fin d → ℝ)).restrict S).withDensity fun z =>
        ENNReal.ofReal (R.weight i z) := by
  unfold sourceMeasure
  rw [(R.chart i).map_absDet_mul (g := fun z => ENNReal.ofReal (R.weight i z))
    (ENNReal.measurable_ofReal.comp (R.measurable_weight i))]
  change ((volume : Measure (Fin d → ℝ)).restrict (R.image i)).withDensity _ = _
  rw [← restrict_withDensity (R.measurableSet_image i), ← restrict_withDensity hS]
  refine Measure.restrict_congr_set (ae_eq_set.2 ⟨?_, ?_⟩)
  · rw [sdiff_eq_empty.2 hsub, measure_empty]
  · rw [withDensity_apply _ (hS.diff (R.measurableSet_image i))]
    refine (setLIntegral_congr_fun (hS.diff (R.measurableSet_image i))
      fun z hz => ?_).trans lintegral_zero
    unfold weight
    rw [coverWeight_eq_zero_of_notMem hz.2, ENNReal.ofReal_zero]

/-- **The assembled transport**: the weighted transports of the charts sum to Lebesgue measure on
the union of the chart images. -/
theorem sum_map_eq :
    ∑ i, (R.sourceMeasure i).map (R.chart i).Φ =
      (volume : Measure (Fin d → ℝ)).restrict (⋃ i, R.image i) := by
  have hU : MeasurableSet (⋃ i, R.image i) := MeasurableSet.iUnion R.measurableSet_image
  have h : ∀ i, (R.sourceMeasure i).map (R.chart i).Φ =
      ((volume : Measure (Fin d → ℝ)).restrict (⋃ j, R.image j)).withDensity
        fun z => ENNReal.ofReal (R.weight i z) :=
    fun i => R.map_sourceMeasure i hU (subset_iUnion R.image i)
  simp_rw [h]
  have hsum := (withDensity_finset_sum ((volume : Measure (Fin d → ℝ)).restrict (⋃ j, R.image j))
    Finset.univ (f := fun i z => ENNReal.ofReal (R.weight i z))
    fun i => ENNReal.measurable_ofReal.comp (R.measurable_weight i)).symm
  rw [hsum]
  have hone : (fun z => ∑ i, ENNReal.ofReal (R.weight i z)) =ᵐ[volume.restrict (⋃ i, R.image i)]
      1 := by
    rw [Filter.EventuallyEq, ae_restrict_iff' hU]
    refine Eventually.of_forall fun z hz => ?_
    unfold weight
    rw [Pi.one_apply, ← ENNReal.ofReal_sum_of_nonneg fun i _ => coverWeight_nonneg R.image i z,
      sum_coverWeight hz, ENNReal.ofReal_one]
  rw [withDensity_congr_ae hone, withDensity_one]

end ResolutionCover

end Grammar
