/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.ContinuousConvergence
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# The graph-law transfer for continuously convergent maps

If probability laws `μ_n ⇒ μ₀` on `P` are uniformly tight and `Tn : P → V` converges
continuously to `T`, then the graph laws converge:
`(id, Tn n)_# μ_n ⇒ (id, T)_# μ₀` (`tendsto_graphLaw_of_continuouslyConverges`).  For a bounded
continuous test `f` on `P × V` put `f_n(p) = f(p, Tn n p)` and `f_∞(p) = f(p, T p)`.  The fixed-map
continuous-mapping theorem handles `∫ f_∞ dμ_n → ∫ f_∞ dμ₀`, and under the **same** `μ_n`
`|∫ f_n dμ_n − ∫ f_∞ dμ_n| ≤ sup_C |f_n − f_∞| + 2‖f‖ μ_n(Cᶜ)`
for a compact `C` carrying all but `δ` of every `μ_n`; `f_n → f_∞` continuously, hence uniformly on
`C`.  On a complete separable metric space tightness of a convergent sequence is automatic
(Prokhorov's easy direction), giving the Polish corollary `tendsto_graphLaw_of_polish`.
-/

open MeasureTheory Filter Topology

namespace Grammar

open BoundedContinuousFunction

section engine

variable {P V : Type*} [TopologicalSpace P] [T2Space P] [MeasurableSpace P] [BorelSpace P]
  [PseudoMetricSpace V] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]

/-- The graph law `(id, S)_# μ` of a measurable map. -/
noncomputable def graphLaw (μ : ProbabilityMeasure P) {S : P → V} (hS : Measurable S) :
    ProbabilityMeasure (P × V) :=
  μ.map (measurable_id.prodMk hS).aemeasurable

theorem integral_graphLaw (μ : ProbabilityMeasure P) {S : P → V} (hS : Measurable S)
    (f : (P × V) →ᵇ ℝ) : ∫ z, f z ∂(graphLaw μ hS : Measure (P × V)) = ∫ p, f (p, S p) ∂μ := by
  unfold graphLaw
  rw [ProbabilityMeasure.toMeasure_map, integral_map (measurable_id.prodMk hS).aemeasurable
    f.continuous.measurable.aestronglyMeasurable]
  rfl

/-- The comparison `|∫ f_n dμ − ∫ f_∞ dμ| ≤ δ + 2‖f‖ μ(Cᶜ)` when `|f_n − f_∞| < δ` on `C`. -/
theorem abs_integral_sub_le_of_close_on {μ : Measure P} [IsProbabilityMeasure μ]
    (f : (P × V) →ᵇ ℝ) {S S' : P → V} (hS : Measurable S) (hS' : Measurable S') {C : Set P}
    (hC : IsCompact C) {δ : ℝ} (hδ : 0 ≤ δ)
    (hclose : ∀ p ∈ C, dist (f (p, S p)) (f (p, S' p)) < δ) :
    |∫ p, f (p, S p) ∂μ - ∫ p, f (p, S' p) ∂μ| ≤ δ + 2 * ‖f‖ * (μ Cᶜ).toReal := by
  have hCm : MeasurableSet Cᶜ := hC.isClosed.measurableSet.compl
  have hm1 : Measurable fun p => f (p, S p) :=
    f.continuous.measurable.comp (measurable_id.prodMk hS)
  have hm2 : Measurable fun p => f (p, S' p) :=
    f.continuous.measurable.comp (measurable_id.prodMk hS')
  have hi1 : Integrable (fun p => f (p, S p)) μ :=
    Integrable.of_bound hm1.aestronglyMeasurable ‖f‖
      (Eventually.of_forall fun p => f.norm_coe_le_norm _)
  have hi2 : Integrable (fun p => f (p, S' p)) μ :=
    Integrable.of_bound hm2.aestronglyMeasurable ‖f‖
      (Eventually.of_forall fun p => f.norm_coe_le_norm _)
  rw [← integral_sub hi1 hi2, ← Real.norm_eq_abs]
  have hg : Integrable (fun p => δ + 2 * ‖f‖ * Cᶜ.indicator (fun _ => (1 : ℝ)) p) μ :=
    (integrable_const δ).add (((integrable_const (1 : ℝ)).indicator hCm).const_mul _)
  refine (norm_integral_le_of_norm_le hg (Eventually.of_forall fun p => ?_)).trans (le_of_eq ?_)
  · by_cases hp : p ∈ C
    · rw [Set.indicator_of_notMem (Set.notMem_compl_iff.2 hp), mul_zero, add_zero, Real.norm_eq_abs,
        ← Real.dist_eq]
      exact (hclose p hp).le
    · rw [Set.indicator_of_mem (Set.mem_compl hp), mul_one]
      have := norm_sub_le (f (p, S p)) (f (p, S' p))
      have h1 := f.norm_coe_le_norm (p, S p)
      have h2 := f.norm_coe_le_norm (p, S' p)
      linarith
  · rw [integral_add (integrable_const δ) (((integrable_const (1 : ℝ)).indicator hCm).const_mul _),
      integral_const, probReal_univ, one_smul, integral_const_mul]
    congr 2
    exact integral_indicator_one hCm

/-- **Graph-law transfer** (tight-input engine): if `μ_n ⇒ μ₀`, the `μ_n` are uniformly tight,
and `Tn → T` continuously with `Tn` measurable, then `(id, Tn n)_# μ_n ⇒ (id, T)_# μ₀`. -/
theorem tendsto_graphLaw_of_continuouslyConverges {μ : ℕ → ProbabilityMeasure P}
    {μ₀ : ProbabilityMeasure P} (hμ : Tendsto μ atTop (𝓝 μ₀))
    (htight : ∀ δ : ℝ, 0 < δ → ∃ C : Set P, IsCompact C ∧ ∀ n, ((μ n : Measure P) Cᶜ).toReal ≤ δ)
    {Tn : ℕ → P → V} {T : P → V} (hTm : ∀ n, Measurable (Tn n))
    (hcc : ContinuouslyConverges Tn T) :
    Tendsto (fun n => graphLaw (μ n) (hTm n)) atTop
      (𝓝 (graphLaw μ₀ hcc.continuous_limit.measurable)) := by
  have hT := hcc.continuous_limit
  refine ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.2 fun f => ?_
  simp_rw [integral_graphLaw]
  -- fixed-map continuous mapping theorem
  have hfix : Tendsto (fun n => ∫ z, f z ∂(graphLaw (μ n) hT.measurable : Measure (P × V))) atTop
      (𝓝 (∫ z, f z ∂(graphLaw μ₀ hT.measurable : Measure (P × V)))) :=
    ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1
      (ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous μ μ₀ hμ (continuous_id.prodMk hT)) f
  simp_rw [integral_graphLaw] at hfix
  -- continuous convergence of the composed observables
  have hcc' : ContinuouslyConverges (fun n p => f (p, Tn n p)) fun p => f (p, T p) := fun p =>
    (f.continuous.tendsto _).comp (tendsto_snd.prodMk_nhds (hcc p))
  have hdiff : Tendsto (fun n => ∫ p, f (p, Tn n p) ∂(μ n : Measure P) -
      ∫ p, f (p, T p) ∂(μ n : Measure P)) atTop (𝓝 0) := by
    refine Metric.tendsto_nhds.2 fun ε hε => ?_
    set δ := ε / (2 * (1 + 2 * ‖f‖)) with hδ
    have hδ0 : 0 < δ := by positivity
    obtain ⟨C, hC, hμC⟩ := htight δ hδ0
    filter_upwards [Metric.tendstoUniformlyOn_iff.1 (hcc'.tendstoUniformlyOn hC) δ hδ0] with n hn
    rw [dist_zero_right, Real.norm_eq_abs]
    calc |∫ p, f (p, Tn n p) ∂(μ n : Measure P) - ∫ p, f (p, T p) ∂(μ n : Measure P)|
        ≤ δ + 2 * ‖f‖ * ((μ n : Measure P) Cᶜ).toReal :=
          abs_integral_sub_le_of_close_on f (hTm n) hT.measurable hC hδ0.le
            fun p hp => by rw [dist_comm]; exact hn p hp
      _ ≤ δ + 2 * ‖f‖ * δ := by gcongr; exact hμC n
      _ = ε / 2 := by rw [hδ]; field_simp
      _ < ε := half_lt_self hε
  have := hdiff.add hfix
  rw [zero_add] at this
  exact this.congr' (Eventually.of_forall fun n => by simp only [sub_add_cancel])

end engine

section polish

variable {P V : Type*} [MetricSpace P] [CompleteSpace P] [SecondCountableTopology P]
  [MeasurableSpace P] [BorelSpace P]
  [PseudoMetricSpace V] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]

/-- A weakly convergent sequence of probability measures on a complete separable metric space is
uniformly tight (the compact set `{μ₀} ∪ range μ` has compact closure; Prokhorov's easy
direction). -/
theorem tight_of_tendsto {μ : ℕ → ProbabilityMeasure P} {μ₀ : ProbabilityMeasure P}
    (hμ : Tendsto μ atTop (𝓝 μ₀)) :
    ∀ δ : ℝ, 0 < δ → ∃ C : Set P, IsCompact C ∧ ∀ n, ((μ n : Measure P) Cᶜ).toReal ≤ δ := by
  intro δ hδ
  have hK : IsCompact (closure (insert μ₀ (Set.range μ))) := hμ.isCompact_insert_range.closure
  obtain ⟨C, hC, hμC⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.1
    (isTightMeasureSet_of_isCompact_closure hK) (ENNReal.ofReal δ) (ENNReal.ofReal_pos.2 hδ)
  exact ⟨C, hC, fun n => ENNReal.toReal_le_of_le_ofReal hδ.le
    (hμC _ ⟨μ n, Set.mem_insert_of_mem _ (Set.mem_range_self n), rfl⟩)⟩

/-- **Graph-law transfer on a Polish space**: `μ_n ⇒ μ₀` and `Tn → T` continuously (with `Tn`
measurable) give `(id, Tn n)_# μ_n ⇒ (id, T)_# μ₀`. -/
theorem tendsto_graphLaw_of_polish {μ : ℕ → ProbabilityMeasure P} {μ₀ : ProbabilityMeasure P}
    (hμ : Tendsto μ atTop (𝓝 μ₀)) {Tn : ℕ → P → V} {T : P → V} (hTm : ∀ n, Measurable (Tn n))
    (hcc : ContinuouslyConverges Tn T) :
    Tendsto (fun n => graphLaw (μ n) (hTm n)) atTop
      (𝓝 (graphLaw μ₀ hcc.continuous_limit.measurable)) :=
  tendsto_graphLaw_of_continuouslyConverges hμ (tight_of_tendsto hμ) hTm hcc

end polish

end Grammar
