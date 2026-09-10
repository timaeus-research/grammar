import Grammar.ResolutionTransport
import Grammar.EmpiricalExpGap

/-!
# Cover assembly modulo a positive-gap remainder

For a finite resolution cover `R` (charts `Φᵢ` with compact domains, exceptional sets null), the
assembled transport `∑ᵢ Φᵢ*(|det Dφᵢ| (ρᵢ∘Φᵢ) dy|_{domᵢ}) = dx|_{⋃ images}` (CXXIV) turns the
Laplace integral over the union of the chart images into the exact sum of the chart pullbacks
(`ResolutionCover.coverIntegral_eq_sum`). Splitting each chart domain into a *core* (a measurable
piece, in applications the box around the divisor carrying the standard form) and the *gap*
`domᵢ \ coreᵢ` on which the phase is bounded below by `κ > 0`, the gap contributions are
exponentially small:

`Z(N) = ∑ᵢ Z^{core}ᵢ(N) + Rem(N)`, `‖Rem(N)‖ ≤ e^{−Nκ} ∑ᵢ ∫_{domᵢ∖coreᵢ} |F∘Φᵢ|`

(`ResolutionCover.coverIntegral_core_assembly`), and likewise for the empirical phase
`−Nφ² + √N φ ξ` under the fluctuation bound `sup|ξ| ≤ ½√(Nκ)` on the gaps, with rate `e^{−Nκ/2}`
(`ResolutionCover.coverIntegral_core_assembly_empirical`).

The core terms are integrals of the pulled-back integrand against the weighted source measure
`|det Dφᵢ| (ρᵢ∘Φᵢ) dy`; feeding them into the standard-integral theorems requires the chart to be
a weighted box in adapted coordinates with certified analytic data — that is the certificate
interface (CXXXVII), not something this file claims. Non-claims: no analytic partition of unity
(the weights `ρᵢ` are normalised indicators), no control of overlaps beyond the exact transport,
no statement for an arbitrary analytic `ResolutionCover`.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

namespace ResolutionCover

variable {d : ℕ} {ι : Type*} [Fintype ι] (R : ResolutionCover d ι)

/-- The integral of `F e^{E}` over the union of the chart images. -/
noncomputable def coverIntegral (F E : (Fin d → ℝ) → ℝ) : ℝ :=
  ∫ x in ⋃ i, R.image i, F x * Real.exp (E x)

/-- The pullback of `F e^{E}` to chart `i`, against the weighted source measure, over `S`. -/
noncomputable def chartIntegral (F E : (Fin d → ℝ) → ℝ) (i : ι) (S : Set (Fin d → ℝ)) : ℝ :=
  ∫ y in S, F ((R.chart i).Φ y) * Real.exp (E ((R.chart i).Φ y)) ∂R.sourceMeasure i

theorem measurable_chart_Φ (i : ι) : Measurable (R.chart i).Φ := (R.chart i).measurable_Φ

/-- A function integrable on the union of the images pulls back to an integrable function against
each weighted source measure. -/
theorem integrable_pullback {G : (Fin d → ℝ) → ℝ} (hGm : Measurable G)
    (hint : Integrable G (volume.restrict (⋃ i, R.image i))) (i : ι) :
    Integrable (fun y => G ((R.chart i).Φ y)) (R.sourceMeasure i) := by
  have hint' : Integrable G (∑ i, (R.sourceMeasure i).map (R.chart i).Φ) := by
    rwa [R.sum_map_eq]
  have h := integrable_finsetSum_measure.1 hint' i (Finset.mem_univ i)
  exact (integrable_map_measure hGm.aestronglyMeasurable
    (R.measurable_chart_Φ i).aemeasurable).1 h

/-- **Exact chart decomposition**: the integral over the union of the chart images is the sum of
the chart pullbacks against the weighted source measures. -/
theorem coverIntegral_eq_sum (F E : (Fin d → ℝ) → ℝ) (hFm : Measurable F) (hEm : Measurable E)
    (hint : Integrable (fun x => F x * Real.exp (E x)) (volume.restrict (⋃ i, R.image i))) :
    R.coverIntegral F E = ∑ i, R.chartIntegral F E i univ := by
  have hGm : Measurable fun x => F x * Real.exp (E x) := hFm.mul (Real.measurable_exp.comp hEm)
  have hint' : Integrable (fun x => F x * Real.exp (E x))
      (∑ i, (R.sourceMeasure i).map (R.chart i).Φ) := by
    rwa [R.sum_map_eq]
  unfold coverIntegral chartIntegral
  rw [← R.sum_map_eq, integral_finsetSum_measure fun i _ =>
    integrable_finsetSum_measure.1 hint' i (Finset.mem_univ i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Measure.restrict_univ,
    integral_map (R.measurable_chart_Φ i).aemeasurable hGm.aestronglyMeasurable]

/-- The chart integral splits over a measurable core and its complement. -/
theorem chartIntegral_univ_eq_add (F E : (Fin d → ℝ) → ℝ) (hFm : Measurable F)
    (hEm : Measurable E)
    (hint : Integrable (fun x => F x * Real.exp (E x)) (volume.restrict (⋃ i, R.image i))) (i : ι)
    {core : Set (Fin d → ℝ)} (hcore : MeasurableSet core) :
    R.chartIntegral F E i univ = R.chartIntegral F E i core + R.chartIntegral F E i coreᶜ := by
  have hGm : Measurable fun x => F x * Real.exp (E x) := hFm.mul (Real.measurable_exp.comp hEm)
  unfold chartIntegral
  rw [Measure.restrict_univ, ← integral_add_compl hcore (R.integrable_pullback hGm hint i)]

theorem sourceMeasure_compl_dom (i : ι) : R.sourceMeasure i (R.chart i).domᶜ = 0 := by
  unfold sourceMeasure
  rw [withDensity_apply _ (R.chart i).dom_compact.isClosed.measurableSet.compl,
    Measure.restrict_restrict (R.chart i).dom_compact.isClosed.measurableSet.compl,
    compl_inter_self, Measure.restrict_empty, lintegral_zero_measure]

/-- Off the chart domain the source measure vanishes, so the complement of the core may be
replaced by the gap `domᵢ \ coreᵢ`. -/
theorem chartIntegral_compl_eq (F E : (Fin d → ℝ) → ℝ) (i : ι) (core : Set (Fin d → ℝ)) :
    R.chartIntegral F E i coreᶜ = R.chartIntegral F E i ((R.chart i).dom \ core) := by
  unfold chartIntegral
  refine setIntegral_congr_set (ae_eq_set.2 ⟨?_, ?_⟩)
  · refine measure_mono_null (fun y hy => ?_) (R.sourceMeasure_compl_dom i)
    intro hdom
    exact hy.2 ⟨hdom, hy.1⟩
  · rw [show ((R.chart i).dom \ core) \ coreᶜ = ∅ from
      eq_empty_of_forall_notMem fun y hy => hy.2 hy.1.2]
    exact measure_empty

/-! ### The positive-gap remainder, population phase -/

/-- **Gap bound for one chart** (population phase): if `κ ≤ K∘Φᵢ` on the gap, the gap contribution
is at most `e^{−Nκ} ∫_{gap} |F∘Φᵢ|`. -/
theorem norm_chartIntegral_gap_le (F K : (Fin d → ℝ) → ℝ) (hFm : Measurable F) (hK : Measurable K)
    (hF : Integrable F (volume.restrict (⋃ i, R.image i))) (i : ι) {core : Set (Fin d → ℝ)}
    (hcore : MeasurableSet core) {κ N : ℝ} (hN : 0 ≤ N)
    (hgap : ∀ y ∈ (R.chart i).dom \ core, κ ≤ K ((R.chart i).Φ y)) :
    ‖R.chartIntegral F (fun x => -N * K x) i coreᶜ‖ ≤
      Real.exp (-(N * κ)) *
        ∫ y in (R.chart i).dom \ core, |F ((R.chart i).Φ y)| ∂R.sourceMeasure i := by
  rw [R.chartIntegral_compl_eq]
  unfold chartIntegral
  have hS : MeasurableSet ((R.chart i).dom \ core) :=
    (R.chart i).dom_compact.isClosed.measurableSet.diff hcore
  have hFi := R.integrable_pullback hFm hF i
  have h := norm_setIntegral_exp_gap_le (μ := R.sourceMeasure i) ((R.chart i).dom \ core) hS
    (fun y => F ((R.chart i).Φ y)) (fun y => |F ((R.chart i).Φ y)|) (fun y => K ((R.chart i).Φ y))
    1 N κ (by rw [one_mul]; exact hN) hFi.aestronglyMeasurable.restrict
    ((hK.comp (R.measurable_chart_Φ i)).aestronglyMeasurable) hFi.abs.integrableOn
    (fun y _ => le_of_eq (Real.norm_eq_abs _)) hgap
  simpa only [one_mul, neg_mul] using h

/-- **Cover assembly modulo a positive-gap remainder** (population phase). With measurable cores
`coreᵢ` and `κ ≤ K∘Φᵢ` on the gaps `domᵢ \ coreᵢ`:
`Z(N) = ∑ᵢ Zᵢ^{core}(N) + Rem(N)` with `‖Rem(N)‖ ≤ e^{−Nκ} ∑ᵢ ∫_{domᵢ∖coreᵢ} |F∘Φᵢ|`. -/
theorem coverIntegral_core_assembly (F K : (Fin d → ℝ) → ℝ) (hFm : Measurable F)
    (hK : Measurable K) (hK0 : ∀ x, 0 ≤ K x) (hF : Integrable F (volume.restrict (⋃ i, R.image i)))
    {N : ℝ} (hN : 0 ≤ N) (core : ι → Set (Fin d → ℝ)) (hcore : ∀ i, MeasurableSet (core i)) {κ : ℝ}
    (hgap : ∀ i, ∀ y ∈ (R.chart i).dom \ core i, κ ≤ K ((R.chart i).Φ y)) :
    R.coverIntegral F (fun x => -N * K x) =
        ∑ i, R.chartIntegral F (fun x => -N * K x) i (core i) +
          ∑ i, R.chartIntegral F (fun x => -N * K x) i (core i)ᶜ ∧
      ‖∑ i, R.chartIntegral F (fun x => -N * K x) i (core i)ᶜ‖ ≤
        Real.exp (-(N * κ)) *
          ∑ i, ∫ y in (R.chart i).dom \ core i, |F ((R.chart i).Φ y)| ∂R.sourceMeasure i := by
  have hEm : Measurable fun x => -N * K x := measurable_const.mul hK
  have hint : Integrable (fun x => F x * Real.exp (-N * K x))
      (volume.restrict (⋃ i, R.image i)) := by
    refine hF.norm.mono' (hFm.mul (Real.measurable_exp.comp hEm)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_mul, Real.norm_eq_abs (Real.exp _), abs_of_pos (Real.exp_pos _)]
    refine mul_le_of_le_one_right (norm_nonneg (F x)) (Real.exp_le_one_iff.2 ?_)
    have := mul_nonneg hN (hK0 x)
    linarith
  refine ⟨?_, ?_⟩
  · rw [R.coverIntegral_eq_sum F _ hFm hEm hint, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => R.chartIntegral_univ_eq_add F _ hFm hEm hint i (hcore i)
  · refine le_trans (norm_sum_le Finset.univ fun i =>
      R.chartIntegral F (fun x => -N * K x) i (core i)ᶜ) ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ =>
      R.norm_chartIntegral_gap_le F K hFm hK hF i (hcore i) hN (hgap i)

/-! ### The positive-gap remainder, empirical phase -/

/-- **Gap bound for one chart** (empirical phase): on the gap, `κ ≤ (φ∘Φᵢ)²` and `|ξ∘Φᵢ| ≤ B`
with `2B ≤ √(Nκ)` give the rate `e^{−Nκ/2}`. -/
theorem norm_chartIntegral_gap_le_empirical (F φ ξ : (Fin d → ℝ) → ℝ) (hFm : Measurable F)
    (hφ : Measurable φ) (hξ : Measurable ξ) (hF : Integrable F (volume.restrict (⋃ i, R.image i)))
    (i : ι) {core : Set (Fin d → ℝ)} (hcore : MeasurableSet core) {κ N B : ℝ} (hN : 0 < N)
    (hgap : ∀ y ∈ (R.chart i).dom \ core, κ ≤ φ ((R.chart i).Φ y) ^ 2)
    (hfl : ∀ y ∈ (R.chart i).dom \ core, |ξ ((R.chart i).Φ y)| ≤ B)
    (hB : 2 * B ≤ Real.sqrt (N * κ)) :
    ‖R.chartIntegral F (fun x => -N * φ x ^ 2 + Real.sqrt N * φ x * ξ x) i coreᶜ‖ ≤
      Real.exp (-(N * (κ / 2))) *
        ∫ y in (R.chart i).dom \ core, |F ((R.chart i).Φ y)| ∂R.sourceMeasure i := by
  rw [R.chartIntegral_compl_eq]
  unfold chartIntegral
  have hS : MeasurableSet ((R.chart i).dom \ core) :=
    (R.chart i).dom_compact.isClosed.measurableSet.diff hcore
  have hFi := R.integrable_pullback hFm hF i
  have h := norm_setIntegral_empirical_exp_gap_le (μ := R.sourceMeasure i)
    ((R.chart i).dom \ core) hS (fun y => F ((R.chart i).Φ y)) (fun y => |F ((R.chart i).Φ y)|)
    (fun y => φ ((R.chart i).Φ y)) (fun y => ξ ((R.chart i).Φ y)) 1 N κ B zero_le_one hN
    hFi.aestronglyMeasurable.restrict ((hφ.comp (R.measurable_chart_Φ i)).aestronglyMeasurable)
    ((hξ.comp (R.measurable_chart_Φ i)).aestronglyMeasurable) hFi.abs.integrableOn
    (fun y _ => le_of_eq (Real.norm_eq_abs _)) hgap hfl hB
  simpa only [one_mul, neg_mul] using h

/-- **Cover assembly modulo a positive-gap remainder** (empirical phase). -/
theorem coverIntegral_core_assembly_empirical (F φ ξ : (Fin d → ℝ) → ℝ) (hFm : Measurable F)
    (hφ : Measurable φ) (hξ : Measurable ξ) (hF : Integrable F (volume.restrict (⋃ i, R.image i)))
    {N : ℝ} (hN : 0 < N)
    (hint : Integrable (fun x => F x * Real.exp (-N * φ x ^ 2 + Real.sqrt N * φ x * ξ x))
      (volume.restrict (⋃ i, R.image i)))
    (core : ι → Set (Fin d → ℝ)) (hcore : ∀ i, MeasurableSet (core i)) {κ B : ℝ}
    (hgap : ∀ i, ∀ y ∈ (R.chart i).dom \ core i, κ ≤ φ ((R.chart i).Φ y) ^ 2)
    (hfl : ∀ i, ∀ y ∈ (R.chart i).dom \ core i, |ξ ((R.chart i).Φ y)| ≤ B)
    (hB : 2 * B ≤ Real.sqrt (N * κ)) :
    R.coverIntegral F (fun x => -N * φ x ^ 2 + Real.sqrt N * φ x * ξ x) =
        ∑ i, R.chartIntegral F (fun x => -N * φ x ^ 2 + Real.sqrt N * φ x * ξ x) i (core i) +
          ∑ i, R.chartIntegral F (fun x => -N * φ x ^ 2 + Real.sqrt N * φ x * ξ x) i (core i)ᶜ ∧
      ‖∑ i, R.chartIntegral F (fun x => -N * φ x ^ 2 + Real.sqrt N * φ x * ξ x) i (core i)ᶜ‖ ≤
        Real.exp (-(N * (κ / 2))) *
          ∑ i, ∫ y in (R.chart i).dom \ core i, |F ((R.chart i).Φ y)| ∂R.sourceMeasure i := by
  have hEm : Measurable fun x => -N * φ x ^ 2 + Real.sqrt N * φ x * ξ x :=
    (measurable_const.mul (hφ.pow_const 2)).add ((measurable_const.mul hφ).mul hξ)
  refine ⟨?_, ?_⟩
  · rw [R.coverIntegral_eq_sum F _ hFm hEm hint, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => R.chartIntegral_univ_eq_add F _ hFm hEm hint i (hcore i)
  · refine le_trans (norm_sum_le Finset.univ fun i =>
      R.chartIntegral F (fun x => -N * φ x ^ 2 + Real.sqrt N * φ x * ξ x) i (core i)ᶜ) ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ =>
      R.norm_chartIntegral_gap_le_empirical F φ ξ hFm hφ hξ hF i (hcore i) hN (hgap i) (hfl i) hB

end ResolutionCover

end Grammar
