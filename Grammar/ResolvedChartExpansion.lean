/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.ChartStratumPieces
import Grammar.CoverAssembly

/-!
# The global weighted expansion over resolution charts

The sixth module of the resolved-space programme (`tide-log/gpt6_bigpicture_v74.md`): the
weight of a resolution chart — the indicator of the compact chart domain times the Jacobian
`|det Dφ_i|`, the normalised cover weight `ρ_i ∘ Φ_i` and a bounded target density
`c ∘ Φ_i` (typically the Boltzmann factor `e^{-N K} p`) — is a bounded measurable `TubeWeight`
(`chartWeight`), and against it the chart pullback of an observable reproduces exactly the
weighted source measure of `CoverAssembly` (`integral_chartWeight_mul`). Summing over the
charts gives the **exact resolved-chart formula**
`∫_{⋃ φ_i(dom_i)} F e^{-NK} p dx = ∑_i ∫ w_i(y) F(φ_i y) dy`
(`coverIntegral_eq_sum_chartWeight`), and stratifying each chart by coordinate size
(`ChartStratumPieces`) gives the **chart–stratum decomposition** `∑_{i,I}` with the empty
stratum kept exactly (`coverIntegral_eq_sum_chart_pieces`); on every nonempty piece the paper's
fibre hypotheses turn the term into the conditional contraction series over the coordinate
stratum (`coverIntegral_eq_sum_pieceContraction`).

Everything is chart-local: there is no glued resolution, and the strata are indexed by
chart–stratum pairs `(i, I)`; the total is cover-independent because every chart transports back
to the same target integral.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Grammar

namespace ResolutionChart

variable {d : ℕ} (C : ResolutionChart d)

/-- The real Jacobian density `|det Dφ|`. -/
noncomputable def jac (y : Fin d → ℝ) : ℝ := |(fderiv ℝ C.φ y).det|

theorem jac_nonneg (y : Fin d → ℝ) : 0 ≤ C.jac y := abs_nonneg _

theorem measurable_jac : Measurable C.jac :=
  continuous_abs.measurable.comp
    (ContinuousLinearMap.continuous_det.measurable.comp (measurable_fderiv ℝ C.φ))

theorem absDet_eq (y : Fin d → ℝ) : C.absDet y = ENNReal.ofReal (C.jac y) := rfl

theorem continuousOn_jac : ContinuousOn C.jac C.dom :=
  continuous_abs.comp_continuousOn (ContinuousLinearMap.continuous_det.comp_continuousOn
    ((C.smooth.continuousOn_fderiv_of_isOpen C.U_open le_rfl).mono C.dom_subset))

/-- The Jacobian is bounded on the compact domain. -/
theorem exists_jac_bound : ∃ B, ∀ y ∈ C.dom, C.jac y ≤ B := by
  obtain ⟨B, hB⟩ := C.dom_compact.exists_bound_of_continuousOn C.continuousOn_jac
  refine ⟨B, fun y hy => ?_⟩
  have h := hB y hy
  rwa [Real.norm_eq_abs, abs_of_nonneg (C.jac_nonneg y)] at h

/-- A nonnegative bound for the Jacobian on the domain. -/
noncomputable def jacBound : ℝ := max (Classical.choose C.exists_jac_bound) 0

theorem jacBound_nonneg : 0 ≤ C.jacBound := le_max_right _ _

theorem jac_le_jacBound {y : Fin d → ℝ} (hy : y ∈ C.dom) : C.jac y ≤ C.jacBound :=
  (Classical.choose_spec C.exists_jac_bound y hy).trans (le_max_left _ _)

end ResolutionChart

namespace TubeWeight

variable {d : ℕ}

/-- **The Boltzmann target density** `e^{-N K} p` for `N ≥ 0`, `K ≥ 0` measurable and a bounded
prior weight `p`. -/
noncomputable def boltzmann (N : ℝ) (hN : 0 ≤ N) (K : (Fin d → ℝ) → ℝ) (hK : Measurable K)
    (hK0 : ∀ x, 0 ≤ K x) (p : TubeWeight d) : TubeWeight d where
  w x := Real.exp (-N * K x) * p.w x
  measurable := (Real.measurable_exp.comp (measurable_const.mul hK)).mul p.measurable
  nonneg x := mul_nonneg (Real.exp_pos _).le (p.nonneg x)
  bound := p.bound
  le_bound x := by
    have h1 : Real.exp (-N * K x) ≤ 1 := by
      rw [Real.exp_le_one_iff, neg_mul]
      exact neg_nonpos.2 (mul_nonneg hN (hK0 x))
    calc Real.exp (-N * K x) * p.w x ≤ 1 * p.bound :=
          mul_le_mul h1 (p.le_bound x) (p.nonneg x) zero_le_one
      _ = p.bound := one_mul _

@[simp] theorem boltzmann_w (N : ℝ) (hN : 0 ≤ N) (K : (Fin d → ℝ) → ℝ) (hK : Measurable K)
    (hK0 : ∀ x, 0 ≤ K x) (p : TubeWeight d) (x : Fin d → ℝ) :
    (boltzmann N hN K hK hK0 p).w x = Real.exp (-N * K x) * p.w x := rfl

end TubeWeight

namespace ResolutionCover

variable {d : ℕ} {ι : Type*} [Fintype ι] (R : ResolutionCover d ι) (i : ι) (c : TubeWeight d)

theorem weight_nonneg (x : Fin d → ℝ) : 0 ≤ R.weight i x := coverWeight_nonneg _ _ _

theorem weight_le_one (x : Fin d → ℝ) : R.weight i x ≤ 1 := coverWeight_le_one _ _ _

/-- **The chart weight** `1_{dom_i} · |det Dφ_i| · (ρ_i ∘ Φ_i) · (c ∘ Φ_i)`: the whole density of
the resolved integrand on chart `i` apart from the observable, as a bounded tube weight. -/
noncomputable def chartWeight : TubeWeight d where
  w := (R.chart i).dom.indicator fun y =>
    (R.chart i).jac y * (R.weight i ((R.chart i).Φ y) * c.w ((R.chart i).Φ y))
  measurable := ((R.chart i).measurable_jac.mul
    (((R.measurable_weight i).comp (R.measurable_chart_Φ i)).mul
      (c.measurable.comp (R.measurable_chart_Φ i)))).indicator (R.chart i).measurableSet_dom
  nonneg y := indicator_nonneg (fun y _ => mul_nonneg ((R.chart i).jac_nonneg y)
    (mul_nonneg (R.weight_nonneg i _) (c.nonneg _))) y
  bound := (R.chart i).jacBound * c.bound
  le_bound y := by
    by_cases hy : y ∈ (R.chart i).dom
    · rw [indicator_of_mem hy]
      calc (R.chart i).jac y * (R.weight i ((R.chart i).Φ y) * c.w ((R.chart i).Φ y))
          ≤ (R.chart i).jacBound * (1 * c.bound) :=
            mul_le_mul ((R.chart i).jac_le_jacBound hy)
              (mul_le_mul (R.weight_le_one i _) (c.le_bound _) (c.nonneg _) zero_le_one)
              (mul_nonneg (R.weight_nonneg i _) (c.nonneg _)) (R.chart i).jacBound_nonneg
        _ = (R.chart i).jacBound * c.bound := by rw [one_mul]
    · rw [indicator_of_notMem hy]
      exact mul_nonneg (R.chart i).jacBound_nonneg c.bound_nonneg

theorem chartWeight_w :
    (R.chartWeight i c).w = (R.chart i).dom.indicator fun y =>
      (R.chart i).jac y * (R.weight i ((R.chart i).Φ y) * c.w ((R.chart i).Φ y)) := rfl

theorem chartWeight_w_of_mem {y : Fin d → ℝ} (hy : y ∈ (R.chart i).dom) :
    (R.chartWeight i c).w y =
      (R.chart i).jac y * (R.weight i ((R.chart i).φ y) * c.w ((R.chart i).φ y)) := by
  rw [chartWeight_w, indicator_of_mem hy, (R.chart i).Φ_eqOn hy]

theorem chartWeight_w_of_notMem {y : Fin d → ℝ} (hy : y ∉ (R.chart i).dom) :
    (R.chartWeight i c).w y = 0 := by
  rw [chartWeight_w, indicator_of_notMem hy]

/-- The density of the weighted source measure of chart `i`. -/
noncomputable def sourceDensity (y : Fin d → ℝ) : ℝ≥0∞ :=
  (R.chart i).absDet y * ENNReal.ofReal (R.weight i ((R.chart i).Φ y))

theorem sourceMeasure_eq :
    R.sourceMeasure i = (volume.restrict (R.chart i).dom).withDensity (R.sourceDensity i) := rfl

theorem measurable_sourceDensity : Measurable (R.sourceDensity i) :=
  (R.chart i).measurable_absDet.mul
    (ENNReal.measurable_ofReal.comp ((R.measurable_weight i).comp (R.measurable_chart_Φ i)))

theorem sourceDensity_lt_top (y : Fin d → ℝ) : R.sourceDensity i y < ⊤ :=
  ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

/-- **The chart weight is the source density**: pointwise, `w_i(y) F(φ_i y)` is the indicator of the
domain times the real source density times `(F · c)(Φ_i y)`. -/
theorem chartWeight_mul_eq (F : (Fin d → ℝ) → ℝ) (y : Fin d → ℝ) :
    (R.chartWeight i c).w y * F ((R.chart i).φ y) =
      (R.chart i).dom.indicator
        (fun y => (R.sourceDensity i y).toReal • (F ((R.chart i).Φ y) * c.w ((R.chart i).Φ y)))
        y := by
  by_cases hy : y ∈ (R.chart i).dom
  · rw [indicator_of_mem hy, R.chartWeight_w_of_mem i c hy, smul_eq_mul, sourceDensity,
      (R.chart i).absDet_eq, ENNReal.toReal_mul, ENNReal.toReal_ofReal ((R.chart i).jac_nonneg y),
      ENNReal.toReal_ofReal (R.weight_nonneg i _), (R.chart i).Φ_eqOn hy]
    ring
  · rw [indicator_of_notMem hy, R.chartWeight_w_of_notMem i c hy, zero_mul]

/-- **The chart weight realises the weighted source measure**: for every observable `F`,
`∫ w_i(y) F(φ_i y) dy = ∫ (F · c)(Φ_i y) dμ_i(y)` with `μ_i` the source measure of
`CoverAssembly`. -/
theorem integral_chartWeight_mul (F : (Fin d → ℝ) → ℝ) :
    ∫ y, (R.chartWeight i c).w y * F ((R.chart i).φ y) =
      ∫ y, F ((R.chart i).Φ y) * c.w ((R.chart i).Φ y) ∂(R.sourceMeasure i) := by
  rw [R.sourceMeasure_eq,
    integral_withDensity_eq_integral_toReal_smul (R.measurable_sourceDensity i)
      (Filter.Eventually.of_forall fun y => R.sourceDensity_lt_top i y),
    ← integral_indicator (R.chart i).measurableSet_dom]
  exact integral_congr_ae (Filter.Eventually.of_forall fun y => R.chartWeight_mul_eq i c F y)

/-- Integrability of `F · c` on the union of the chart images gives integrability of the weighted
chart pullback. -/
theorem integrable_chartWeight_mul {F : (Fin d → ℝ) → ℝ} (hFm : Measurable F)
    (hint : Integrable (fun x => F x * c.w x) (volume.restrict (⋃ i, R.image i))) :
    Integrable fun y => (R.chartWeight i c).w y * F ((R.chart i).φ y) := by
  have h := R.integrable_pullback (hFm.mul c.measurable) hint i
  rw [R.sourceMeasure_eq, integrable_withDensity_iff_integrable_smul' (R.measurable_sourceDensity i)
    (Filter.Eventually.of_forall fun y => R.sourceDensity_lt_top i y)] at h
  have h' := (integrable_indicator_iff (R.chart i).measurableSet_dom).2 h
  exact h'.congr (Filter.Eventually.of_forall fun y => (R.chartWeight_mul_eq i c F y).symm)

/-- **The exact resolved-chart formula** for a bounded target density `c`:
`∫_{⋃ φ_i(dom_i)} F c dx = ∑_i ∫ w_i(y) F(φ_i y) dy`. -/
theorem integral_union_eq_sum_chartWeight {F : (Fin d → ℝ) → ℝ} (hFm : Measurable F)
    (hint : Integrable (fun x => F x * c.w x) (volume.restrict (⋃ i, R.image i))) :
    ∫ x in ⋃ i, R.image i, F x * c.w x =
      ∑ i, ∫ y, (R.chartWeight i c).w y * F ((R.chart i).φ y) := by
  have hGm : Measurable fun x => F x * c.w x := hFm.mul c.measurable
  have hint' : Integrable (fun x => F x * c.w x) (∑ i, (R.sourceMeasure i).map (R.chart i).Φ) := by
    rwa [R.sum_map_eq]
  rw [← R.sum_map_eq, integral_finsetSum_measure fun i _ =>
    integrable_finsetSum_measure.1 hint' i (Finset.mem_univ i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_map (R.measurable_chart_Φ i).aemeasurable hGm.aestronglyMeasurable,
    R.integral_chartWeight_mul]

section Boltzmann

variable (N : ℝ) (hN : 0 ≤ N) (K : (Fin d → ℝ) → ℝ) (hK : Measurable K) (hK0 : ∀ x, 0 ≤ K x)
  (p : TubeWeight d)

/-- **The exact resolved-chart formula for the Boltzmann integral**:
`∫_{⋃ φ_i(dom_i)} F e^{-NK} p dx = ∑_i ∫ w_i(y) F(φ_i y) dy` with the Boltzmann chart weights
`w_i = 1_{dom_i} |det Dφ_i| (ρ_i ∘ Φ_i) (e^{-NK} p) ∘ Φ_i`. -/
theorem coverIntegral_eq_sum_chartWeight {F : (Fin d → ℝ) → ℝ} (hFm : Measurable F)
    (hint : Integrable (fun x => F x * p.w x * Real.exp (-N * K x))
      (volume.restrict (⋃ i, R.image i))) :
    R.coverIntegral (fun x => F x * p.w x) (fun x => -N * K x) =
      ∑ i, ∫ y, (R.chartWeight i (TubeWeight.boltzmann N hN K hK hK0 p)).w y
        * F ((R.chart i).φ y) := by
  have hfun : (fun x => F x * p.w x * Real.exp (-N * K x)) =
      fun x => F x * (TubeWeight.boltzmann N hN K hK hK0 p).w x := by
    funext x
    rw [TubeWeight.boltzmann_w]
    ring
  unfold coverIntegral
  rw [← R.integral_union_eq_sum_chartWeight _ hFm (hfun ▸ hint)]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => congrFun hfun x)

/-- **The chart–stratum decomposition of the resolved integral**: exactly, over the charts `i` and
the coordinate-size strata `I ⊆ D i` of each chart, with the empty stratum kept as a separate
exact term. -/
theorem coverIntegral_eq_sum_chart_pieces (D : ι → Finset (Fin d)) (ε : ℝ)
    {F : (Fin d → ℝ) → ℝ} (hFm : Measurable F)
    (hint : Integrable (fun x => F x * p.w x * Real.exp (-N * K x))
      (volume.restrict (⋃ i, R.image i))) :
    R.coverIntegral (fun x => F x * p.w x) (fun x => -N * K x) =
      ∑ i, ((∑ I ∈ (D i).powerset.filter (fun I => I.Nonempty),
          ∫ y in sizePiece (D i) ε I,
            (R.chartWeight i (TubeWeight.boltzmann N hN K hK hK0 p)).w y * F ((R.chart i).φ y)) +
        ∫ y in sizePiece (D i) ε ∅,
          (R.chartWeight i (TubeWeight.boltzmann N hN K hK hK0 p)).w y * F ((R.chart i).φ y)) := by
  rw [R.coverIntegral_eq_sum_chartWeight N hN K hK hK0 p hFm hint]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine integral_eq_sum_pieces_nonempty_add (D i) (ε := ε) _ (F := fun y => F ((R.chart i).φ y))
    ?_
  refine R.integrable_chartWeight_mul i _ hFm ?_
  refine hint.congr (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  rw [TubeWeight.boltzmann_w]
  ring

end Boltzmann

end ResolutionCover

section PieceContraction

variable {d : ℕ} (D : Finset (Fin d)) {ε : ℝ} (hε : 0 < ε) (wt : TubeWeight d)

/-- **The per chart–stratum contraction term**: on a nonempty stratum `I` the conditional
contraction series of the coordinate stratum `P_I` evaluated at the foot of `y`; zero on the empty
stratum (which is kept as an exact remainder). -/
noncomputable def pieceContraction (G : (Fin d → ℝ) → ℝ) (I : Finset (Fin d)) (y : Fin d → ℝ) :
    ℝ :=
  if hne : I.Nonempty then
    condContractionSeries (stratumTube hε I hne) (stratumChart I hne) wt G
      (planeFoot (stratumSplit I hne) y)
  else 0

theorem pieceContraction_of_nonempty (G : (Fin d → ℝ) → ℝ) {I : Finset (Fin d)}
    (hne : I.Nonempty) (y : Fin d → ℝ) :
    pieceContraction hε wt G I y =
      condContractionSeries (stratumTube hε I hne) (stratumChart I hne) wt G
        (planeFoot (stratumSplit I hne) y) := by
  unfold pieceContraction
  rw [dif_pos hne]

end PieceContraction

namespace ResolutionCover

variable {d : ℕ} {ι : Type*} [Fintype ι] (R : ResolutionCover d ι)
  (N : ℝ) (hN : 0 ≤ N) (K : (Fin d → ℝ) → ℝ) (hK : Measurable K) (hK0 : ∀ x, 0 ≤ K x)
  (p : TubeWeight d)

/-- **The global weighted expansion over charts and strata**: under the paper's fibre power-series
hypotheses for the pulled-back observable `F ∘ φ_i` on every nonempty chart–stratum piece
(with the Boltzmann chart weight in the fibre measures), the resolved Boltzmann integral is the sum
over chart–stratum pairs `(i, I)` of the weighted conditional contraction series over the coordinate
stratum `P_I`, plus the exact contribution of the pieces away from the divisor. -/
theorem coverIntegral_eq_sum_pieceContraction (D : ι → Finset (Fin d)) {ε : ℝ} (hε : 0 < ε)
    {F : (Fin d → ℝ) → ℝ} (hFm : Measurable F)
    (hint : Integrable (fun x => F x * p.w x * Real.exp (-N * K x))
      (volume.restrict (⋃ i, R.image i)))
    (q : ι → ∀ I : Finset (Fin d), I.Nonempty →
      (Fin (d - (I.card - 1 + 1)) → ℝ) → FormalMultilinearSeries ℝ (Fin (I.card - 1 + 1) → ℝ) ℝ)
    (Rad : ι → ∀ I : Finset (Fin d), I.Nonempty → (Fin (d - (I.card - 1 + 1)) → ℝ) → ℝ≥0∞)
    (hq : ∀ i I (hne : I.Nonempty), I ⊆ D i → ∀ z, HasFPowerSeriesOnBall
      (fun n => F ((R.chart i).φ (planeSplit (stratumSplit I hne) (z, n)))) (q i I hne z) 0
      (Rad i I hne z))
    (hη : ∀ i I (hne : I.Nonempty), I ⊆ D i → ∀ z, ∀ᵐ n ∂fibreMeasure volume
      (tubeDensity (stratumTube hε I hne) (stratumChart I hne)
        (R.chartWeight i (TubeWeight.boltzmann N hN K hK hK0 p))) z,
      n ∈ Metric.eball (0 : Fin (I.card - 1 + 1) → ℝ) (Rad i I hne z))
    (hdom : ∀ i I (hne : I.Nonempty), I ⊆ D i → ∀ z, Summable fun k =>
      ‖q i I hne z k‖ * ∫ n, ‖n‖ ^ k ∂fibreMeasure volume
        (tubeDensity (stratumTube hε I hne) (stratumChart I hne)
          (R.chartWeight i (TubeWeight.boltzmann N hN K hK hK0 p))) z) :
    R.coverIntegral (fun x => F x * p.w x) (fun x => -N * K x) =
      ∑ i, ((∑ I ∈ (D i).powerset.filter (fun I => I.Nonempty),
          ∫ y in sizePiece (D i) ε I,
            (R.chartWeight i (TubeWeight.boltzmann N hN K hK hK0 p)).w y *
              pieceContraction hε (R.chartWeight i (TubeWeight.boltzmann N hN K hK hK0 p))
                (fun y => F ((R.chart i).φ y)) I y) +
        ∫ y in sizePiece (D i) ε ∅,
          (R.chartWeight i (TubeWeight.boltzmann N hN K hK hK0 p)).w y * F ((R.chart i).φ y)) := by
  rw [R.coverIntegral_eq_sum_chart_pieces N hN K hK hK0 p D ε hFm hint]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun I hI => ?_
  obtain ⟨hIpow, hne⟩ := Finset.mem_filter.1 hI
  have hID : I ⊆ D i := Finset.mem_powerset.1 hIpow
  have hFi : Integrable fun y =>
      (R.chartWeight i (TubeWeight.boltzmann N hN K hK hK0 p)).w y * F ((R.chart i).φ y) := by
    refine R.integrable_chartWeight_mul i _ hFm ?_
    refine hint.congr (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    rw [TubeWeight.boltzmann_w]
    ring
  rw [integral_sizePiece_eq_integral_condContraction (D i) hε I hID hne _
    (F := fun y => F ((R.chart i).φ y)) hFi.integrableOn (hq i I hne hID) (hη i I hne hID)
    (hdom i I hne hID)]
  refine setIntegral_congr_fun (measurableSet_sizePiece (D i) ε I) fun y _ => ?_
  rw [pieceContraction_of_nonempty hε _ _ hne]

end ResolutionCover

end Grammar
