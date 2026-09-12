/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.PartitionAssembly
import Grammar.GlobalExponentBound

/-!
# Consequences of a positive leading term (CCLXVI)

From a leading-term certificate `Z(N)/(N^{−λ}(log N)^k) → c` with `c > 0` (equivalently
`Z ~ c N^{−λ}(log N)^k`), proved once for the generic interface:

* **two-sided bounds**: eventually `c/2 · N^{−λ}(log N)^k ≤ Z(N) ≤ 2c · N^{−λ}(log N)^k`
  (`HasLeadingTerm.eventually_between`), hence `Z = Θ(N^{−λ}(log N)^k)` (`HasLeadingTerm.isTheta`);
* **the free energy with its constant**:
  `−log Z(N) − (λ log N − k log log N) → −log c` (`HasLeadingTerm.tendsto_neg_log`), so
  `−log Z(N) = λ log N − k log log N − log c + o(1)`, in particular `= λ log N − k log log N + O(1)`
  (`HasLeadingTerm.freeEnergy_isBigO`).

Thin wrappers state the free-energy limit for the three cover theorems: the scalar product-chart
theorem (CCXLV), the variable-unit product-chart theorem (CCLX) and the supplied-partition theorem
(CCLXV). These are consequences of the leading equivalent — not a subleading expansion and not a
remainder rate.
-/

open MeasureTheory Set Filter Topology Asymptotics

namespace Grammar

section Generic

variable {Z : ℝ → ℝ} {c lam : ℝ} {k : ℕ}

/-- **Two-sided bounds** from a positive leading term: eventually `c/2 · scale ≤ Z ≤ 2c · scale`. -/
theorem HasLeadingTerm.eventually_between (h : HasLeadingTerm Z c lam k) (hc : 0 < c) :
    ∀ᶠ N in atTop, c / 2 * powLogScale lam k N ≤ Z N ∧ Z N ≤ 2 * c * powLogScale lam k N := by
  have hlo : ∀ᶠ N in atTop, c / 2 < Z N / powLogScale lam k N :=
    h.eventually (eventually_gt_nhds (by linarith))
  have hhi : ∀ᶠ N in atTop, Z N / powLogScale lam k N < 2 * c :=
    h.eventually (eventually_lt_nhds (by linarith))
  filter_upwards [hlo, hhi, eventually_gt_atTop 1] with N h1 h2 hN
  have hP := powLogScale_pos lam k hN
  constructor
  · have := (lt_div_iff₀ hP).1 h1
    linarith
  · have := (div_lt_iff₀ hP).1 h2
    linarith

/-- **`Θ`-comparison** from a positive leading term. -/
theorem HasLeadingTerm.isTheta (h : HasLeadingTerm Z c lam k) (hc : 0 < c) :
    Z =Θ[atTop] powLogScale lam k := by
  have hb := h.eventually_between hc
  constructor
  · refine IsBigO.of_bound (2 * c) ?_
    filter_upwards [hb, eventually_gt_atTop 1] with N hN hN1
    have hP := powLogScale_pos lam k hN1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hP,
      abs_of_pos (lt_of_lt_of_le (by positivity) hN.1)]
    exact hN.2
  · refine IsBigO.of_bound (2 / c) ?_
    filter_upwards [hb, eventually_gt_atTop 1] with N hN hN1
    have hP := powLogScale_pos lam k hN1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hP,
      abs_of_pos (lt_of_lt_of_le (by positivity) hN.1)]
    have : powLogScale lam k N = 2 / c * (c / 2 * powLogScale lam k N) := by
      field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left hN.1 (by positivity)

/-- **The free energy with its constant**: `−log Z(N) − (λ log N − k log log N) → −log c`. -/
theorem HasLeadingTerm.tendsto_neg_log (h : HasLeadingTerm Z c lam k) (hc : 0 < c) :
    Tendsto (fun N => -Real.log (Z N) - (lam * Real.log N - k * Real.log (Real.log N))) atTop
      (𝓝 (-Real.log c)) := by
  have hlog : Tendsto (fun N => -Real.log (Z N / powLogScale lam k N)) atTop (𝓝 (-Real.log c)) :=
    (Tendsto.log h hc.ne').neg
  refine hlog.congr' ?_
  filter_upwards [h.eventually_pos hc, eventually_gt_atTop 1] with N hZ hN
  rw [Real.log_div hZ.ne' (powLogScale_pos lam k hN).ne', log_powLogScale lam k hN]
  ring

/-- **The free energy asymptotic** `−log Z(N) = λ log N − k log log N + O(1)` from a positive
leading term. -/
theorem HasLeadingTerm.freeEnergy_isBigO (h : HasLeadingTerm Z c lam k) (hc : 0 < c) :
    (fun N => -Real.log (Z N) - (lam * Real.log N - k * Real.log (Real.log N))) =O[atTop]
      fun _ : ℝ => (1 : ℝ) :=
  (h.tendsto_neg_log hc).isBigO_one ℝ

end Generic

/-! ### Wrappers for the cover theorems -/

namespace ResolutionCover

variable {d : ℕ} {ι : Type*} [Fintype ι] (R : ResolutionCover d ι) {K : (Fin d → ℝ) → ℝ}

section Scalar

variable (Ps : ∀ i, ProductMonomialChart R i K) (hK0 : ∀ x, 0 ≤ K x) {ε : ℝ} (hε : 0 < ε)
  (hεb : ∀ i, ε ≤ (Ps i).b) {F : (Fin d → ℝ) → ℝ} {p : TubeWeight d}
  (hFc : ∀ i, ContinuousOn (fun y => F ((R.chart i).φ y)) (Ps i).W)
  (hpc : ∀ i, ContinuousOn (fun y => p.w ((R.chart i).φ y)) (Ps i).W) (hFm : Measurable F)
  (hF : Integrable (fun x => F x * p.w x) (volume.restrict (⋃ i, R.image i))) (hK : Measurable K)

include hK0 hε hεb hFc hpc hFm hF hK in
/-- **The free energy of a cover of product charts** (normal-independent units):
`−log Z_N[F] − (λ* log N − k* log log N) → −log c`. -/
theorem tendsto_freeEnergy_of_productCharts_extremal (hact : (R.activeCoords Ps).Nonempty)
    (hF0 : ∀ x, 0 ≤ F x) (hp0 : ∀ x, 0 ≤ p.w x) (hr0 : ∀ i x, 0 ≤ (Ps i).r x) (i₀ : ι)
    (I₀ : Finset (Fin d)) (hI₀ : I₀ ⊆ (Ps i₀).e.support) (hne₀ : I₀.Nonempty)
    (hall : ∀ j ∈ I₀, (Ps i₀).ratio j = R.coverLam Ps hact)
    (hdeg : I₀.card - 1 = R.coverDeg Ps hact)
    (hpos : 0 < volume ((Ps i₀).dominantFace (fun i => (Ps i).e.support) ε I₀ hne₀ F p)) :
    Tendsto (fun N => -Real.log (R.boltzmannIntegral F K p N) -
        (R.coverLam Ps hact * Real.log N - R.coverDeg Ps hact * Real.log (Real.log N))) atTop
      (𝓝 (-Real.log (R.productCoeffD Ps hK0 hε hεb hFc hpc hFm hF hK (R.coverLam Ps hact)
        (R.coverDeg Ps hact)))) :=
  (R.hasLeadingTerm_boltzmannIntegral_of_productChartsD_extremal Ps hK0 hε hεb hpc hK hFc hFm hF
    hact).tendsto_neg_log
    (R.boltzmannIntegral_isEquivalent_of_productCharts_extremal Ps hK0 hε hεb hFc hpc hFm hF hK
      hact hF0 hp0 hr0 i₀ I₀ hI₀ hne₀ hall hdeg hpos).1

end Scalar

section Var

variable (Ps : ∀ i, ProductMonomialChartVar R i K) (hK0 : ∀ x, 0 ≤ K x) {ε : ℝ} (hε : 0 < ε)
  (hεb : ∀ i, ε ≤ (Ps i).b) {F : (Fin d → ℝ) → ℝ} {p : TubeWeight d}
  (hFc : ∀ i, ContinuousOn (fun y => F ((R.chart i).φ y)) (Ps i).W)
  (hpc : ∀ i, ContinuousOn (fun y => p.w ((R.chart i).φ y)) (Ps i).W) (hFm : Measurable F)
  (hF : Integrable (fun x => F x * p.w x) (volume.restrict (⋃ i, R.image i))) (hK : Measurable K)

include hK0 hε hεb hFc hpc hFm hF hK in
/-- **The free energy of a cover of product charts with normal-dependent units.** -/
theorem tendsto_freeEnergy_of_productChartsV_extremal (hact : (R.activeCoordsV Ps).Nonempty)
    (hF0 : ∀ x, 0 ≤ F x) (hp0 : ∀ x, 0 ≤ p.w x) (hr0 : ∀ i x, 0 ≤ (Ps i).r x) (i₀ : ι)
    (I₀ : Finset (Fin d)) (hI₀ : I₀ ⊆ (Ps i₀).e.support) (hne₀ : I₀.Nonempty)
    (hall : ∀ j ∈ I₀, (Ps i₀).ratio j = R.coverLamV Ps hact)
    (hdeg : I₀.card - 1 = R.coverDegV Ps hact)
    (hpos : 0 < volume ((Ps i₀).dominantFace (fun i => (Ps i).e.support) ε I₀ hne₀ F p)) :
    Tendsto (fun N => -Real.log (R.boltzmannIntegral F K p N) -
        (R.coverLamV Ps hact * Real.log N - R.coverDegV Ps hact * Real.log (Real.log N))) atTop
      (𝓝 (-Real.log (R.productCoeffV Ps hK0 hε hεb hFc hpc hFm hF hK (R.coverLamV Ps hact)
        (R.coverDegV Ps hact)))) :=
  (R.hasLeadingTerm_boltzmannIntegral_of_productChartsV_extremal Ps hK0 hε hεb hFc hpc hFm hF hK
    hact).tendsto_neg_log
    (R.boltzmannIntegral_isEquivalent_of_productChartsV_extremal Ps hK0 hε hεb hFc hpc hFm hF hK
      hact hF0 hp0 hr0 i₀ I₀ hI₀ hne₀ hall hdeg hpos).1

end Var

section Partition

variable (Ps : ∀ i, ProductMonomialChartVar (ofChart (R.chart i)) () K) (P : SubordinatePartition R)
  (hK0 : ∀ x, 0 ≤ K x) {ε : ℝ} (hε : 0 < ε) (hεb : ∀ i, ε ≤ (Ps i).b) {p : TubeWeight d}
  (hpc : ∀ i, ContinuousOn (fun y => p.w ((R.chart i).φ y)) (Ps i).W)
  (hψ : ∀ i, ContinuousOn (fun y => P.ψ i ((R.chart i).φ y)) (Ps i).W) (hK : Measurable K)
  (hact : ∀ i, ((ofChart (R.chart i)).activeCoordsV (fun _ => Ps i)).Nonempty)
  {F : (Fin d → ℝ) → ℝ} (hFc : ∀ i, ContinuousOn (fun y => F ((R.chart i).φ y)) (Ps i).W)
  (hFm : Measurable F) (hF : Integrable (fun x => F x * p.w x) (volume.restrict (⋃ i, R.image i)))
  [Nonempty ι]

include hK0 hε hεb hpc hψ hK hact hFc hFm hF in
/-- **The free energy along a supplied partition of unity.** -/
theorem tendsto_freeEnergy_of_partition (hF0 : ∀ x, 0 ≤ F x) (hp0 : ∀ x, 0 ≤ p.w x)
    (hr0 : ∀ i x, 0 ≤ (Ps i).r x) (i₀ : ι)
    (htied : R.chartLam Ps hact i₀ = R.partitionLam Ps hact ∧
      R.chartDeg Ps hact i₀ = R.partitionDeg Ps hact)
    (I₀ : Finset (Fin d)) (hI₀ : I₀ ⊆ (Ps i₀).e.support) (hne₀ : I₀.Nonempty)
    (hall : ∀ j ∈ I₀, (Ps i₀).ratio j = R.chartLam Ps hact i₀)
    (hdeg : I₀.card - 1 = R.chartDeg Ps hact i₀)
    (hpos : 0 < volume ((Ps i₀).dominantFace (fun _ => (Ps i₀).e.support) ε I₀ hne₀ F
      (p.mulPartition P i₀))) :
    Tendsto (fun N => -Real.log (R.boltzmannIntegral F K p N) -
        (R.partitionLam Ps hact * Real.log N - R.partitionDeg Ps hact * Real.log (Real.log N)))
      atTop (𝓝 (-Real.log (R.partitionCoeff Ps P hK0 hε hεb hpc hψ hK hact hFc hFm hF))) :=
  (R.hasLeadingTerm_boltzmannIntegral_of_partition Ps P hK0 hε hεb hpc hψ hK hact hFc hFm
    hF).tendsto_neg_log
    (R.partitionCoeff_pos Ps P hK0 hε hεb hpc hψ hK hact hFc hFm hF hF0 hp0 hr0 i₀ htied I₀ hI₀
      hne₀ hall hdeg hpos)

end Partition

end ResolutionCover

end Grammar
