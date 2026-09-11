/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.LeadingTermInterface
import Grammar.AnalyticJacobian

/-!
# The divisor-free pieces are negligible at every power–log scale

The paper's Step 2 (eq:localisation) discards the region away from the exceptional divisor as an
`O(e^{-nε})` remainder. In the chart–stratum decomposition of CCXXIV–CCXXV that region is the
divisor-free piece `sizePiece D ε ∅` of each chart — every divisor coordinate of size `≥ ε` — and
here its contribution is certified negligible: exponential decay beats every power–log scale
(`tendsto_exp_neg_mul_div_powLogScale`, `HasLeadingTerm.of_exp_bound`); on a piece where the
phase `K ∘ φ_i` is bounded below by `δ > 0` the piece integral is bounded by `C e^{-δN}`
(`abs_pieceIntegral_le_exp`), hence is a leading-term certificate with coefficient `0` at every pair
(`hasLeadingTerm_pieceIntegral_zero_of_phase_bound`); and on a hironaka monomial chart the phase is
bounded below on the divisor-free piece of the compact domain, since `K ∘ φ = u · y^e` with `|u|`
bounded below on the compact domain and `|y^e| ≥ ∏ ε^{e_j}` when every divisor coordinate has size
`≥ ε` (`IsMonomialChart.exists_phase_lower_bound_divisorFree`). Consequently, for a resolution
cover of monomial charts with divisor coordinates `D_i = supp e_i`, the leading-coefficient
interface needs certificates only for the nonempty chart–stratum pieces
(`hasLeadingTerm_boltzmannIntegral_of_monomial`).

Non-claims: the certificates for the nonempty pieces remain hypotheses; the divisor-free bound is
`C e^{-δN}` with `δ` depending on the chart, the threshold `ε` and the compact domain.
-/

open MeasureTheory Set Filter Topology Monomialize.Analytic Monomialize.VolumeScaling
open scoped ENNReal

namespace Grammar

/-! ### Exponential decay against the power–log scales -/

section ExpScale

/-- `e^{-δN}` is `o` of every power–log scale. -/
theorem tendsto_exp_neg_mul_div_powLogScale {δ : ℝ} (hδ : 0 < δ) (lam : ℝ) (k : ℕ) :
    Tendsto (fun N => Real.exp (-δ * N) / powLogScale lam k N) atTop (𝓝 0) := by
  have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero lam δ hδ
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h ?_ ?_
  · exact (eventually_gt_atTop 1).mono fun N hN =>
      div_nonneg (Real.exp_pos _).le (powLogScale_pos lam k hN).le
  · filter_upwards [eventually_gt_atTop 1, eventually_ge_atTop (Real.exp 1)] with N hN hNe
    have hN0 : 0 < N := by linarith
    have hlog : 1 ≤ Real.log N := by
      rw [Real.le_log_iff_exp_le hN0]
      exact hNe
    have hpow : 1 ≤ Real.log N ^ k := one_le_pow₀ hlog
    unfold powLogScale
    rw [Real.rpow_neg hN0.le, ← div_div, div_inv_eq_mul, mul_comm]
    exact div_le_self (mul_nonneg (Real.rpow_pos_of_pos hN0 _).le (Real.exp_pos _).le) hpow

/-- An exponentially small function is a leading-term certificate with coefficient `0` at every
power–log scale. -/
theorem HasLeadingTerm.of_exp_bound {Z : ℝ → ℝ} {C δ : ℝ} (hδ : 0 < δ)
    (hZ : ∀ᶠ N in atTop, |Z N| ≤ C * Real.exp (-δ * N)) (lam : ℝ) (k : ℕ) :
    HasLeadingTerm Z 0 lam k := by
  have h := (tendsto_exp_neg_mul_div_powLogScale hδ lam k).const_mul C
  rw [mul_zero] at h
  refine squeeze_zero_norm' ?_ h
  filter_upwards [hZ, eventually_gt_atTop 1] with N hN hN1
  have hs := powLogScale_pos lam k hN1
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hs, ← mul_div_assoc]
  exact div_le_div_of_nonneg_right hN hs.le

end ExpScale

/-! ### The phase lower bound on the divisor-free piece of a monomial chart -/

section MonomialBound

variable {d : ℕ}

/-- On the divisor-free piece every divisor coordinate has size `≥ ε`, so `|y^e| ≥ ∏ ε^{e_j}`. -/
theorem prod_pow_le_abs_monomialEval {e : Fin d →₀ ℕ} {ε : ℝ} (hε : 0 < ε) {y : Fin d → ℝ}
    (hy : y ∈ sizePiece e.support ε ∅) :
    ∏ j ∈ e.support, ε ^ e j ≤ |monomialEval y e| := by
  have hmono : monomialEval y e = ∏ j ∈ e.support, y j ^ e j := rfl
  rw [hmono, Finset.abs_prod]
  refine Finset.prod_le_prod (fun j _ => pow_nonneg hε.le _) fun j hj => ?_
  rw [abs_pow]
  refine pow_le_pow_left₀ hε.le ?_ _
  have h := hy j hj
  simp only [Finset.notMem_empty, iff_false, not_lt] at h
  exact h

/-- **The phase is bounded below on the divisor-free piece of a monomial chart**: for a compact
domain, `K ≥ 0` and `K ∘ φ = u · y^e` with `u` continuous and nonvanishing,
`K (φ y) ≥ δ > 0` whenever `y ∈ dom` has all divisor coordinates of size `≥ ε`. -/
theorem IsMonomialChart.exists_phase_lower_bound_divisorFree {K : (Fin d → ℝ) → ℝ}
    {φ : (Fin d → ℝ) → (Fin d → ℝ)} {dom : Set (Fin d → ℝ)} {e h : Fin d →₀ ℕ}
    {W : Set (Fin d → ℝ)} (hc : IsMonomialChart K φ dom e h W) (hdom : IsCompact dom)
    (hK0 : ∀ x, 0 ≤ K x) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ, 0 < δ ∧ ∀ y ∈ dom ∩ sizePiece e.support ε ∅, δ ≤ K (φ y) := by
  obtain ⟨u, hu, hu0, hKu⟩ := hc.exists_unit
  rcases dom.eq_empty_or_nonempty with hne | hne
  · exact ⟨1, one_pos, fun y hy => absurd hy.1 (by rw [hne]; exact notMem_empty y)⟩
  obtain ⟨y₀, hy₀, hmin⟩ := hdom.exists_isMinOn hne
    (continuous_abs.comp_continuousOn (hu.mono hc.subset))
  have hu₀ : 0 < |u y₀| := abs_pos.2 (hu0 y₀ (hc.subset hy₀))
  refine ⟨|u y₀| * ∏ j ∈ e.support, ε ^ e j,
    mul_pos hu₀ (Finset.prod_pos fun j _ => pow_pos hε _), fun y hy => ?_⟩
  have hyW : y ∈ W := hc.subset hy.1
  have hK : K (φ y) = |u y| * |monomialEval y e| := by
    rw [← abs_of_nonneg (hK0 (φ y)), hKu y hyW, abs_mul]
  rw [hK]
  exact mul_le_mul (isMinOn_iff.1 hmin y hy.1) (prod_pow_le_abs_monomialEval hε hy.2)
    (Finset.prod_nonneg fun j _ => pow_nonneg hε.le _) (abs_nonneg _)

end MonomialBound

/-! ### The divisor-free piece integrals of a resolution cover -/

namespace ResolutionCover

variable {d : ℕ} {ι : Type*} [Fintype ι] (R : ResolutionCover d ι) (i : ι)

theorem boltzmannChartDensity_eq_exp_mul (N : ℝ) (K : (Fin d → ℝ) → ℝ) (p : TubeWeight d)
    (y : Fin d → ℝ) :
    R.boltzmannChartDensity i N K p y =
      Real.exp (-N * K ((R.chart i).Φ y)) * R.boltzmannChartDensity i 0 K p y := by
  unfold boltzmannChartDensity
  by_cases hy : y ∈ (R.chart i).dom
  · rw [indicator_of_mem hy, indicator_of_mem hy, neg_zero, zero_mul, Real.exp_zero, one_mul]
    ring
  · rw [indicator_of_notMem hy, indicator_of_notMem hy, mul_zero]

theorem boltzmannChartDensity_nonneg (N : ℝ) (K : (Fin d → ℝ) → ℝ) (p : TubeWeight d)
    (y : Fin d → ℝ) : 0 ≤ R.boltzmannChartDensity i N K p y :=
  indicator_nonneg (fun y _ => mul_nonneg ((R.chart i).jac_nonneg y) (mul_nonneg
    (R.weight_nonneg i _) (mul_nonneg (Real.exp_pos _).le (p.nonneg _)))) y

variable (D : ι → Finset (Fin d)) (ε : ℝ) (I : Finset (Fin d)) {F K : (Fin d → ℝ) → ℝ}
  {p : TubeWeight d}

theorem integrable_boltzmannChartDensity_zero_mul (hFm : Measurable F)
    (hF : Integrable (fun x => F x * p.w x) (volume.restrict (⋃ i, R.image i)))
    (hK : Measurable K) (hK0 : ∀ x, 0 ≤ K x) :
    Integrable fun y => R.boltzmannChartDensity i 0 K p y * F ((R.chart i).φ y) := by
  rw [← R.chartWeight_boltzmann_w i 0 le_rfl K hK hK0 p]
  refine R.integrable_chartWeight_mul i _ hFm (hF.congr (Eventually.of_forall fun x => ?_))
  simp only [TubeWeight.boltzmann_w, neg_zero, zero_mul, Real.exp_zero, one_mul]

/-- **The exponential bound on a piece with phase `≥ δ`**: for `N ≥ 0`,
`|Z_{N;i,I}| ≤ (∫_{piece} |w_{0} F∘φ_i|) e^{-δN}`. -/
theorem abs_pieceIntegral_le_exp (hFm : Measurable F)
    (hF : Integrable (fun x => F x * p.w x) (volume.restrict (⋃ i, R.image i)))
    (hK : Measurable K) (hK0 : ∀ x, 0 ≤ K x) {δ : ℝ}
    (hδK : ∀ y ∈ (R.chart i).dom ∩ sizePiece (D i) ε I, δ ≤ K ((R.chart i).φ y)) {N : ℝ}
    (hN : 0 ≤ N) :
    |R.pieceIntegral D ε i I F K p N| ≤
      (∫ y in sizePiece (D i) ε I, |R.boltzmannChartDensity i 0 K p y * F ((R.chart i).φ y)|) *
        Real.exp (-δ * N) := by
  unfold pieceIntegral
  refine abs_integral_le_integral_abs.trans ?_
  rw [mul_comm, ← integral_const_mul]
  refine integral_mono_of_nonneg (Eventually.of_forall fun y => abs_nonneg _)
    ((R.integrable_boltzmannChartDensity_zero_mul i hFm hF hK hK0).abs.integrableOn.const_mul _) ?_
  refine (ae_restrict_iff' (measurableSet_sizePiece (D i) ε I)).2
    (Eventually.of_forall fun y hy => ?_)
  beta_reduce
  rw [R.boltzmannChartDensity_eq_exp_mul i N K p y, mul_assoc, abs_mul,
    abs_of_pos (Real.exp_pos _)]
  by_cases hdom : y ∈ (R.chart i).dom
  · refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    rw [Real.exp_le_exp, (R.chart i).Φ_eqOn hdom]
    have h := hδK y ⟨hdom, hy⟩
    nlinarith
  · have h0 : R.boltzmannChartDensity i 0 K p y = 0 := by
      unfold boltzmannChartDensity
      rw [indicator_of_notMem hdom]
    rw [h0, zero_mul, abs_zero, mul_zero, mul_zero]

/-- **A piece on which the phase is bounded below is negligible at every power–log scale.** -/
theorem hasLeadingTerm_pieceIntegral_zero_of_phase_bound (hFm : Measurable F)
    (hF : Integrable (fun x => F x * p.w x) (volume.restrict (⋃ i, R.image i)))
    (hK : Measurable K) (hK0 : ∀ x, 0 ≤ K x) {δ : ℝ} (hδ : 0 < δ)
    (hδK : ∀ y ∈ (R.chart i).dom ∩ sizePiece (D i) ε I, δ ≤ K ((R.chart i).φ y))
    (lam : ℝ) (k : ℕ) : HasLeadingTerm (R.pieceIntegral D ε i I F K p) 0 lam k :=
  HasLeadingTerm.of_exp_bound hδ ((eventually_ge_atTop 0).mono fun _ hN =>
    R.abs_pieceIntegral_le_exp i D ε I hFm hF hK hK0 hδK hN) lam k

/-- **The divisor-free piece of a monomial chart is negligible at every power–log scale.** -/
theorem hasLeadingTerm_pieceIntegral_empty_of_monomial {e h : Fin d →₀ ℕ} {W : Set (Fin d → ℝ)}
    (hc : IsMonomialChart K (R.chart i).φ (R.chart i).dom e h W) (hD : D i = e.support)
    (hε : 0 < ε) (hFm : Measurable F)
    (hF : Integrable (fun x => F x * p.w x) (volume.restrict (⋃ i, R.image i)))
    (hK : Measurable K) (hK0 : ∀ x, 0 ≤ K x) (lam : ℝ) (k : ℕ) :
    HasLeadingTerm (R.pieceIntegral D ε i ∅ F K p) 0 lam k := by
  obtain ⟨δ, hδ, hδK⟩ :=
    IsMonomialChart.exists_phase_lower_bound_divisorFree hc (R.chart i).dom_compact hK0 hε
  refine R.hasLeadingTerm_pieceIntegral_zero_of_phase_bound i D ε ∅ hFm hF hK hK0 hδ ?_ lam k
  rw [hD]
  exact hδK

end ResolutionCover

/-! ### The leading-coefficient interface on a cover of monomial charts -/

namespace ResolutionCover

variable {d : ℕ} {ι : Type*} [Fintype ι] (R : ResolutionCover d ι)

/-- **The leading-coefficient interface for a resolution cover of monomial charts**: with the
divisor coordinates `D_i = supp e_i`, certificates for the nonempty chart–stratum pieces and an
extremal pair for them give the leading term of the resolved Boltzmann integral, the divisor-free
pieces being negligible. -/
theorem hasLeadingTerm_boltzmannIntegral_of_monomial (e h : ι → Fin d →₀ ℕ)
    (W : ι → Set (Fin d → ℝ)) {K : (Fin d → ℝ) → ℝ}
    (hc : ∀ i, IsMonomialChart K (R.chart i).φ (R.chart i).dom (e i) (h i) (W i)) {ε : ℝ}
    (hε : 0 < ε) {F : (Fin d → ℝ) → ℝ} {p : TubeWeight d} (hFm : Measurable F)
    (hF : Integrable (fun x => F x * p.w x) (volume.restrict (⋃ i, R.image i)))
    (hK : Measurable K) (hK0 : ∀ x, 0 ≤ K x)
    (c lam : ι → Finset (Fin d) → ℝ) (k : ι → Finset (Fin d) → ℕ) (lam₀ : ℝ) (k₀ : ℕ)
    (hpiece : ∀ i, ∀ I ∈ (e i).support.powerset.filter (fun I => I.Nonempty),
      HasLeadingTerm (R.pieceIntegral (fun i => (e i).support) ε i I F K p) (c i I) (lam i I)
        (k i I))
    (hlam : ∀ i, ∀ I ∈ (e i).support.powerset.filter (fun I => I.Nonempty), lam₀ ≤ lam i I)
    (hk : ∀ i, ∀ I ∈ (e i).support.powerset.filter (fun I => I.Nonempty),
      lam i I = lam₀ → k i I ≤ k₀) :
    HasLeadingTerm (R.boltzmannIntegral F K p)
      (∑ i, ∑ I ∈ ((e i).support.powerset.filter (fun I => I.Nonempty)).filter
        (fun I => lam i I = lam₀ ∧ k i I = k₀), c i I) lam₀ k₀ :=
  R.hasLeadingTerm_boltzmannIntegral (fun i => (e i).support) ε hFm hF hK hK0 c lam k lam₀ k₀
    hpiece hlam hk fun i =>
      R.hasLeadingTerm_pieceIntegral_empty_of_monomial i (fun i => (e i).support) ε (hc i) rfl hε
        hFm hF hK hK0 lam₀ k₀

end ResolutionCover

end Grammar
