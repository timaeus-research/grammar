/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.BlowUpObservables
import Grammar.GaussianDepthThreeTwoTerm

/-!
# The blow-up model: the posterior expectations of `x²` and `y²`

With the raw Gaussian prior, `E[f] = ∫ f e^{−NK}φ / ∫ e^{−NK}φ` for `K = x²(x² + y²)/2`.  From the
partition function's two-term expansion `√N Z_N = √(π/2)(log N + 5 log 2 − γ) + O(log N/√N)`
(DCXV) and the numerator limits `N X_N → π`, `√N Y_N → 2√(2π)` (DCXXXII):

  `log N · E[y²] → 4`  and  `√N log N · E[x²] → √(2π)`

(★★★ `tendsto_log_mul_blowupY_div`, `tendsto_sqrt_log_mul_blowupX_div`; examples_slop §4: the
output direction `y` is seen at order `1/log N`, the direction `x` only at order `1/(√N log N)`).
The `y`-numerator also has a rate, `|√N Y_N − 2√(2π)| ≤ 3√(2π)/(2√N)` for `N ≥ 1`
(★★ `abs_sqrt_mul_blowupY_sub_le`): the deficit is `√(2π)∫ (1 − e^{−(t⁴+t²)/2N})(1 + t²)^{−3/2}`,
at most
`|t|/(2N)` for `|t| ≤ N^{1/4}` and at most `|t|^{−3}` beyond (Astra round-12 target 1).
Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

/-! ### Positivity of the partition function -/

theorem blowupLaplace_pos {N : ℝ} (hN : 0 ≤ N) : 0 < blowupLaplace N := by
  rw [blowupLaplace_eq_integral hN]
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  refine mul_pos hs ?_
  have hint : Integrable fun x : ℝ =>
      Real.exp (-N * x ^ 4 / 2) * Real.exp (-x ^ 2 / 2) / Real.sqrt (1 + N * x ^ 2) := by
    have hg : Integrable fun x : ℝ => Real.exp (-x ^ 2 / 2) := by
      have := integrable_exp_neg_mul_sq (b := 1 / 2) (by norm_num)
      refine this.congr (Eventually.of_forall fun x => ?_)
      simp only; congr 1; ring
    refine hg.mono' ((by fun_prop : Measurable fun x : ℝ =>
      Real.exp (-N * x ^ 4 / 2) * Real.exp (-x ^ 2 / 2) / Real.sqrt (1 + N * x ^ 2))
        |>.aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
    have h1 : 0 < 1 + N * x ^ 2 := by positivity
    have hs1 : 1 ≤ Real.sqrt (1 + N * x ^ 2) := Real.one_le_sqrt.2 (by nlinarith [sq_nonneg x])
    have he : Real.exp (-N * x ^ 4 / 2) ≤ 1 := Real.exp_le_one_iff.2 (by
      have : 0 ≤ N * x ^ 4 := by positivity
      linarith)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_iff₀ (by positivity)]
    calc Real.exp (-N * x ^ 4 / 2) * Real.exp (-x ^ 2 / 2)
        ≤ 1 * Real.exp (-x ^ 2 / 2) := mul_le_mul_of_nonneg_right he (Real.exp_pos _).le
      _ = Real.exp (-x ^ 2 / 2) * 1 := by ring
      _ ≤ Real.exp (-x ^ 2 / 2) * Real.sqrt (1 + N * x ^ 2) :=
          mul_le_mul_of_nonneg_left hs1 (Real.exp_pos _).le
  rw [integral_pos_iff_support_of_nonneg (fun x => by positivity) hint,
    Function.support_eq_univ (fun x => by positivity)]
  simp

/-! ### The partition function against `log N` -/

/-- `√N Z_N / log N → √(π/2)`. -/
theorem tendsto_sqrt_mul_blowupLaplace_div_log :
    Tendsto (fun N : ℝ => Real.sqrt N * blowupLaplace N / Real.log N) atTop
      (𝓝 (Real.sqrt (Real.pi / 2))) := by
  set c := Real.sqrt (Real.pi / 2) with hc
  set b := 5 * Real.log 2 - Real.eulerMascheroniConstant with hb
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hc0 : 0 < c := Real.sqrt_pos.2 (by positivity)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero_norm' ?_ (a := fun N : ℝ => Real.sqrt (2 * Real.pi) * (17 / 2) / Real.sqrt N +
    c * |b| / Real.log N) ?_
  · filter_upwards [eventually_ge_atTop (3 : ℝ)] with N hN3
    have hN : 1 ≤ N := by linarith
    have hN0 : 0 < N := by linarith
    have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
    have hℓ : 1 ≤ Real.log N := by
      rw [← Real.log_exp 1]
      exact Real.log_le_log (Real.exp_pos _) (by linarith [Real.exp_one_lt_d9])
    have hℓ0 : 0 < Real.log N := by linarith
    have hℓs : Real.log N ≤ 2 * Real.sqrt N := log_le_two_sqrt hN0
    have h := blowupLaplace_two_term_bound hN
    rw [← hc, show Real.log N + 5 * Real.log 2 - Real.eulerMascheroniConstant = Real.log N + b by
      rw [hb]; ring] at h
    rw [norm_norm, Real.norm_eq_abs]
    have e : Real.sqrt N * blowupLaplace N / Real.log N - c =
        Real.sqrt N / Real.log N * (blowupLaplace N - c * (Real.log N + b) / Real.sqrt N) +
          c * b / Real.log N := by
      field_simp
      ring
    rw [e]
    calc |Real.sqrt N / Real.log N * (blowupLaplace N - c * (Real.log N + b) / Real.sqrt N) +
          c * b / Real.log N|
        ≤ |Real.sqrt N / Real.log N * (blowupLaplace N - c * (Real.log N + b) / Real.sqrt N)| +
          |c * b / Real.log N| := abs_add_le _ _
      _ = Real.sqrt N / Real.log N * |blowupLaplace N - c * (Real.log N + b) / Real.sqrt N| +
          c * |b| / Real.log N := by
          rw [abs_mul, abs_of_pos (by positivity), abs_div, abs_mul, abs_of_pos hc0,
            abs_of_pos hℓ0]
      _ ≤ Real.sqrt N / Real.log N * (Real.sqrt (2 * Real.pi) * (Real.log N / 2 + 8) / N) +
          c * |b| / Real.log N := by gcongr
      _ ≤ Real.sqrt (2 * Real.pi) * (17 / 2) / Real.sqrt N + c * |b| / Real.log N := by
          gcongr
          have hNN : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN0.le
          have h8 : Real.log N / 2 + 8 ≤ 17 / 2 * Real.log N := by linarith
          rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
          calc Real.sqrt N * (Real.sqrt (2 * Real.pi) * (Real.log N / 2 + 8)) * Real.sqrt N
              = Real.sqrt (2 * Real.pi) * (Real.log N / 2 + 8) * N := by
                linear_combination (Real.sqrt (2 * Real.pi) * (Real.log N / 2 + 8)) * hNN
            _ ≤ Real.sqrt (2 * Real.pi) * (17 / 2 * Real.log N) * N := by gcongr
            _ = Real.sqrt (2 * Real.pi) * (17 / 2) * (Real.log N * N) := by ring
  · have h1 : Tendsto (fun N : ℝ => Real.sqrt (2 * Real.pi) * (17 / 2) / Real.sqrt N) atTop
        (𝓝 0) := by
      have := tendsto_one_div_sqrt.const_mul (Real.sqrt (2 * Real.pi) * (17 / 2))
      simpa [div_eq_mul_inv, mul_comm] using this
    have h2 : Tendsto (fun N : ℝ => c * |b| / Real.log N) atTop (𝓝 0) := by
      have := (tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop).const_mul (c * |b|)
      simpa [div_eq_mul_inv] using this
    simpa using h1.add h2

/-! ### The rate for the `y`-numerator -/

/-- ★★ `|√N Y_N − 2√(2π)| ≤ 3√(2π)/(2√N)` for `N ≥ 1`. -/
theorem abs_sqrt_mul_blowupY_sub_le {N : ℝ} (hN : 1 ≤ N) :
    |Real.sqrt N * blowupY N - 2 * Real.sqrt (2 * Real.pi)| ≤
      3 * Real.sqrt (2 * Real.pi) / (2 * Real.sqrt N) := by
  have hN0 : 0 < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have hsN1 : 1 ≤ Real.sqrt N := Real.one_le_sqrt.2 hN
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  set T := Real.sqrt (Real.sqrt N) with hT
  have hT0 : 0 < T := Real.sqrt_pos.2 hsN
  have hT1 : 1 ≤ T := Real.one_le_sqrt.2 hsN1
  have hT2 : T ^ 2 = Real.sqrt N := Real.sq_sqrt hsN.le
  have hNN : Real.sqrt N ^ 2 = N := Real.sq_sqrt hN0.le
  have hscaled := blowupY_scaled hsN
  rw [hNN] at hscaled
  rw [hscaled, show (2 : ℝ) * Real.sqrt (2 * Real.pi) = Real.sqrt (2 * Real.pi) *
      ∫ t : ℝ, 1 / ((1 + t ^ 2) * Real.sqrt (1 + t ^ 2)) by
        rw [integral_one_add_sq_pow_three_half]; ring]
  -- the deficit
  set f : ℝ → ℝ := fun t => (1 - Real.exp (-t ^ 4 / (2 * N)) * Real.exp (-t ^ 2 / (2 * N))) /
    ((1 + t ^ 2) * Real.sqrt (1 + t ^ 2)) with hf
  have hf0 : ∀ t, 0 ≤ f t := fun t => by
    simp only [hf]
    have h1 : Real.exp (-t ^ 4 / (2 * N)) * Real.exp (-t ^ 2 / (2 * N)) ≤ 1 := by
      rw [← Real.exp_add]
      exact Real.exp_le_one_iff.2 (by
        have : 0 ≤ t ^ 4 / (2 * N) := by positivity
        have : 0 ≤ t ^ 2 / (2 * N) := by positivity
        rw [neg_div, neg_div]; linarith)
    have : 0 < (1 + t ^ 2) * Real.sqrt (1 + t ^ 2) := by positivity
    exact div_nonneg (by linarith) this.le
  have hf_le3 : ∀ t, 0 < t → f t ≤ 1 / t ^ 3 := fun t ht => by
    simp only [hf]
    have h1 : 0 ≤ Real.exp (-t ^ 4 / (2 * N)) * Real.exp (-t ^ 2 / (2 * N)) := by positivity
    have hsq : t ≤ Real.sqrt (1 + t ^ 2) := by
      rw [← Real.sqrt_sq ht.le]
      exact Real.sqrt_le_sqrt (by rw [Real.sq_sqrt (sq_nonneg t)]; linarith)
    have h2 : t ^ 3 ≤ (1 + t ^ 2) * Real.sqrt (1 + t ^ 2) := by
      calc t ^ 3 = t ^ 2 * t := by ring
        _ ≤ (1 + t ^ 2) * Real.sqrt (1 + t ^ 2) :=
          mul_le_mul (by linarith) hsq ht.le (by positivity)
    calc (1 - Real.exp (-t ^ 4 / (2 * N)) * Real.exp (-t ^ 2 / (2 * N))) /
          ((1 + t ^ 2) * Real.sqrt (1 + t ^ 2))
        ≤ 1 / ((1 + t ^ 2) * Real.sqrt (1 + t ^ 2)) :=
          div_le_div_of_nonneg_right (by linarith) (by positivity)
      _ ≤ 1 / t ^ 3 := div_le_div_of_nonneg_left zero_le_one (by positivity) h2
  have hf_le1 : ∀ t, 0 ≤ t → f t ≤ t / (2 * N) := fun t ht => by
    simp only [hf]
    have hu : 1 - Real.exp (-t ^ 4 / (2 * N)) * Real.exp (-t ^ 2 / (2 * N)) ≤
        (t ^ 4 + t ^ 2) / (2 * N) := by
      rw [← Real.exp_add]
      have := Real.add_one_le_exp (-t ^ 4 / (2 * N) + -t ^ 2 / (2 * N))
      have e : -t ^ 4 / (2 * N) + -t ^ 2 / (2 * N) = -((t ^ 4 + t ^ 2) / (2 * N)) := by ring
      rw [e] at this ⊢
      linarith
    have hpos : 0 < (1 + t ^ 2) * Real.sqrt (1 + t ^ 2) := by positivity
    have hsq : t ≤ Real.sqrt (1 + t ^ 2) := by
      rw [← Real.sqrt_sq ht]
      exact Real.sqrt_le_sqrt (by rw [Real.sq_sqrt (sq_nonneg t)]; linarith)
    rw [div_le_iff₀ hpos]
    calc 1 - Real.exp (-t ^ 4 / (2 * N)) * Real.exp (-t ^ 2 / (2 * N))
        ≤ (t ^ 4 + t ^ 2) / (2 * N) := hu
      _ = t / (2 * N) * (t * (1 + t ^ 2)) := by ring
      _ ≤ t / (2 * N) * (Real.sqrt (1 + t ^ 2) * (1 + t ^ 2)) := by
          gcongr
      _ = t / (2 * N) * ((1 + t ^ 2) * Real.sqrt (1 + t ^ 2)) := by ring
  have hcont : Continuous f := by
    simp only [hf]
    exact (continuous_const.sub (by fun_prop)).div (by fun_prop) fun t => by positivity
  have hfeven : ∀ t, f |t| = f t := fun t => by
    simp only [hf]
    rw [sq_abs, show |t| ^ 4 = t ^ 4 by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs, ← pow_mul]]
  -- the integral identity: deficit
  have hdef : Real.sqrt (2 * Real.pi) * (∫ t : ℝ, 1 / ((1 + t ^ 2) * Real.sqrt (1 + t ^ 2))) -
      Real.sqrt (2 * Real.pi) *
        (∫ t : ℝ, Real.exp (-t ^ 4 / (2 * N)) * Real.exp (-t ^ 2 / (2 * N)) /
        ((1 + t ^ 2) * Real.sqrt (1 + t ^ 2))) = Real.sqrt (2 * Real.pi) * ∫ t, f t := by
    rw [← mul_sub]
    congr 1
    have hint1 : Integrable fun t : ℝ => 1 / ((1 + t ^ 2) * Real.sqrt (1 + t ^ 2)) := by
      refine integrable_inv_one_add_sq.mono'
        (continuous_const.div (by fun_prop) fun t => by positivity :
          Continuous fun t : ℝ => 1 / ((1 + t ^ 2) * Real.sqrt (1 + t ^ 2))).aestronglyMeasurable
        (Eventually.of_forall fun t => ?_)
      have hpos : 0 < 1 + t ^ 2 := by positivity
      have hs1 : 1 ≤ Real.sqrt (1 + t ^ 2) :=
        Real.one_le_sqrt.2 (le_add_of_nonneg_right (sq_nonneg t))
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), one_div,
        inv_le_inv₀ (by positivity) hpos]
      nlinarith
    have hint2 : Integrable fun t : ℝ => Real.exp (-t ^ 4 / (2 * N)) * Real.exp (-t ^ 2 / (2 * N)) /
        ((1 + t ^ 2) * Real.sqrt (1 + t ^ 2)) := by
      refine hint1.mono' ((by fun_prop : Measurable fun t : ℝ =>
        Real.exp (-t ^ 4 / (2 * N)) * Real.exp (-t ^ 2 / (2 * N)) /
          ((1 + t ^ 2) * Real.sqrt (1 + t ^ 2))).aestronglyMeasurable)
        (Eventually.of_forall fun t => ?_)
      have hpos : 0 < (1 + t ^ 2) * Real.sqrt (1 + t ^ 2) := by positivity
      have h1 : Real.exp (-t ^ 4 / (2 * N)) * Real.exp (-t ^ 2 / (2 * N)) ≤ 1 := by
        rw [← Real.exp_add]
        exact Real.exp_le_one_iff.2 (by
          have : 0 ≤ t ^ 4 / (2 * N) := by positivity
          have : 0 ≤ t ^ 2 / (2 * N) := by positivity
          rw [neg_div, neg_div]; linarith)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_div_iff_of_pos_right hpos]
      exact h1
    rw [← integral_sub hint1 hint2]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [hf]
    have hpos : 0 < (1 + t ^ 2) * Real.sqrt (1 + t ^ 2) := by positivity
    field_simp
  have hfint : 0 ≤ ∫ t, f t := integral_nonneg hf0
  rw [show Real.sqrt (2 * Real.pi) * (∫ t : ℝ, Real.exp (-t ^ 4 / (2 * N)) *
      Real.exp (-t ^ 2 / (2 * N)) / ((1 + t ^ 2) * Real.sqrt (1 + t ^ 2))) -
      Real.sqrt (2 * Real.pi) * ∫ t : ℝ, 1 / ((1 + t ^ 2) * Real.sqrt (1 + t ^ 2)) =
      -(Real.sqrt (2 * Real.pi) * ∫ t, f t) by rw [← hdef]; ring, abs_neg,
    abs_of_nonneg (by positivity)]
  -- evenness and the split at `T = N^{1/4}`
  have hI0 : ∫ t, f t = 2 * ∫ t in Ioi (0 : ℝ), f t := by
    rw [← integral_comp_abs (f := f)]
    exact integral_congr_ae (Eventually.of_forall fun t => (hfeven t).symm)
  have hint_Ioc : IntegrableOn f (Ioc 0 T) := hcont.integrableOn_Ioc
  have hmaj3 : IntegrableOn (fun t : ℝ => 1 / t ^ 3) (Ioi T) := by
    have := integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) hT0
    refine this.congr_fun (fun t ht => ?_) measurableSet_Ioi
    have : 0 < t := lt_trans hT0 ht
    simp only
    rw [Real.rpow_neg this.le, one_div, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hint_Ioi : IntegrableOn f (Ioi T) := by
    refine hmaj3.mono' hcont.aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    exact Eventually.of_forall fun t ht => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hf0 t)]
      exact hf_le3 t (lt_trans hT0 ht)
  have hsplit : ∫ t in Ioi (0 : ℝ), f t = (∫ t in Ioc 0 T, f t) + ∫ t in Ioi T, f t := by
    rw [← Ioc_union_Ioi_eq_Ioi hT0.le,
      setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hint_Ioc hint_Ioi]
  have h1 : ∫ t in Ioc 0 T, f t ≤ 1 / (4 * Real.sqrt N) := by
    have hg : IntegrableOn (fun t : ℝ => t / (2 * N)) (Ioc 0 T) :=
      (continuous_id.div_const _).integrableOn_Ioc
    calc ∫ t in Ioc 0 T, f t ≤ ∫ t in Ioc 0 T, t / (2 * N) :=
          setIntegral_mono_on hint_Ioc hg measurableSet_Ioc fun t ht => hf_le1 t ht.1.le
      _ = T ^ 2 / (4 * N) := by
          rw [← intervalIntegral.integral_of_le hT0.le, intervalIntegral.integral_div, integral_id]
          ring
      _ = 1 / (4 * Real.sqrt N) := by
          rw [hT2, div_eq_div_iff (by positivity) (by positivity)]
          linear_combination 4 * hNN
  have h2 : ∫ t in Ioi T, f t ≤ 1 / (2 * Real.sqrt N) := by
    calc ∫ t in Ioi T, f t ≤ ∫ t in Ioi T, 1 / t ^ 3 :=
          setIntegral_mono_on hint_Ioi hmaj3 measurableSet_Ioi fun t ht =>
            hf_le3 t (lt_trans hT0 ht)
      _ = 1 / (2 * Real.sqrt N) := by
          have h := integral_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) hT0
          have e : ∀ t ∈ Ioi T, t ^ (-3 : ℝ) = 1 / t ^ 3 := by
            intro t ht
            have : 0 < t := lt_trans hT0 ht
            rw [Real.rpow_neg this.le, one_div, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num,
              Real.rpow_natCast]
          rw [setIntegral_congr_fun measurableSet_Ioi e] at h
          rw [h, show (-3 : ℝ) + 1 = -2 by norm_num, Real.rpow_neg hT0.le, Real.rpow_two, hT2]
          field_simp
  calc Real.sqrt (2 * Real.pi) * ∫ t, f t
      = Real.sqrt (2 * Real.pi) * (2 * ((∫ t in Ioc 0 T, f t) + ∫ t in Ioi T, f t)) := by
        rw [hI0, hsplit]
    _ ≤ Real.sqrt (2 * Real.pi) * (2 * (1 / (4 * Real.sqrt N) + 1 / (2 * Real.sqrt N))) := by
        gcongr
    _ = 3 * Real.sqrt (2 * Real.pi) / (2 * Real.sqrt N) := by
        field_simp
        ring

/-! ### The posterior expectations -/

/-- ★★★ `log N · E[y²] → 4`: `log N · Y_N/Z_N → 4`. -/
theorem tendsto_log_mul_blowupY_div :
    Tendsto (fun N : ℝ => Real.log N * (blowupY N / blowupLaplace N)) atTop (𝓝 4) := by
  have hc : 0 < Real.sqrt (Real.pi / 2) := Real.sqrt_pos.2 (by positivity)
  have h := tendsto_sqrt_mul_blowupY.div tendsto_sqrt_mul_blowupLaplace_div_log hc.ne'
  have hval : 2 * Real.sqrt (2 * Real.pi) / Real.sqrt (Real.pi / 2) = 4 := by
    rw [← sqrt_two_pi_div_two]
    have := Real.sqrt_pos.2 (by positivity : (0 : ℝ) < 2 * Real.pi)
    field_simp
    norm_num
  rw [hval] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
  have hN0 : 0 < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have hℓ : 0 < Real.log N := Real.log_pos hN
  have hZ : 0 < blowupLaplace N := blowupLaplace_pos hN0.le
  simp only [Pi.div_apply]
  field_simp

/-- ★★★ `√N log N · E[x²] → √(2π)`: `√N log N · X_N/Z_N → √(2π)`. -/
theorem tendsto_sqrt_log_mul_blowupX_div :
    Tendsto (fun N : ℝ => Real.sqrt N * Real.log N * (blowupX N / blowupLaplace N)) atTop
      (𝓝 (Real.sqrt (2 * Real.pi))) := by
  have hc : 0 < Real.sqrt (Real.pi / 2) := Real.sqrt_pos.2 (by positivity)
  have h := tendsto_mul_blowupX.div tendsto_sqrt_mul_blowupLaplace_div_log hc.ne'
  have hval : Real.pi / Real.sqrt (Real.pi / 2) = Real.sqrt (2 * Real.pi) := by
    rw [← sqrt_two_pi_div_two]
    have hs := Real.sqrt_pos.2 (by positivity : (0 : ℝ) < 2 * Real.pi)
    have h1 : Real.sqrt (2 * Real.pi) ^ 2 = 2 * Real.pi := Real.sq_sqrt (by positivity)
    have h2 : Real.sqrt (Real.pi * 2) ^ 2 = Real.pi * 2 := Real.sq_sqrt (by positivity)
    field_simp
    linear_combination (-1 : ℝ) * h2
  rw [hval] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
  have hN0 : 0 < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have hℓ : 0 < Real.log N := Real.log_pos hN
  have hZ : 0 < blowupLaplace N := blowupLaplace_pos hN0.le
  have hNN : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN0.le
  simp only [Pi.div_apply]
  rw [div_eq_iff (by positivity)]
  field_simp
  linear_combination (-(blowupX N)) * hNN

end Grammar
