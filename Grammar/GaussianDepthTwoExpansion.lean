/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.GaussianDepthTwo
import Grammar.RenormalisedExpIntegral

/-!
# The depth-two Gaussian deep linear network: the two-term expansion

With `J(ε) = ∫₀^∞ 2 e^{−w²}/√(w² + ε) dw` (the conditional reduction of `Grammar.GaussianDepthTwo`
in the variable `x = √2 w`), the partition function is `Z_N = J(1/(2N))/√(2πN)` exactly
(`gaussLaplace2_eq_J`), and

  `J(ε) = log(4/ε) − γ + R(ε)`,  `|R(ε)| ≤ ε (log(1/ε) + 3)`  for `0 < ε ≤ 1`  (★★ `J_two_term`):

the elementary part `∫₀¹ 2/√(w² + ε) dw = 2 log((1 + √(1+ε))/√ε) ∈ [log(4/ε), log(4/ε) + ε]`
(`integral_elem`, `elem_bounds`), the renormalised constant
`∫₀^∞ (e^{−w²} − 1_{(0,1]}(w))·2/w dw = −γ`
(`integral_renormalised_sq`, from `Grammar.RenormalisedExpIntegral` by `v = w²`), and the error
`∫ (e^{−w²} − 1_{(0,1]})(2/√(w²+ε) − 2/w)` bounded by `2ε/(w(w²+ε))` against `min(w², e^{−w²})`.
Hence

  `Z_N = (log N + 3 log 2 − γ)/√(2πN) + O(N^{−3/2} log N)`  (★★★ `gaussLaplace2_two_term`),

the note's eq. (dln_gauss) at `L = 2` with an explicit remainder (Astra round-5 target 2).
Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

/-- `J(ε) = ∫₀^∞ 2 e^{−w²}/√(w² + ε) dw`. -/
noncomputable def gaussJ (ε : ℝ) : ℝ :=
  ∫ w in Ioi (0 : ℝ), 2 * Real.exp (-w ^ 2) / Real.sqrt (w ^ 2 + ε)

/-! ### The elementary part -/

/-- `∫₀¹ 2/√(w² + ε) dw = 2 log((1 + √(1 + ε))/√ε)`. -/
theorem integral_elem {ε : ℝ} (hε : 0 < ε) :
    ∫ w in (0 : ℝ)..1, 2 / Real.sqrt (w ^ 2 + ε) =
      2 * Real.log ((1 + Real.sqrt (1 + ε)) / Real.sqrt ε) := by
  have hderiv : ∀ w ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun w => 2 * Real.log (w + Real.sqrt (w ^ 2 + ε)))
      (2 / Real.sqrt (w ^ 2 + ε)) w := by
    intro w hw
    rw [uIcc_of_le zero_le_one] at hw
    have hpos : 0 < w ^ 2 + ε := by positivity
    have hsq : 0 < Real.sqrt (w ^ 2 + ε) := Real.sqrt_pos.2 hpos
    have hne : w + Real.sqrt (w ^ 2 + ε) ≠ 0 := by linarith [hw.1]
    have h1 : HasDerivAt (fun w : ℝ => w ^ 2 + ε) (2 * w) w := by
      simpa using (hasDerivAt_pow 2 w).add_const ε
    have h2 : HasDerivAt (fun w : ℝ => Real.sqrt (w ^ 2 + ε))
        (1 / (2 * Real.sqrt (w ^ 2 + ε)) * (2 * w)) w := (Real.hasDerivAt_sqrt hpos.ne').comp w h1
    have h3 : HasDerivAt (fun w : ℝ => w + Real.sqrt (w ^ 2 + ε))
        (1 + 1 / (2 * Real.sqrt (w ^ 2 + ε)) * (2 * w)) w := (hasDerivAt_id w).add h2
    have h4 := ((Real.hasDerivAt_log hne).comp w h3).const_mul 2
    refine h4.congr_deriv ?_
    have hs2 : Real.sqrt (w ^ 2 + ε) ^ 2 = w ^ 2 + ε := Real.sq_sqrt hpos.le
    field_simp
    nlinarith [hs2]
  have hint : IntervalIntegrable (fun w => 2 / Real.sqrt (w ^ 2 + ε)) volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    refine (continuousOn_const.div (by fun_prop) fun w _ => ?_)
    exact (Real.sqrt_pos.2 (by positivity)).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp only [one_pow, zero_pow (two_ne_zero), zero_add, Real.sqrt_eq_rpow]
  rw [← mul_sub, ← Real.log_div (by positivity) (by positivity)]

/-- `log(4/ε) ≤ 2 log((1 + √(1+ε))/√ε) ≤ log(4/ε) + ε` for `0 < ε ≤ 1`. -/
theorem elem_bounds {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Real.log (4 / ε) ≤ 2 * Real.log ((1 + Real.sqrt (1 + ε)) / Real.sqrt ε) ∧
      2 * Real.log ((1 + Real.sqrt (1 + ε)) / Real.sqrt ε) ≤ Real.log (4 / ε) + ε := by
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have h1 : 1 ≤ Real.sqrt (1 + ε) := Real.one_le_sqrt.2 (by linarith)
  have h2 : Real.sqrt (1 + ε) ≤ 1 + ε / 2 := Real.sqrt_one_add_le (by linarith)
  have e : 2 * Real.log ((1 + Real.sqrt (1 + ε)) / Real.sqrt ε) =
      Real.log ((1 + Real.sqrt (1 + ε)) ^ 2 / ε) := by
    have h : ((1 + Real.sqrt (1 + ε)) / Real.sqrt ε) ^ 2 = (1 + Real.sqrt (1 + ε)) ^ 2 / ε := by
      rw [div_pow, Real.sq_sqrt hε.le]
    rw [← h, Real.log_pow]; push_cast; ring
  rw [e]
  constructor
  · refine Real.log_le_log (by positivity) ?_
    rw [div_le_div_iff_of_pos_right hε]
    nlinarith
  · have h3 : (1 + Real.sqrt (1 + ε)) ^ 2 / ε ≤ 4 / ε * (1 + ε) := by
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hε]
      nlinarith
    calc Real.log ((1 + Real.sqrt (1 + ε)) ^ 2 / ε) ≤ Real.log (4 / ε * (1 + ε)) :=
          Real.log_le_log (by positivity) h3
      _ = Real.log (4 / ε) + Real.log (1 + ε) := Real.log_mul (by positivity) (by positivity)
      _ ≤ Real.log (4 / ε) + ε := by linarith [Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + ε)]

/-! ### The pointwise gap `2/w − 2/√(w² + ε)` and the elementary bounds -/

/-- `0 ≤ 2/w − 2/√(w² + ε) ≤ 2ε/(w(w² + ε))` for `w, ε > 0`. -/
theorem gap_bounds {ε w : ℝ} (hε : 0 < ε) (hw : 0 < w) :
    0 ≤ 2 / w - 2 / Real.sqrt (w ^ 2 + ε) ∧
      2 / w - 2 / Real.sqrt (w ^ 2 + ε) ≤ 2 * ε / (w * (w ^ 2 + ε)) := by
  have hpos : 0 < w ^ 2 + ε := by positivity
  have hs2 : Real.sqrt (w ^ 2 + ε) ^ 2 = w ^ 2 + ε := Real.sq_sqrt hpos.le
  have hs0 : 0 < Real.sqrt (w ^ 2 + ε) := Real.sqrt_pos.2 hpos
  have hws : w ≤ Real.sqrt (w ^ 2 + ε) := by
    rw [Real.le_sqrt hw.le hpos.le]; linarith
  generalize Real.sqrt (w ^ 2 + ε) = s at hs2 hs0 hws ⊢
  constructor
  · have : 2 / s ≤ 2 / w := div_le_div_of_nonneg_left (by norm_num) hw hws
    linarith
  · rw [div_sub_div _ _ hw.ne' hs0.ne', div_le_div_iff₀ (by positivity) (by positivity)]
    have hε' : ε = s ^ 2 - w ^ 2 := by linarith
    subst hε'
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg w) hs0.le) (sub_nonneg.2 hws)]

/-- `0 ≤ 1 − e^{−w²} ≤ w²`. -/
theorem one_sub_exp_neg_sq_bounds (w : ℝ) :
    0 ≤ 1 - Real.exp (-w ^ 2) ∧ 1 - Real.exp (-w ^ 2) ≤ w ^ 2 := by
  constructor
  · linarith [Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg w] : -w ^ 2 ≤ 0)]
  · linarith [Real.add_one_le_exp (-w ^ 2)]

/-- The inner remainder integrand is bounded by `2εw/(w² + ε)`. -/
theorem rem_inner_bound {ε w : ℝ} (hε : 0 < ε) (hw : 0 < w) :
    |(Real.exp (-w ^ 2) - 1) * (2 / Real.sqrt (w ^ 2 + ε) - 2 / w)| ≤
      2 * ε * w / (w ^ 2 + ε) := by
  obtain ⟨h1, h2⟩ := gap_bounds hε hw
  obtain ⟨h3, h4⟩ := one_sub_exp_neg_sq_bounds w
  rw [abs_mul, abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
  calc -(Real.exp (-w ^ 2) - 1) * -(2 / Real.sqrt (w ^ 2 + ε) - 2 / w)
      ≤ w ^ 2 * (2 * ε / (w * (w ^ 2 + ε))) :=
        mul_le_mul (by linarith) (by linarith) (by linarith) (by positivity)
    _ = 2 * ε * w / (w ^ 2 + ε) := by field_simp

/-- `∫₀¹ 2εw/(w² + ε) dw = ε (log(1 + ε) − log ε)`. -/
theorem integral_majorant {ε : ℝ} (hε : 0 < ε) :
    ∫ w in (0 : ℝ)..1, 2 * ε * w / (w ^ 2 + ε) = ε * (Real.log (1 + ε) - Real.log ε) := by
  have hderiv : ∀ w ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun w => ε * Real.log (w ^ 2 + ε))
      (2 * ε * w / (w ^ 2 + ε)) w := by
    intro w _
    have hpos : 0 < w ^ 2 + ε := by positivity
    have h1 : HasDerivAt (fun w : ℝ => w ^ 2 + ε) (2 * w) w := by
      simpa using (hasDerivAt_pow 2 w).add_const ε
    have h2 := ((Real.hasDerivAt_log hpos.ne').comp w h1).const_mul ε
    refine h2.congr_deriv ?_
    field_simp
  have hint : IntervalIntegrable (fun w => 2 * ε * w / (w ^ 2 + ε)) volume 0 1 :=
    ContinuousOn.intervalIntegrable
      ((by fun_prop : ContinuousOn (fun w : ℝ => 2 * ε * w) (uIcc 0 1)).div (by fun_prop)
        fun w _ => by positivity)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp only [one_pow, zero_pow two_ne_zero, zero_add]
  ring

/-- `|∫₀¹ (e^{−w²} − 1)(2/√(w² + ε) − 2/w) dw| ≤ ε (log(1/ε) + 1)` for `0 < ε ≤ 1`. -/
theorem rem_inner_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    |∫ w in Ioc (0 : ℝ) 1, (Real.exp (-w ^ 2) - 1) * (2 / Real.sqrt (w ^ 2 + ε) - 2 / w)| ≤
      ε * (Real.log (1 / ε) + 1) := by
  have hmaj : IntegrableOn (fun w : ℝ => 2 * ε * w / (w ^ 2 + ε)) (Ioc 0 1) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    exact ContinuousOn.intervalIntegrable
      ((by fun_prop : ContinuousOn (fun w : ℝ => 2 * ε * w) (uIcc 0 1)).div (by fun_prop)
        fun w _ => by positivity)
  have h := norm_integral_le_of_norm_le (μ := volume.restrict (Ioc (0 : ℝ) 1))
    (f := fun w => (Real.exp (-w ^ 2) - 1) * (2 / Real.sqrt (w ^ 2 + ε) - 2 / w)) hmaj ?_
  · rw [Real.norm_eq_abs] at h
    refine h.trans ?_
    rw [← intervalIntegral.integral_of_le zero_le_one, integral_majorant hε]
    have h1 : Real.log (1 + ε) ≤ 1 := by
      linarith [Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + ε)]
    rw [one_div, Real.log_inv]
    nlinarith [mul_le_mul_of_nonneg_left h1 hε.le]
  · rw [ae_restrict_iff' measurableSet_Ioc]
    exact Eventually.of_forall fun w hw => by
      rw [Real.norm_eq_abs]; exact rem_inner_bound hε hw.1

/-- `|∫₁^∞ e^{−w²}(2/√(w² + ε) − 2/w) dw| ≤ ε` for `ε > 0`. -/
theorem rem_outer_le {ε : ℝ} (hε : 0 < ε) :
    |∫ w in Ioi (1 : ℝ), Real.exp (-w ^ 2) * (2 / Real.sqrt (w ^ 2 + ε) - 2 / w)| ≤ ε := by
  have hmaj : IntegrableOn (fun w : ℝ => 2 * ε * Real.exp (-w)) (Ioi 1) := by
    refine IntegrableOn.congr_fun (s := Ioi 1)
      ((exp_neg_integrableOn_Ioi 1 one_pos).const_mul (2 * ε)) (fun w _ => ?_) measurableSet_Ioi
    simp
  have h := norm_integral_le_of_norm_le (μ := volume.restrict (Ioi (1 : ℝ)))
    (f := fun w => Real.exp (-w ^ 2) * (2 / Real.sqrt (w ^ 2 + ε) - 2 / w)) hmaj ?_
  · rw [Real.norm_eq_abs] at h
    refine h.trans ?_
    rw [integral_const_mul, integral_exp_neg_Ioi]
    have he : 2 < Real.exp 1 := by linarith [Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)]
    have h2 : Real.exp (-1) * 2 ≤ 1 := by
      rw [Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos 1)]; linarith
    nlinarith
  · rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun w hw => ?_
    have hw : (1 : ℝ) < w := hw
    have hw0 : 0 < w := by linarith
    obtain ⟨h1, h2⟩ := gap_bounds hε hw0
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_nonpos (by linarith)]
    have h3 : Real.exp (-w ^ 2) ≤ Real.exp (-w) := Real.exp_le_exp.2 (by nlinarith)
    have h4 : 2 * ε / (w * (w ^ 2 + ε)) ≤ 2 * ε := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [mul_le_mul hw.le (by nlinarith : (1 : ℝ) ≤ w ^ 2 + ε) zero_le_one hw0.le]
    calc Real.exp (-w ^ 2) * -(2 / Real.sqrt (w ^ 2 + ε) - 2 / w) ≤ Real.exp (-w) * (2 * ε) :=
          mul_le_mul h3 (by linarith) (by linarith) (Real.exp_pos _).le
      _ = 2 * ε * Real.exp (-w) := by ring

/-! ### The renormalised constant in the variable `w = √v` -/

/-- `∫₀^∞ (e^{−w²} − 1_{(0,1]}(w))·2/w dw = −γ`. -/
theorem integral_renormalised_sq :
    ∫ w in Ioi (0 : ℝ), (Real.exp (-w ^ 2) - (Ioc 0 1).indicator 1 w) * (2 / w) =
      -Real.eulerMascheroniConstant := by
  rw [← integral_renormalised_exp_inv, ← integral_comp_rpow_Ioi_of_pos
    (g := fun u => (Real.exp (-u) - (Ioc 0 1).indicator 1 u) / u) two_pos]
  refine setIntegral_congr_fun measurableSet_Ioi fun w hw => ?_
  have hw : (0 : ℝ) < w := hw
  have hI : (Ioc (0 : ℝ) 1).indicator (1 : ℝ → ℝ) (w ^ 2) = (Ioc 0 1).indicator 1 w := by
    by_cases h : w ≤ 1
    · have hm : w ^ 2 ∈ Ioc (0 : ℝ) 1 := ⟨by positivity, by nlinarith⟩
      have hm' : w ∈ Ioc (0 : ℝ) 1 := ⟨hw, h⟩
      rw [indicator_of_mem hm, indicator_of_mem hm', Pi.one_apply, Pi.one_apply]
    · have h' := not_le.1 h
      have hm : w ^ 2 ∉ Ioc (0 : ℝ) 1 := fun hm => absurd hm.2 (not_le.2 (by nlinarith))
      have hm' : w ∉ Ioc (0 : ℝ) 1 := fun hm => absurd hm.2 (not_le.2 h')
      rw [indicator_of_notMem hm, indicator_of_notMem hm']
  simp only [smul_eq_mul]
  rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_two, hI]
  field_simp

/-! ### Integrability and the splitting of the renormalised constant -/

theorem measurable_renorm :
    Measurable fun w : ℝ => (Real.exp (-w ^ 2) - (Ioc 0 1).indicator 1 w) * (2 / w) :=
  ((by fun_prop : Measurable fun w : ℝ => Real.exp (-w ^ 2)).sub
    (measurable_one.indicator measurableSet_Ioc)).mul (by fun_prop)

theorem integrableOn_renorm_inner :
    IntegrableOn (fun w : ℝ => (Real.exp (-w ^ 2) - (Ioc 0 1).indicator 1 w) * (2 / w))
      (Ioc 0 1) := by
  refine Measure.integrableOn_of_bounded (M := 2)
    (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top) measurable_renorm.aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioc]
  refine Eventually.of_forall fun w hw => ?_
  obtain ⟨h3, h4⟩ := one_sub_exp_neg_sq_bounds w
  have hw0 : 0 < w := hw.1
  rw [Real.norm_eq_abs, indicator_of_mem hw, Pi.one_apply, abs_mul, abs_of_nonpos (by linarith),
    abs_of_pos (by positivity)]
  calc -(Real.exp (-w ^ 2) - 1) * (2 / w) ≤ w ^ 2 * (2 / w) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = 2 * w := by field_simp
    _ ≤ 2 := by linarith [hw.2]

theorem integrableOn_renorm_outer :
    IntegrableOn (fun w : ℝ => (Real.exp (-w ^ 2) - (Ioc 0 1).indicator 1 w) * (2 / w))
      (Ioi 1) := by
  have hmaj : IntegrableOn (fun w : ℝ => 2 * Real.exp (-w)) (Ioi 1) := by
    refine IntegrableOn.congr_fun (s := Ioi 1)
      ((exp_neg_integrableOn_Ioi 1 one_pos).const_mul 2) (fun w _ => ?_) measurableSet_Ioi
    simp
  refine hmaj.mono' measurable_renorm.aestronglyMeasurable.restrict ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Eventually.of_forall fun w hw => ?_
  have hw : (1 : ℝ) < w := hw
  have hw0 : 0 < w := by linarith
  have hm : w ∉ Ioc (0 : ℝ) 1 := fun hm => absurd hm.2 (not_le.2 hw)
  rw [Real.norm_eq_abs, indicator_of_notMem hm, sub_zero, abs_mul, abs_of_pos (Real.exp_pos _),
    abs_of_pos (by positivity)]
  have h3 : Real.exp (-w ^ 2) ≤ Real.exp (-w) := Real.exp_le_exp.2 (by nlinarith)
  have h4 : 2 / w ≤ 2 := by rw [div_le_iff₀ hw0]; linarith
  calc Real.exp (-w ^ 2) * (2 / w) ≤ Real.exp (-w) * 2 :=
        mul_le_mul h3 h4 (by positivity) (Real.exp_pos _).le
    _ = 2 * Real.exp (-w) := by ring

/-- `∫₀¹ (e^{−w²} − 1)·2/w dw + ∫₁^∞ e^{−w²}·2/w dw = −γ`. -/
theorem renorm_split :
    (∫ w in Ioc (0 : ℝ) 1, (Real.exp (-w ^ 2) - 1) * (2 / w)) +
      ∫ w in Ioi (1 : ℝ), Real.exp (-w ^ 2) * (2 / w) = -Real.eulerMascheroniConstant := by
  rw [← integral_renormalised_sq, ← Ioc_union_Ioi_eq_Ioi zero_le_one,
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi integrableOn_renorm_inner
      integrableOn_renorm_outer]
  congr 1
  · exact setIntegral_congr_fun measurableSet_Ioc fun w hw => by
      rw [indicator_of_mem hw, Pi.one_apply]
  · exact setIntegral_congr_fun measurableSet_Ioi fun w hw => by
      rw [indicator_of_notMem (fun hm => absurd hm.2 (not_le.2 hw)), sub_zero]

theorem integrableOn_gaussJ {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun w : ℝ => 2 * Real.exp (-w ^ 2) / Real.sqrt (w ^ 2 + ε)) (Ioi 0) := by
  have hmaj : Integrable fun w : ℝ => 2 / Real.sqrt ε * Real.exp (-1 * w ^ 2) :=
    (integrable_exp_neg_mul_sq one_pos).const_mul _
  refine (hmaj.mono' (Measurable.aestronglyMeasurable ?_) ?_).integrableOn
  · refine (by fun_prop : Measurable fun w : ℝ => 2 * Real.exp (-w ^ 2)).div (by fun_prop)
  · refine Eventually.of_forall fun w => ?_
    have hs : Real.sqrt ε ≤ Real.sqrt (w ^ 2 + ε) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg w])
    have hs0 : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), neg_one_mul, mul_comm (2 / Real.sqrt ε),
      ← mul_div_assoc, mul_comm]
    exact div_le_div_of_nonneg_left (by positivity) hs0 hs

theorem integrableOn_elem {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun w : ℝ => 2 / Real.sqrt (w ^ 2 + ε)) (Ioc 0 1) := by
  rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  refine ContinuousOn.intervalIntegrable (continuousOn_const.div (by fun_prop) fun w _ => ?_)
  exact (Real.sqrt_pos.2 (by positivity)).ne'

/-- ★★ **The two-term expansion of `J`**:
`|J(ε) − (log(4/ε) − γ)| ≤ ε (log(1/ε) + 3)` for `0 < ε ≤ 1`. -/
theorem gaussJ_two_term {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    |gaussJ ε - (Real.log (4 / ε) - Real.eulerMascheroniConstant)| ≤
      ε * (Real.log (1 / ε) + 3) := by
  have hA := integrableOn_gaussJ hε
  have hA1 : IntegrableOn (fun w : ℝ => 2 * Real.exp (-w ^ 2) / Real.sqrt (w ^ 2 + ε)) (Ioc 0 1) :=
    hA.mono_set Ioc_subset_Ioi_self
  have hA2 : IntegrableOn (fun w : ℝ => 2 * Real.exp (-w ^ 2) / Real.sqrt (w ^ 2 + ε)) (Ioi 1) :=
    hA.mono_set (Ioi_subset_Ioi zero_le_one)
  have hp1 := integrableOn_elem hε
  have hq1 : IntegrableOn (fun w : ℝ => (Real.exp (-w ^ 2) - 1) * (2 / w)) (Ioc 0 1) :=
    integrableOn_renorm_inner.congr_fun (fun w hw => by
      simp only; rw [indicator_of_mem hw, Pi.one_apply]) measurableSet_Ioc
  have hq2 : IntegrableOn (fun w : ℝ => Real.exp (-w ^ 2) * (2 / w)) (Ioi 1) :=
    integrableOn_renorm_outer.congr_fun (fun w hw => by
      simp only; rw [indicator_of_notMem (fun hm => absurd hm.2 (not_le.2 hw)), sub_zero])
      measurableSet_Ioi
  have hJ : gaussJ ε = (∫ w in Ioc (0 : ℝ) 1, 2 * Real.exp (-w ^ 2) / Real.sqrt (w ^ 2 + ε)) +
      ∫ w in Ioi (1 : ℝ), 2 * Real.exp (-w ^ 2) / Real.sqrt (w ^ 2 + ε) := by
    unfold gaussJ
    rw [← Ioc_union_Ioi_eq_Ioi zero_le_one,
      setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hA1 hA2]
  have hE : ∫ w in Ioc (0 : ℝ) 1, 2 / Real.sqrt (w ^ 2 + ε) =
      2 * Real.log ((1 + Real.sqrt (1 + ε)) / Real.sqrt ε) := by
    rw [← intervalIntegral.integral_of_le zero_le_one, integral_elem hε]
  have hR1 : ∫ w in Ioc (0 : ℝ) 1, 2 * Real.exp (-w ^ 2) / Real.sqrt (w ^ 2 + ε) =
      (∫ w in Ioc (0 : ℝ) 1, 2 / Real.sqrt (w ^ 2 + ε)) +
        (∫ w in Ioc (0 : ℝ) 1, (Real.exp (-w ^ 2) - 1) * (2 / w)) +
        ∫ w in Ioc (0 : ℝ) 1, (Real.exp (-w ^ 2) - 1) * (2 / Real.sqrt (w ^ 2 + ε) - 2 / w) := by
    have e : ∀ w ∈ Ioc (0 : ℝ) 1, (Real.exp (-w ^ 2) - 1) * (2 / Real.sqrt (w ^ 2 + ε) - 2 / w) =
        2 * Real.exp (-w ^ 2) / Real.sqrt (w ^ 2 + ε) - 2 / Real.sqrt (w ^ 2 + ε) -
          (Real.exp (-w ^ 2) - 1) * (2 / w) := fun w _ => by ring
    have hAp : IntegrableOn (fun w : ℝ => 2 * Real.exp (-w ^ 2) / Real.sqrt (w ^ 2 + ε) -
        2 / Real.sqrt (w ^ 2 + ε)) (Ioc 0 1) := hA1.sub hp1
    rw [setIntegral_congr_fun measurableSet_Ioc e, integral_sub hAp hq1, integral_sub hA1 hp1]
    ring
  have hR2 : ∫ w in Ioi (1 : ℝ), 2 * Real.exp (-w ^ 2) / Real.sqrt (w ^ 2 + ε) =
      (∫ w in Ioi (1 : ℝ), Real.exp (-w ^ 2) * (2 / w)) +
        ∫ w in Ioi (1 : ℝ), Real.exp (-w ^ 2) * (2 / Real.sqrt (w ^ 2 + ε) - 2 / w) := by
    have e : ∀ w ∈ Ioi (1 : ℝ), Real.exp (-w ^ 2) * (2 / Real.sqrt (w ^ 2 + ε) - 2 / w) =
        2 * Real.exp (-w ^ 2) / Real.sqrt (w ^ 2 + ε) - Real.exp (-w ^ 2) * (2 / w) :=
      fun w _ => by ring
    rw [setIntegral_congr_fun measurableSet_Ioi e, integral_sub hA2 hq2]
    ring
  have hb1 := elem_bounds hε hε1
  have hb2 := rem_inner_le hε hε1
  have hb3 := rem_outer_le hε
  have hγ := renorm_split
  rw [hJ, hR1, hR2, hE]
  rw [abs_le] at hb2 hb3 ⊢
  constructor <;> nlinarith [hb1.1, hb1.2, hb2.1, hb2.2, hb3.1, hb3.2, hγ]

/-! ### Transfer to the partition function -/

/-- ★★ **`Z_N = J(1/(2N))/√(2πN)`** for `N > 0` (from the conditional reduction, `x = √2 w`). -/
theorem gaussLaplace2_eq_J {N : ℝ} (hN : 0 < N) :
    gaussLaplace2 N = gaussJ (1 / (2 * N)) / Real.sqrt (2 * Real.pi * N) := by
  rw [gaussLaplace2_eq_integral hN.le]
  have h1 : ∫ x : ℝ, Real.exp (-x ^ 2 / 2) / Real.sqrt (1 + N * x ^ 2) =
      2 * ∫ x in Ioi (0 : ℝ), Real.exp (-x ^ 2 / 2) / Real.sqrt (1 + N * x ^ 2) := by
    rw [← integral_comp_abs (f := fun x => Real.exp (-x ^ 2 / 2) / Real.sqrt (1 + N * x ^ 2))]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [sq_abs]
  have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  have h2 : ∫ x in Ioi (0 : ℝ), Real.exp (-x ^ 2 / 2) / Real.sqrt (1 + N * x ^ 2) =
      Real.sqrt 2 * ∫ w in Ioi (0 : ℝ), Real.exp (-(Real.sqrt 2 * w) ^ 2 / 2) /
        Real.sqrt (1 + N * (Real.sqrt 2 * w) ^ 2) := by
    rw [integral_comp_mul_left_Ioi (fun x => Real.exp (-x ^ 2 / 2) / Real.sqrt (1 + N * x ^ 2)) 0
      hs2, mul_zero, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hs2.ne', one_mul]
  have h3 : ∀ w ∈ Ioi (0 : ℝ), Real.exp (-(Real.sqrt 2 * w) ^ 2 / 2) /
      Real.sqrt (1 + N * (Real.sqrt 2 * w) ^ 2) =
      (Real.sqrt (2 * N))⁻¹ * (Real.exp (-w ^ 2) / Real.sqrt (w ^ 2 + 1 / (2 * N))) := by
    intro w _
    have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have e1 : -(Real.sqrt 2 * w) ^ 2 / 2 = -w ^ 2 := by rw [mul_pow, hs]; ring
    have e2 : 1 + N * (Real.sqrt 2 * w) ^ 2 = (2 * N) * (w ^ 2 + 1 / (2 * N)) := by
      rw [mul_pow, hs]; field_simp; ring
    rw [e1, e2, Real.sqrt_mul (by positivity)]
    field_simp
  rw [h1, h2, setIntegral_congr_fun measurableSet_Ioi h3, integral_const_mul]
  unfold gaussJ
  simp_rw [mul_div_assoc]
  rw [integral_const_mul]
  have hsπ : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN
  set I := ∫ w in Ioi (0 : ℝ), Real.exp (-w ^ 2) / Real.sqrt (w ^ 2 + 1 / (2 * N)) with hI
  clear_value I
  rw [Real.sqrt_mul (x := 2 * Real.pi) (by positivity) N,
    Real.sqrt_mul (x := 2) (by norm_num) Real.pi, Real.sqrt_mul (x := 2) (by norm_num) N]
  field_simp

/-- ★★ **The two-term expansion with an explicit remainder**: for `N ≥ 1/2`,
`|Z_N − (log N + 3 log 2 − γ)/√(2πN)| ≤ (log(2N) + 3)/(2N √(2πN))`. -/
theorem gaussLaplace2_two_term_bound {N : ℝ} (hN : 1 / 2 ≤ N) :
    |gaussLaplace2 N - (Real.log N + 3 * Real.log 2 - Real.eulerMascheroniConstant) /
      Real.sqrt (2 * Real.pi * N)| ≤
      (Real.log (2 * N) + 3) / (2 * N * Real.sqrt (2 * Real.pi * N)) := by
  have hN0 : 0 < N := by linarith
  have hε : 0 < 1 / (2 * N) := by positivity
  have hε1 : 1 / (2 * N) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  have hb := gaussJ_two_term hε hε1
  have hs : 0 < Real.sqrt (2 * Real.pi * N) := Real.sqrt_pos.2 (by positivity)
  have hlog4 : Real.log (4 / (1 / (2 * N))) = Real.log N + 3 * Real.log 2 := by
    rw [show (4 : ℝ) / (1 / (2 * N)) = 2 ^ 3 * N by field_simp; ring,
      Real.log_mul (by norm_num) hN0.ne', Real.log_pow]
    push_cast; ring
  have hlog1 : Real.log (1 / (1 / (2 * N))) = Real.log (2 * N) := by rw [one_div_one_div]
  rw [hlog4, hlog1] at hb
  rw [gaussLaplace2_eq_J hN0, ← sub_div, abs_div, abs_of_pos hs,
    show (Real.log (2 * N) + 3) / (2 * N * Real.sqrt (2 * Real.pi * N)) =
      1 / (2 * N) * (Real.log (2 * N) + 3) / Real.sqrt (2 * Real.pi * N) by field_simp]
  exact div_le_div_of_nonneg_right hb hs.le

/-- ★★★ **The depth-two Gaussian deep linear network expansion**:
`Z_N = (log N + 3 log 2 − γ)/√(2πN) + O(N^{−3/2} log N)` (the note's eq. (dln_gauss) at
`L = 2`). -/
theorem gaussLaplace2_two_term :
    (fun N : ℝ => gaussLaplace2 N -
      (Real.log N + 3 * Real.log 2 - Real.eulerMascheroniConstant) / Real.sqrt (2 * Real.pi * N))
      =O[atTop] fun N => N ^ (-(3 / 2 : ℝ)) * Real.log N := by
  refine Asymptotics.IsBigO.of_bound (5 / (2 * Real.sqrt (2 * Real.pi))) ?_
  filter_upwards [eventually_ge_atTop (3 : ℝ)] with N hN3
  have hN : 0 < N := by linarith
  have hlog : 1 ≤ Real.log N := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos _) (by linarith [Real.exp_one_lt_d9])
  have hb := gaussLaplace2_two_term_bound (by linarith : 1 / 2 ≤ N)
  have hsπ : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hN.le _) (by linarith))]
  refine hb.trans ?_
  have hlog2 : Real.log (2 * N) = Real.log 2 + Real.log N := Real.log_mul two_ne_zero hN.ne'
  have h2 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hpow : N ^ (-(3 / 2 : ℝ)) = 1 / (N * Real.sqrt N) := by
    rw [Real.rpow_neg hN.le, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hN,
      Real.rpow_one, Real.sqrt_eq_rpow, inv_eq_one_div]
  rw [hpow, Real.sqrt_mul (by positivity) N]
  calc (Real.log (2 * N) + 3) / (2 * N * (Real.sqrt (2 * Real.pi) * Real.sqrt N))
      ≤ 5 * Real.log N / (2 * N * (Real.sqrt (2 * Real.pi) * Real.sqrt N)) :=
        div_le_div_of_nonneg_right (by linarith) (by positivity)
    _ = 5 / (2 * Real.sqrt (2 * Real.pi)) * (1 / (N * Real.sqrt N) * Real.log N) := by
        field_simp

end Grammar
