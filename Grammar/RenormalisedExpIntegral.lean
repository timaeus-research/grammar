/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.GammaSecondDerivHalf

/-!
# The renormalised exponential integral `∫₀^∞ (e^{−v} − 1_{(0,1)}(v))/v dv = −γ`

Euler's constant as a renormalised integral: with `Γ'(1) = −γ` (Mathlib) read as the real
integral `∫₀^∞ e^{−v} log v dv = −γ` (`integral_exp_neg_log`), and
`log v = ∫₀^∞ (1_{u ≤ v} − 1_{u ≤ 1}) du/u` (`integral_kernel_log`), Fubini gives

  `∫₀^∞ (e^{−v} − 1_{(0,1]}(v))/v dv = −γ`  (★★★ `integral_renormalised_exp_inv`).

This is the constant behind the two-term expansion of the depth-two Gaussian partition function
`Z_N = (log N + 3 log 2 − γ)/√(2πN) + …` (examples_slop §2, eq. dln_gauss at `L = 2`; the `J(ε)`
route of Astra round 5, completed in `Grammar.GaussianDepthTwoExpansion`).  Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

/-- `∫₀^∞ e^{−v} log v dv = Γ'(1) = −γ`. -/
theorem integral_exp_neg_log :
    ∫ v in Ioi (0 : ℝ), Real.exp (-v) * Real.log v = -Real.eulerMascheroniConstant := by
  have h1 : HasDerivAt Complex.Gamma
      (∫ t : ℝ in Ioi 0, (t : ℂ) ^ ((1 : ℂ) - 1) *
        ((Real.log t : ℂ) * (Real.exp (-t) : ℂ))) 1 := by
    have h := Complex.hasDerivAt_GammaIntegral (s := 1) (by norm_num)
    refine h.congr_of_eventuallyEq ?_
    have hopen : {s : ℂ | 0 < s.re} ∈ nhds (1 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hopen] with s hs
    exact Complex.Gamma_eq_integral hs
  have huniq := h1.unique Complex.hasDerivAt_Gamma_one
  have hcast : (∫ t : ℝ in Ioi 0, (t : ℂ) ^ ((1 : ℂ) - 1) *
      ((Real.log t : ℂ) * (Real.exp (-t) : ℂ))) =
      ((∫ v in Ioi (0 : ℝ), Real.exp (-v) * Real.log v : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [sub_self, Complex.cpow_zero]
    push_cast
    ring
  rw [hcast] at huniq
  exact_mod_cast huniq

/-- The kernel `(1_{u ≤ v} − 1_{u ≤ 1})/u` written as an indicator of the interval between `1` and
`v`, with sign. -/
noncomputable def logKernel (v u : ℝ) : ℝ :=
  (Ioc 1 v).indicator (fun u => u⁻¹) u - (Ioc v 1).indicator (fun u => u⁻¹) u

theorem measurable_logKernel : Measurable (Function.uncurry logKernel) := by
  unfold logKernel Function.uncurry
  refine Measurable.sub ?_ ?_
  · refine Measurable.ite ?_ (measurable_inv.comp measurable_snd) measurable_const
    exact (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd measurable_fst)
  · refine Measurable.ite ?_ (measurable_inv.comp measurable_snd) measurable_const
    exact (measurableSet_lt measurable_fst measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const)

/-- `∫₀^∞ logKernel v u du = log v` for `v > 0`. -/
theorem integral_kernel_log {v : ℝ} (hv : 0 < v) :
    ∫ u in Ioi (0 : ℝ), logKernel v u = Real.log v := by
  unfold logKernel
  rcases le_or_gt 1 v with h | h
  · have e : ∀ u ∈ Ioi (0 : ℝ), (Ioc 1 v).indicator (fun u : ℝ => u⁻¹) u -
        (Ioc v 1).indicator (fun u : ℝ => u⁻¹) u = (Ioc 1 v).indicator (fun u : ℝ => u⁻¹) u := by
      intro u _
      rw [Ioc_eq_empty (show ¬ v < (1 : ℝ) from not_lt.2 h)]
      simp
    rw [setIntegral_congr_fun measurableSet_Ioi e, setIntegral_indicator measurableSet_Ioc,
      show Ioi (0 : ℝ) ∩ Ioc 1 v = Ioc 1 v from inter_eq_right.2 fun u hu => lt_trans one_pos hu.1,
      ← intervalIntegral.integral_of_le h, integral_inv_of_pos one_pos hv, div_one]
  · have e : ∀ u ∈ Ioi (0 : ℝ), (Ioc 1 v).indicator (fun u : ℝ => u⁻¹) u -
        (Ioc v 1).indicator (fun u : ℝ => u⁻¹) u = -(Ioc v 1).indicator (fun u : ℝ => u⁻¹) u := by
      intro u _
      rw [Ioc_eq_empty (show ¬ (1 : ℝ) < v from not_lt.2 h.le)]
      simp
    rw [setIntegral_congr_fun measurableSet_Ioi e, integral_neg,
      setIntegral_indicator measurableSet_Ioc,
      show Ioi (0 : ℝ) ∩ Ioc v 1 = Ioc v 1 from inter_eq_right.2 fun u hu => lt_trans hv hu.1,
      ← intervalIntegral.integral_of_le h.le, integral_inv_of_pos hv one_pos, one_div,
      Real.log_inv, neg_neg]

/-- The inner `v`-integral: `∫₀^∞ e^{−v} logKernel v u dv = (e^{−u} − 1_{u ≤ 1})/u` for `u > 0`. -/
theorem integral_exp_kernel {u : ℝ} (hu : 0 < u) :
    ∫ v in Ioi (0 : ℝ), Real.exp (-v) * logKernel v u =
      (Real.exp (-u) - (Ioc 0 1).indicator 1 u) / u := by
  unfold logKernel
  -- `u ∈ Ioc 1 v ↔ 1 < u ∧ u ≤ v`; `u ∈ Ioc v 1 ↔ v < u ∧ u ≤ 1`
  have e : ∀ v ∈ Ioi (0 : ℝ), Real.exp (-v) * ((Ioc 1 v).indicator (fun u : ℝ => u⁻¹) u -
      (Ioc v 1).indicator (fun u : ℝ => u⁻¹) u) =
      (if 1 < u then (Ici u).indicator (fun v => Real.exp (-v)) v else 0) * u⁻¹ -
        (if u ≤ 1 then (Iio u).indicator (fun v => Real.exp (-v)) v else 0) * u⁻¹ := by
    intro v _
    simp only [indicator, mem_Ioc, mem_Ici, mem_Iio]
    by_cases h1 : 1 < u <;> by_cases h2 : u ≤ v <;> by_cases h3 : v < u <;> by_cases h4 : u ≤ 1 <;>
      simp [h1, h2, h3, h4]
  rw [setIntegral_congr_fun measurableSet_Ioi e]
  have hexp : IntegrableOn (fun v : ℝ => Real.exp (-v)) (Ioi 0) := by
    have := exp_neg_integrableOn_Ioi (0 : ℝ) one_pos
    refine this.congr_fun (fun v _ => ?_) measurableSet_Ioi
    simp
  have hA : IntegrableOn (fun v : ℝ => (if 1 < u then (Ici u).indicator (fun v => Real.exp (-v)) v
      else 0) * u⁻¹) (Ioi 0) := by
    split_ifs
    · exact (hexp.indicator measurableSet_Ici).mul_const _
    · simp
  have hB : IntegrableOn (fun v : ℝ => (if u ≤ 1 then (Iio u).indicator (fun v => Real.exp (-v)) v
      else 0) * u⁻¹) (Ioi 0) := by
    split_ifs
    · exact (hexp.indicator measurableSet_Iio).mul_const _
    · simp
  rw [integral_sub hA hB, integral_mul_const, integral_mul_const]
  rcases lt_or_ge 1 u with h1 | h1
  · have h2 : ¬ u ≤ 1 := not_le.2 h1
    simp only [if_pos h1, if_neg h2, integral_zero, zero_mul, sub_zero]
    rw [setIntegral_indicator measurableSet_Ici,
      show Ioi (0 : ℝ) ∩ Ici u = Ici u from inter_eq_right.2 fun v hv => lt_of_lt_of_le hu hv,
      integral_Ici_eq_integral_Ioi, integral_exp_neg_Ioi, indicator_of_notMem (by
        simp only [mem_Ioc, not_and, not_le]; intro _; exact h1), sub_zero, div_eq_mul_inv]
  · have h2 : ¬ 1 < u := not_lt.2 h1
    simp only [if_neg h2, if_pos h1, integral_zero, zero_mul, zero_sub]
    rw [setIntegral_indicator measurableSet_Iio,
      show Ioi (0 : ℝ) ∩ Iio u = Ioo 0 u from rfl, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hu.le,
      indicator_of_mem (s := Ioc (0 : ℝ) 1) (f := (1 : ℝ → ℝ)) ⟨hu, h1⟩]
    have : ∫ v in (0 : ℝ)..u, Real.exp (-v) = 1 - Real.exp (-u) := by
      have := intervalIntegral.integral_comp_neg (a := 0) (b := u) (f := Real.exp)
      rw [this, neg_zero, integral_exp, Real.exp_zero]
    rw [this, Pi.one_apply, div_eq_mul_inv]
    ring

/-- `∫₀^∞ |logKernel v u| du = |log v|` for `v > 0`. -/
theorem integral_abs_kernel_log {v : ℝ} (hv : 0 < v) :
    ∫ u in Ioi (0 : ℝ), |logKernel v u| = |Real.log v| := by
  unfold logKernel
  rcases le_or_gt 1 v with h | h
  · have e : ∀ u ∈ Ioi (0 : ℝ), |(Ioc 1 v).indicator (fun u : ℝ => u⁻¹) u -
        (Ioc v 1).indicator (fun u : ℝ => u⁻¹) u| = (Ioc 1 v).indicator (fun u : ℝ => u⁻¹) u := by
      intro u hu
      rw [Ioc_eq_empty (show ¬ v < (1 : ℝ) from not_lt.2 h)]
      simp only [indicator_empty, sub_zero]
      exact abs_of_nonneg
        (indicator_nonneg (fun u hu => inv_nonneg.2 (le_trans zero_le_one hu.1.le)) u)
    rw [setIntegral_congr_fun measurableSet_Ioi e, setIntegral_indicator measurableSet_Ioc,
      show Ioi (0 : ℝ) ∩ Ioc 1 v = Ioc 1 v from inter_eq_right.2 fun u hu => lt_trans one_pos hu.1,
      ← intervalIntegral.integral_of_le h, integral_inv_of_pos one_pos hv, div_one,
      abs_of_nonneg (Real.log_nonneg h)]
  · have e : ∀ u ∈ Ioi (0 : ℝ), |(Ioc 1 v).indicator (fun u : ℝ => u⁻¹) u -
        (Ioc v 1).indicator (fun u : ℝ => u⁻¹) u| = (Ioc v 1).indicator (fun u : ℝ => u⁻¹) u := by
      intro u hu
      rw [Ioc_eq_empty (show ¬ (1 : ℝ) < v from not_lt.2 h.le)]
      simp only [indicator_empty, zero_sub, abs_neg]
      exact abs_of_nonneg (indicator_nonneg (fun u hu => inv_nonneg.2 (le_trans hv.le hu.1.le)) u)
    rw [setIntegral_congr_fun measurableSet_Ioi e, setIntegral_indicator measurableSet_Ioc,
      show Ioi (0 : ℝ) ∩ Ioc v 1 = Ioc v 1 from inter_eq_right.2 fun u hu => lt_trans hv hu.1,
      ← intervalIntegral.integral_of_le h.le, integral_inv_of_pos hv one_pos, one_div,
      Real.log_inv]
    exact (abs_of_nonpos (Real.log_nonpos hv.le h.le)).symm

/-- The kernel is integrable in `u` on `(0, ∞)` for every `v > 0`. -/
theorem integrableOn_logKernel {v : ℝ} (hv : 0 < v) : IntegrableOn (logKernel v) (Ioi 0) := by
  unfold logKernel
  have h1 : IntegrableOn (fun u : ℝ => u⁻¹) (Ioc 1 v) := by
    rcases le_or_gt 1 v with h | h
    · rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le h]
      exact intervalIntegral.intervalIntegrable_inv (fun x hx => by
        rw [uIcc_of_le h] at hx; exact ne_of_gt (lt_of_lt_of_le one_pos hx.1)) continuousOn_id
    · rw [Ioc_eq_empty (show ¬ (1 : ℝ) < v from not_lt.2 h.le)]
      exact integrableOn_empty
  have h2 : IntegrableOn (fun u : ℝ => u⁻¹) (Ioc v 1) := by
    rcases le_or_gt v 1 with h | h
    · rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le h]
      exact intervalIntegral.intervalIntegrable_inv (fun x hx => by
        rw [uIcc_of_le h] at hx; exact ne_of_gt (lt_of_lt_of_le hv hx.1)) continuousOn_id
    · rw [Ioc_eq_empty (show ¬ v < (1 : ℝ) from not_lt.2 h.le)]
      exact integrableOn_empty
  exact ((h1.integrable_indicator measurableSet_Ioc).sub
    (h2.integrable_indicator measurableSet_Ioc)).integrableOn

/-- `e^{−v}|log v|` is integrable on `(0, ∞)`. -/
theorem integrableOn_exp_neg_abs_log :
    IntegrableOn (fun v : ℝ => Real.exp (-v) * |Real.log v|) (Ioi 0) := by
  have hint : IntegrableOn (fun v : ℝ => (2 * v ^ (-(1 / 2 : ℝ)) + v) * Real.exp (-v)) (Ioi 0) := by
    have h1 := integrableOn_rpow_mul_exp_neg_rpow (s := -(1 / 2 : ℝ)) (p := 1) (by norm_num) one_pos
    have h2 := integrableOn_rpow_mul_exp_neg_rpow (s := 1) (p := 1) (by norm_num) one_pos
    refine IntegrableOn.congr_fun ((h1.const_mul 2).add h2) (fun v hv => ?_) measurableSet_Ioi
    simp only [Pi.add_apply, Real.rpow_one]
    ring
  refine hint.mono' (by fun_prop : Measurable fun v : ℝ =>
    Real.exp (-v) * |Real.log v|).aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Eventually.of_forall fun v hv => ?_
  have hv' : (0 : ℝ) < v := hv
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have := abs_log_le_rpow v hv'
  calc Real.exp (-v) * |Real.log v| ≤ Real.exp (-v) * (2 * v ^ (-(1 / 2 : ℝ)) + v) :=
        mul_le_mul_of_nonneg_left this (Real.exp_pos _).le
    _ = (2 * v ^ (-(1 / 2 : ℝ)) + v) * Real.exp (-v) := by ring

/-- ★★★ **Euler's constant as a renormalised integral**:
`∫₀^∞ (e^{−u} − 1_{(0,1]}(u))/u du = −γ`. -/
theorem integral_renormalised_exp_inv :
    ∫ u in Ioi (0 : ℝ), (Real.exp (-u) - (Ioc 0 1).indicator 1 u) / u =
      -Real.eulerMascheroniConstant := by
  set g : ℝ → ℝ → ℝ := fun u v => Real.exp (-v) * logKernel v u with hg
  have hmeas : AEStronglyMeasurable (Function.uncurry g)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    refine Measurable.aestronglyMeasurable ?_
    have : Function.uncurry g = fun p : ℝ × ℝ => Real.exp (-p.2) *
        Function.uncurry logKernel (p.2, p.1) := by
      funext p; rfl
    rw [this]
    exact ((Real.measurable_exp.comp measurable_snd.neg).mul
      (measurable_logKernel.comp (measurable_snd.prodMk measurable_fst)))
  have hint : Integrable (Function.uncurry g)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    rw [integrable_prod_iff' hmeas]
    constructor
    · rw [ae_restrict_iff' measurableSet_Ioi]
      refine Eventually.of_forall fun v hv => ?_
      have hv' : (0 : ℝ) < v := hv
      refine ((integrableOn_logKernel hv').const_mul (Real.exp (-v))).congr
        (Eventually.of_forall fun x => ?_)
      rfl
    · have e : ∀ v ∈ Ioi (0 : ℝ), (∫ u in Ioi (0 : ℝ), ‖Function.uncurry g (u, v)‖) =
          Real.exp (-v) * |Real.log v| := by
        intro v hv
        have hv' : (0 : ℝ) < v := hv
        simp only [hg, Function.uncurry_apply_pair, Real.norm_eq_abs, abs_mul,
          abs_of_pos (Real.exp_pos _)]
        rw [integral_const_mul, integral_abs_kernel_log hv']
      exact (integrableOn_exp_neg_abs_log.congr_fun (fun v hv => (e v hv).symm) measurableSet_Ioi)
  have hswap := integral_integral_swap hint
  -- the two iterated integrals
  have hL : ∫ v in Ioi (0 : ℝ), ∫ u in Ioi (0 : ℝ), g u v = -Real.eulerMascheroniConstant := by
    rw [← integral_exp_neg_log]
    refine setIntegral_congr_fun measurableSet_Ioi fun v hv => ?_
    have hv' : (0 : ℝ) < v := hv
    simp only [hg]
    rw [integral_const_mul, integral_kernel_log hv']
  have hR : ∫ u in Ioi (0 : ℝ), ∫ v in Ioi (0 : ℝ), g u v =
      ∫ u in Ioi (0 : ℝ), (Real.exp (-u) - (Ioc 0 1).indicator 1 u) / u := by
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    have hu' : (0 : ℝ) < u := hu
    simp only [hg]
    exact integral_exp_kernel hu'
  rw [← hR, hswap, hL]

end Grammar
