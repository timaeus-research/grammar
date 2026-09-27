/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.CrossingFlatPrior

/-!
# The depth-two deep linear network with flat prior: the partition function to all orders

For `K = (w₁w₂)²/2` on `[−1, 1]²` with the flat prior,

  `Z_N = ∫_{[−1,1]²} e^{−N K} dw = √(2π/N) (log N + γ + log 2) + 4 ∫_1^∞ e^{−Nt²/2} log t dt`,

with `0 ≤ 4 ∫_1^∞ e^{−Nt²/2} log t dt ≤ 4 e^{−N/2}/N`  (★★★ `crossing_flat_allOrders`,
`crossing_flat_remainder_le`): a single pole of order two at the exponent `½`, the coefficients
`√(2π)` of `N^{−1/2} log N` and `√(2π)(γ + log 2)` of `N^{−1/2}`, and an exponentially small
remainder — the complete expansion of examples_slop §2, eq. (dln_flat) at `L = 2`.  The
constant term is the Gaussian logarithmic moment, obtained from Mathlib's derivative of the
Gamma integral at `½` (`Complex.hasDerivAt_GammaIntegral`, `Complex.hasDerivAt_Gamma_one_half`):
`∫_0^∞ e^{−u²/2} log u du = −(√(2π)/4)(γ + log 2)`.  Zero `sorry`/`axiom`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Grammar

/-- `Γ'(½) = ∫_0^∞ t^{−1/2} log t e^{−t} dt = −√π (γ + 2 log 2)`. -/
theorem integral_rpow_log_exp_half :
    ∫ t in Ioi (0 : ℝ), t ^ (-(1 / 2 : ℝ)) * (Real.log t * Real.exp (-t)) =
      -Real.sqrt Real.pi * (Real.eulerMascheroniConstant + 2 * Real.log 2) := by
  have h1 : HasDerivAt Complex.Gamma
      (∫ t : ℝ in Ioi 0, (t : ℂ) ^ ((1 / 2 : ℂ) - 1) *
        ((Real.log t : ℂ) * (Real.exp (-t) : ℂ))) (1 / 2) := by
    have h := Complex.hasDerivAt_GammaIntegral (s := 1 / 2) (by norm_num)
    refine h.congr_of_eventuallyEq ?_
    have hopen : {s : ℂ | 0 < s.re} ∈ nhds (1 / 2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hopen] with s hs
    exact Complex.Gamma_eq_integral hs
  have huniq := h1.unique Complex.hasDerivAt_Gamma_one_half
  have hcast : (∫ t : ℝ in Ioi 0, (t : ℂ) ^ ((1 / 2 : ℂ) - 1) *
      ((Real.log t : ℂ) * (Real.exp (-t) : ℂ))) =
      ((∫ t in Ioi (0 : ℝ), t ^ (-(1 / 2 : ℝ)) * (Real.log t * Real.exp (-t)) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht' : (0 : ℝ) < t := ht
    push_cast
    rw [Complex.ofReal_cpow ht'.le]
    congr 2
    push_cast
    ring
  rw [hcast] at huniq
  apply Complex.ofReal_injective
  rw [huniq]
  push_cast
  rw [← Complex.ofNat_log]

/-- `∫_0^∞ e^{−x²} log x dx = −(√π/4)(γ + 2 log 2)`. -/
theorem integral_exp_neg_sq_log :
    ∫ x in Ioi (0 : ℝ), Real.exp (-x ^ 2) * Real.log x =
      -(Real.sqrt Real.pi / 4) * (Real.eulerMascheroniConstant + 2 * Real.log 2) := by
  have h := integral_comp_rpow_Ioi_of_pos
    (g := fun y : ℝ => y ^ (-(1 / 2 : ℝ)) * (Real.log y * Real.exp (-y)) / 4) (p := 2) two_pos
  have e : ∀ x ∈ Ioi (0 : ℝ), ((2 : ℝ) * x ^ ((2 : ℝ) - 1)) •
      (fun y : ℝ => y ^ (-(1 / 2 : ℝ)) * (Real.log y * Real.exp (-y)) / 4) (x ^ (2 : ℝ)) =
      Real.exp (-x ^ 2) * Real.log x := by
    intro x hx
    have hx' : (0 : ℝ) < x := hx
    simp only [smul_eq_mul]
    rw [← Real.rpow_mul hx'.le, Real.log_rpow hx', show (2 : ℝ) - 1 = 1 by norm_num,
      Real.rpow_one, show (2 : ℝ) * (-(1 / 2)) = -1 by norm_num, Real.rpow_neg_one,
      Real.rpow_two]
    field_simp
    ring
  rw [← setIntegral_congr_fun measurableSet_Ioi e, h, integral_div, integral_rpow_log_exp_half]
  ring

/-- `|log x| ≤ 2 x^{−1/2} + x` for `x > 0`. -/
theorem abs_log_le_rpow (x : ℝ) (hx : 0 < x) : |Real.log x| ≤ 2 * x ^ (-(1 / 2 : ℝ)) + x := by
  have h0 : 0 ≤ x ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hx.le _
  rcases le_or_gt 1 x with h | h
  · rw [abs_of_nonneg (Real.log_nonneg h)]
    have := Real.log_le_sub_one_of_pos hx
    linarith
  · rw [abs_of_neg (Real.log_neg hx h)]
    have h1 : Real.log (x ^ (-(1 / 2 : ℝ))) = -(1 / 2) * Real.log x := Real.log_rpow hx _
    have h2 := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx (-(1 / 2 : ℝ)))
    linarith

/-- `e^{−bx²} log x` is integrable on `(0, ∞)` for `b > 0`. -/
theorem integrableOn_exp_neg_mul_sq_log {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun x : ℝ => Real.exp (-b * x ^ 2) * Real.log x) (Ioi 0) := by
  have hg : IntegrableOn (fun x : ℝ => (2 * x ^ (-(1 / 2 : ℝ)) + x) * Real.exp (-b * x ^ 2))
      (Ioi 0) := by
    have h1 := (integrable_rpow_mul_exp_neg_mul_sq hb (s := -(1 / 2)) (by norm_num)).integrableOn
      (s := Ioi (0 : ℝ))
    have h2 := (integrable_rpow_mul_exp_neg_mul_sq hb (s := 1) (by norm_num)).integrableOn
      (s := Ioi (0 : ℝ))
    refine IntegrableOn.congr_fun ((h1.const_mul 2).add h2) (fun x _ => ?_) measurableSet_Ioi
    simp only [Pi.add_apply, Real.rpow_one]
    ring
  refine hg.mono' ?_ ?_
  · exact (by fun_prop : Measurable fun x : ℝ => Real.exp (-b * x ^ 2) * Real.log x)
      |>.aestronglyMeasurable
  · refine ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc Real.exp (-b * x ^ 2) * |Real.log x|
        ≤ Real.exp (-b * x ^ 2) * (2 * x ^ (-(1 / 2 : ℝ)) + x) :=
          mul_le_mul_of_nonneg_left (abs_log_le_rpow x hx) (Real.exp_pos _).le
      _ = _ := by ring

/-- The Gaussian logarithmic moment `∫_0^∞ e^{−u²/2} log u du = −(√(2π)/4)(γ + log 2)`. -/
theorem integral_exp_neg_sq_half_log :
    ∫ u in Ioi (0 : ℝ), Real.exp (-u ^ 2 / 2) * Real.log u =
      -(Real.sqrt (2 * Real.pi) / 4) * (Real.eulerMascheroniConstant + Real.log 2) := by
  have hs2 : 0 < Real.sqrt 2 := by positivity
  have h := integral_comp_mul_left_Ioi (fun u : ℝ => Real.exp (-u ^ 2 / 2) * Real.log u) 0 hs2
  rw [mul_zero, smul_eq_mul] at h
  have e : ∀ x ∈ Ioi (0 : ℝ), (fun u : ℝ => Real.exp (-u ^ 2 / 2) * Real.log u) (Real.sqrt 2 * x) =
      Real.log (Real.sqrt 2) * Real.exp (-x ^ 2) + Real.exp (-x ^ 2) * Real.log x := by
    intro x hx
    simp only
    rw [mul_pow, Real.sq_sqrt (by norm_num), Real.log_mul hs2.ne' (ne_of_gt hx),
      show -(2 * x ^ 2) / 2 = -x ^ 2 by ring]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi e] at h
  have hint1 : IntegrableOn (fun x : ℝ => Real.exp (-x ^ 2)) (Ioi 0) :=
    (integrable_exp_neg_mul_sq one_pos).integrableOn.congr_fun (fun x _ => by simp)
      measurableSet_Ioi
  have hint2 : IntegrableOn (fun x : ℝ => Real.exp (-x ^ 2) * Real.log x) (Ioi 0) :=
    (integrableOn_exp_neg_mul_sq_log one_pos).congr_fun (fun x _ => by simp) measurableSet_Ioi
  rw [integral_add (hint1.const_mul _) hint2, integral_const_mul, integral_exp_neg_sq_log] at h
  have hg : ∫ x in Ioi (0 : ℝ), Real.exp (-x ^ 2) = Real.sqrt Real.pi / 2 := by
    have := integral_gaussian_Ioi 1
    simpa using this
  rw [hg, Real.log_sqrt (by norm_num)] at h
  have hI : ∫ u in Ioi (0 : ℝ), Real.exp (-u ^ 2 / 2) * Real.log u =
      Real.sqrt 2 * (Real.log 2 / 2 * (Real.sqrt Real.pi / 2) +
        -(Real.sqrt Real.pi / 4) * (Real.eulerMascheroniConstant + 2 * Real.log 2)) := by
    rw [h]
    field_simp
  rw [hI, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  ring

/-- ★★★ **The depth-two deep linear network with flat prior, to all orders**: for `N > 0`,
`∫_{[−1,1]²} e^{−N (w₁w₂)²/2} dw = √(2π/N)(log N + γ + log 2) + 4∫_1^∞ e^{−Nt²/2} log t dt`. -/
theorem crossing_flat_allOrders {N : ℝ} (hN : 0 < N) :
    ∫ w in Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1, Real.exp (-N * (w.1 * w.2) ^ 2 / 2) =
      Real.sqrt (2 * Real.pi) / Real.sqrt N *
        (Real.log N + Real.eulerMascheroniConstant + Real.log 2) +
        4 * ∫ t in Ioi (1 : ℝ), Real.exp (-N * t ^ 2 / 2) * Real.log t := by
  set G : ℝ → ℝ := fun t => Real.exp (-N * t ^ 2 / 2) * (-2 * Real.log t) with hG
  have hGeven : ∀ t, G (-t) = G t := by
    intro t; simp only [hG, neg_sq, Real.log_neg_eq_log]
  have hGint : IntegrableOn (fun t : ℝ => Real.exp (-N * t ^ 2 / 2) * Real.log t) (Ioi 0) :=
    (integrableOn_exp_neg_mul_sq_log (half_pos hN)).congr_fun (fun x _ => by ring_nf)
      measurableSet_Ioi
  -- C1: the reduction to the polar distribution `2 log(1/|t|) = −2 log t`
  have hred : ∫ w in Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1, Real.exp (-N * (w.1 * w.2) ^ 2 / 2) =
      ∫ t in Ioo (-1 : ℝ) 1, G t := by
    have hl := lintegral_crossing_flat (Ψ := fun t => ENNReal.ofReal (Real.exp (-N * t ^ 2 / 2)))
      (by fun_prop)
    have hbox : IntegrableOn (fun w : ℝ × ℝ => Real.exp (-N * (w.1 * w.2) ^ 2 / 2))
        (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1) :=
      (by fun_prop : Continuous fun w : ℝ × ℝ =>
        Real.exp (-N * (w.1 * w.2) ^ 2 / 2)).continuousOn.integrableOn_compact
        (isCompact_Icc.prod isCompact_Icc)
    have hfun : ∀ t : ℝ, Real.exp (-N * t ^ 2 / 2) * (2 * Real.log (1 / |t|)) = G t := by
      intro t; simp only [hG]; rw [one_div, Real.log_inv, Real.log_abs]; ring
    have hGI : IntervalIntegrable G volume (-1) 1 :=
      ((intervalIntegral.intervalIntegrable_log' (a := -1) (b := 1)).const_mul
        (-2)).continuousOn_mul
        (by fun_prop : Continuous fun t : ℝ => Real.exp (-N * t ^ 2 / 2)).continuousOn
    have hGIo : IntegrableOn G (Ioo (-1 : ℝ) 1) := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)] at hGI
      exact hGI.mono_set Ioo_subset_Ioc_self
    have hGnn : ∀ t ∈ Ioo (-1 : ℝ) 1, 0 ≤ G t := by
      intro t ht
      rw [← hfun]
      refine mul_nonneg (Real.exp_pos _).le (mul_nonneg zero_le_two ?_)
      rcases eq_or_ne t 0 with rfl | h0
      · simp
      · refine Real.log_nonneg ((le_one_div one_pos (abs_pos.mpr h0)).mpr ?_)
        rw [one_div_one]
        exact (abs_lt.mpr ht).le
    have hnn0 : 0 ≤ ∫ t in Ioo (-1 : ℝ) 1, G t :=
      setIntegral_nonneg measurableSet_Ioo hGnn
    have hnn1 : 0 ≤ ∫ w in Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1,
        Real.exp (-N * (w.1 * w.2) ^ 2 / 2) :=
      setIntegral_nonneg (measurableSet_Icc.prod measurableSet_Icc) fun w _ => (Real.exp_pos _).le
    rw [← ENNReal.ofReal_eq_ofReal_iff hnn1 hnn0,
      ofReal_integral_eq_lintegral_ofReal hbox (ae_of_all _ fun w => (Real.exp_pos _).le),
      ofReal_integral_eq_lintegral_ofReal hGIo
        (ae_restrict_of_forall_mem measurableSet_Ioo hGnn), hl]
    refine setLIntegral_congr_fun measurableSet_Ioo fun t _ => ?_
    rw [← hfun, ENNReal.ofReal_mul (Real.exp_pos _).le]
  -- C2: symmetry, `∫_{−1}^{1} G = 2 ∫_0^1 G`
  have hsym : ∫ t in Ioo (-1 : ℝ) 1, G t = 2 * ∫ t in (0 : ℝ)..1, G t := by
    have hGI : IntervalIntegrable G volume (-1) 1 :=
      ((intervalIntegral.intervalIntegrable_log' (a := -1) (b := 1)).const_mul
        (-2)).continuousOn_mul
        (by fun_prop : Continuous fun t : ℝ => Real.exp (-N * t ^ 2 / 2)).continuousOn
    have h1 : IntervalIntegrable G volume (-1) 0 :=
      hGI.mono_set (uIcc_subset_uIcc_left (by norm_num [uIcc_of_le]))
    have h2 : IntervalIntegrable G volume 0 1 :=
      hGI.mono_set (uIcc_subset_uIcc_right (by norm_num [uIcc_of_le]))
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num),
      ← intervalIntegral.integral_add_adjacent_intervals h1 h2]
    have : ∫ t in (-1 : ℝ)..0, G t = ∫ t in (0 : ℝ)..1, G t := by
      rw [show (-1 : ℝ) = -(1 : ℝ) by norm_num, show (0 : ℝ) = -(0 : ℝ) by norm_num,
        ← intervalIntegral.integral_comp_neg]
      simp only [hGeven, neg_zero]
    rw [this]; ring
  -- C3: `∫_0^1 = ∫_0^∞ − ∫_1^∞`
  have hsplit : ∫ t in (0 : ℝ)..1, G t =
      -2 * ((∫ t in Ioi (0 : ℝ), Real.exp (-N * t ^ 2 / 2) * Real.log t) -
        ∫ t in Ioi (1 : ℝ), Real.exp (-N * t ^ 2 / 2) * Real.log t) := by
    have hu := setIntegral_union (f := fun t : ℝ => Real.exp (-N * t ^ 2 / 2) * Real.log t)
      (μ := volume) (s := Ioc (0 : ℝ) 1) (t := Ioi 1) Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hGint.mono_set Ioc_subset_Ioi_self) (hGint.mono_set (Ioi_subset_Ioi one_pos.le))
    rw [Ioc_union_Ioi_eq_Ioi zero_le_one] at hu
    rw [intervalIntegral.integral_of_le zero_le_one]
    have : ∫ t in Ioc (0 : ℝ) 1, G t =
        -2 * ∫ t in Ioc (0 : ℝ) 1, Real.exp (-N * t ^ 2 / 2) * Real.log t := by
      rw [← integral_const_mul]; refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
      simp only [hG]; ring
    rw [this, hu]; ring
  -- C4: the scaling `t = u/√N`
  have hscale : ∫ t in Ioi (0 : ℝ), Real.exp (-N * t ^ 2 / 2) * Real.log t =
      (Real.sqrt N)⁻¹ * (-(Real.sqrt (2 * Real.pi) / 4) *
        (Real.eulerMascheroniConstant + Real.log 2)) -
        Real.log (Real.sqrt N) * (Real.sqrt (Real.pi / (N / 2)) / 2) := by
    have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN
    have h := integral_comp_mul_left_Ioi (fun u : ℝ => Real.exp (-u ^ 2 / 2) * Real.log u) 0 hsN
    rw [mul_zero, smul_eq_mul, integral_exp_neg_sq_half_log] at h
    have e : ∀ t ∈ Ioi (0 : ℝ),
        (fun u : ℝ => Real.exp (-u ^ 2 / 2) * Real.log u) (Real.sqrt N * t) =
        Real.log (Real.sqrt N) * Real.exp (-N * t ^ 2 / 2) +
          Real.exp (-N * t ^ 2 / 2) * Real.log t := by
      intro t ht
      simp only
      rw [mul_pow, Real.sq_sqrt hN.le, Real.log_mul hsN.ne' (ne_of_gt ht),
        show -(N * t ^ 2) / 2 = -N * t ^ 2 / 2 by ring]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi e] at h
    have hint1 : IntegrableOn (fun t : ℝ => Real.exp (-N * t ^ 2 / 2)) (Ioi 0) :=
      (integrable_exp_neg_mul_sq (half_pos hN)).integrableOn.congr_fun (fun x _ => by ring_nf)
        measurableSet_Ioi
    rw [integral_add (hint1.const_mul _) hGint, integral_const_mul] at h
    have hg : ∫ t in Ioi (0 : ℝ), Real.exp (-N * t ^ 2 / 2) =
        Real.sqrt (Real.pi / (N / 2)) / 2 := by
      have := integral_gaussian_Ioi (N / 2)
      rw [← this]
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      ring_nf
    rw [hg] at h
    linarith
  -- assemble
  rw [hred, hsym, hsplit, hscale, Real.log_sqrt hN.le,
    show Real.pi / (N / 2) = 2 * Real.pi / N by field_simp,
    Real.sqrt_div (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
  ring

/-- The remainder is nonnegative and exponentially small:
`0 ≤ ∫_1^∞ e^{−Nt²/2} log t dt ≤ e^{−N/2}/N`. -/
theorem crossing_flat_remainder_le {N : ℝ} (hN : 0 < N) :
    0 ≤ ∫ t in Ioi (1 : ℝ), Real.exp (-N * t ^ 2 / 2) * Real.log t ∧
      ∫ t in Ioi (1 : ℝ), Real.exp (-N * t ^ 2 / 2) * Real.log t ≤ Real.exp (-N / 2) / N := by
  have hint : IntegrableOn (fun t : ℝ => Real.exp (-N * t ^ 2 / 2) * Real.log t) (Ioi 1) :=
    ((integrableOn_exp_neg_mul_sq_log (half_pos hN)).congr_fun (fun x _ => by ring_nf)
      measurableSet_Ioi).mono_set (Ioi_subset_Ioi zero_le_one)
  have hint' : IntegrableOn (fun t : ℝ => t * Real.exp (-N * t ^ 2 / 2)) (Ioi 1) :=
    ((integrable_rpow_mul_exp_neg_mul_sq (half_pos hN) (s := 1) (by norm_num)).integrableOn
      (s := Ioi (1 : ℝ))).congr_fun (fun x _ => by simp only [Real.rpow_one]; ring_nf)
      measurableSet_Ioi
  -- the antiderivative `−e^{−Nt²/2}/N`
  have hderiv : ∀ t ∈ Ioi (1 : ℝ),
      HasDerivAt (fun t => -Real.exp (-N * t ^ 2 / 2) / N) (t * Real.exp (-N * t ^ 2 / 2)) t := by
    intro t _
    have h := ((hasDerivAt_pow 2 t).const_mul (-N)).div_const 2
    have h2 := (Real.hasDerivAt_exp _).comp t h
    have h3 := (h2.neg).div_const N
    refine h3.congr_deriv ?_
    field_simp
    ring
  have htend : Filter.Tendsto (fun t : ℝ => -Real.exp (-N * t ^ 2 / 2) / N) Filter.atTop
      (nhds 0) := by
    have h1 : Filter.Tendsto (fun t : ℝ => -N * t ^ 2 / 2) Filter.atTop Filter.atBot := by
      have := (Filter.tendsto_pow_atTop two_ne_zero : Filter.Tendsto (fun t : ℝ => t ^ 2)
        Filter.atTop Filter.atTop)
      exact (this.const_mul_atTop_of_neg (neg_neg_of_pos hN)).atBot_div_const two_pos
    have h2 := Real.tendsto_exp_atBot.comp h1
    have h3 := (h2.neg).div_const N
    simpa using h3
  have hval : ∫ t in Ioi (1 : ℝ), t * Real.exp (-N * t ^ 2 / 2) = Real.exp (-N / 2) / N := by
    rw [integral_Ioi_of_hasDerivAt_of_tendsto (by fun_prop : Continuous fun t : ℝ =>
      -Real.exp (-N * t ^ 2 / 2) / N).continuousWithinAt hderiv hint' htend]
    ring_nf
  constructor
  · exact setIntegral_nonneg measurableSet_Ioi fun t ht =>
      mul_nonneg (Real.exp_pos _).le (Real.log_nonneg (le_of_lt ht))
  · rw [← hval]
    refine setIntegral_mono_on hint hint' measurableSet_Ioi fun t ht => ?_
    have ht1 : (1 : ℝ) < t := ht
    have := Real.log_le_sub_one_of_pos (zero_lt_one.trans ht1)
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le

end Grammar
