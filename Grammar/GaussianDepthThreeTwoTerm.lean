/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.GaussianDepthThree
import Grammar.MonomialRenormalised

/-!
# The depth-three Gaussian DLN: the second logarithmic coefficient

Refining `Grammar.GaussianDepthThree`: with the depth-two expansion inserted on `|x| ≥ N^{−1/2}`
and the Gaussian kept on the whole outer region through `h(x) = e^{−x²/2} − 1_{(0,1]}(x)`, whose
renormalised constant is `R₀ = ∫₀^∞ h(x)/x dx = (log 2 − γ)/2` (`integral_gaussH_div`, from
`Grammar.MonomialRenormalised`), the depth-two remainder integrated with its full logarithm
`∫_{N^{−1/2}}^∞ (log(2Nx²)+3)/x³ dx = O(N)` (`depthThree_rem_le`), and the cutoff terms
`∫₀^{N^{−1/2}} h/x = O(1/N)`, `∫ h log x/x = O(1)`,

  `|Z_3(N) − [(log N)² + 4(2 log 2 − γ) log N]/(4π√N)| ≤ 12/√N`  for `N ≥ 1`
  (★★★ `gaussLaplaceL_three_two_term_bound`),

so the second coefficient of the note's eq. (dln_gauss) at `L = 3` is `(2 log 2 − γ)/π`
(★★★ `gaussLaplaceL_three_two_term`, the `O(N^{−1/2})` form); the constant term stays a derivation
(Astra round-8 target 2).  Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

/-- `h(x) = e^{−x²/2} − 1_{(0,1]}(x)`. -/
noncomputable def gaussH (x : ℝ) : ℝ := Real.exp (-x ^ 2 / 2) - (Ioc 0 1).indicator 1 x

/-- `R₀ = ∫₀^∞ h(x)/x dx = (log 2 − γ)/2`. -/
theorem integral_gaussH_div :
    ∫ x in Ioi (0 : ℝ), gaussH x / x = (Real.log 2 - Real.eulerMascheroniConstant) / 2 := by
  have h := ampRenorm_monoAmp_one
  unfold ampRenorm monoAmp at h
  have e : ∀ u ∈ Ioi (0 : ℝ), (Real.exp (-u ^ (2 * 1) / 2) - (Ioc 0 1).indicator 1 u) * (2 / u) =
      2 * (gaussH u / u) := fun u _ => by unfold gaussH; ring
  rw [setIntegral_congr_fun measurableSet_Ioi e, integral_const_mul] at h
  linarith

theorem measurable_gaussH : Measurable gaussH := by
  unfold gaussH
  exact (by fun_prop : Measurable fun x : ℝ => Real.exp (-x ^ 2 / 2)).sub
    (measurable_one.indicator measurableSet_Ioc)

theorem gaussH_inner {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) :
    -(x ^ 2 / 2) ≤ gaussH x ∧ gaussH x ≤ 0 := by
  unfold gaussH
  rw [indicator_of_mem hx, Pi.one_apply]
  constructor
  · linarith [Real.add_one_le_exp (-x ^ 2 / 2)]
  · linarith [Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg x] : -x ^ 2 / 2 ≤ 0)]

theorem gaussH_outer {x : ℝ} (hx : 1 < x) :
    0 ≤ gaussH x ∧ gaussH x ≤ Real.exp (-x / 2) := by
  unfold gaussH
  rw [indicator_of_notMem (fun hm => absurd hm.2 (not_le.2 hx)), sub_zero]
  exact ⟨(Real.exp_pos _).le, Real.exp_le_exp.2 (by nlinarith)⟩

/-- `∫₀^∞ h/x` is integrable on `(0, ∞)`. -/
theorem integrableOn_gaussH_div : IntegrableOn (fun x : ℝ => gaussH x / x) (Ioi 0) := by
  have h1 := integrableOn_ampRenorm_inner (monoAmp_ampData one_pos)
  have h2 := integrableOn_ampRenorm_outer (monoAmp_ampData one_pos)
  have e : ∀ x : ℝ, gaussH x / x = 1 / 2 * ((monoAmp 1 x - (Ioc 0 1).indicator 1 x) * (2 / x)) := by
    intro x; unfold gaussH monoAmp; ring
  simp_rw [e]
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  have h1' : IntegrableOn (fun x : ℝ => 1 / 2 * ((monoAmp 1 x - (Ioc 0 1).indicator 1 x) * (2 / x)))
      (Ioc 0 1) := h1.const_mul _
  have h2' : IntegrableOn (fun x : ℝ => 1 / 2 * ((monoAmp 1 x - (Ioc 0 1).indicator 1 x) * (2 / x)))
      (Ioi 1) := h2.const_mul _
  exact h1'.union h2'

/-- The cutoff piece `|∫₀^a h/x| ≤ a²/2` for `0 ≤ a ≤ 1`. -/
theorem abs_integral_gaussH_div_Ioc_le {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    |∫ x in Ioc (0 : ℝ) a, gaussH x / x| ≤ a ^ 2 / 2 := by
  have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (0 : ℝ) a)
    (f := fun x => gaussH x / x) (C := a / 2)
    (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top) (fun x hx => by
      have hx0 : 0 < x := hx.1
      obtain ⟨h1, h2⟩ := gaussH_inner ⟨hx0, hx.2.trans ha1⟩
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hx0, abs_of_nonpos h2, div_le_iff₀ hx0]
      nlinarith [hx.2])
  have hv : volume.real (Ioc (0 : ℝ) a) = a := by
    rw [measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith), sub_zero]
  rw [Real.norm_eq_abs, hv] at h
  linarith [h]

theorem measurable_gaussH_log : Measurable fun x : ℝ => gaussH x * Real.log x / x :=
  (measurable_gaussH.mul Real.measurable_log).div measurable_id

/-- On `(0, 1]`, `|h(x) log x/x| ≤ 1/2`. -/
theorem norm_gaussH_log_inner {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) :
    ‖gaussH x * Real.log x / x‖ ≤ 1 / 2 := by
  have hx0 : 0 < x := hx.1
  obtain ⟨h1, h2⟩ := gaussH_inner hx
  have hlog : Real.log x ≤ 0 := Real.log_nonpos hx0.le hx.2
  have hxlog : -(x * Real.log x) ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (inv_pos.2 hx0)
    rw [Real.log_inv] at this
    have h := mul_le_mul_of_nonneg_left this hx0.le
    rw [mul_sub, mul_inv_cancel₀ hx0.ne'] at h
    nlinarith
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hx0, abs_mul, abs_of_nonpos h2, abs_of_nonpos hlog,
    div_le_iff₀ hx0]
  nlinarith

/-- On `(1, ∞)`, `|h(x) log x/x| ≤ e^{−x/2}`. -/
theorem norm_gaussH_log_outer {x : ℝ} (hx : 1 < x) :
    ‖gaussH x * Real.log x / x‖ ≤ Real.exp (-x / 2) := by
  have hx0 : 0 < x := by linarith
  obtain ⟨h1, h2⟩ := gaussH_outer hx
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx.le
  have hlx : Real.log x ≤ x := by linarith [Real.log_le_sub_one_of_pos hx0]
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hx0, abs_mul, abs_of_nonneg h1, abs_of_nonneg hlog0,
    div_le_iff₀ hx0]
  exact mul_le_mul h2 hlx hlog0 (Real.exp_pos _).le

theorem integrableOn_exp_neg_half_Ioi_one :
    IntegrableOn (fun x : ℝ => Real.exp (-x / 2)) (Ioi 1) := by
  refine IntegrableOn.congr_fun (s := Ioi 1)
    (exp_neg_integrableOn_Ioi 1 (by norm_num : (0 : ℝ) < 1 / 2)) (fun w _ => ?_) measurableSet_Ioi
  congr 1
  ring

theorem integrableOn_gaussH_log_Ioc {a : ℝ} (ha0 : 0 ≤ a) :
    IntegrableOn (fun x : ℝ => gaussH x * Real.log x / x) (Ioc a 1) := by
  refine Measure.integrableOn_of_bounded (M := 1 / 2)
    (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
    measurable_gaussH_log.aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioc]
  exact Eventually.of_forall fun x hx => norm_gaussH_log_inner ⟨lt_of_le_of_lt ha0 hx.1, hx.2⟩

theorem integrableOn_gaussH_log_Ioi_one :
    IntegrableOn (fun x : ℝ => gaussH x * Real.log x / x) (Ioi 1) := by
  refine integrableOn_exp_neg_half_Ioi_one.mono' measurable_gaussH_log.aestronglyMeasurable.restrict
    ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  exact Eventually.of_forall fun x hx => norm_gaussH_log_outer hx

theorem integrableOn_gaussH_log {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    IntegrableOn (fun x : ℝ => gaussH x * Real.log x / x) (Ioi a) := by
  rw [← Ioc_union_Ioi_eq_Ioi ha1]
  exact (integrableOn_gaussH_log_Ioc ha0).union integrableOn_gaussH_log_Ioi_one

/-- The logarithmic piece `|∫_a^∞ h(x) log x/x dx| ≤ 3` for `0 ≤ a ≤ 1`. -/
theorem abs_integral_gaussH_log_le {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    |∫ x in Ioi a, gaussH x * Real.log x / x| ≤ 3 := by
  have hbound_in : |∫ x in Ioc a 1, gaussH x * Real.log x / x| ≤ 1 / 2 := by
    have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc a 1)
      (f := fun x => gaussH x * Real.log x / x) (C := 1 / 2)
      (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top)
      (fun x hx => norm_gaussH_log_inner ⟨lt_of_le_of_lt ha0 hx.1, hx.2⟩)
    have hv : volume.real (Ioc a 1) = 1 - a := by
      rw [measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
    rw [Real.norm_eq_abs, hv] at h
    nlinarith
  have hbound_out : |∫ x in Ioi 1, gaussH x * Real.log x / x| ≤ 2 := by
    have h := norm_integral_le_of_norm_le (μ := volume.restrict (Ioi (1 : ℝ)))
      (f := fun x => gaussH x * Real.log x / x) integrableOn_exp_neg_half_Ioi_one (by
        rw [ae_restrict_iff' measurableSet_Ioi]
        exact Eventually.of_forall fun x hx => norm_gaussH_log_outer hx)
    rw [Real.norm_eq_abs, integral_exp_neg_div_Ioi_one (by norm_num : (0 : ℝ) < 2)] at h
    have := Real.exp_le_one_iff.2 (by norm_num : (-1 / 2 : ℝ) ≤ 0)
    nlinarith [Real.exp_pos (-1 / 2)]
  rw [← Ioc_union_Ioi_eq_Ioi ha1, setIntegral_union (Ioc_disjoint_Ioi le_rfl)
    measurableSet_Ioi (integrableOn_gaussH_log_Ioc ha0) integrableOn_gaussH_log_Ioi_one]
  calc |(∫ x in Ioc a 1, gaussH x * Real.log x / x) + ∫ x in Ioi 1, gaussH x * Real.log x / x|
      ≤ |∫ x in Ioc a 1, gaussH x * Real.log x / x| + |∫ x in Ioi 1, gaussH x * Real.log x / x| :=
        abs_add_le _ _
    _ ≤ 1 / 2 + 2 := add_le_add hbound_in hbound_out
    _ ≤ 3 := by norm_num

/-! ### The depth-two remainder integrated with its full logarithm -/

/-- `log y ≤ 2√y` for `y > 0`. -/
theorem log_le_two_sqrt {y : ℝ} (hy : 0 < y) : Real.log y ≤ 2 * Real.sqrt y := by
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.2 hy
  have h := Real.log_le_sub_one_of_pos hs
  rw [Real.log_sqrt hy.le] at h
  linarith

/-- The pointwise bound `|F(x) − g(x)L(x)| ≤ x^{−3}/(πN^{3/2}) + x^{−2}/(2πN)` for `x ≥ N^{−1/2}`,
where `L(x) = (log N + 2 log x + c)/(√(2π)√N x)`. -/
theorem depthThree_rem_pointwise {N x : ℝ} (hN : 1 ≤ N) (hx : 1 / Real.sqrt N ≤ x) :
    |depthThreeF N x - gaussDensity x *
      ((Real.log N + 2 * Real.log x + 3 * Real.log 2 - Real.eulerMascheroniConstant) /
        (Real.sqrt (2 * Real.pi) * (Real.sqrt N * x)))| ≤
      1 / (Real.pi * (N * Real.sqrt N)) * x ^ (-3 : ℝ) + 1 / (2 * Real.pi * N) * x ^ (-2 : ℝ) := by
  have hN0 : 0 < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
  have hNx : 1 ≤ N * x ^ 2 := by
    have h2 : 1 / Real.sqrt N * Real.sqrt N = 1 := by field_simp
    have h3 : (1 / Real.sqrt N) ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ (by positivity) hx 2
    have h4 : (1 / Real.sqrt N) ^ 2 * N = 1 := by
      rw [div_pow, one_pow, Real.sq_sqrt hN0.le]; field_simp
    nlinarith
  obtain ⟨hb, -⟩ := gaussLaplace2_bounds hNx
  have hsqrt : Real.sqrt (N * x ^ 2) = Real.sqrt N * x := by
    rw [Real.sqrt_mul hN0.le, Real.sqrt_sq hx0.le]
  have hlog : Real.log (N * x ^ 2) = Real.log N + 2 * Real.log x := by
    rw [Real.log_mul hN0.ne' (by positivity), Real.log_pow]; push_cast; ring
  rw [hsqrt, hlog] at hb
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hsq : Real.sqrt (2 * Real.pi) * Real.sqrt (2 * Real.pi) = 2 * Real.pi :=
    Real.mul_self_sqrt (by positivity)
  -- the numerator of the remainder: `log(2Nx²) + 3 ≤ 4 + 2√N x`
  have hnum : Real.log (2 * (N * x ^ 2)) + 3 ≤ 4 + 2 * (Real.sqrt N * x) := by
    have h1 : Real.log (2 * (N * x ^ 2)) = Real.log 2 + Real.log (N * x ^ 2) :=
      Real.log_mul two_ne_zero (by positivity)
    have h2 : Real.log 2 ≤ 1 := by
      linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
    have h3 := log_le_two_sqrt (by positivity : 0 < N * x ^ 2)
    rw [hsqrt] at h3
    linarith
  have hnum0 : 0 ≤ Real.log (2 * (N * x ^ 2)) + 3 := by
    have : 0 ≤ Real.log (2 * (N * x ^ 2)) := Real.log_nonneg (by nlinarith)
    linarith
  have hg : gaussDensity x ≤ 1 / Real.sqrt (2 * Real.pi) := by
    unfold gaussDensity
    exact div_le_div_of_nonneg_right (Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg x])) hs.le
  have hg0 : 0 ≤ gaussDensity x := gaussDensity_nonneg x
  have hrpow3 : x ^ (-3 : ℝ) = 1 / x ^ 3 := by
    rw [Real.rpow_neg hx0.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, one_div]
  have hrpow2 : x ^ (-2 : ℝ) = 1 / x ^ 2 := by
    rw [Real.rpow_neg hx0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, one_div]
  rw [hrpow3, hrpow2]
  unfold depthThreeF
  rw [← mul_sub, abs_mul, abs_of_nonneg hg0]
  generalize hsdef : Real.sqrt (2 * Real.pi) = s at hb hs hsq hg ⊢
  have hpi : Real.pi = s * s / 2 := by linarith
  calc gaussDensity x * |gaussLaplace2 (N * x ^ 2) -
        (Real.log N + 2 * Real.log x + 3 * Real.log 2 - Real.eulerMascheroniConstant) /
          (s * (Real.sqrt N * x))|
      ≤ 1 / s *
          ((Real.log (2 * (N * x ^ 2)) + 3) / (2 * (N * x ^ 2) * (s * (Real.sqrt N * x)))) :=
        mul_le_mul hg hb (abs_nonneg _) (by positivity)
    _ ≤ 1 / s * ((4 + 2 * (Real.sqrt N * x)) / (2 * (N * x ^ 2) * (s * (Real.sqrt N * x)))) := by
        gcongr
    _ = 1 / (Real.pi * (N * Real.sqrt N)) * (1 / x ^ 3) + 1 / (2 * Real.pi * N) * (1 / x ^ 2) := by
        rw [hpi]
        field_simp
        ring

/-- `∫_{N^{−1/2}}^∞ |F − gL| ≤ 1/(π√N)`. -/
theorem depthThree_rem_le {N : ℝ} (hN : 1 ≤ N) :
    |∫ x in Ioi (1 / Real.sqrt N), (depthThreeF N x - gaussDensity x *
      ((Real.log N + 2 * Real.log x + 3 * Real.log 2 - Real.eulerMascheroniConstant) /
        (Real.sqrt (2 * Real.pi) * (Real.sqrt N * x))))| ≤ 1 / (Real.pi * Real.sqrt N) := by
  have hN0 : 0 < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have ha0 : 0 < 1 / Real.sqrt N := by positivity
  have h3 : IntegrableOn (fun x : ℝ => x ^ (-3 : ℝ)) (Ioi (1 / Real.sqrt N)) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) ha0
  have h2 : IntegrableOn (fun x : ℝ => x ^ (-2 : ℝ)) (Ioi (1 / Real.sqrt N)) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) ha0
  have hmaj : IntegrableOn (fun x : ℝ => 1 / (Real.pi * (N * Real.sqrt N)) * x ^ (-3 : ℝ) +
      1 / (2 * Real.pi * N) * x ^ (-2 : ℝ)) (Ioi (1 / Real.sqrt N)) :=
    (h3.const_mul _).add (h2.const_mul _)
  have h := norm_integral_le_of_norm_le (μ := volume.restrict (Ioi (1 / Real.sqrt N)))
    (f := fun x => depthThreeF N x - gaussDensity x *
      ((Real.log N + 2 * Real.log x + 3 * Real.log 2 - Real.eulerMascheroniConstant) /
        (Real.sqrt (2 * Real.pi) * (Real.sqrt N * x)))) hmaj ?_
  · rw [Real.norm_eq_abs] at h
    refine h.trans ?_
    rw [integral_add (h3.const_mul _) (h2.const_mul _), integral_const_mul, integral_const_mul,
      integral_Ioi_rpow_of_lt (by norm_num) ha0, integral_Ioi_rpow_of_lt (by norm_num) ha0]
    have e3 : (1 / Real.sqrt N) ^ (-3 + 1 : ℝ) = N := by
      rw [show (-3 + 1 : ℝ) = -2 by norm_num, Real.rpow_neg (by positivity), one_div,
        Real.inv_rpow hsN.le, inv_inv, Real.rpow_two, Real.sq_sqrt hN0.le]
    have e2 : (1 / Real.sqrt N) ^ (-2 + 1 : ℝ) = Real.sqrt N := by
      rw [show (-2 + 1 : ℝ) = -1 by norm_num, Real.rpow_neg_one, one_div, inv_inv]
    rw [e3, e2]
    have hpi : 0 < Real.pi := Real.pi_pos
    have hsq : Real.sqrt N ^ 2 = N := Real.sq_sqrt hN0.le
    refine le_of_eq ?_
    field_simp
    linear_combination 2 * hsq
  · rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun x hx => ?_
    rw [Real.norm_eq_abs]
    exact depthThree_rem_pointwise hN (le_of_lt hx)

/-! ### The main term with the Gaussian kept -/

/-- The `(a, 1]`-integrand `P(x) = (log N + 2 log x + c)/x`. -/
noncomputable def depthThreeP (N x : ℝ) : ℝ :=
  (Real.log N + 2 * Real.log x + (3 * Real.log 2 - Real.eulerMascheroniConstant)) / x

theorem integrableOn_depthThreeP {N : ℝ} (hN : 1 ≤ N) :
    IntegrableOn (depthThreeP N) (Ioc (1 / Real.sqrt N) 1) := by
  have hN0 : 0 < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have ha0 : 0 < 1 / Real.sqrt N := by positivity
  have ha1 : 1 / Real.sqrt N ≤ 1 := by
    rw [div_le_one hsN]; exact Real.one_le_sqrt.2 hN
  rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le ha1]
  refine ContinuousOn.intervalIntegrable ?_
  unfold depthThreeP
  have hlogc : ContinuousOn Real.log (uIcc (1 / Real.sqrt N) 1) :=
    Real.continuousOn_log.mono fun x hx => by
      rw [uIcc_of_le ha1] at hx
      exact ne_of_gt (lt_of_lt_of_le ha0 hx.1)
  refine ContinuousOn.div (by fun_prop) continuousOn_id fun x hx => ?_
  rw [uIcc_of_le ha1] at hx
  exact ne_of_gt (lt_of_lt_of_le ha0 hx.1)

/-- `∫_a^1 P = (log N)²/4 + (c/2) log N` (from `integral_depthThreeM`). -/
theorem integral_depthThreeP {N : ℝ} (hN : 1 ≤ N) :
    ∫ x in Ioc (1 / Real.sqrt N) 1, depthThreeP N x =
      (Real.log N) ^ 2 / 4 + (3 * Real.log 2 - Real.eulerMascheroniConstant) / 2 * Real.log N := by
  have hN0 : 0 < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have e : ∀ x ∈ Ioc (1 / Real.sqrt N) 1, depthThreeP N x =
      2 * Real.pi * Real.sqrt N * depthThreeM N x := by
    intro x hx
    have hx0 : 0 < x := lt_trans (by positivity) hx.1
    unfold depthThreeP depthThreeM
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioc e, integral_const_mul, integral_depthThreeM hN]
  field_simp

/-- The pointwise decomposition of the main-term integrand on `(a, ∞)`:
`g(x) L(x) = (1/(2π√N)) (1_{(a,1]} P(x) + (log N + c) h(x)/x + 2 h(x) log x/x)`. -/
theorem depthThree_gL_eq {N x : ℝ} (hN : 1 ≤ N) (hx : 1 / Real.sqrt N < x) :
    gaussDensity x *
      ((Real.log N + 2 * Real.log x + 3 * Real.log 2 - Real.eulerMascheroniConstant) /
        (Real.sqrt (2 * Real.pi) * (Real.sqrt N * x))) =
      1 / (2 * Real.pi * Real.sqrt N) * ((Ioc (1 / Real.sqrt N) 1).indicator (depthThreeP N) x +
        ((Real.log N + (3 * Real.log 2 - Real.eulerMascheroniConstant)) * (gaussH x / x) +
          2 * (gaussH x * Real.log x / x))) := by
  have hN0 : 0 < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have hx0 : 0 < x := lt_trans (by positivity) hx
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hsq : Real.sqrt (2 * Real.pi) * Real.sqrt (2 * Real.pi) = 2 * Real.pi :=
    Real.mul_self_sqrt (by positivity)
  unfold gaussDensity gaussH depthThreeP
  generalize hsdef : Real.sqrt (2 * Real.pi) = s at hs hsq ⊢
  have hpi : Real.pi = s * s / 2 := by linarith
  rw [hpi]
  by_cases h1 : x ≤ 1
  · have hm : x ∈ Ioc (1 / Real.sqrt N) 1 := ⟨hx, h1⟩
    have hm' : x ∈ Ioc (0 : ℝ) 1 := ⟨hx0, h1⟩
    rw [indicator_of_mem hm, indicator_of_mem hm', Pi.one_apply]
    field_simp
    ring
  · have h1' := not_le.1 h1
    rw [indicator_of_notMem (fun hm => absurd hm.2 (not_le.2 h1')),
      indicator_of_notMem (fun hm => absurd hm.2 (not_le.2 h1')), sub_zero]
    field_simp
    ring

theorem integrableOn_depthThree_gL {N : ℝ} (hN : 1 ≤ N) :
    IntegrableOn (fun x : ℝ => gaussDensity x *
      ((Real.log N + 2 * Real.log x + 3 * Real.log 2 - Real.eulerMascheroniConstant) /
        (Real.sqrt (2 * Real.pi) * (Real.sqrt N * x)))) (Ioi (1 / Real.sqrt N)) := by
  have hN0 : 0 < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have ha0 : 0 < 1 / Real.sqrt N := by positivity
  have ha1 : 1 / Real.sqrt N ≤ 1 := by
    rw [div_le_one hsN]; exact Real.one_le_sqrt.2 hN
  have hP₁ : IntegrableOn ((Ioc (1 / Real.sqrt N) 1).indicator (depthThreeP N))
      (Ioi (1 / Real.sqrt N)) :=
    ((integrableOn_depthThreeP hN).integrable_indicator measurableSet_Ioc).integrableOn
  have hQ1 : IntegrableOn (fun x : ℝ => gaussH x / x) (Ioi (1 / Real.sqrt N)) :=
    integrableOn_gaussH_div.mono_set (Ioi_subset_Ioi ha0.le)
  have hQ2 := integrableOn_gaussH_log ha0.le ha1
  have h : IntegrableOn (fun x : ℝ => 1 / (2 * Real.pi * Real.sqrt N) *
      ((Ioc (1 / Real.sqrt N) 1).indicator (depthThreeP N) x +
        ((Real.log N + (3 * Real.log 2 - Real.eulerMascheroniConstant)) * (gaussH x / x) +
          2 * (gaussH x * Real.log x / x)))) (Ioi (1 / Real.sqrt N)) :=
    (hP₁.add ((hQ1.const_mul _).add (hQ2.const_mul _))).const_mul _
  exact h.congr_fun (fun x hx => (depthThree_gL_eq hN hx).symm) measurableSet_Ioi

/-- ★★ **The main term**: with `I_a = ∫₀^a h/x` and `J_a = ∫_a^∞ h log x/x`, `a = N^{−1/2}`,
`∫_a^∞ g L = (1/(2π√N)) ((log N)²/4 + (c/2) log N + (log N + c)(R₀ − I_a) + 2 J_a)`. -/
theorem integral_depthThree_main {N : ℝ} (hN : 1 ≤ N) :
    ∫ x in Ioi (1 / Real.sqrt N), gaussDensity x *
      ((Real.log N + 2 * Real.log x + 3 * Real.log 2 - Real.eulerMascheroniConstant) /
        (Real.sqrt (2 * Real.pi) * (Real.sqrt N * x))) =
      1 / (2 * Real.pi * Real.sqrt N) * ((Real.log N) ^ 2 / 4 +
        (3 * Real.log 2 - Real.eulerMascheroniConstant) / 2 * Real.log N +
        (Real.log N + (3 * Real.log 2 - Real.eulerMascheroniConstant)) *
          ((Real.log 2 - Real.eulerMascheroniConstant) / 2 -
            ∫ x in Ioc (0 : ℝ) (1 / Real.sqrt N), gaussH x / x) +
        2 * ∫ x in Ioi (1 / Real.sqrt N), gaussH x * Real.log x / x) := by
  have hN0 : 0 < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have ha0 : 0 < 1 / Real.sqrt N := by positivity
  have ha1 : 1 / Real.sqrt N ≤ 1 := by
    rw [div_le_one hsN]; exact Real.one_le_sqrt.2 hN
  have hP₁ : IntegrableOn ((Ioc (1 / Real.sqrt N) 1).indicator (depthThreeP N))
      (Ioi (1 / Real.sqrt N)) :=
    ((integrableOn_depthThreeP hN).integrable_indicator measurableSet_Ioc).integrableOn
  have hQ1 : IntegrableOn (fun x : ℝ => gaussH x / x) (Ioi (1 / Real.sqrt N)) :=
    integrableOn_gaussH_div.mono_set (Ioi_subset_Ioi ha0.le)
  have hQ2 := integrableOn_gaussH_log ha0.le ha1
  have hQ1' : IntegrableOn (fun x : ℝ =>
      (Real.log N + (3 * Real.log 2 - Real.eulerMascheroniConstant)) * (gaussH x / x))
      (Ioi (1 / Real.sqrt N)) := hQ1.const_mul _
  have hQ2' : IntegrableOn (fun x : ℝ => 2 * (gaussH x * Real.log x / x))
      (Ioi (1 / Real.sqrt N)) := hQ2.const_mul _
  have hQ : IntegrableOn (fun x : ℝ =>
      (Real.log N + (3 * Real.log 2 - Real.eulerMascheroniConstant)) * (gaussH x / x) +
        2 * (gaussH x * Real.log x / x)) (Ioi (1 / Real.sqrt N)) := hQ1'.add hQ2'
  rw [setIntegral_congr_fun measurableSet_Ioi (fun x hx => depthThree_gL_eq hN hx),
    integral_const_mul, integral_add hP₁ hQ, integral_add hQ1' hQ2', integral_const_mul,
    integral_const_mul,
    setIntegral_indicator measurableSet_Ioc,
    show Ioi (1 / Real.sqrt N) ∩ Ioc (1 / Real.sqrt N) 1 = Ioc (1 / Real.sqrt N) 1 from
      inter_eq_right.2 fun x hx => hx.1,
    integral_depthThreeP hN]
  -- `∫_a^∞ h/x = R₀ − ∫₀^a h/x`
  have hsplit : ∫ x in Ioi (1 / Real.sqrt N), gaussH x / x =
      (Real.log 2 - Real.eulerMascheroniConstant) / 2 -
        ∫ x in Ioc (0 : ℝ) (1 / Real.sqrt N), gaussH x / x := by
    rw [← integral_gaussH_div, ← Ioc_union_Ioi_eq_Ioi ha0.le,
      setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
        (integrableOn_gaussH_div.mono_set Ioc_subset_Ioi_self) hQ1]
    ring
  rw [hsplit]
  ring

/-! ### Assembly -/

/-- ★★★ **The depth-three Gaussian DLN, two terms with bounded residual**: for `N ≥ 1`,
`|Z_3(N) − [(log N)² + 4(2 log 2 − γ) log N]/(4π√N)| ≤ 12/√N`. -/
theorem gaussLaplaceL_three_two_term_bound {N : ℝ} (hN : 1 ≤ N) :
    |gaussLaplaceL 3 N - ((Real.log N) ^ 2 +
      4 * (2 * Real.log 2 - Real.eulerMascheroniConstant) * Real.log N) /
        (4 * Real.pi * Real.sqrt N)| ≤ 12 / Real.sqrt N := by
  have hN0 : 0 < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have hsN1 : 1 ≤ Real.sqrt N := Real.one_le_sqrt.2 hN
  have hsNN : Real.sqrt N ≤ N := by nlinarith [Real.sq_sqrt hN0.le]
  have ha0 : 0 < 1 / Real.sqrt N := by positivity
  have ha1 : 1 / Real.sqrt N ≤ 1 := by rw [div_le_one hsN]; exact hsN1
  have hℓ : 0 ≤ Real.log N := Real.log_nonneg hN
  have hℓ2 : Real.log N ≤ 2 * Real.sqrt N := log_le_two_sqrt hN0
  have hpi := Real.pi_gt_three
  have hs2 : 2 ≤ Real.sqrt (2 * Real.pi) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    nlinarith
  obtain ⟨hc1, hc3⟩ := three_log_two_sub_gamma_bounds
  have hR0 : 0 < Real.log 2 - Real.eulerMascheroniConstant ∧
      Real.log 2 - Real.eulerMascheroniConstant < 1 := by
    have := Real.log_two_gt_d9
    have := Real.eulerMascheroniConstant_lt_two_thirds
    have := Real.one_half_lt_eulerMascheroniConstant
    have h4 : Real.log 2 ≤ 1 := by
      linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
    constructor <;> linarith
  -- the split of the recursion integral
  have hF := integrable_depthThreeF hN0.le
  have hsplit : ∫ x in Ioi (0 : ℝ), depthThreeF N x =
      (∫ x in Ioc (0 : ℝ) (1 / Real.sqrt N), depthThreeF N x) +
        ∫ x in Ioi (1 / Real.sqrt N), depthThreeF N x := by
    rw [← Ioc_union_Ioi_eq_Ioi ha0.le,
      setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hF.integrableOn hF.integrableOn]
  have hgL := integrableOn_depthThree_gL hN
  have hmid : ∫ x in Ioi (1 / Real.sqrt N), depthThreeF N x =
      (∫ x in Ioi (1 / Real.sqrt N), gaussDensity x *
        ((Real.log N + 2 * Real.log x + 3 * Real.log 2 - Real.eulerMascheroniConstant) /
          (Real.sqrt (2 * Real.pi) * (Real.sqrt N * x)))) +
        ∫ x in Ioi (1 / Real.sqrt N), (depthThreeF N x - gaussDensity x *
          ((Real.log N + 2 * Real.log x + 3 * Real.log 2 - Real.eulerMascheroniConstant) /
            (Real.sqrt (2 * Real.pi) * (Real.sqrt N * x)))) := by
    rw [integral_sub hF.integrableOn hgL]; ring
  have h0 := depthThree_inner_le hN0.le ha0.le
  have hE := depthThree_rem_le hN
  have hI := abs_integral_gaussH_div_Ioc_le ha0.le ha1
  have hJ := abs_integral_gaussH_log_le ha0.le ha1
  have hmain := integral_depthThree_main hN
  rw [gaussLaplaceL_three hN0.le]
  change |(∫ x, depthThreeF N x) - _| ≤ _
  rw [integral_depthThreeF_eq_two_mul, hsplit, hmid, hmain]
  set I₀ := ∫ x in Ioc (0 : ℝ) (1 / Real.sqrt N), depthThreeF N x with hI₀
  set E := ∫ x in Ioi (1 / Real.sqrt N), (depthThreeF N x - gaussDensity x *
    ((Real.log N + 2 * Real.log x + 3 * Real.log 2 - Real.eulerMascheroniConstant) /
      (Real.sqrt (2 * Real.pi) * (Real.sqrt N * x)))) with hEdef
  set Ia := ∫ x in Ioc (0 : ℝ) (1 / Real.sqrt N), gaussH x / x with hIa
  set Ja := ∫ x in Ioi (1 / Real.sqrt N), gaussH x * Real.log x / x with hJa
  clear_value I₀ E Ia Ja
  set c := 3 * Real.log 2 - Real.eulerMascheroniConstant with hc
  set d := Real.log 2 - Real.eulerMascheroniConstant with hd
  have hcd : 2 * Real.log 2 - Real.eulerMascheroniConstant = c / 2 + d / 2 := by rw [hc, hd]; ring
  rw [hcd]
  clear_value c d
  set ℓ := Real.log N with hℓdef
  clear_value ℓ
  clear hI₀ hEdef hIa hJa hc hd hℓdef hsplit hmid hmain hgL hF
  have hkey : 2 * (I₀ + (1 / (2 * Real.pi * Real.sqrt N) * (ℓ ^ 2 / 4 + c / 2 * ℓ +
      (ℓ + c) * (d / 2 - Ia) + 2 * Ja) + E)) -
      (ℓ ^ 2 + 4 * (c / 2 + d / 2) * ℓ) / (4 * Real.pi * Real.sqrt N) =
      2 * I₀ + 2 * E + 1 / (Real.pi * Real.sqrt N) * (c * (d / 2) - (ℓ + c) * Ia + 2 * Ja) := by
    field_simp
    ring
  rw [hkey]
  rw [abs_le] at h0 hE hI hJ ⊢
  -- the bracket is bounded by 10
  have hIa2 : (1 / Real.sqrt N) ^ 2 = 1 / N := by
    rw [div_pow, one_pow, Real.sq_sqrt hN0.le]
  rw [hIa2] at hI
  have hbr : |c * (d / 2) - (ℓ + c) * Ia + 2 * Ja| ≤ 10 := by
    have h1 : |c * (d / 2)| ≤ 3 / 2 := by
      rw [abs_of_nonneg (by nlinarith)]; nlinarith
    have h2 : |(ℓ + c) * Ia| ≤ 5 / 2 := by
      rw [abs_mul, abs_of_nonneg (by linarith)]
      have hIabs : |Ia| ≤ 1 / N / 2 := abs_le.2 hI
      calc (ℓ + c) * |Ia| ≤ (2 * Real.sqrt N + 3) * (1 / N / 2) :=
            mul_le_mul (by linarith) hIabs (abs_nonneg _) (by positivity)
        _ ≤ 5 / 2 := by
            rw [show (2 * Real.sqrt N + 3) * (1 / N / 2) = (2 * Real.sqrt N + 3) / (2 * N) by ring,
              div_le_iff₀ (by positivity)]
            nlinarith
    have h3 : |2 * Ja| ≤ 6 := by rw [abs_mul, abs_of_pos two_pos]; linarith [abs_le.2 hJ]
    calc |c * (d / 2) - (ℓ + c) * Ia + 2 * Ja| ≤ |c * (d / 2) - (ℓ + c) * Ia| + |2 * Ja| :=
          abs_add_le _ _
      _ ≤ |c * (d / 2)| + |(ℓ + c) * Ia| + |2 * Ja| := by
          linarith [abs_sub (c * (d / 2)) ((ℓ + c) * Ia)]
      _ ≤ 10 := by linarith
  rw [abs_le] at hbr
  have hT0 : 2 * (1 / Real.sqrt (2 * Real.pi) * (1 / Real.sqrt N)) ≤ 1 / Real.sqrt N := by
    rw [show 2 * (1 / Real.sqrt (2 * Real.pi) * (1 / Real.sqrt N)) =
      (2 / Real.sqrt (2 * Real.pi)) / Real.sqrt N by field_simp]
    refine div_le_div_of_nonneg_right ?_ hsN.le
    rw [div_le_iff₀ (by linarith)]; linarith
  have hT1 : 2 * (1 / (Real.pi * Real.sqrt N)) ≤ 1 / Real.sqrt N := by
    rw [show 2 * (1 / (Real.pi * Real.sqrt N)) = (2 / Real.pi) / Real.sqrt N by field_simp]
    refine div_le_div_of_nonneg_right ?_ hsN.le
    rw [div_le_iff₀ (by positivity)]; linarith
  have hT2 : 1 / (Real.pi * Real.sqrt N) * 10 ≤ 4 / Real.sqrt N := by
    rw [show 1 / (Real.pi * Real.sqrt N) * 10 = (10 / Real.pi) / Real.sqrt N by field_simp]
    refine div_le_div_of_nonneg_right ?_ hsN.le
    rw [div_le_iff₀ (by positivity)]; linarith
  have hT2' : 1 / (Real.pi * Real.sqrt N) * (c * (d / 2) - (ℓ + c) * Ia + 2 * Ja) ≤
      4 / Real.sqrt N := by
    have : 0 ≤ 1 / (Real.pi * Real.sqrt N) := by positivity
    nlinarith
  have hT2'' : -(4 / Real.sqrt N) ≤ 1 / (Real.pi * Real.sqrt N) *
      (c * (d / 2) - (ℓ + c) * Ia + 2 * Ja) := by
    have : 0 ≤ 1 / (Real.pi * Real.sqrt N) := by positivity
    nlinarith
  have hsum : 1 / Real.sqrt N + 1 / Real.sqrt N + 4 / Real.sqrt N ≤ 12 / Real.sqrt N := by
    rw [← add_div, ← add_div]
    exact div_le_div_of_nonneg_right (by norm_num) hsN.le
  constructor <;> linarith [h0.1, h0.2, hE.1, hE.2]

/-- ★★★ `Z_3(N) = [(log N)² + 4(2 log 2 − γ) log N]/(4π√N) + O(N^{−1/2})`: the second coefficient
of the depth-three expansion is `(2 log 2 − γ)/π`. -/
theorem gaussLaplaceL_three_two_term :
    (fun N : ℝ => gaussLaplaceL 3 N - ((Real.log N) ^ 2 +
      4 * (2 * Real.log 2 - Real.eulerMascheroniConstant) * Real.log N) /
        (4 * Real.pi * Real.sqrt N)) =O[atTop] fun N => (Real.sqrt N)⁻¹ := by
  refine Asymptotics.IsBigO.of_bound 12 ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with N hN
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 (by linarith)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hsN), ← div_eq_mul_inv]
  exact gaussLaplaceL_three_two_term_bound hN

end Grammar
