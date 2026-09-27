/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.GaussianDepthThreeTwoTerm
import Grammar.ConeAveragedPosterior

/-!
# The depth-three Gaussian DLN: the constant term as an integral-defined limit

DCXXIII bounds the residual `√N Z_3(N) − [(log N)² + 4(2 log 2 − γ) log N]/(4π)` by `12`; here it
converges (★★★ `gaussLaplaceL_three_residual`):

  `√N Z_3(N) − [(log N)² + 4(2 log 2 − γ) log N]/(4π) → (c R₀ + 2J)/π + (2/s) Q`,

`c = 3 log 2 − γ`, `R₀ = (log 2 − γ)/2`, `s = √(2π)`, with the two integral-defined constants
`J = ∫₀^∞ h(x) log x/x dx` (`gaussJlog`) and `Q = ∫₀^∞ q(v) dv` (`depthThreeQint`),
`q(v) = Z_2(v²) − 1_{(1,∞)}(v)(2 log v + c)/(s v)` (`depthThreeQ`).  The route is the DCXXIII
decomposition `Z_3 = 2(I₀ + M + E)` at the cutoff `a = N^{−1/2}`: the inner piece `√N I₀` and the
remainder `√N E` are, after `x = v/√N`, the integrals of `g(v/√N) Z_2(v²)` on `(0,1]` and of
`g(v/√N) q(v)` on `(1,∞)`, which converge by dominated convergence (`q` is `O(v^{−2})` from
`gaussLaplace2_bounds`) to `(1/s) ∫ q`; the cutoff term `(log N + c) I_a` is `O(log N/N)` and the
logarithmic moment `J_a → J`.  The exact values `J = R₀²/2 + π²/48` and `Q = (c² + 5π²/6)/(4s)`,
which
give `((4 log 2 − 2γ)² + π²)/(4π)`, stay derivations (examples_slop §2; Astra round-10 target 3).
Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

/-! ### Measurability of the depth-two partition function -/

theorem measurable_gaussLaplace2 : Measurable gaussLaplace2 := by
  unfold gaussLaplace2
  exact (by fun_prop : Continuous fun p : ℝ × (ℝ × ℝ) =>
    Real.exp (-p.1 * (p.2.1 * p.2.2) ^ 2 / 2) *
      (Real.exp (-(p.2.1 ^ 2 + p.2.2 ^ 2) / 2) / (2 * Real.pi))).stronglyMeasurable
        |>.integral_prod_right'.measurable

/-! ### The function `q` -/

/-- `q(v) = Z_2(v²) − 1_{(1,∞)}(v)(2 log v + c)/(s v)`, `c = 3 log 2 − γ`, `s = √(2π)`. -/
noncomputable def depthThreeQ (v : ℝ) : ℝ :=
  gaussLaplace2 (v ^ 2) - (Ioi (1 : ℝ)).indicator (fun v =>
    (2 * Real.log v + (3 * Real.log 2 - Real.eulerMascheroniConstant)) /
      (Real.sqrt (2 * Real.pi) * v)) v

theorem measurable_depthThreeQ : Measurable depthThreeQ := by
  unfold depthThreeQ
  exact (measurable_gaussLaplace2.comp (measurable_id.pow_const 2)).sub
    (Measurable.indicator (by fun_prop) measurableSet_Ioi)

theorem depthThreeQ_inner {v : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) :
    depthThreeQ v = gaussLaplace2 (v ^ 2) := by
  unfold depthThreeQ
  rw [indicator_apply, if_neg (fun h : v ∈ Ioi (1 : ℝ) => absurd hv.2 (not_le.2 h)), sub_zero]

/-- On `(1,∞)`: `|q(v)| ≤ 4/(s v²)`, from `gaussLaplace2_bounds` at `t = v²`. -/
theorem depthThreeQ_outer_le {v : ℝ} (hv : 1 < v) :
    |depthThreeQ v| ≤ 4 / (Real.sqrt (2 * Real.pi) * v ^ 2) := by
  have hv0 : 0 < v := by linarith
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have ht : 1 ≤ v ^ 2 := one_le_pow₀ hv.le
  have hb := (gaussLaplace2_bounds ht).1
  rw [Real.sqrt_sq hv0.le, Real.log_pow] at hb
  unfold depthThreeQ
  rw [indicator_of_mem (show v ∈ Ioi (1 : ℝ) from hv)]
  have e : gaussLaplace2 (v ^ 2) -
      (2 * Real.log v + (3 * Real.log 2 - Real.eulerMascheroniConstant)) /
      (Real.sqrt (2 * Real.pi) * v) = gaussLaplace2 (v ^ 2) -
      ((2 : ℕ) * Real.log v + 3 * Real.log 2 - Real.eulerMascheroniConstant) /
        (Real.sqrt (2 * Real.pi) * v) := by push_cast; ring
  rw [e]
  refine hb.trans ?_
  -- `log(2v²) + 3 ≤ 8v`
  have hlog2 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hlogv : Real.log v ≤ 2 * Real.sqrt v := log_le_two_sqrt hv0
  have hsv : Real.sqrt v ≤ v := by
    rw [Real.sqrt_le_left hv0.le]; nlinarith
  have hnum : Real.log (2 * v ^ 2) + 3 ≤ 8 * v := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    push_cast
    nlinarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hv2 : 0 ≤ v ^ 2 := sq_nonneg v
  nlinarith [mul_le_mul_of_nonneg_right hnum (by positivity : 0 ≤ Real.sqrt (2 * Real.pi) * v ^ 2),
    hs, hv2]

theorem integrableOn_depthThreeQ_inner : IntegrableOn depthThreeQ (Ioc 0 1) := by
  refine Measure.integrableOn_of_bounded (M := 1) measure_Ioc_lt_top.ne
    measurable_depthThreeQ.aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioc]
  refine Eventually.of_forall fun v hv => ?_
  rw [depthThreeQ_inner hv, Real.norm_eq_abs, abs_of_nonneg (gaussLaplace2_nonneg (sq_nonneg _))]
  exact gaussLaplace2_le_one (sq_nonneg _)

theorem integrableOn_depthThreeQ_outer : IntegrableOn depthThreeQ (Ioi 1) := by
  have h : IntegrableOn (fun v : ℝ => 4 / Real.sqrt (2 * Real.pi) * v ^ (-2 : ℝ)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos).const_mul _
  refine h.mono' measurable_depthThreeQ.aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Eventually.of_forall fun v hv => ?_
  have hv1 : (1 : ℝ) < v := hv
  have hv0 : 0 < v := by linarith
  rw [Real.norm_eq_abs]
  refine (depthThreeQ_outer_le hv1).trans (le_of_eq ?_)
  rw [Real.rpow_neg hv0.le, Real.rpow_two]
  field_simp

theorem integrableOn_depthThreeQ : IntegrableOn depthThreeQ (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  exact integrableOn_depthThreeQ_inner.union integrableOn_depthThreeQ_outer

/-! ### The two integral-defined constants -/

/-- `J = ∫₀^∞ h(x) log x/x dx`. -/
noncomputable def gaussJlog : ℝ := ∫ x in Ioi (0 : ℝ), gaussH x * Real.log x / x

/-- `Q = ∫₀^∞ q(v) dv`. -/
noncomputable def depthThreeQint : ℝ := ∫ v in Ioi (0 : ℝ), depthThreeQ v

/-- The depth-three constant `(c R₀ + 2J)/π + (2/s) Q`. -/
noncomputable def depthThreeConst : ℝ :=
  ((3 * Real.log 2 - Real.eulerMascheroniConstant) *
      ((Real.log 2 - Real.eulerMascheroniConstant) / 2) +
    2 * gaussJlog) / Real.pi + 2 / Real.sqrt (2 * Real.pi) * depthThreeQint

/-! ### The small pieces -/

theorem tendsto_log_div_atTop : Tendsto (fun N : ℝ => Real.log N / N) atTop (𝓝 0) := by
  have := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  simpa using this

/-- `(log N + c) I_a → 0`, `I_a = ∫₀^a h/x`, `|I_a| ≤ a²/2 = 1/(2N)`. -/
theorem tendsto_cutoff_term :
    Tendsto (fun N : ℝ => (Real.log N + (3 * Real.log 2 - Real.eulerMascheroniConstant)) *
      ∫ x in Ioc (0 : ℝ) (1 / Real.sqrt N), gaussH x / x) atTop (𝓝 0) := by
  obtain ⟨hc1, hc3⟩ := three_log_two_sub_gamma_bounds
  refine squeeze_zero_norm' ?_ (f := fun N : ℝ =>
    (Real.log N + (3 * Real.log 2 - Real.eulerMascheroniConstant)) *
      ∫ x in Ioc (0 : ℝ) (1 / Real.sqrt N), gaussH x / x)
    (a := fun N => (Real.log N / N + 3 / N) / 2) ?_
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with N hN
    have hN0 : 0 < N := by linarith
    have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
    have ha1 : 1 / Real.sqrt N ≤ 1 := by
      rw [div_le_one hsN]; exact Real.one_le_sqrt.2 hN
    have hI := abs_integral_gaussH_div_Ioc_le (by positivity : 0 ≤ 1 / Real.sqrt N) ha1
    rw [div_pow, one_pow, Real.sq_sqrt hN0.le] at hI
    have hℓ : 0 ≤ Real.log N := Real.log_nonneg hN
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by linarith)]
    calc (Real.log N + (3 * Real.log 2 - Real.eulerMascheroniConstant)) *
          |∫ x in Ioc (0 : ℝ) (1 / Real.sqrt N), gaussH x / x|
        ≤ (Real.log N + 3) * (1 / N / 2) :=
          mul_le_mul (by linarith) hI (abs_nonneg _) (by linarith)
      _ = (Real.log N / N + 3 / N) / 2 := by field_simp
  · have h1 := tendsto_log_div_atTop
    have h2 : Tendsto (fun N : ℝ => 3 / N) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
    have := (h1.add h2).div_const 2
    simpa using this

/-- `J_a = ∫_a^∞ h log x/x → J` as `a = N^{−1/2} → 0`. -/
theorem tendsto_logMoment_term :
    Tendsto (fun N : ℝ => ∫ x in Ioi (1 / Real.sqrt N), gaussH x * Real.log x / x) atTop
      (𝓝 gaussJlog) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero_norm' ?_ (a := fun N : ℝ => 1 / Real.sqrt N / 2) ?_
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with N hN
    have hN0 : 0 < N := by linarith
    have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
    have ha0 : 0 ≤ 1 / Real.sqrt N := by positivity
    have ha1 : 1 / Real.sqrt N ≤ 1 := by
      rw [div_le_one hsN]; exact Real.one_le_sqrt.2 hN
    have hsplit : gaussJlog = (∫ x in Ioc (0 : ℝ) (1 / Real.sqrt N), gaussH x * Real.log x / x) +
        ∫ x in Ioi (1 / Real.sqrt N), gaussH x * Real.log x / x := by
      unfold gaussJlog
      rw [← Ioc_union_Ioi_eq_Ioi ha0,
        setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
          (integrableOn_gaussH_log_Ioc le_rfl |>.mono_set (Ioc_subset_Ioc_right ha1))
          (integrableOn_gaussH_log ha0 ha1)]
    rw [norm_norm, hsplit, show ∀ A B : ℝ, B - (A + B) = -A from fun A B => by ring, norm_neg]
    have hb := norm_setIntegral_le_of_norm_le_const (μ := volume)
      (s := Ioc (0 : ℝ) (1 / Real.sqrt N))
      (f := fun x => gaussH x * Real.log x / x) (C := 1 / 2) measure_Ioc_lt_top
      (fun x hx => norm_gaussH_log_inner ⟨hx.1, hx.2.trans ha1⟩)
    refine hb.trans (le_of_eq ?_)
    rw [measureReal_def, Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal ha0]
    ring
  · have := tendsto_one_div_sqrt.div_const 2
    simpa using this

/-! ### The inner piece after `x = v/√N` -/

theorem gaussDensity_zero : gaussDensity 0 = 1 / Real.sqrt (2 * Real.pi) := by
  unfold gaussDensity; simp

theorem depthThreeF_scaled {N v : ℝ} (hN : 0 < N) :
    depthThreeF N (v / Real.sqrt N) = gaussDensity (v / Real.sqrt N) * gaussLaplace2 (v ^ 2) := by
  unfold depthThreeF
  congr 2
  rw [div_pow, Real.sq_sqrt hN.le]
  field_simp

/-- `√N ∫₀^a F_N = ∫₀^1 g(v/√N) Z_2(v²) dv`. -/
theorem sqrt_mul_inner_eq {N : ℝ} (hN : 0 < N) :
    Real.sqrt N * ∫ x in Ioc (0 : ℝ) (1 / Real.sqrt N), depthThreeF N x =
      ∫ v in Ioc (0 : ℝ) 1, gaussDensity (v / Real.sqrt N) * gaussLaplace2 (v ^ 2) := by
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN
  have h := intervalIntegral.integral_comp_div (a := 0) (b := 1) (depthThreeF N) hsN.ne'
  rw [zero_div, smul_eq_mul,
    intervalIntegral.integral_of_le (a := 0) (b := 1 / Real.sqrt N) (by positivity),
    intervalIntegral.integral_of_le (a := 0) (b := 1) zero_le_one] at h
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioc fun v _ => ?_
  exact depthThreeF_scaled hN

theorem tendsto_inner_term :
    Tendsto (fun N : ℝ => Real.sqrt N * ∫ x in Ioc (0 : ℝ) (1 / Real.sqrt N), depthThreeF N x)
      atTop (𝓝 (1 / Real.sqrt (2 * Real.pi) * ∫ v in Ioc (0 : ℝ) 1, depthThreeQ v)) := by
  have hlim : (1 / Real.sqrt (2 * Real.pi) * ∫ v in Ioc (0 : ℝ) 1, depthThreeQ v) =
      ∫ v in Ioc (0 : ℝ) 1, 1 / Real.sqrt (2 * Real.pi) * gaussLaplace2 (v ^ 2) := by
    rw [← integral_const_mul]
    exact (setIntegral_congr_fun measurableSet_Ioc fun v hv => by rw [depthThreeQ_inner hv]).symm
  rw [hlim]
  refine (tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict (Ioc (0 : ℝ) 1))
    (F := fun N v => gaussDensity (v / Real.sqrt N) * gaussLaplace2 (v ^ 2))
    (f := fun v => 1 / Real.sqrt (2 * Real.pi) * gaussLaplace2 (v ^ 2))
    (fun _ => 1 / Real.sqrt (2 * Real.pi))
    (Eventually.of_forall fun N => (continuous_gaussDensity.comp (continuous_id.div_const _)
      |>.measurable.mul (measurable_gaussLaplace2.comp
        (measurable_id.pow_const 2))).aestronglyMeasurable)
    (Eventually.of_forall fun N => ?_) (integrableOn_const measure_Ioc_lt_top.ne)
    (Eventually.of_forall fun v => ?_)).congr' ?_
  · rw [ae_restrict_iff' measurableSet_Ioc]
    refine Eventually.of_forall fun v _ => ?_
    have hg := gaussDensity_nonneg (v / Real.sqrt N)
    have hz0 := gaussLaplace2_nonneg (sq_nonneg v)
    have hz1 := gaussLaplace2_le_one (sq_nonneg v)
    have hg1 : gaussDensity (v / Real.sqrt N) ≤ 1 / Real.sqrt (2 * Real.pi) := by
      unfold gaussDensity
      exact div_le_div_of_nonneg_right
        (Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg (v / Real.sqrt N)]))
        (Real.sqrt_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hg hz0)]
    calc gaussDensity (v / Real.sqrt N) * gaussLaplace2 (v ^ 2)
        ≤ 1 / Real.sqrt (2 * Real.pi) * 1 := mul_le_mul hg1 hz1 hz0 (by positivity)
      _ = 1 / Real.sqrt (2 * Real.pi) := mul_one _
  · have h1 : Tendsto (fun N : ℝ => v / Real.sqrt N) atTop (𝓝 0) := by
      have := tendsto_one_div_sqrt.const_mul v
      simp only [mul_zero] at this
      refine this.congr fun N => ?_
      ring
    have := ((continuous_gaussDensity.tendsto 0).comp h1).mul_const (gaussLaplace2 (v ^ 2))
    rw [gaussDensity_zero] at this
    exact this
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with N hN
    exact (sqrt_mul_inner_eq hN).symm

/-! ### The remainder piece after `x = v/√N` -/

/-- The remainder integrand at `x = v/√N` is `g(v/√N) q(v)` for `v > 1`. -/
theorem depthThree_rem_scaled {N v : ℝ} (hN : 0 < N) (hv : 1 < v) :
    depthThreeF N (1 / Real.sqrt N * v) - gaussDensity (1 / Real.sqrt N * v) *
      ((Real.log N + 2 * Real.log (1 / Real.sqrt N * v) +
        3 * Real.log 2 - Real.eulerMascheroniConstant) /
        (Real.sqrt (2 * Real.pi) * (Real.sqrt N * (1 / Real.sqrt N * v)))) =
      gaussDensity (1 / Real.sqrt N * v) * depthThreeQ v := by
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN
  have hv0 : 0 < v := by linarith
  have e1 : 1 / Real.sqrt N * v = v / Real.sqrt N := by ring
  rw [e1, depthThreeF_scaled hN]
  unfold depthThreeQ
  rw [indicator_of_mem (show v ∈ Ioi (1 : ℝ) from hv)]
  have hlog : Real.log (v / Real.sqrt N) = Real.log v - Real.log N / 2 := by
    rw [Real.log_div hv0.ne' hsN.ne', Real.log_sqrt hN.le]
  rw [hlog, show Real.sqrt N * (v / Real.sqrt N) = v by field_simp]
  rw [show Real.log N + 2 * (Real.log v - Real.log N / 2) + 3 * Real.log 2 -
    Real.eulerMascheroniConstant = 2 * Real.log v + (3 * Real.log 2 - Real.eulerMascheroniConstant)
    by ring]
  ring

/-- `√N ∫_a^∞ (F_N − gL_N) = ∫₁^∞ g(v/√N) q(v) dv`. -/
theorem sqrt_mul_rem_eq {N : ℝ} (hN : 0 < N) :
    Real.sqrt N * ∫ x in Ioi (1 / Real.sqrt N), (depthThreeF N x - gaussDensity x *
      ((Real.log N + 2 * Real.log x + 3 * Real.log 2 - Real.eulerMascheroniConstant) /
        (Real.sqrt (2 * Real.pi) * (Real.sqrt N * x)))) =
      ∫ v in Ioi (1 : ℝ), gaussDensity (v / Real.sqrt N) * depthThreeQ v := by
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN
  have hb : 0 < 1 / Real.sqrt N := by positivity
  have h := integral_comp_mul_left_Ioi (fun x => depthThreeF N x - gaussDensity x *
      ((Real.log N + 2 * Real.log x + 3 * Real.log 2 - Real.eulerMascheroniConstant) /
        (Real.sqrt (2 * Real.pi) * (Real.sqrt N * x)))) 1 hb
  rw [mul_one, smul_eq_mul, inv_div, div_one] at h
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi fun v hv => ?_
  have hv1 : (1 : ℝ) < v := hv
  rw [depthThree_rem_scaled hN hv1]
  congr 2
  ring

theorem tendsto_rem_term :
    Tendsto (fun N : ℝ => Real.sqrt N * ∫ x in Ioi (1 / Real.sqrt N), (depthThreeF N x -
      gaussDensity x *
        ((Real.log N + 2 * Real.log x + 3 * Real.log 2 - Real.eulerMascheroniConstant) /
          (Real.sqrt (2 * Real.pi) * (Real.sqrt N * x))))) atTop
      (𝓝 (1 / Real.sqrt (2 * Real.pi) * ∫ v in Ioi (1 : ℝ), depthThreeQ v)) := by
  rw [← integral_const_mul]
  refine (tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict (Ioi (1 : ℝ)))
    (F := fun N v => gaussDensity (v / Real.sqrt N) * depthThreeQ v)
    (f := fun v => 1 / Real.sqrt (2 * Real.pi) * depthThreeQ v)
    (fun v => 1 / Real.sqrt (2 * Real.pi) * |depthThreeQ v|)
    (Eventually.of_forall fun N => (continuous_gaussDensity.comp (continuous_id.div_const _)
      |>.measurable.mul measurable_depthThreeQ).aestronglyMeasurable)
    (Eventually.of_forall fun N => ?_)
    (integrableOn_depthThreeQ_outer.abs.const_mul _)
    (Eventually.of_forall fun v => ?_)).congr' ?_
  · refine Eventually.of_forall fun v => ?_
    have hg := gaussDensity_nonneg (v / Real.sqrt N)
    have hg1 : gaussDensity (v / Real.sqrt N) ≤ 1 / Real.sqrt (2 * Real.pi) := by
      unfold gaussDensity
      exact div_le_div_of_nonneg_right
        (Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg (v / Real.sqrt N)]))
        (Real.sqrt_nonneg _)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hg]
    exact mul_le_mul_of_nonneg_right hg1 (abs_nonneg _)
  · have h1 : Tendsto (fun N : ℝ => v / Real.sqrt N) atTop (𝓝 0) := by
      have := tendsto_one_div_sqrt.const_mul v
      simp only [mul_zero] at this
      refine this.congr fun N => ?_
      ring
    have := ((continuous_gaussDensity.tendsto 0).comp h1).mul_const (depthThreeQ v)
    rw [gaussDensity_zero] at this
    exact this
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with N hN
    exact (sqrt_mul_rem_eq hN).symm

/-! ### The residual limit -/

/-- The DCXXIII decomposition, scaled by `√N`: for `N ≥ 1`,
`√N Z_3 − [ℓ² + 4(2 log 2 − γ)ℓ]/(4π) = 2√N I₀ + 2√N E + (1/π)(c d/2 − (ℓ + c) I_a + 2 J_a)`. -/
theorem sqrt_mul_gaussLaplaceL_three_eq {N : ℝ} (hN : 1 ≤ N) :
    Real.sqrt N * gaussLaplaceL 3 N - ((Real.log N) ^ 2 +
      4 * (2 * Real.log 2 - Real.eulerMascheroniConstant) * Real.log N) / (4 * Real.pi) =
      2 * (Real.sqrt N * ∫ x in Ioc (0 : ℝ) (1 / Real.sqrt N), depthThreeF N x) +
      2 * (Real.sqrt N * ∫ x in Ioi (1 / Real.sqrt N), (depthThreeF N x - gaussDensity x *
        ((Real.log N + 2 * Real.log x + 3 * Real.log 2 - Real.eulerMascheroniConstant) /
          (Real.sqrt (2 * Real.pi) * (Real.sqrt N * x))))) +
      1 / Real.pi * ((3 * Real.log 2 - Real.eulerMascheroniConstant) *
          ((Real.log 2 - Real.eulerMascheroniConstant) / 2) -
        (Real.log N + (3 * Real.log 2 - Real.eulerMascheroniConstant)) *
          (∫ x in Ioc (0 : ℝ) (1 / Real.sqrt N), gaussH x / x) +
        2 * ∫ x in Ioi (1 / Real.sqrt N), gaussH x * Real.log x / x) := by
  have hN0 : 0 < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have ha0 : 0 < 1 / Real.sqrt N := by positivity
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
  have hmain := integral_depthThree_main hN
  rw [gaussLaplaceL_three hN0.le]
  change Real.sqrt N * (∫ x, depthThreeF N x) - _ = _
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
  have hsq : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN0.le
  field_simp
  ring

/-- ★★★ **The depth-three constant as a limit**:
`√N Z_3(N) − [(log N)² + 4(2 log 2 − γ) log N]/(4π) → (c R₀ + 2J)/π + (2/s) Q`. -/
theorem gaussLaplaceL_three_residual :
    Tendsto (fun N : ℝ => Real.sqrt N * gaussLaplaceL 3 N - ((Real.log N) ^ 2 +
      4 * (2 * Real.log 2 - Real.eulerMascheroniConstant) * Real.log N) / (4 * Real.pi)) atTop
      (𝓝 depthThreeConst) := by
  have hQ : depthThreeQint = (∫ v in Ioc (0 : ℝ) 1, depthThreeQ v) +
      ∫ v in Ioi (1 : ℝ), depthThreeQ v := by
    unfold depthThreeQint
    rw [← Ioc_union_Ioi_eq_Ioi zero_le_one,
      setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
        integrableOn_depthThreeQ_inner integrableOn_depthThreeQ_outer]
  have h := ((tendsto_inner_term.const_mul 2).add (tendsto_rem_term.const_mul 2)).add
    (((tendsto_const_nhds (x := (3 * Real.log 2 - Real.eulerMascheroniConstant) *
      ((Real.log 2 - Real.eulerMascheroniConstant) / 2))).sub tendsto_cutoff_term).add
      (tendsto_logMoment_term.const_mul 2) |>.const_mul (1 / Real.pi))
  have hconst : depthThreeConst =
      2 * (1 / Real.sqrt (2 * Real.pi) * ∫ v in Ioc (0 : ℝ) 1, depthThreeQ v) +
      2 * (1 / Real.sqrt (2 * Real.pi) * ∫ v in Ioi (1 : ℝ), depthThreeQ v) +
      1 / Real.pi * (((3 * Real.log 2 - Real.eulerMascheroniConstant) *
        ((Real.log 2 - Real.eulerMascheroniConstant) / 2) - 0) + 2 * gaussJlog) := by
    unfold depthThreeConst
    rw [hQ]
    ring
  rw [hconst]
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with N hN
  exact (sqrt_mul_gaussLaplaceL_three_eq hN).symm

end Grammar
