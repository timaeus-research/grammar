/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.GammaSecondDerivOne
import Grammar.GaussianDepthAllTwoTerm
import Grammar.GaussianDepthThreeResidual
import Grammar.LogWeightedPrim

/-!
# The exact logarithmic moment `J = ∫₀^∞ h(x) log x/x dx = R₀²/2 + π²/48`

`h(x) = e^{−x²/2} − 1_{(0,1]}(x)` and `R₀ = (log 2 − γ)/2`.  The weighted version of DCXI's kernel
argument: `∫₀^∞ logKernel(v,u) log u du = ½(log v)²` (`integral_kernel_log_sq`), so Fubini against
`e^{−v}` gives (★★ `integral_renormalised_exp_log`)

  `∫₀^∞ (e^{−u} − 1_{(0,1]}(u)) log u/u du = ½ ∫₀^∞ e^{−v} log² v dv = ½ Γ''(1) = ½(γ² + π²/6)`;

moving the cutoff to `½` costs `∫_{½}^1 log u/u = −½(log 2)²` (`integral_renormalised_exp_log_half`)
and `∫_{½}^1 du/u = log 2` (`integral_renormalised_exp_inv_half`), and the substitution `y = x²/2`
turns `J` into `¼ ∫ (e^{−y} − 1_{(0,½]}(y))(log 2 + log y)/y dy` (`gaussJlog_eq_half_cut`), whence
(★★★ `gaussJlog_eq`)

  `J = ¼[log 2 (log 2 − γ) + ½(γ² + π²/6) − ½(log 2)²] = (log 2 − γ)²/8 + π²/48 = R₀²/2 + π²/48`.

With DCXXXI/DCXXXVI this makes the third logarithmic coefficient of the Gaussian DLN explicit up to
the single remaining constant `Q` (examples_slop §2; Astra round-12 target 2).
Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

/-! ### The weighted kernel -/

/-- `∫₁^v log u/u du = ½ (log v)²` for `v > 0` (as an interval integral). -/
theorem integral_log_div_self {v : ℝ} (hv : 0 < v) :
    ∫ u in (1 : ℝ)..v, u⁻¹ * Real.log u = (Real.log v) ^ 2 / 2 := by
  have hderiv : ∀ u ∈ uIcc (1 : ℝ) v, HasDerivAt (fun u => (Real.log u) ^ 2 / 2)
      (u⁻¹ * Real.log u) u := by
    intro u hu
    have hu0 : 0 < u := by
      rcases le_or_gt 1 v with h | h
      · rw [uIcc_of_le h] at hu; exact lt_of_lt_of_le one_pos hu.1
      · rw [uIcc_of_ge h.le] at hu; exact lt_of_lt_of_le hv hu.1
    have := ((Real.hasDerivAt_log hu0.ne').pow 2).div_const 2
    refine this.congr_deriv ?_
    ring
  have hint : IntervalIntegrable (fun u : ℝ => u⁻¹ * Real.log u) volume 1 v := by
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.mul (continuousOn_inv₀.mono fun u hu => ?_)
      (Real.continuousOn_log.mono fun u hu => ?_)
    · rcases le_or_gt 1 v with h | h
      · rw [uIcc_of_le h] at hu
        exact mem_compl_singleton_iff.2 (ne_of_gt (lt_of_lt_of_le one_pos hu.1))
      · rw [uIcc_of_ge h.le] at hu
        exact mem_compl_singleton_iff.2 (ne_of_gt (lt_of_lt_of_le hv hu.1))
    · rcases le_or_gt 1 v with h | h
      · rw [uIcc_of_le h] at hu
        exact mem_compl_singleton_iff.2 (ne_of_gt (lt_of_lt_of_le one_pos hu.1))
      · rw [uIcc_of_ge h.le] at hu
        exact mem_compl_singleton_iff.2 (ne_of_gt (lt_of_lt_of_le hv hu.1))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp

/-- `∫₀^∞ logKernel v u · log u du = ½ (log v)²` for `v > 0`. -/
theorem integral_kernel_log_sq {v : ℝ} (hv : 0 < v) :
    ∫ u in Ioi (0 : ℝ), logKernel v u * Real.log u = (Real.log v) ^ 2 / 2 := by
  unfold logKernel
  rcases le_or_gt 1 v with h | h
  · have e : ∀ u ∈ Ioi (0 : ℝ), ((Ioc 1 v).indicator (fun u : ℝ => u⁻¹) u -
        (Ioc v 1).indicator (fun u : ℝ => u⁻¹) u) * Real.log u =
        (Ioc 1 v).indicator (fun u : ℝ => u⁻¹ * Real.log u) u := by
      intro u _
      rw [Ioc_eq_empty (show ¬ v < (1 : ℝ) from not_lt.2 h)]
      simp only [indicator_empty, sub_zero]
      rw [indicator_mul_left]
    rw [setIntegral_congr_fun measurableSet_Ioi e, setIntegral_indicator measurableSet_Ioc,
      show Ioi (0 : ℝ) ∩ Ioc 1 v = Ioc 1 v from inter_eq_right.2 fun u hu => lt_trans one_pos hu.1,
      ← intervalIntegral.integral_of_le h, integral_log_div_self hv]
  · have e : ∀ u ∈ Ioi (0 : ℝ), ((Ioc 1 v).indicator (fun u : ℝ => u⁻¹) u -
        (Ioc v 1).indicator (fun u : ℝ => u⁻¹) u) * Real.log u =
        -(Ioc v 1).indicator (fun u : ℝ => u⁻¹ * Real.log u) u := by
      intro u _
      rw [Ioc_eq_empty (show ¬ (1 : ℝ) < v from not_lt.2 h.le)]
      simp only [indicator_empty, zero_sub, neg_mul]
      rw [indicator_mul_left]
    rw [setIntegral_congr_fun measurableSet_Ioi e, integral_neg,
      setIntegral_indicator measurableSet_Ioc,
      show Ioi (0 : ℝ) ∩ Ioc v 1 = Ioc v 1 from inter_eq_right.2 fun u hu => lt_trans hv hu.1,
      ← intervalIntegral.integral_of_le h.le, ← intervalIntegral.integral_symm,
      integral_log_div_self hv]

/-- `∫₀^∞ |logKernel v u · log u| du = ½ (log v)²` for `v > 0`. -/
theorem integral_abs_kernel_log_sq {v : ℝ} (hv : 0 < v) :
    ∫ u in Ioi (0 : ℝ), |logKernel v u * Real.log u| = (Real.log v) ^ 2 / 2 := by
  rw [← integral_kernel_log_sq hv]
  refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
  have hu0 : (0 : ℝ) < u := hu
  unfold logKernel
  rcases le_or_gt 1 v with h | h
  · rw [Ioc_eq_empty (show ¬ v < (1 : ℝ) from not_lt.2 h)]
    simp only [indicator_empty, sub_zero]
    refine abs_of_nonneg ?_
    by_cases hm : u ∈ Ioc 1 v
    · rw [indicator_of_mem hm]
      exact mul_nonneg (inv_nonneg.2 hu0.le) (Real.log_nonneg hm.1.le)
    · rw [indicator_of_notMem hm, zero_mul]
  · rw [Ioc_eq_empty (show ¬ (1 : ℝ) < v from not_lt.2 h.le)]
    simp only [indicator_empty, zero_sub, neg_mul]
    refine abs_of_nonneg ?_
    by_cases hm : u ∈ Ioc v 1
    · rw [indicator_of_mem hm]
      have : Real.log u ≤ 0 := Real.log_nonpos hu0.le hm.2
      have : 0 ≤ u⁻¹ := inv_nonneg.2 hu0.le
      nlinarith
    · rw [indicator_of_notMem hm, zero_mul, neg_zero]

/-- The weighted kernel is integrable in `u` on `(0, ∞)` for every `v > 0`. -/
theorem integrableOn_logKernel_log {v : ℝ} (hv : 0 < v) :
    IntegrableOn (fun u => logKernel v u * Real.log u) (Ioi 0) := by
  have hc : ∀ a b : ℝ, 0 < a → a ≤ b → IntegrableOn (fun u : ℝ => u⁻¹ * Real.log u) (Ioc a b) := by
    intro a b ha hab
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.mul (continuousOn_inv₀.mono fun u hu => ?_)
      (Real.continuousOn_log.mono fun u hu => ?_)
    · rw [uIcc_of_le hab] at hu
      exact mem_compl_singleton_iff.2 (ne_of_gt (lt_of_lt_of_le ha hu.1))
    · rw [uIcc_of_le hab] at hu
      exact mem_compl_singleton_iff.2 (ne_of_gt (lt_of_lt_of_le ha hu.1))
  have h1 : IntegrableOn (fun u : ℝ => u⁻¹ * Real.log u) (Ioc 1 v) := by
    rcases le_or_gt 1 v with h | h
    · exact hc 1 v one_pos h
    · rw [Ioc_eq_empty (show ¬ (1 : ℝ) < v from not_lt.2 h.le)]
      exact integrableOn_empty
  have h2 : IntegrableOn (fun u : ℝ => u⁻¹ * Real.log u) (Ioc v 1) := by
    rcases le_or_gt v 1 with h | h
    · exact hc v 1 hv h
    · rw [Ioc_eq_empty (show ¬ v < (1 : ℝ) from not_lt.2 h.le)]
      exact integrableOn_empty
  refine ((h1.integrable_indicator measurableSet_Ioc).sub
    (h2.integrable_indicator measurableSet_Ioc)).integrableOn.congr_fun (fun u _ => ?_)
    measurableSet_Ioi
  simp only [Pi.sub_apply]
  unfold logKernel
  rw [sub_mul, indicator_mul_left, indicator_mul_left]

/-- The inner `v`-integral of the weighted kernel:
`∫₀^∞ e^{−v} logKernel v u log u dv = (e^{−u} − 1_{u ≤ 1}) log u/u`. -/
theorem integral_exp_kernel_log {u : ℝ} (hu : 0 < u) :
    ∫ v in Ioi (0 : ℝ), Real.exp (-v) * (logKernel v u * Real.log u) =
      (Real.exp (-u) - (Ioc 0 1).indicator 1 u) * Real.log u / u := by
  have e : ∀ v : ℝ, Real.exp (-v) * (logKernel v u * Real.log u) =
      (Real.exp (-v) * logKernel v u) * Real.log u := fun v => by ring
  simp_rw [e]
  rw [integral_mul_const, integral_exp_kernel hu]
  ring

/-- `e^{−v} log² v` is integrable on `(0, ∞)`: `log² v ≤ 16 v^{−1/2} + v²`. -/
theorem integrableOn_exp_neg_log_sq :
    IntegrableOn (fun v : ℝ => Real.exp (-v) * (Real.log v) ^ 2) (Ioi 0) := by
  have hint : IntegrableOn (fun v : ℝ => (16 * v ^ (-(1 / 2 : ℝ)) + v ^ (2 : ℝ)) * Real.exp (-v))
      (Ioi 0) := by
    have h1 := integrableOn_rpow_mul_exp_neg_rpow (s := -(1 / 2 : ℝ)) (p := 1) (by norm_num) one_pos
    have h2 := integrableOn_rpow_mul_exp_neg_rpow (s := 2) (p := 1) (by norm_num) one_pos
    refine IntegrableOn.congr_fun ((h1.const_mul 16).add h2) (fun v hv => ?_) measurableSet_Ioi
    simp only [Pi.add_apply, Real.rpow_one]
    ring
  refine hint.mono' (by fun_prop : Measurable fun v : ℝ =>
    Real.exp (-v) * (Real.log v) ^ 2).aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Eventually.of_forall fun v hv => ?_
  have hv' : (0 : ℝ) < v := hv
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hbd : (Real.log v) ^ 2 ≤ 16 * v ^ (-(1 / 2 : ℝ)) + v ^ (2 : ℝ) := by
    have h0 : 0 ≤ v ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hv'.le _
    have h2 : 0 ≤ v ^ (2 : ℝ) := Real.rpow_nonneg hv'.le _
    rcases le_or_gt v 1 with h | h
    · have := abs_log_le_rpow_neg_div v (1 / 4) hv' h (by norm_num)
      have hsq : (Real.log v) ^ 2 = |Real.log v| ^ 2 := (sq_abs _).symm
      have hq : (v ^ (-(1 / 4 : ℝ)) / (1 / 4)) ^ 2 = 16 * v ^ (-(1 / 2 : ℝ)) := by
        rw [div_pow, ← Real.rpow_natCast, ← Real.rpow_mul hv'.le]
        norm_num
        ring
      rw [hsq]
      calc |Real.log v| ^ 2 ≤ (v ^ (-(1 / 4 : ℝ)) / (1 / 4)) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) this 2
        _ = 16 * v ^ (-(1 / 2 : ℝ)) := hq
        _ ≤ 16 * v ^ (-(1 / 2 : ℝ)) + v ^ (2 : ℝ) := by linarith
    · have hl : 0 ≤ Real.log v := Real.log_nonneg h.le
      have hlv : Real.log v ≤ v := by linarith [Real.log_le_sub_one_of_pos hv']
      have : (Real.log v) ^ 2 ≤ v ^ (2 : ℝ) := by
        rw [Real.rpow_two]
        exact pow_le_pow_left₀ hl hlv 2
      linarith
  calc Real.exp (-v) * (Real.log v) ^ 2 ≤ Real.exp (-v) * (16 * v ^ (-(1 / 2 : ℝ)) + v ^ (2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hbd (Real.exp_pos _).le
    _ = (16 * v ^ (-(1 / 2 : ℝ)) + v ^ (2 : ℝ)) * Real.exp (-v) := by ring

/-- The weighted kernel `e^{−v} logKernel(v,u) log u` is integrable on `(0,∞)²`. -/
theorem integrable_expKernelLog_prod :
    Integrable (Function.uncurry fun u v : ℝ => Real.exp (-v) * (logKernel v u * Real.log u))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  set g : ℝ → ℝ → ℝ := fun u v => Real.exp (-v) * (logKernel v u * Real.log u) with hg
  have hmeas : AEStronglyMeasurable (Function.uncurry g)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    refine Measurable.aestronglyMeasurable ?_
    have : Function.uncurry g = fun p : ℝ × ℝ => Real.exp (-p.2) *
        (Function.uncurry logKernel (p.2, p.1) * Real.log p.1) := by
      funext p; rfl
    rw [this]
    exact ((Real.measurable_exp.comp measurable_snd.neg).mul
      ((measurable_logKernel.comp (measurable_snd.prodMk measurable_fst)).mul
        (Real.measurable_log.comp measurable_fst)))
  rw [integrable_prod_iff' hmeas]
  constructor
  · rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun v hv => ?_
    have hv' : (0 : ℝ) < v := hv
    refine ((integrableOn_logKernel_log hv').const_mul (Real.exp (-v))).congr
      (Eventually.of_forall fun x => ?_)
    rfl
  · have e : ∀ v ∈ Ioi (0 : ℝ), (∫ u in Ioi (0 : ℝ), ‖Function.uncurry g (u, v)‖) =
        Real.exp (-v) * ((Real.log v) ^ 2 / 2) := by
      intro v hv
      have hv' : (0 : ℝ) < v := hv
      simp only [hg, Function.uncurry_apply_pair, Real.norm_eq_abs, abs_mul,
        abs_of_pos (Real.exp_pos _)]
      rw [integral_const_mul, ← integral_abs_kernel_log_sq hv']
      congr 1
      refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
      rw [abs_mul]
    refine IntegrableOn.congr_fun (integrableOn_exp_neg_log_sq.div_const 2)
      (fun v hv => ?_) measurableSet_Ioi
    rw [e v hv]
    ring

/-- `(e^{−u} − 1_{(0,1]}(u)) log u/u` is integrable on `(0, ∞)` (the marginal of the product). -/
theorem integrableOn_renormalised_exp_log :
    IntegrableOn (fun u : ℝ => (Real.exp (-u) - (Ioc 0 1).indicator 1 u) * Real.log u / u)
      (Ioi 0) := by
  refine IntegrableOn.congr_fun integrable_expKernelLog_prod.integral_prod_left
    (fun u hu => ?_) measurableSet_Ioi
  have hu' : (0 : ℝ) < u := hu
  simp only [Function.uncurry_apply_pair]
  exact integral_exp_kernel_log hu'

/-- ★★ **The weighted renormalised integral**:
`∫₀^∞ (e^{−u} − 1_{(0,1]}(u)) log u/u du = ½ Γ''(1) = ½(γ² + π²/6)`. -/
theorem integral_renormalised_exp_log :
    ∫ u in Ioi (0 : ℝ), (Real.exp (-u) - (Ioc 0 1).indicator 1 u) * Real.log u / u =
      (Real.eulerMascheroniConstant ^ 2 + Real.pi ^ 2 / 6) / 2 := by
  set g : ℝ → ℝ → ℝ := fun u v => Real.exp (-v) * (logKernel v u * Real.log u) with hg
  have hint : Integrable (Function.uncurry g)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) :=
    integrable_expKernelLog_prod
  have hswap := integral_integral_swap hint
  have hL : ∫ v in Ioi (0 : ℝ), ∫ u in Ioi (0 : ℝ), g u v =
      (Real.eulerMascheroniConstant ^ 2 + Real.pi ^ 2 / 6) / 2 := by
    rw [← integral_exp_neg_log_sq, ← integral_div]
    refine setIntegral_congr_fun measurableSet_Ioi fun v hv => ?_
    have hv' : (0 : ℝ) < v := hv
    simp only [hg]
    rw [integral_const_mul, integral_kernel_log_sq hv']
    ring
  have hR : ∫ u in Ioi (0 : ℝ), ∫ v in Ioi (0 : ℝ), g u v =
      ∫ u in Ioi (0 : ℝ), (Real.exp (-u) - (Ioc 0 1).indicator 1 u) * Real.log u / u := by
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    have hu' : (0 : ℝ) < u := hu
    simp only [hg]
    exact integral_exp_kernel_log hu'
  rw [← hR, hswap, hL]

/-! ### Moving the cutoff to `½` -/

/-- `u⁻¹ log u` is integrable on `(a, b]` for `0 < a ≤ b`. -/
theorem integrableOn_inv_mul_log_Ioc {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntegrableOn (fun u : ℝ => u⁻¹ * Real.log u) (Ioc a b) := by
  rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  refine ContinuousOn.intervalIntegrable ?_
  refine ContinuousOn.mul (continuousOn_inv₀.mono fun u hu => ?_)
    (Real.continuousOn_log.mono fun u hu => ?_)
  · rw [uIcc_of_le hab] at hu
    exact mem_compl_singleton_iff.2 (ne_of_gt (lt_of_lt_of_le ha hu.1))
  · rw [uIcc_of_le hab] at hu
    exact mem_compl_singleton_iff.2 (ne_of_gt (lt_of_lt_of_le ha hu.1))

/-- `u⁻¹` is integrable on `(a, b]` for `0 < a ≤ b`. -/
theorem integrableOn_inv_Ioc_pos {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntegrableOn (fun u : ℝ => u⁻¹) (Ioc a b) := by
  rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  refine ContinuousOn.intervalIntegrable (continuousOn_inv₀.mono fun u hu => ?_)
  rw [uIcc_of_le hab] at hu
  exact mem_compl_singleton_iff.2 (ne_of_gt (lt_of_lt_of_le ha hu.1))

/-- `∫_{½}^1 du/u = log 2`. -/
theorem integral_Ioc_half_one_inv : ∫ u in Ioc (1 / 2 : ℝ) 1, u⁻¹ = Real.log 2 := by
  rw [← intervalIntegral.integral_of_le (by norm_num), integral_inv_of_pos (by norm_num) one_pos]
  norm_num

/-- `∫_{½}^1 log u/u du = −½ (log 2)²`. -/
theorem integral_Ioc_half_one_inv_mul_log :
    ∫ u in Ioc (1 / 2 : ℝ) 1, u⁻¹ * Real.log u = -(Real.log 2) ^ 2 / 2 := by
  rw [← intervalIntegral.integral_of_le (by norm_num), intervalIntegral.integral_symm,
    integral_log_div_self (by norm_num), one_div, Real.log_inv]
  ring

/-- Pointwise: changing the cutoff from `1` to `½` adds `1_{(½,1]}(u)/u`. -/
theorem half_cut_split_inv {u : ℝ} (hu : 0 < u) :
    (Real.exp (-u) - (Ioc 0 (1 / 2)).indicator 1 u) / u =
      (Real.exp (-u) - (Ioc 0 1).indicator 1 u) / u +
        (Ioc (1 / 2 : ℝ) 1).indicator (fun u => u⁻¹) u := by
  rcases le_or_gt u (1 / 2) with h | h
  · have hm₁ : u ∈ Ioc (0 : ℝ) (1 / 2) := mem_Ioc.2 ⟨hu, h⟩
    have hm₂ : u ∈ Ioc (0 : ℝ) 1 := mem_Ioc.2 ⟨hu, by linarith⟩
    have hm₃ : u ∉ Ioc (1 / 2 : ℝ) 1 := fun hm => absurd hm.1 (not_lt.2 h)
    rw [indicator_of_mem hm₁, indicator_of_mem hm₂, indicator_of_notMem hm₃, add_zero]
  · have hm₁ : u ∉ Ioc (0 : ℝ) (1 / 2) := fun hm => absurd hm.2 (not_le.2 h)
    rcases le_or_gt u 1 with h1 | h1
    · have hm₂ : u ∈ Ioc (0 : ℝ) 1 := mem_Ioc.2 ⟨hu, h1⟩
      have hm₃ : u ∈ Ioc (1 / 2 : ℝ) 1 := mem_Ioc.2 ⟨h, h1⟩
      rw [indicator_of_notMem hm₁, indicator_of_mem hm₂, indicator_of_mem hm₃, Pi.one_apply]
      field_simp
      ring
    · have hm₂ : u ∉ Ioc (0 : ℝ) 1 := fun hm => absurd hm.2 (not_le.2 h1)
      have hm₃ : u ∉ Ioc (1 / 2 : ℝ) 1 := fun hm => absurd hm.2 (not_le.2 h1)
      rw [indicator_of_notMem hm₁, indicator_of_notMem hm₂, indicator_of_notMem hm₃, add_zero]

/-- Pointwise: the log-weighted version of `half_cut_split_inv`. -/
theorem half_cut_split_log {u : ℝ} (hu : 0 < u) :
    (Real.exp (-u) - (Ioc 0 (1 / 2)).indicator 1 u) * Real.log u / u =
      (Real.exp (-u) - (Ioc 0 1).indicator 1 u) * Real.log u / u +
        (Ioc (1 / 2 : ℝ) 1).indicator (fun u => u⁻¹ * Real.log u) u := by
  rcases le_or_gt u (1 / 2) with h | h
  · have hm₁ : u ∈ Ioc (0 : ℝ) (1 / 2) := mem_Ioc.2 ⟨hu, h⟩
    have hm₂ : u ∈ Ioc (0 : ℝ) 1 := mem_Ioc.2 ⟨hu, by linarith⟩
    have hm₃ : u ∉ Ioc (1 / 2 : ℝ) 1 := fun hm => absurd hm.1 (not_lt.2 h)
    rw [indicator_of_mem hm₁, indicator_of_mem hm₂, indicator_of_notMem hm₃, add_zero]
  · have hm₁ : u ∉ Ioc (0 : ℝ) (1 / 2) := fun hm => absurd hm.2 (not_le.2 h)
    rcases le_or_gt u 1 with h1 | h1
    · have hm₂ : u ∈ Ioc (0 : ℝ) 1 := mem_Ioc.2 ⟨hu, h1⟩
      have hm₃ : u ∈ Ioc (1 / 2 : ℝ) 1 := mem_Ioc.2 ⟨h, h1⟩
      rw [indicator_of_notMem hm₁, indicator_of_mem hm₂, indicator_of_mem hm₃, Pi.one_apply]
      field_simp
      ring
    · have hm₂ : u ∉ Ioc (0 : ℝ) 1 := fun hm => absurd hm.2 (not_le.2 h1)
      have hm₃ : u ∉ Ioc (1 / 2 : ℝ) 1 := fun hm => absurd hm.2 (not_le.2 h1)
      rw [indicator_of_notMem hm₁, indicator_of_notMem hm₂, indicator_of_notMem hm₃, add_zero]

/-- Integrability with the cutoff at `½`. -/
theorem integrableOn_renormalised_exp_inv_half :
    IntegrableOn (fun u : ℝ => (Real.exp (-u) - (Ioc 0 (1 / 2)).indicator 1 u) / u) (Ioi 0) := by
  have hind : IntegrableOn ((Ioc (1 / 2 : ℝ) 1).indicator (fun u : ℝ => u⁻¹)) (Ioi 0) :=
    ((integrableOn_inv_Ioc_pos (by norm_num) (by norm_num)).integrable_indicator
      measurableSet_Ioc).integrableOn
  refine IntegrableOn.congr_fun (integrableOn_renormalised_exp_inv.add hind)
    (fun u hu => ?_) measurableSet_Ioi
  have hu' : (0 : ℝ) < u := hu
  exact (half_cut_split_inv hu').symm

/-- Log-weighted integrability with the cutoff at `½`. -/
theorem integrableOn_renormalised_exp_log_half :
    IntegrableOn (fun u : ℝ => (Real.exp (-u) - (Ioc 0 (1 / 2)).indicator 1 u) * Real.log u / u)
      (Ioi 0) := by
  have hind : IntegrableOn ((Ioc (1 / 2 : ℝ) 1).indicator (fun u : ℝ => u⁻¹ * Real.log u))
      (Ioi 0) :=
    ((integrableOn_inv_mul_log_Ioc (by norm_num) (by norm_num)).integrable_indicator
      measurableSet_Ioc).integrableOn
  refine IntegrableOn.congr_fun (integrableOn_renormalised_exp_log.add hind)
    (fun u hu => ?_) measurableSet_Ioi
  have hu' : (0 : ℝ) < u := hu
  exact (half_cut_split_log hu').symm

/-- `∫₀^∞ (e^{−u} − 1_{(0,½]}(u))/u du = log 2 − γ`. -/
theorem integral_renormalised_exp_inv_half :
    ∫ u in Ioi (0 : ℝ), (Real.exp (-u) - (Ioc 0 (1 / 2)).indicator 1 u) / u =
      Real.log 2 - Real.eulerMascheroniConstant := by
  have hind : IntegrableOn ((Ioc (1 / 2 : ℝ) 1).indicator (fun u : ℝ => u⁻¹)) (Ioi 0) :=
    ((integrableOn_inv_Ioc_pos (by norm_num) (by norm_num)).integrable_indicator
      measurableSet_Ioc).integrableOn
  rw [setIntegral_congr_fun measurableSet_Ioi fun u (hu : (0 : ℝ) < u) => half_cut_split_inv hu,
    integral_add integrableOn_renormalised_exp_inv hind, integral_renormalised_exp_inv,
    setIntegral_indicator measurableSet_Ioc,
    show Ioi (0 : ℝ) ∩ Ioc (1 / 2) 1 = Ioc (1 / 2) 1 from
      inter_eq_right.2 fun u hu => lt_trans (by norm_num) hu.1,
    integral_Ioc_half_one_inv]
  ring

/-- `∫₀^∞ (e^{−u} − 1_{(0,½]}(u)) log u/u du = ½(γ² + π²/6) − ½(log 2)²`. -/
theorem integral_renormalised_exp_log_half :
    ∫ u in Ioi (0 : ℝ), (Real.exp (-u) - (Ioc 0 (1 / 2)).indicator 1 u) * Real.log u / u =
      (Real.eulerMascheroniConstant ^ 2 + Real.pi ^ 2 / 6) / 2 - (Real.log 2) ^ 2 / 2 := by
  have hind : IntegrableOn ((Ioc (1 / 2 : ℝ) 1).indicator (fun u : ℝ => u⁻¹ * Real.log u))
      (Ioi 0) :=
    ((integrableOn_inv_mul_log_Ioc (by norm_num) (by norm_num)).integrable_indicator
      measurableSet_Ioc).integrableOn
  rw [setIntegral_congr_fun measurableSet_Ioi fun u (hu : (0 : ℝ) < u) => half_cut_split_log hu,
    integral_add integrableOn_renormalised_exp_log hind, integral_renormalised_exp_log,
    setIntegral_indicator measurableSet_Ioc,
    show Ioi (0 : ℝ) ∩ Ioc (1 / 2) 1 = Ioc (1 / 2) 1 from
      inter_eq_right.2 fun u hu => lt_trans (by norm_num) hu.1,
    integral_Ioc_half_one_inv_mul_log]
  ring

/-! ### The substitution `y = x²/2` -/

/-- `J = ¼ ∫₀^∞ (e^{−y} − 1_{(0,½]}(y)) (log 2 + log y)/y dy`. -/
theorem gaussJlog_eq_half_cut :
    gaussJlog = (∫ y in Ioi (0 : ℝ),
      (Real.exp (-y) - (Ioc 0 (1 / 2)).indicator 1 y) * (Real.log 2 + Real.log y) / y) / 4 := by
  set g : ℝ → ℝ := fun w =>
    (Real.exp (-w / 2) - (Ioc 0 1).indicator 1 w) * Real.log w / (4 * w) with hg
  have h1 : gaussJlog = ∫ w in Ioi (0 : ℝ), g w := by
    unfold gaussJlog
    rw [← integral_comp_rpow_Ioi_of_pos (g := g) (p := 2) two_pos]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx' : (0 : ℝ) < x := hx
    simp only [hg, smul_eq_mul, Real.rpow_two]
    rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]
    have hind : (Ioc (0 : ℝ) 1).indicator (1 : ℝ → ℝ) (x ^ 2) =
        (Ioc (0 : ℝ) 1).indicator 1 x := by
      by_cases h : x ≤ 1
      · rw [indicator_of_mem (mem_Ioc.2 ⟨by positivity, by nlinarith⟩ : x ^ 2 ∈ Ioc (0 : ℝ) 1),
          indicator_of_mem (mem_Ioc.2 ⟨hx', h⟩ : x ∈ Ioc (0 : ℝ) 1)]
        rfl
      · rw [indicator_of_notMem (fun hm : x ^ 2 ∈ Ioc (0 : ℝ) 1 => h (by nlinarith [hm.2])),
          indicator_of_notMem (fun hm : x ∈ Ioc (0 : ℝ) 1 => h hm.2)]
    unfold gaussH
    rw [hind, Real.log_pow, Nat.cast_ofNat]
    field_simp
    ring
  have h2 : ∫ w in Ioi (0 : ℝ), g w = 2 * ∫ y in Ioi (0 : ℝ), g (2 * y) := by
    rw [integral_comp_mul_left_Ioi g 0 two_pos, mul_zero, smul_eq_mul]
    ring
  have e : ∀ y ∈ Ioi (0 : ℝ), g (2 * y) =
      ((Real.exp (-y) - (Ioc 0 (1 / 2)).indicator 1 y) * (Real.log 2 + Real.log y) / y) / 8 := by
    intro y hy
    have hy' : (0 : ℝ) < y := hy
    simp only [hg]
    have hind : (Ioc (0 : ℝ) 1).indicator (1 : ℝ → ℝ) (2 * y) =
        (Ioc (0 : ℝ) (1 / 2)).indicator 1 y := by
      by_cases h : y ≤ 1 / 2
      · rw [indicator_of_mem (mem_Ioc.2 ⟨by positivity, by linarith⟩ : 2 * y ∈ Ioc (0 : ℝ) 1),
          indicator_apply, if_pos (mem_Ioc.2 ⟨hy', h⟩ : y ∈ Ioc (0 : ℝ) (1 / 2))]
        rfl
      · rw [indicator_of_notMem (fun hm : 2 * y ∈ Ioc (0 : ℝ) 1 => h (by linarith [hm.2])),
          indicator_of_notMem (fun hm : y ∈ Ioc (0 : ℝ) (1 / 2) => h hm.2)]
    rw [hind, Real.log_mul two_ne_zero hy'.ne', show -(2 * y) / 2 = -y by ring]
    field_simp
    ring
  rw [h1, h2, setIntegral_congr_fun measurableSet_Ioi e, integral_div]
  ring

/-- ★★★ **The exact logarithmic moment**: `J = R₀²/2 + π²/48` with `R₀ = (log 2 − γ)/2`. -/
theorem gaussJlog_eq : gaussJlog = gaussR₀ ^ 2 / 2 + Real.pi ^ 2 / 48 := by
  rw [gaussJlog_eq_half_cut]
  have e : ∀ y ∈ Ioi (0 : ℝ),
      (Real.exp (-y) - (Ioc 0 (1 / 2)).indicator 1 y) * (Real.log 2 + Real.log y) / y =
        Real.log 2 * ((Real.exp (-y) - (Ioc 0 (1 / 2)).indicator 1 y) / y) +
          (Real.exp (-y) - (Ioc 0 (1 / 2)).indicator 1 y) * Real.log y / y := by
    intro y hy
    have hy' : (0 : ℝ) < y := hy
    field_simp
  have hA : Integrable (fun y : ℝ =>
      Real.log 2 * ((Real.exp (-y) - (Ioc 0 (1 / 2)).indicator 1 y) / y))
      (volume.restrict (Ioi 0)) := integrableOn_renormalised_exp_inv_half.const_mul _
  rw [setIntegral_congr_fun measurableSet_Ioi e, integral_add hA
    integrableOn_renormalised_exp_log_half, integral_const_mul,
    integral_renormalised_exp_inv_half, integral_renormalised_exp_log_half]
  unfold gaussR₀
  ring

end Grammar
