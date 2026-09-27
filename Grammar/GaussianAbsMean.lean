/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.ConeSecondCoefficientSymmetric

/-!
# The absolute mean of a shifted Gaussian: `E|a + G| = a b(a) + 2γ(a)`

`b(a) = 2∫₀^a γ = 2Φ(a) − 1` (`coneB`): `b' = 2γ`, `|b| ≤ 1`, `b(±∞) = ±1`.  The tilted absolute
moment `m(a) = coneAbsMean a = E_{N(a,1)}|T| = ∫ |t| γ(t − a) dt` is evaluated by the fundamental
theorem of calculus on `(−∞, 0]` and `[0, ∞)` with the antiderivative
`F(t) = −γ(t − a) + a ∫₀^{t−a} γ` of `t γ(t − a)`:

  `m(a) = a b(a) + 2 γ(a)`   (★★ `coneAbsMean_eq`).

Used by the exact value of the cone's second coefficient (examples_slop §3; Astra round-13
target 1).  Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

/-! ### The Gaussian density: derivative, tails, half masses -/

theorem hasDerivAt_gaussDensity (u : ℝ) :
    HasDerivAt gaussDensity (-u * gaussDensity u) u := by
  unfold gaussDensity
  have h : HasDerivAt (fun u : ℝ => -u ^ 2 / 2) (-u) u := by
    have := ((hasDerivAt_pow 2 u).neg).div_const 2
    refine this.congr_deriv ?_
    simp
    ring
  have := (h.exp).div_const (Real.sqrt (2 * Real.pi))
  refine this.congr_deriv ?_
  ring

theorem gaussDensity_le_one (u : ℝ) : gaussDensity u ≤ 1 := by
  unfold gaussDensity
  have hs : 2 ≤ Real.sqrt (2 * Real.pi) := sqrt_two_pi_bounds.1
  rw [div_le_one (by linarith)]
  have : Real.exp (-u ^ 2 / 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg u])
  linarith

theorem tendsto_gaussDensity_atTop : Tendsto gaussDensity atTop (𝓝 0) := by
  unfold gaussDensity
  have h1 : Tendsto (fun u : ℝ => -u ^ 2 / 2) atTop atBot := by
    have hp : Tendsto (fun u : ℝ => u ^ 2) atTop atTop := tendsto_pow_atTop two_ne_zero
    have := tendsto_neg_atTop_atBot.comp hp
    exact this.atBot_div_const two_pos
  have h2 := Real.tendsto_exp_atBot.comp h1
  have h3 := h2.div_const (Real.sqrt (2 * Real.pi))
  simpa [Function.comp_def] using h3

theorem tendsto_gaussDensity_atBot : Tendsto gaussDensity atBot (𝓝 0) := by
  have h := tendsto_gaussDensity_atTop.comp tendsto_neg_atBot_atTop
  refine h.congr fun u => ?_
  simp [gaussDensity_neg]

theorem integral_gaussDensity_Ioi : ∫ t in Ioi (0 : ℝ), gaussDensity t = 1 / 2 := by
  unfold gaussDensity
  rw [integral_div]
  have e : ∀ t ∈ Ioi (0 : ℝ), Real.exp (-t ^ 2 / 2) = Real.exp (-(1 / 2) * t ^ 2) := by
    intro t _; congr 1; ring
  rw [setIntegral_congr_fun measurableSet_Ioi e, integral_gaussian_Ioi,
    show Real.pi / (1 / 2) = 2 * Real.pi by ring]
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  field_simp

theorem integral_gaussDensity_Iic : ∫ t in Iic (0 : ℝ), gaussDensity t = 1 / 2 := by
  calc ∫ t in Iic (0 : ℝ), gaussDensity t = ∫ t in Iic (0 : ℝ), gaussDensity (-t) :=
        setIntegral_congr_fun measurableSet_Iic fun t _ => (gaussDensity_neg t).symm
    _ = ∫ t in Ioi (-(0 : ℝ)), gaussDensity t := integral_comp_neg_Iic 0 gaussDensity
    _ = 1 / 2 := by rw [neg_zero, integral_gaussDensity_Ioi]

theorem integral_gaussDensity : ∫ t, gaussDensity t = 1 := by
  rw [← intervalIntegral.integral_Iic_add_Ioi (b := 0) integrable_gaussDensity.integrableOn
    integrable_gaussDensity.integrableOn, integral_gaussDensity_Iic, integral_gaussDensity_Ioi]
  norm_num

/-! ### `b(a) = 2∫₀^a γ` -/

/-- `b(a) = 2∫₀^a γ = 2Φ(a) − 1`. -/
noncomputable def coneB (a : ℝ) : ℝ := 2 * ∫ t in (0 : ℝ)..a, gaussDensity t

theorem hasDerivAt_intervalIntegral_gaussDensity (a : ℝ) :
    HasDerivAt (fun u => ∫ t in (0 : ℝ)..u, gaussDensity t) (gaussDensity a) a :=
  intervalIntegral.integral_hasDerivAt_right (continuous_gaussDensity.intervalIntegrable _ _)
    (continuous_gaussDensity.stronglyMeasurableAtFilter _ _) continuous_gaussDensity.continuousAt

theorem hasDerivAt_coneB (a : ℝ) : HasDerivAt coneB (2 * gaussDensity a) a := by
  unfold coneB
  exact (hasDerivAt_intervalIntegral_gaussDensity a).const_mul 2

theorem continuous_coneB : Continuous coneB :=
  continuous_iff_continuousAt.2 fun a => (hasDerivAt_coneB a).continuousAt

/-- `|∫₀^a γ| ≤ ½`. -/
theorem abs_intervalIntegral_gaussDensity_le (a : ℝ) :
    |∫ t in (0 : ℝ)..a, gaussDensity t| ≤ 1 / 2 := by
  rcases le_or_gt 0 a with h | h
  · rw [intervalIntegral.integral_of_le h, abs_of_nonneg
      (setIntegral_nonneg measurableSet_Ioc fun t _ => gaussDensity_nonneg t),
      ← integral_gaussDensity_Ioi]
    exact setIntegral_mono_set integrable_gaussDensity.integrableOn
      (Eventually.of_forall fun t => gaussDensity_nonneg t)
      (Eventually.of_forall fun t (ht : t ∈ Ioc 0 a) => ht.1)
  · rw [intervalIntegral.integral_symm, intervalIntegral.integral_of_le h.le, abs_neg,
      abs_of_nonneg (setIntegral_nonneg measurableSet_Ioc fun t _ => gaussDensity_nonneg t),
      ← integral_gaussDensity_Iic]
    exact setIntegral_mono_set integrable_gaussDensity.integrableOn
      (Eventually.of_forall fun t => gaussDensity_nonneg t)
      (Eventually.of_forall fun t (ht : t ∈ Ioc a 0) => ht.2)

theorem abs_coneB_le (a : ℝ) : |coneB a| ≤ 1 := by
  unfold coneB
  rw [abs_mul, abs_two]
  linarith [abs_intervalIntegral_gaussDensity_le a]

theorem tendsto_intervalIntegral_gaussDensity_atTop :
    Tendsto (fun u => ∫ t in (0 : ℝ)..u, gaussDensity t) atTop (𝓝 (1 / 2)) := by
  have h := intervalIntegral_tendsto_integral_Ioi 0 integrable_gaussDensity.integrableOn
    (tendsto_id (x := atTop))
  rw [integral_gaussDensity_Ioi] at h
  exact h

theorem tendsto_intervalIntegral_gaussDensity_atBot :
    Tendsto (fun u => ∫ t in (0 : ℝ)..u, gaussDensity t) atBot (𝓝 (-(1 / 2))) := by
  have h := intervalIntegral_tendsto_integral_Iic 0 integrable_gaussDensity.integrableOn
    (tendsto_id (x := atBot))
  rw [integral_gaussDensity_Iic] at h
  have h' := h.neg
  refine h'.congr fun u => ?_
  simp only [id]
  rw [intervalIntegral.integral_symm, neg_neg]

theorem tendsto_coneB_atTop : Tendsto coneB atTop (𝓝 1) := by
  have h := tendsto_intervalIntegral_gaussDensity_atTop.const_mul 2
  unfold coneB
  norm_num at h
  exact h

theorem tendsto_coneB_atBot : Tendsto coneB atBot (𝓝 (-1)) := by
  have h := tendsto_intervalIntegral_gaussDensity_atBot.const_mul 2
  unfold coneB
  norm_num at h
  exact h

/-! ### `m(a) = a b(a) + 2γ(a)` -/

/-- `m(a) = ∫ |t| γ(t − a) dt`. -/
theorem coneAbsMean_eq_integral (a : ℝ) :
    coneAbsMean a = ∫ t, |t| * gaussDensity (t - a) := by
  unfold coneAbsMean
  simp only [coneTilt_zero]
  rw [integral_gaussTilt]
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hE : 0 < Real.exp (a ^ 2 / 2) := Real.exp_pos _
  rw [div_eq_iff (by positivity), ← integral_mul_const]
  congr 1
  funext t
  unfold gaussDensity
  rw [gaussTilt_eq]
  field_simp

/-- The antiderivative `F(t) = −γ(t − a) + a ∫₀^{t−a} γ` of `t γ(t − a)`. -/
noncomputable def absMeanPrim (a t : ℝ) : ℝ :=
  -gaussDensity (t - a) + a * ∫ x in (0 : ℝ)..(t - a), gaussDensity x

theorem hasDerivAt_absMeanPrim (a t : ℝ) :
    HasDerivAt (absMeanPrim a) (t * gaussDensity (t - a)) t := by
  unfold absMeanPrim
  have h1 : HasDerivAt (fun t => gaussDensity (t - a)) (-(t - a) * gaussDensity (t - a)) t :=
    (hasDerivAt_gaussDensity (t - a)).comp_sub_const t a
  have h2 : HasDerivAt (fun t => ∫ x in (0 : ℝ)..(t - a), gaussDensity x)
      (gaussDensity (t - a)) t :=
    (hasDerivAt_intervalIntegral_gaussDensity (t - a)).comp_sub_const t a
  refine (h1.neg.add (h2.const_mul a)).congr_deriv ?_
  ring

theorem tendsto_absMeanPrim_atTop (a : ℝ) :
    Tendsto (absMeanPrim a) atTop (𝓝 (a * (1 / 2))) := by
  unfold absMeanPrim
  have h1 : Tendsto (fun t => gaussDensity (t - a)) atTop (𝓝 0) :=
    tendsto_gaussDensity_atTop.comp (tendsto_atTop_add_const_right atTop (-a) tendsto_id)
  have h2 : Tendsto (fun t => ∫ x in (0 : ℝ)..(t - a), gaussDensity x) atTop (𝓝 (1 / 2)) :=
    tendsto_intervalIntegral_gaussDensity_atTop.comp
      (tendsto_atTop_add_const_right atTop (-a) tendsto_id)
  have := h1.neg.add (h2.const_mul a)
  simpa using this

theorem tendsto_absMeanPrim_atBot (a : ℝ) :
    Tendsto (absMeanPrim a) atBot (𝓝 (a * (-(1 / 2)))) := by
  unfold absMeanPrim
  have h1 : Tendsto (fun t => gaussDensity (t - a)) atBot (𝓝 0) :=
    tendsto_gaussDensity_atBot.comp (tendsto_atBot_add_const_right atBot (-a) tendsto_id)
  have h2 : Tendsto (fun t => ∫ x in (0 : ℝ)..(t - a), gaussDensity x) atBot (𝓝 (-(1 / 2))) :=
    tendsto_intervalIntegral_gaussDensity_atBot.comp
      (tendsto_atBot_add_const_right atBot (-a) tendsto_id)
  have := h1.neg.add (h2.const_mul a)
  simpa using this

/-- `F(0) = −γ(a) − a b(a)/2`. -/
theorem absMeanPrim_zero (a : ℝ) : absMeanPrim a 0 = -gaussDensity a - a * (coneB a / 2) := by
  unfold absMeanPrim coneB
  rw [zero_sub, gaussDensity_neg]
  have h : ∫ x in (0 : ℝ)..(-a), gaussDensity x = -∫ x in (0 : ℝ)..a, gaussDensity x := by
    have e : ∫ x in (0 : ℝ)..(-a), gaussDensity x = ∫ x in (0 : ℝ)..(-a), gaussDensity (-x) :=
      intervalIntegral.integral_congr fun x _ => (gaussDensity_neg x).symm
    rw [e, intervalIntegral.integral_comp_neg, neg_neg, neg_zero, intervalIntegral.integral_symm]
  rw [h]
  ring

theorem integrable_abs_mul_gaussDensity_sub (a : ℝ) :
    Integrable (fun t : ℝ => |t| * gaussDensity (t - a)) := by
  have := (integrable_abs_gaussTilt a).const_mul (Real.exp (-a ^ 2 / 2) / Real.sqrt (2 * Real.pi))
  refine this.congr (Eventually.of_forall fun t => ?_)
  simp only
  unfold gaussDensity
  rw [gaussTilt_eq]
  have hE : Real.exp (-a ^ 2 / 2) * Real.exp (a ^ 2 / 2) = 1 := by
    rw [← Real.exp_add, show -a ^ 2 / 2 + a ^ 2 / 2 = 0 by ring, Real.exp_zero]
  linear_combination (|t| * Real.exp (-(t - a) ^ 2 / 2) / Real.sqrt (2 * Real.pi)) * hE

/-- ★★ **The absolute mean**: `m(a) = a b(a) + 2 γ(a)`. -/
theorem coneAbsMean_eq (a : ℝ) : coneAbsMean a = a * coneB a + 2 * gaussDensity a := by
  rw [coneAbsMean_eq_integral, ← intervalIntegral.integral_Iic_add_Ioi (b := 0)
    (integrable_abs_mul_gaussDensity_sub a).integrableOn
    (integrable_abs_mul_gaussDensity_sub a).integrableOn]
  have hR : ∫ t in Ioi (0 : ℝ), |t| * gaussDensity (t - a) =
      a * (1 / 2) - absMeanPrim a 0 := by
    rw [← integral_Ioi_of_hasDerivAt_of_tendsto (f := absMeanPrim a)
      (hasDerivAt_absMeanPrim a 0).continuousAt.continuousWithinAt
      (fun t _ => hasDerivAt_absMeanPrim a t)
      ?_ (tendsto_absMeanPrim_atTop a)]
    · refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : (0 : ℝ) < t) => ?_
      rw [abs_of_pos ht]
    · refine IntegrableOn.congr_fun (integrable_abs_mul_gaussDensity_sub a).integrableOn
        (fun t (ht : (0 : ℝ) < t) => ?_) measurableSet_Ioi
      rw [abs_of_pos ht]
  have hL : ∫ t in Iic (0 : ℝ), |t| * gaussDensity (t - a) =
      (-absMeanPrim a 0) - (-(a * (-(1 / 2)))) := by
    rw [← integral_Iic_of_hasDerivAt_of_tendsto (f := fun t => -absMeanPrim a t)
      (f' := fun t => -(t * gaussDensity (t - a)))
      (hasDerivAt_absMeanPrim a 0).neg.continuousAt.continuousWithinAt
      (fun t _ => (hasDerivAt_absMeanPrim a t).neg)
      ?_ (tendsto_absMeanPrim_atBot a).neg]
    · refine setIntegral_congr_fun measurableSet_Iic fun t (ht : t ≤ 0) => ?_
      rw [abs_of_nonpos ht]
      ring
    · refine IntegrableOn.congr_fun (integrable_abs_mul_gaussDensity_sub a).integrableOn
        (fun t (ht : t ≤ 0) => ?_) measurableSet_Iic
      rw [abs_of_nonpos ht]
      ring
  rw [hL, hR, absMeanPrim_zero]
  ring

end Grammar
