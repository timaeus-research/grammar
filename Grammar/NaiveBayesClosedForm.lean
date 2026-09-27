/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.NaiveBayesDensity

/-!
# The closed form of the naive Bayes fibre volume

For `b₁, b₂ ∈ (0,1)` the quadrant product `P(t) = min((1−b₁)t, b₁(1−t))·min((1−b₂)t, b₂(1−t))`
and the quadrant integral `J(z) = ∫₀¹ dt/(t(1−t)) · log⁺(P(t)/(t(1−t)z))` satisfy, for
`0 < z < M := min(b₁(1−b₂), b₂(1−b₁))`,

  `J(z) = log(M/z) · log(AD/(Mz))`,  `A = (1−b₁)(1−b₂)`, `D = b₁b₂`.

The proof is the layer cake: `log⁺(Q/z) = ∫_z^∞ 1[w ≤ Q] dw/w`, Tonelli, and the superlevel set
`{t : w ≤ P(t)/(t(1−t))} = [w/(A+w), D/(D+w)]` for `w ≤ M` (empty above `M`), whose
`∫ dt/(t(1−t))` is `log(AD/w²)`; then `∫_z^M log(AD/w²) dw/w = log(M/z) log(AD/(Mz))`.
No case analysis on the order of `b₁, b₂` is needed: a product of two minima of nonnegative
numbers is the minimum of the four products.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Grammar

/-- The quadrant product `P(t) = min((1−b₁)t, b₁(1−t)) · min((1−b₂)t, b₂(1−t))`. -/
noncomputable def quadP (b₁ b₂ t : ℝ) : ℝ :=
  min ((1 - b₁) * t) (b₁ * (1 - t)) * min ((1 - b₂) * t) (b₂ * (1 - t))

/-- The quadrant integral `∫₀¹ dt/(t(1−t)) log⁺(P(t)/(t(1−t)z))`. -/
noncomputable def quadJ (b₁ b₂ z : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal (t * (1 - t))⁻¹ *
    ENNReal.ofReal (max (Real.log (quadP b₁ b₂ t / (t * (1 - t)) / z)) 0)

/-- A product of minima of nonnegative numbers is the minimum of the four products. -/
theorem min_mul_min_eq {x₁ y₁ x₂ y₂ : ℝ} (hx₁ : 0 ≤ x₁) (hy₁ : 0 ≤ y₁) (hx₂ : 0 ≤ x₂)
    (hy₂ : 0 ≤ y₂) :
    min x₁ y₁ * min x₂ y₂ = min (min (x₁ * x₂) (x₁ * y₂)) (min (y₁ * x₂) (y₁ * y₂)) := by
  rw [min_mul_of_nonneg _ _ (le_min hx₂ hy₂), mul_min_of_nonneg _ _ hx₁, mul_min_of_nonneg _ _ hy₁]

section Quadrant

variable {b₁ b₂ : ℝ} (hb₁ : 0 < b₁) (hb₁' : b₁ < 1) (hb₂ : 0 < b₂) (hb₂' : b₂ < 1)
include hb₁ hb₁' hb₂ hb₂'

/-- The superlevel set `{t ∈ (0,1) : w ≤ P(t)/(t(1−t))}` for `0 < w ≤ M` is the interval
`[w/(A+w), D/(D+w)]`. -/
theorem quad_superlevel {w : ℝ} (hw : 0 < w) (hwM : w ≤ min (b₁ * (1 - b₂)) (b₂ * (1 - b₁))) :
    {t | t ∈ Ioo (0 : ℝ) 1 ∧ w ≤ quadP b₁ b₂ t / (t * (1 - t))} =
      Icc (w / ((1 - b₁) * (1 - b₂) + w)) (b₁ * b₂ / (b₁ * b₂ + w)) := by
  have hA : 0 < (1 - b₁) * (1 - b₂) := mul_pos (sub_pos.mpr hb₁') (sub_pos.mpr hb₂')
  have hD : 0 < b₁ * b₂ := mul_pos hb₁ hb₂
  have hM₁ : w ≤ b₁ * (1 - b₂) := hwM.trans (min_le_left _ _)
  have hM₂ : w ≤ b₂ * (1 - b₁) := hwM.trans (min_le_right _ _)
  ext t
  simp only [mem_ofPred_eq, mem_Ioo, mem_Icc]
  constructor
  · rintro ⟨⟨ht0, ht1⟩, hle⟩
    have hc : 0 < t * (1 - t) := mul_pos ht0 (sub_pos.mpr ht1)
    rw [le_div_iff₀ hc, quadP, min_mul_min_eq (by nlinarith) (by nlinarith) (by nlinarith)
      (by nlinarith), le_min_iff, le_min_iff, le_min_iff] at hle
    obtain ⟨⟨h1, -⟩, ⟨-, h4⟩⟩ := hle
    constructor
    · rw [div_le_iff₀ (by positivity)]; nlinarith
    · rw [le_div_iff₀ (by positivity)]; nlinarith
  · rintro ⟨h1, h4⟩
    have ht0 : 0 < t := lt_of_lt_of_le (div_pos hw (by positivity)) h1
    have ht1 : t < 1 := lt_of_le_of_lt h4 (by rw [div_lt_one (by positivity)]; linarith)
    have hc : 0 < t * (1 - t) := mul_pos ht0 (sub_pos.mpr ht1)
    refine ⟨⟨ht0, ht1⟩, ?_⟩
    rw [div_le_iff₀ (by positivity)] at h1
    rw [le_div_iff₀ (by positivity)] at h4
    rw [le_div_iff₀ hc, quadP, min_mul_min_eq (by nlinarith) (by nlinarith) (by nlinarith)
      (by nlinarith), le_min_iff, le_min_iff, le_min_iff]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> nlinarith

/-- Above `M` the superlevel set is empty. -/
theorem quad_superlevel_empty {w : ℝ}
    (hwM : min (b₁ * (1 - b₂)) (b₂ * (1 - b₁)) < w) :
    {t | t ∈ Ioo (0 : ℝ) 1 ∧ w ≤ quadP b₁ b₂ t / (t * (1 - t))} = ∅ := by
  ext t
  simp only [mem_ofPred_eq, mem_Ioo, mem_empty_iff_false, iff_false, not_and]
  rintro ⟨ht0, ht1⟩ hle
  have hc : 0 < t * (1 - t) := mul_pos ht0 (sub_pos.mpr ht1)
  rw [le_div_iff₀ hc, quadP, min_mul_min_eq (by nlinarith) (by nlinarith) (by nlinarith)
    (by nlinarith), le_min_iff, le_min_iff, le_min_iff] at hle
  obtain ⟨⟨-, h2⟩, ⟨h3, -⟩⟩ := hle
  rcases min_lt_iff.mp hwM with h | h
  · nlinarith
  · nlinarith

end Quadrant

/-- `∫_a^b dt/(t(1−t)) = log(b/(1−b)) − log(a/(1−a))` for `0 < a ≤ b < 1`, as a lower integral. -/
theorem lintegral_Icc_inv_mul_one_sub {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    ∫⁻ t in Icc a b, ENNReal.ofReal (t * (1 - t))⁻¹ =
      ENNReal.ofReal (Real.log (b / (1 - b)) - Real.log (a / (1 - a))) := by
  have hcont : ContinuousOn (fun t : ℝ => (t * (1 - t))⁻¹) (Icc a b) := by
    refine ContinuousOn.inv₀ (by fun_prop) fun t ht => ?_
    exact (mul_pos (ha.trans_le ht.1) (sub_pos.mpr (ht.2.trans_lt hb))).ne'
  have hnn : ∀ t ∈ Icc a b, 0 ≤ (t * (1 - t))⁻¹ := fun t ht =>
    inv_nonneg.mpr (mul_nonneg (ha.le.trans ht.1) (sub_nonneg.mpr (ht.2.trans hb.le)))
  rw [← ofReal_integral_eq_lintegral_ofReal (hcont.integrableOn_Icc)
    (ae_restrict_of_forall_mem measurableSet_Icc hnn)]
  congr 1
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  have hderiv : ∀ t ∈ uIcc a b,
      HasDerivAt (fun t => Real.log t - Real.log (1 - t)) ((t * (1 - t))⁻¹) t := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    have ht0 : t ≠ 0 := (ha.trans_le ht.1).ne'
    have ht1 : 1 - t ≠ 0 := (sub_pos.mpr (ht.2.trans_lt hb)).ne'
    have h := (Real.hasDerivAt_log ht0).sub
      ((Real.hasDerivAt_log ht1).comp t ((hasDerivAt_id t).const_sub 1))
    have e : t⁻¹ - (1 - t)⁻¹ * -1 = (t * (1 - t))⁻¹ := by
      field_simp
      ring
    exact h.congr_deriv e
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (hcont.intervalIntegrable_of_Icc hab)]
  rw [Real.log_div (ha.trans_le hab).ne' (sub_pos.mpr hb).ne',
    Real.log_div ha.ne' (sub_pos.mpr (hab.trans_lt hb)).ne']

/-- The layer cake for `log⁺`: `log⁺(Q/z) = ∫_{w > z} 1[w ≤ Q] dw/w` for `z > 0`. -/
theorem ofReal_logPlus_eq_lintegral {Q z : ℝ} (hQ : 0 < Q) (hz : 0 < z) :
    ENNReal.ofReal (max (Real.log (Q / z)) 0) =
      ∫⁻ w in Ioi z, (Iic Q).indicator (fun w => ENNReal.ofReal w⁻¹) w := by
  rw [lintegral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
    inter_comm, Ioi_inter_Iic, restrict_Ioc_eq_restrict_Icc]
  rcases le_or_gt z Q with hzQ | hzQ
  · rw [lintegral_Icc_inv hz hzQ]
    congr 1
    exact max_eq_left (Real.log_nonneg ((one_le_div hz).mpr hzQ))
  · rw [Icc_eq_empty (not_le.mpr hzQ), Measure.restrict_empty, lintegral_zero_measure,
      max_eq_right (Real.log_nonpos (by positivity) ((div_le_one hz).mpr hzQ.le)),
      ENNReal.ofReal_zero]

/-- `∫_z^M log(AD/w²) dw/w = log(M/z) log(AD/(Mz))` for `0 < z ≤ M`, `M² ≤ AD`. -/
theorem lintegral_log_div_sq {A D M z : ℝ} (hA : 0 < A) (hD : 0 < D) (hz : 0 < z) (hzM : z ≤ M)
    (hM : M ^ 2 ≤ A * D) :
    ∫⁻ w in Icc z M, ENNReal.ofReal w⁻¹ * ENNReal.ofReal (Real.log (A * D / w ^ 2)) =
      ENNReal.ofReal (Real.log (M / z) * Real.log (A * D / (M * z))) := by
  have hAD : 0 < A * D := mul_pos hA hD
  have hnn : ∀ w ∈ Icc z M, 0 ≤ w⁻¹ * Real.log (A * D / w ^ 2) := by
    intro w hw
    have hw0 : 0 < w := hz.trans_le hw.1
    refine mul_nonneg (inv_nonneg.mpr hw0.le) (Real.log_nonneg ?_)
    rw [le_div_iff₀ (by positivity), one_mul]
    nlinarith [hw.2, hw.1]
  have hcont : ContinuousOn (fun w : ℝ => w⁻¹ * Real.log (A * D / w ^ 2)) (Icc z M) := by
    refine ContinuousOn.mul (continuousOn_inv₀.mono fun w hw => (hz.trans_le hw.1).ne') ?_
    refine ContinuousOn.log (continuousOn_const.div (continuous_pow 2).continuousOn
      fun w hw => (pow_pos (hz.trans_le hw.1) 2).ne') fun w hw => ?_
    exact (div_pos hAD (pow_pos (hz.trans_le hw.1) 2)).ne'
  have e : ∀ w ∈ Icc z M, ENNReal.ofReal w⁻¹ * ENNReal.ofReal (Real.log (A * D / w ^ 2)) =
      ENNReal.ofReal (w⁻¹ * Real.log (A * D / w ^ 2)) := fun w hw =>
    (ENNReal.ofReal_mul (inv_nonneg.mpr (hz.trans_le hw.1).le)).symm
  rw [setLIntegral_congr_fun measurableSet_Icc e,
    ← ofReal_integral_eq_lintegral_ofReal hcont.integrableOn_Icc
      (ae_restrict_of_forall_mem measurableSet_Icc hnn)]
  congr 1
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hzM]
  have hderiv : ∀ w ∈ uIcc z M, HasDerivAt
      (fun w => Real.log (A * D) * Real.log w - Real.log w ^ 2)
      (w⁻¹ * Real.log (A * D / w ^ 2)) w := by
    intro w hw
    rw [uIcc_of_le hzM] at hw
    have hw0 : 0 < w := hz.trans_le hw.1
    have h := ((Real.hasDerivAt_log hw0.ne').const_mul (Real.log (A * D))).sub
      ((Real.hasDerivAt_log hw0.ne').pow 2)
    refine h.congr_deriv ?_
    rw [Real.log_div hAD.ne' (pow_pos hw0 2).ne', Real.log_pow]
    push_cast
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (hcont.intervalIntegrable_of_Icc hzM)]
  have hM0 : 0 < M := hz.trans_le hzM
  rw [Real.log_div hM0.ne' hz.ne', Real.log_div hAD.ne' (mul_pos hM0 hz).ne',
    Real.log_mul hM0.ne' hz.ne']
  ring

section Quadrant

variable {b₁ b₂ : ℝ} (hb₁ : 0 < b₁) (hb₁' : b₁ < 1) (hb₂ : 0 < b₂) (hb₂' : b₂ < 1)
include hb₁ hb₁' hb₂ hb₂'

theorem quadP_pos {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) : 0 < quadP b₁ b₂ t :=
  mul_pos (lt_min (mul_pos (sub_pos.mpr hb₁') ht.1) (mul_pos hb₁ (sub_pos.mpr ht.2)))
    (lt_min (mul_pos (sub_pos.mpr hb₂') ht.1) (mul_pos hb₂ (sub_pos.mpr ht.2)))

omit hb₁ hb₁' hb₂ hb₂' in
theorem measurable_quadQ : Measurable fun t => quadP b₁ b₂ t / (t * (1 - t)) := by
  unfold quadP
  exact (((by fun_prop : Measurable fun t : ℝ => (1 - b₁) * t).min (by fun_prop)).mul
    ((by fun_prop : Measurable fun t : ℝ => (1 - b₂) * t).min (by fun_prop))).div (by fun_prop)

/-- The superlevel integral `∫_{w ≤ P/(t(1−t))} dt/(t(1−t))`: `log(AD/w²)` for `0 < w ≤ M`, and
`0` above `M`. -/
theorem lintegral_quad_superlevel {w : ℝ} (hw : 0 < w) :
    ∫⁻ t in {t | t ∈ Ioo (0 : ℝ) 1 ∧ w ≤ quadP b₁ b₂ t / (t * (1 - t))},
        ENNReal.ofReal (t * (1 - t))⁻¹ =
      (Iic (min (b₁ * (1 - b₂)) (b₂ * (1 - b₁)))).indicator
        (fun w => ENNReal.ofReal (Real.log ((1 - b₁) * (1 - b₂) * (b₁ * b₂) / w ^ 2))) w := by
  have hA : 0 < (1 - b₁) * (1 - b₂) := mul_pos (sub_pos.mpr hb₁') (sub_pos.mpr hb₂')
  have hD : 0 < b₁ * b₂ := mul_pos hb₁ hb₂
  rcases le_or_gt w (min (b₁ * (1 - b₂)) (b₂ * (1 - b₁))) with hwM | hwM
  · have hM₁ : w ≤ b₁ * (1 - b₂) := hwM.trans (min_le_left _ _)
    have hM₂ : w ≤ b₂ * (1 - b₁) := hwM.trans (min_le_right _ _)
    have hw2 : w ^ 2 ≤ (1 - b₁) * (1 - b₂) * (b₁ * b₂) := by nlinarith
    have hab : w / ((1 - b₁) * (1 - b₂) + w) ≤ b₁ * b₂ / (b₁ * b₂ + w) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    rw [quad_superlevel hb₁ hb₁' hb₂ hb₂' hw hwM, indicator_of_mem (mem_Iic.mpr hwM),
      lintegral_Icc_inv_mul_one_sub (div_pos hw (by positivity)) hab
        (by rw [div_lt_one (by positivity)]; linarith)]
    congr 1
    have hDw : b₁ * b₂ + w ≠ 0 := by positivity
    have hAw : (1 - b₁) * (1 - b₂) + w ≠ 0 := by positivity
    have e1 : b₁ * b₂ / (b₁ * b₂ + w) / (1 - b₁ * b₂ / (b₁ * b₂ + w)) = b₁ * b₂ / w := by
      rw [one_sub_div hDw, div_div_div_cancel_right₀ hDw, add_sub_cancel_left]
    have e2 : w / ((1 - b₁) * (1 - b₂) + w) / (1 - w / ((1 - b₁) * (1 - b₂) + w)) =
        w / ((1 - b₁) * (1 - b₂)) := by
      rw [one_sub_div hAw, div_div_div_cancel_right₀ hAw, add_sub_cancel_right]
    rw [e1, e2, ← Real.log_div (by positivity) (by positivity)]
    congr 1
    field_simp
  · rw [quad_superlevel_empty hb₁ hb₁' hb₂ hb₂' hwM, Measure.restrict_empty,
      lintegral_zero_measure, indicator_of_notMem fun h => not_le.mpr hwM (mem_Iic.mp h)]

/-- ★★ The quadrant integral in closed form: for `0 < z < M = min(b₁(1−b₂), b₂(1−b₁))`,
`J(z) = log(M/z) · log(AD/(Mz))` with `A = (1−b₁)(1−b₂)`, `D = b₁b₂`. -/
theorem quadJ_eq {z : ℝ} (hz : 0 < z) (hzM : z < min (b₁ * (1 - b₂)) (b₂ * (1 - b₁))) :
    quadJ b₁ b₂ z = ENNReal.ofReal (Real.log (min (b₁ * (1 - b₂)) (b₂ * (1 - b₁)) / z) *
      Real.log ((1 - b₁) * (1 - b₂) * (b₁ * b₂) / (min (b₁ * (1 - b₂)) (b₂ * (1 - b₁)) * z))) := by
  set M := min (b₁ * (1 - b₂)) (b₂ * (1 - b₁)) with hMdef
  have hA : 0 < (1 - b₁) * (1 - b₂) := mul_pos (sub_pos.mpr hb₁') (sub_pos.mpr hb₂')
  have hD : 0 < b₁ * b₂ := mul_pos hb₁ hb₂
  have hM2 : M ^ 2 ≤ (1 - b₁) * (1 - b₂) * (b₁ * b₂) := by
    have h1 : M ≤ b₁ * (1 - b₂) := min_le_left _ _
    have h2 : M ≤ b₂ * (1 - b₁) := min_le_right _ _
    have h0 : 0 ≤ M := le_min (by nlinarith) (by nlinarith)
    nlinarith [mul_le_mul h1 h2 h0 (by nlinarith)]
  have hQm : Measurable fun t => quadP b₁ b₂ t / (t * (1 - t)) := measurable_quadQ
  have hind : ∀ t, Measurable fun w =>
      (Iic (quadP b₁ b₂ t / (t * (1 - t)))).indicator (fun w => ENNReal.ofReal w⁻¹) w :=
    fun t => measurable_inv.ennreal_ofReal.indicator measurableSet_Iic
  have hc : Measurable fun t : ℝ => ENNReal.ofReal (t * (1 - t))⁻¹ :=
    (by fun_prop : Measurable fun t : ℝ => (t * (1 - t))⁻¹).ennreal_ofReal
  have hmeas : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (p.1 * (1 - p.1))⁻¹ *
      (Iic (quadP b₁ b₂ p.1 / (p.1 * (1 - p.1)))).indicator (fun w => ENNReal.ofReal w⁻¹) p.2 := by
    have e : (fun p : ℝ × ℝ => (Iic (quadP b₁ b₂ p.1 / (p.1 * (1 - p.1)))).indicator
        (fun w => ENNReal.ofReal w⁻¹) p.2) = fun p =>
        if p.2 ≤ quadP b₁ b₂ p.1 / (p.1 * (1 - p.1)) then ENNReal.ofReal p.2⁻¹ else 0 := by
      funext p; simp [indicator_apply]
    refine ((by fun_prop : Measurable fun p : ℝ × ℝ => (p.1 * (1 - p.1))⁻¹).ennreal_ofReal).mul ?_
    rw [e]
    exact Measurable.ite (measurableSet_le measurable_snd (hQm.comp measurable_fst))
      measurable_snd.inv.ennreal_ofReal measurable_const
  calc quadJ b₁ b₂ z
      = ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal (t * (1 - t))⁻¹ * ∫⁻ w in Ioi z,
          (Iic (quadP b₁ b₂ t / (t * (1 - t)))).indicator (fun w => ENNReal.ofReal w⁻¹) w := by
        unfold quadJ
        refine setLIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
        rw [ofReal_logPlus_eq_lintegral (div_pos (quadP_pos hb₁ hb₁' hb₂ hb₂' ht)
          (mul_pos ht.1 (sub_pos.mpr ht.2))) hz]
    _ = ∫⁻ t in Ioo (0 : ℝ) 1, ∫⁻ w in Ioi z, ENNReal.ofReal (t * (1 - t))⁻¹ *
          (Iic (quadP b₁ b₂ t / (t * (1 - t)))).indicator (fun w => ENNReal.ofReal w⁻¹) w := by
        refine lintegral_congr fun t => ?_
        rw [lintegral_const_mul _ (hind t)]
    _ = ∫⁻ w in Ioi z, ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal (t * (1 - t))⁻¹ *
          (Iic (quadP b₁ b₂ t / (t * (1 - t)))).indicator (fun w => ENNReal.ofReal w⁻¹) w :=
        lintegral_lintegral_swap hmeas.aemeasurable
    _ = ∫⁻ w in Ioi z, ENNReal.ofReal w⁻¹ *
          ∫⁻ t in {t | t ∈ Ioo (0 : ℝ) 1 ∧ w ≤ quadP b₁ b₂ t / (t * (1 - t))},
            ENNReal.ofReal (t * (1 - t))⁻¹ := by
        refine lintegral_congr fun w => ?_
        have hset : MeasurableSet {t | t ∈ Ioo (0 : ℝ) 1 ∧ w ≤ quadP b₁ b₂ t / (t * (1 - t))} :=
          measurableSet_Ioo.inter (measurableSet_le measurable_const hQm)
        rw [← lintegral_const_mul _ hc, ← lintegral_indicator measurableSet_Ioo,
          ← lintegral_indicator hset]
        refine lintegral_congr fun t => ?_
        simp only [indicator_apply, mem_Iic, mem_ofPred_eq]
        split_ifs <;> simp_all [mul_comm]
    _ = ∫⁻ w in Ioi z, ENNReal.ofReal w⁻¹ * (Iic M).indicator
          (fun w => ENNReal.ofReal (Real.log ((1 - b₁) * (1 - b₂) * (b₁ * b₂) / w ^ 2))) w := by
        refine setLIntegral_congr_fun measurableSet_Ioi fun w hw => ?_
        rw [lintegral_quad_superlevel hb₁ hb₁' hb₂ hb₂' (hz.trans hw)]
    _ = ∫⁻ w in Icc z M, ENNReal.ofReal w⁻¹ *
          ENNReal.ofReal (Real.log ((1 - b₁) * (1 - b₂) * (b₁ * b₂) / w ^ 2)) := by
        have e : ∀ w : ℝ, ENNReal.ofReal w⁻¹ * (Iic M).indicator
            (fun w => ENNReal.ofReal (Real.log ((1 - b₁) * (1 - b₂) * (b₁ * b₂) / w ^ 2))) w =
            (Iic M).indicator (fun w => ENNReal.ofReal w⁻¹ *
              ENNReal.ofReal (Real.log ((1 - b₁) * (1 - b₂) * (b₁ * b₂) / w ^ 2))) w := by
          intro w; simp only [indicator_apply]; split_ifs <;> simp
        simp_rw [e]
        rw [lintegral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
          inter_comm, Ioi_inter_Iic, restrict_Ioc_eq_restrict_Icc]
    _ = _ := lintegral_log_div_sq hA hD hz hzM.le hM2

end Quadrant

section Assemble

theorem nbHi_mul_self {l t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    nbHi l t * (t * (1 - t)) = min ((1 - l) * t) (l * (1 - t)) := by
  have hc : 0 < t * (1 - t) := mul_pos ht.1 (sub_pos.mpr ht.2)
  have ht0 : t ≠ 0 := ht.1.ne'
  have ht1 : 1 - t ≠ 0 := (sub_pos.mpr ht.2).ne'
  rw [nbHi, min_mul_of_nonneg _ _ hc.le]
  congr 1 <;> field_simp

theorem nbLo_mul_self {l t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    nbLo l t * (t * (1 - t)) = min ((1 - (1 - l)) * t) ((1 - l) * (1 - t)) := by
  have hc : 0 < t * (1 - t) := mul_pos ht.1 (sub_pos.mpr ht.2)
  have ht0 : t ≠ 0 := ht.1.ne'
  have ht1 : 1 - t ≠ 0 := (sub_pos.mpr ht.2).ne'
  rw [nbLo, min_mul_of_nonneg _ _ hc.le, sub_sub_cancel]
  congr 1 <;> field_simp

/-- The rectangle density at the slice `t`, for `z > 0`, is the sum of the two quadrant terms. -/
theorem prodDensity_nb_pos {l₁ l₂ t z : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (hz : 0 < z) :
    prodDensity (nbLo l₁ t) (nbHi l₁ t) (nbLo l₂ t) (nbHi l₂ t) (z / (t * (1 - t))) =
      ENNReal.ofReal (max (Real.log (quadP l₁ l₂ t / (t * (1 - t)) / z)) 0) +
      ENNReal.ofReal (max (Real.log (quadP (1 - l₁) (1 - l₂) t / (t * (1 - t)) / z)) 0) := by
  have hc : 0 < t * (1 - t) := mul_pos ht.1 (sub_pos.mpr ht.2)
  have hw : 0 < z / (t * (1 - t)) := div_pos hz hc
  have e1 : nbHi l₁ t * nbHi l₂ t / (z / (t * (1 - t))) = quadP l₁ l₂ t / (t * (1 - t)) / z := by
    rw [quadP, ← nbHi_mul_self ht, ← nbHi_mul_self ht]
    field_simp
  have e2 : nbLo l₁ t * nbLo l₂ t / (z / (t * (1 - t))) =
      quadP (1 - l₁) (1 - l₂) t / (t * (1 - t)) / z := by
    rw [quadP, ← nbLo_mul_self ht, ← nbLo_mul_self ht]
    field_simp
  rw [prodDensity, if_pos hw, e1, e2]

/-- The rectangle density at the slice `t`, for `z < 0`, is the sum of the two mixed quadrant
terms at `−z`. -/
theorem prodDensity_nb_neg {l₁ l₂ t z : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (hz : z < 0) :
    prodDensity (nbLo l₁ t) (nbHi l₁ t) (nbLo l₂ t) (nbHi l₂ t) (z / (t * (1 - t))) =
      ENNReal.ofReal (max (Real.log (quadP l₁ (1 - l₂) t / (t * (1 - t)) / -z)) 0) +
      ENNReal.ofReal (max (Real.log (quadP (1 - l₁) l₂ t / (t * (1 - t)) / -z)) 0) := by
  have hc : 0 < t * (1 - t) := mul_pos ht.1 (sub_pos.mpr ht.2)
  have hw : z / (t * (1 - t)) < 0 := div_neg_of_neg_of_pos hz hc
  have e1 : nbHi l₁ t * nbLo l₂ t / -(z / (t * (1 - t))) =
      quadP l₁ (1 - l₂) t / (t * (1 - t)) / -z := by
    rw [quadP, ← nbHi_mul_self ht, ← nbLo_mul_self ht]
    field_simp
  have e2 : nbLo l₁ t * nbHi l₂ t / -(z / (t * (1 - t))) =
      quadP (1 - l₁) l₂ t / (t * (1 - t)) / -z := by
    rw [quadP, ← nbLo_mul_self ht, ← nbHi_mul_self ht]
    field_simp
  rw [prodDensity, if_neg (not_lt.mpr hw.le), if_pos hw, e1, e2]

theorem measurable_quadJ_integrand (b₁ b₂ z : ℝ) : Measurable fun t : ℝ =>
    ENNReal.ofReal (t * (1 - t))⁻¹ *
      ENNReal.ofReal (max (Real.log (quadP b₁ b₂ t / (t * (1 - t)) / z)) 0) :=
  (by fun_prop : Measurable fun t : ℝ => (t * (1 - t))⁻¹).ennreal_ofReal.mul
    ((Real.measurable_log.comp ((measurable_quadQ (b₁ := b₁) (b₂ := b₂)).div_const z)).max
      measurable_const).ennreal_ofReal

theorem nbFibreDensity_eq_quadJ_pos {l₁ l₂ z : ℝ} (hz : 0 < z) :
    nbFibreDensity l₁ l₂ z = quadJ l₁ l₂ z + quadJ (1 - l₁) (1 - l₂) z := by
  unfold nbFibreDensity quadJ
  rw [← lintegral_add_left (measurable_quadJ_integrand l₁ l₂ z)]
  refine setLIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
  rw [prodDensity_nb_pos ht hz, mul_add]

theorem nbFibreDensity_eq_quadJ_neg {l₁ l₂ z : ℝ} (hz : z < 0) :
    nbFibreDensity l₁ l₂ z = quadJ l₁ (1 - l₂) (-z) + quadJ (1 - l₁) l₂ (-z) := by
  unfold nbFibreDensity quadJ
  rw [← lintegral_add_left (measurable_quadJ_integrand l₁ (1 - l₂) (-z))]
  refine setLIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
  rw [prodDensity_nb_neg ht hz, mul_add]

/-- Nonnegativity of the closed form. -/
theorem closed_nonneg {V M z : ℝ} (hz : 0 < z) (hzM : z ≤ M) (hM : M ^ 2 ≤ V) :
    0 ≤ Real.log (M / z) * Real.log (V / (M * z)) := by
  have hM0 : 0 < M := hz.trans_le hzM
  refine mul_nonneg (Real.log_nonneg ((one_le_div hz).mpr hzM)) (Real.log_nonneg ?_)
  rw [le_div_iff₀ (mul_pos hM0 hz), one_mul]
  nlinarith

variable {l₁ l₂ : ℝ} (h₁ : 0 < l₁) (h₁' : l₁ < 1) (h₂ : 0 < l₂) (h₂' : l₂ < 1)
include h₁ h₁' h₂ h₂'

/-- ★★★ The exact fibre volume of the naive Bayes moment map, `μ > 0`: for
`0 < μ < M₊ = min(λ₁(1−λ₂), λ₂(1−λ₁))`,
`ρ(λ, μ) = 2 log(M₊/μ) · log(V/(M₊μ))`, `V = λ₁(1−λ₁)λ₂(1−λ₂)`. -/
theorem nbFibreDensity_closed_pos {z : ℝ} (hz : 0 < z)
    (hzM : z < min (l₁ * (1 - l₂)) (l₂ * (1 - l₁))) :
    nbFibreDensity l₁ l₂ z = ENNReal.ofReal (2 *
      (Real.log (min (l₁ * (1 - l₂)) (l₂ * (1 - l₁)) / z) *
        Real.log (l₁ * (1 - l₁) * (l₂ * (1 - l₂)) /
          (min (l₁ * (1 - l₂)) (l₂ * (1 - l₁)) * z)))) := by
  have eM : min ((1 - l₁) * (1 - (1 - l₂))) ((1 - l₂) * (1 - (1 - l₁))) =
      min (l₁ * (1 - l₂)) (l₂ * (1 - l₁)) := by
    rw [min_comm]; congr 1 <;> ring
  have eV : (1 - (1 - l₁)) * (1 - (1 - l₂)) * ((1 - l₁) * (1 - l₂)) =
      l₁ * (1 - l₁) * (l₂ * (1 - l₂)) := by ring
  have eV' : (1 - l₁) * (1 - l₂) * (l₁ * l₂) = l₁ * (1 - l₁) * (l₂ * (1 - l₂)) := by ring
  have hM2 : (min (l₁ * (1 - l₂)) (l₂ * (1 - l₁))) ^ 2 ≤ l₁ * (1 - l₁) * (l₂ * (1 - l₂)) := by
    have h1 := min_le_left (l₁ * (1 - l₂)) (l₂ * (1 - l₁))
    have h2 := min_le_right (l₁ * (1 - l₂)) (l₂ * (1 - l₁))
    have h0 : 0 ≤ min (l₁ * (1 - l₂)) (l₂ * (1 - l₁)) := le_min (by nlinarith) (by nlinarith)
    nlinarith [mul_le_mul h1 h2 h0 (by nlinarith)]
  rw [nbFibreDensity_eq_quadJ_pos hz, quadJ_eq h₁ h₁' h₂ h₂' hz hzM,
    quadJ_eq (sub_pos.mpr h₁') (sub_lt_self 1 h₁) (sub_pos.mpr h₂') (sub_lt_self 1 h₂) hz
      (by rw [eM]; exact hzM), eM, eV, eV',
    ← ENNReal.ofReal_add (closed_nonneg hz hzM.le hM2) (closed_nonneg hz hzM.le hM2)]
  congr 1; ring

/-- ★★★ The exact fibre volume, `μ < 0`: for `−M₋ < μ < 0`, `M₋ = min(λ₁λ₂, (1−λ₁)(1−λ₂))`,
`ρ(λ, μ) = 2 log(M₋/|μ|) · log(V/(M₋|μ|))`. -/
theorem nbFibreDensity_closed_neg {z : ℝ} (hz : z < 0)
    (hzM : -z < min (l₁ * l₂) ((1 - l₁) * (1 - l₂))) :
    nbFibreDensity l₁ l₂ z = ENNReal.ofReal (2 *
      (Real.log (min (l₁ * l₂) ((1 - l₁) * (1 - l₂)) / -z) *
        Real.log (l₁ * (1 - l₁) * (l₂ * (1 - l₂)) /
          (min (l₁ * l₂) ((1 - l₁) * (1 - l₂)) * -z)))) := by
  have hz' : 0 < -z := neg_pos.mpr hz
  have eM₁ : min (l₁ * (1 - (1 - l₂))) ((1 - l₂) * (1 - l₁)) =
      min (l₁ * l₂) ((1 - l₁) * (1 - l₂)) := by rw [sub_sub_cancel, mul_comm (1 - l₂) (1 - l₁)]
  have eM₂ : min ((1 - l₁) * (1 - l₂)) (l₂ * (1 - (1 - l₁))) =
      min (l₁ * l₂) ((1 - l₁) * (1 - l₂)) := by rw [min_comm, sub_sub_cancel, mul_comm l₂ l₁]
  have eV₁ : (1 - l₁) * (1 - (1 - l₂)) * (l₁ * (1 - l₂)) = l₁ * (1 - l₁) * (l₂ * (1 - l₂)) := by
    ring
  have eV₂ : (1 - (1 - l₁)) * (1 - l₂) * ((1 - l₁) * l₂) = l₁ * (1 - l₁) * (l₂ * (1 - l₂)) := by
    ring
  have hM2 : (min (l₁ * l₂) ((1 - l₁) * (1 - l₂))) ^ 2 ≤ l₁ * (1 - l₁) * (l₂ * (1 - l₂)) := by
    have h1 := min_le_left (l₁ * l₂) ((1 - l₁) * (1 - l₂))
    have h2 := min_le_right (l₁ * l₂) ((1 - l₁) * (1 - l₂))
    have h0 : 0 ≤ min (l₁ * l₂) ((1 - l₁) * (1 - l₂)) := le_min (by nlinarith) (by nlinarith)
    nlinarith [mul_le_mul h1 h2 h0 (by nlinarith)]
  rw [nbFibreDensity_eq_quadJ_neg hz,
    quadJ_eq h₁ h₁' (sub_pos.mpr h₂') (sub_lt_self 1 h₂) hz' (by rw [eM₁]; exact hzM),
    quadJ_eq (sub_pos.mpr h₁') (sub_lt_self 1 h₁) h₂ h₂' hz' (by rw [eM₂]; exact hzM),
    eM₁, eM₂, eV₁, eV₂,
    ← ENNReal.ofReal_add (closed_nonneg hz' hzM.le hM2) (closed_nonneg hz' hzM.le hM2)]
  congr 1; ring

end Assemble

end Grammar
