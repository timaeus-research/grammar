/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.CrossingFlatAllOrders
import Grammar.RankOneGauss

/-!
# The depth-two deep linear network with flat prior and a frozen field

For `K_N = (w₁w₂)²/2 − N^{−1/2} ξ w₁w₂` on `[−1, 1]²` (the regression with zero target and a
constant field `ξ`), the frozen partition function is

  `Z_N[1; ξ] = N^{−1/2} [ √(2π) e^{ξ²/2} log N − 2 m₁(ξ) ] − N^{−1/2} R_N(ξ)`,

with the shifted logarithmic moment `m₁(ξ) = ∫_ℝ e^{−z²/2 + ξz} log|z| dz` and the tail
`R_N(ξ) = ∫_{|z| ≥ √N} e^{−z²/2 + ξz} (log N − 2 log|z|) dz` (★★★ `crossing_flat_field`):
the tilt `e^{ξ²/2}` multiplies the leading logarithm, and the field first enters the constant
term through the fluctuation function `m₁` (examples_slop §2, eq. (dln_frozen)).
Zero `sorry`/`axiom`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Grammar

/-- The shifted logarithmic moment `m₁(ξ) = ∫ e^{−z²/2 + ξz} log|z| dz`. -/
noncomputable def logMomentShift (ξ : ℝ) : ℝ := ∫ z, Real.exp (-z ^ 2 / 2 + ξ * z) * Real.log |z|

/-- `e^{−z²/2 + ξz} log|z|` is integrable on `ℝ`. -/
theorem integrable_exp_quadratic_log (ξ : ℝ) :
    Integrable fun z : ℝ => Real.exp (-z ^ 2 / 2 + ξ * z) * Real.log |z| := by
  -- dominate by `e^{ξ²} (2|z|^{−1/2} + |z|) e^{−z²/4}`
  set g : ℝ → ℝ := fun z => (2 * |z| ^ (-(1 / 2 : ℝ)) + |z|) * Real.exp (-(1 / 4) * z ^ 2) with hg
  have hgeven : ∀ z, g (-z) = g z := by intro z; simp only [hg, abs_neg, neg_sq]
  have hpos : IntegrableOn g (Ioi 0) := by
    have h1 := (integrable_rpow_mul_exp_neg_mul_sq (b := 1 / 4) (by norm_num)
      (s := -(1 / 2)) (by norm_num)).integrableOn (s := Ioi (0 : ℝ))
    have h2 := (integrable_rpow_mul_exp_neg_mul_sq (b := 1 / 4) (by norm_num) (s := 1)
      (by norm_num)).integrableOn (s := Ioi (0 : ℝ))
    refine IntegrableOn.congr_fun ((h1.const_mul 2).add h2) (fun z hz => ?_) measurableSet_Ioi
    simp only [hg, Pi.add_apply, Real.rpow_one, abs_of_pos (mem_Ioi.mp hz)]
    ring
  have hneg : IntegrableOn g (Iio 0) := by
    have := hpos.comp_neg
    rw [Set.neg_Ioi, neg_zero] at this
    exact this.congr_fun (fun z _ => hgeven z) measurableSet_Iio
  have hgI : Integrable g := by
    rw [← integrableOn_univ, ← Iio_union_Ici, integrableOn_union]
    refine ⟨hneg, ?_⟩
    rw [IntegrableOn, Measure.restrict_congr_set Ioi_ae_eq_Ici.symm]
    exact hpos
  refine (hgI.const_mul (Real.exp (ξ ^ 2))).mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
  · exact (by fun_prop : Measurable fun z : ℝ =>
      Real.exp (-z ^ 2 / 2 + ξ * z) * Real.log |z|).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    rcases eq_or_ne z 0 with rfl | hz
    · simp [hg]
    · have hlog := abs_log_le_rpow |z| (abs_pos.mpr hz)
      have hexp : Real.exp (-z ^ 2 / 2 + ξ * z) ≤
          Real.exp (ξ ^ 2) * Real.exp (-(1 / 4) * z ^ 2) := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr (by nlinarith [sq_nonneg (z / 2 - ξ)])
      calc Real.exp (-z ^ 2 / 2 + ξ * z) * abs (Real.log |z|)
          ≤ (Real.exp (ξ ^ 2) * Real.exp (-(1 / 4) * z ^ 2)) *
              (2 * |z| ^ (-(1 / 2 : ℝ)) + |z|) :=
            mul_le_mul hexp hlog (abs_nonneg _) (by positivity)
        _ = Real.exp (ξ ^ 2) * g z := by simp only [hg]; ring

/-- `e^{−z²/2 + ξz}` is integrable on `ℝ`. -/
theorem integrable_exp_quadratic' (ξ : ℝ) :
    Integrable fun z : ℝ => Real.exp (-z ^ 2 / 2 + ξ * z) := by
  have hb : 0 < (((1 / 2 : ℝ) : ℂ)).re := by rw [Complex.ofReal_re]; norm_num
  have h := (integrable_cexp_quadratic hb ((ξ : ℝ) : ℂ) 0).norm
  refine h.congr (Filter.Eventually.of_forall fun z => ?_)
  simp only
  rw [Complex.norm_exp]
  have : -(((1 / 2 : ℝ) : ℂ)) * (z : ℂ) ^ 2 + ((ξ : ℝ) : ℂ) * (z : ℂ) + 0 =
      ((-z ^ 2 / 2 + ξ * z : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.ofReal_re]

/-- The Gaussian with a linear term: `∫ e^{−z²/2 + ξz} dz = √(2π) e^{ξ²/2}`. -/
theorem integral_exp_quadratic_half (ξ : ℝ) :
    ∫ z : ℝ, Real.exp (-z ^ 2 / 2 + ξ * z) = Real.sqrt (2 * Real.pi) * Real.exp (ξ ^ 2 / 2) := by
  have h := integral_exp_quadratic_real (α := 1 / 2) (by norm_num) ξ 0
  have e : (fun y : ℝ => Real.exp (-(1 / 2) * y ^ 2 + ξ * y - 0)) =
      fun z => Real.exp (-z ^ 2 / 2 + ξ * z) := by funext y; ring_nf
  rw [e] at h
  rw [h, show Real.pi / (1 / 2) = 2 * Real.pi by ring,
    show ξ ^ 2 / (4 * (1 / 2)) - 0 = ξ ^ 2 / 2 by ring]

/-- ★★★ **The depth-two deep linear network with flat prior and a frozen field**: for `N > 0`,
`∫_{[−1,1]²} e^{−N(w₁w₂)²/2 + √N ξ w₁w₂} dw
  = N^{−1/2}[√(2π) e^{ξ²/2} log N − 2 m₁(ξ) − ∫_{|z| ≥ √N} e^{−z²/2 + ξz}(log N − 2 log|z|) dz]`. -/
theorem crossing_flat_field {N : ℝ} (hN : 0 < N) (ξ : ℝ) :
    ∫ w in Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1,
        Real.exp (-N * (w.1 * w.2) ^ 2 / 2 + Real.sqrt N * ξ * (w.1 * w.2)) =
      (Real.sqrt N)⁻¹ * (Real.sqrt (2 * Real.pi) * Real.exp (ξ ^ 2 / 2) * Real.log N -
        2 * logMomentShift ξ -
        ∫ z in (Ioc (-Real.sqrt N) (Real.sqrt N))ᶜ,
          Real.exp (-z ^ 2 / 2 + ξ * z) * (Real.log N - 2 * Real.log |z|)) := by
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN
  have hsq : Real.sqrt N ^ 2 = N := Real.sq_sqrt hN.le
  have hae : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ 0 := by rw [ae_iff]; simp
  set H : ℝ → ℝ := fun z => Real.exp (-z ^ 2 / 2 + ξ * z) * (Real.log N - 2 * Real.log |z|) with hH
  set h : ℝ → ℝ := fun t =>
    Real.exp (-N * t ^ 2 / 2 + Real.sqrt N * ξ * t) * (2 * Real.log (1 / |t|)) with hh
  have hHint : Integrable H := by
    have := ((integrable_exp_quadratic' ξ).const_mul (Real.log N)).sub
      ((integrable_exp_quadratic_log ξ).const_mul 2)
    refine this.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only [hH, Pi.sub_apply]; ring
  -- C1: reduction to the polar distribution (Bochner form)
  have hl := lintegral_crossing_flat_field N ξ (f := fun _ => (1 : ℝ)) measurable_const
  simp only [one_mul] at hl
  have hbox : IntegrableOn (fun w : ℝ × ℝ =>
      Real.exp (-N * (w.1 * w.2) ^ 2 / 2 + Real.sqrt N * ξ * (w.1 * w.2)))
      (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1) :=
    (by fun_prop : Continuous fun w : ℝ × ℝ =>
      Real.exp (-N * (w.1 * w.2) ^ 2 / 2 + Real.sqrt N * ξ * (w.1 * w.2))).continuousOn
      |>.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hboxnn : 0 ≤ᵐ[volume.restrict (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)] fun w : ℝ × ℝ =>
      Real.exp (-N * (w.1 * w.2) ^ 2 / 2 + Real.sqrt N * ξ * (w.1 * w.2)) :=
    ae_of_all _ fun w => (Real.exp_pos _).le
  have hhnn : ∀ t ∈ Ioo (-1 : ℝ) 1, 0 ≤ h t := by
    intro t ht
    refine mul_nonneg (Real.exp_pos _).le (mul_nonneg zero_le_two ?_)
    rcases eq_or_ne t 0 with rfl | h0
    · simp
    · refine Real.log_nonneg ((le_one_div one_pos (abs_pos.mpr h0)).mpr ?_)
      rw [one_div_one]
      exact (abs_lt.mpr ht).le
  have hhm : Measurable h := by rw [hh]; fun_prop
  have hR : ∫⁻ t in Ioo (-1 : ℝ) 1,
      ENNReal.ofReal (Real.exp (-N * t ^ 2 / 2 + Real.sqrt N * ξ * t)) *
        ENNReal.ofReal (2 * Real.log (1 / |t|)) = ∫⁻ t in Ioo (-1 : ℝ) 1, ENNReal.ofReal (h t) :=
    setLIntegral_congr_fun measurableSet_Ioo fun t _ => by
      rw [hh, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  rw [hR] at hl
  have hhIo : IntegrableOn h (Ioo (-1 : ℝ) 1) := by
    refine ⟨hhm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    have : ∫⁻ t in Ioo (-1 : ℝ) 1, ‖h t‖ₑ = ∫⁻ t in Ioo (-1 : ℝ) 1, ENNReal.ofReal (h t) :=
      lintegral_congr_ae ((ae_restrict_of_forall_mem measurableSet_Ioo hhnn).mono
        fun t ht => Real.enorm_eq_ofReal ht)
    rw [this, ← hl, ← ofReal_integral_eq_lintegral_ofReal hbox hboxnn]
    exact ENNReal.ofReal_lt_top
  have hred : ∫ w in Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1,
      Real.exp (-N * (w.1 * w.2) ^ 2 / 2 + Real.sqrt N * ξ * (w.1 * w.2)) =
      ∫ t in Ioo (-1 : ℝ) 1, h t := by
    rw [← ENNReal.ofReal_eq_ofReal_iff (integral_nonneg_of_ae hboxnn)
      (setIntegral_nonneg measurableSet_Ioo hhnn), ofReal_integral_eq_lintegral_ofReal hbox hboxnn,
      ofReal_integral_eq_lintegral_ofReal hhIo (ae_restrict_of_forall_mem measurableSet_Ioo hhnn),
      hl]
  -- C2: scaling `t = z/√N`: `h t = H (√N t)` off `t = 0`
  have hscale : ∫ t in Ioo (-1 : ℝ) 1, h t =
      (Real.sqrt N)⁻¹ * ∫ z in Ioc (-Real.sqrt N) (Real.sqrt N), H z := by
    have e : ∀ t ≠ (0 : ℝ), h t = H (Real.sqrt N * t) := by
      intro t ht
      simp only [hh, hH]
      rw [mul_pow, hsq, abs_mul, abs_of_pos hsN, Real.log_mul hsN.ne' (abs_ne_zero.mpr ht),
        Real.log_sqrt hN.le, one_div, Real.log_inv]
      ring_nf
    have hae' : (fun t => h t) =ᵐ[volume.restrict (Ioo (-1 : ℝ) 1)] fun t => H (Real.sqrt N * t) :=
      (ae_restrict_of_ae hae).mono fun t ht => e t ht
    rw [integral_congr_ae hae', ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by norm_num), intervalIntegral.integral_comp_mul_left
        (fun z => H z) hsN.ne', smul_eq_mul, intervalIntegral.integral_of_le (by linarith),
      mul_neg, mul_one]
  -- C3: the full-line integral of `H`
  have hfull : ∫ z, H z = Real.sqrt (2 * Real.pi) * Real.exp (ξ ^ 2 / 2) * Real.log N -
      2 * logMomentShift ξ := by
    have e : (fun z => H z) = fun z => Real.log N * Real.exp (-z ^ 2 / 2 + ξ * z) -
        2 * (Real.exp (-z ^ 2 / 2 + ξ * z) * Real.log |z|) := by
      funext z; simp only [hH]; ring
    rw [e, integral_sub ((integrable_exp_quadratic' ξ).const_mul _)
      ((integrable_exp_quadratic_log ξ).const_mul 2), integral_const_mul, integral_const_mul,
      integral_exp_quadratic_half, logMomentShift]
    ring
  have hsplit : ∫ z in Ioc (-Real.sqrt N) (Real.sqrt N), H z =
      (∫ z, H z) - ∫ z in (Ioc (-Real.sqrt N) (Real.sqrt N))ᶜ, H z := by
    rw [← integral_add_compl measurableSet_Ioc hHint]; ring
  rw [hred, hscale, hsplit, hfull]

end Grammar
