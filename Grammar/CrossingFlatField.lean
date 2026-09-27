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

/-- The first shifted logarithmic moment with a linear insertion,
`m₁⁽¹⁾(ξ) = ∫ z e^{−z²/2 + ξz} log|z| dz`. -/
noncomputable def logMomentShift₁ (ξ : ℝ) : ℝ :=
  ∫ z, z * (Real.exp (-z ^ 2 / 2 + ξ * z) * Real.log |z|)

/-- The even dominating function `(2|z|^{−1/2} + |z|) e^{−z²/4}` is integrable on `ℝ`. -/
theorem integrable_dominant :
    Integrable fun z : ℝ => (2 * |z| ^ (-(1 / 2 : ℝ)) + |z|) * Real.exp (-(1 / 4) * z ^ 2) := by
  set g : ℝ → ℝ := fun z => (2 * |z| ^ (-(1 / 2 : ℝ)) + |z|) * Real.exp (-(1 / 4) * z ^ 2)
    with hgdef
  have hgeven : ∀ z, g (-z) = g z := by intro z; simp only [hgdef, abs_neg, neg_sq]
  have hpos : IntegrableOn g (Ioi 0) := by
    have h1 := (integrable_rpow_mul_exp_neg_mul_sq (b := 1 / 4) (by norm_num)
      (s := -(1 / 2)) (by norm_num)).integrableOn (s := Ioi (0 : ℝ))
    have h2 := (integrable_rpow_mul_exp_neg_mul_sq (b := 1 / 4) (by norm_num) (s := 1)
      (by norm_num)).integrableOn (s := Ioi (0 : ℝ))
    refine IntegrableOn.congr_fun ((h1.const_mul 2).add h2) (fun z hz => ?_) measurableSet_Ioi
    simp only [hgdef, Pi.add_apply, Real.rpow_one, abs_of_pos (mem_Ioi.mp hz)]
    ring
  have hneg : IntegrableOn g (Iio 0) := by
    have := hpos.comp_neg
    rw [Set.neg_Ioi, neg_zero] at this
    exact this.congr_fun (fun z _ => hgeven z) measurableSet_Iio
  rw [← integrableOn_univ, ← Iio_union_Ici, integrableOn_union]
  refine ⟨hneg, ?_⟩
  rw [IntegrableOn, Measure.restrict_congr_set Ioi_ae_eq_Ici.symm]
  exact hpos

/-- `z e^{−z²/2 + ξz} log|z|` is integrable on `ℝ`. -/
theorem integrable_mul_exp_quadratic_log (ξ : ℝ) :
    Integrable fun z : ℝ => z * (Real.exp (-z ^ 2 / 2 + ξ * z) * Real.log |z|) := by
  refine (integrable_dominant.const_mul (Real.exp (2 * ξ ^ 2 + 1))).mono' ?_
    (Filter.Eventually.of_forall fun z => ?_)
  · exact (by fun_prop : Measurable fun z : ℝ =>
      z * (Real.exp (-z ^ 2 / 2 + ξ * z) * Real.log |z|)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
    rcases eq_or_ne z 0 with rfl | hz
    · simp
    · have hlog := abs_log_le_rpow |z| (abs_pos.mpr hz)
      have hexp : |z| * Real.exp (-z ^ 2 / 2 + ξ * z) ≤
          Real.exp (2 * ξ ^ 2 + 1) * Real.exp (-(1 / 4) * z ^ 2) := by
        rw [← Real.exp_add]
        have h1 : |z| ≤ Real.exp (z ^ 2 / 8 + 1) := by
          have h2 : |z| ≤ z ^ 2 / 8 + 2 := by
            nlinarith [abs_nonneg z, sq_abs z, sq_nonneg (abs z - 4)]
          have h3 := Real.add_one_le_exp (z ^ 2 / 8 + 1)
          linarith
        calc |z| * Real.exp (-z ^ 2 / 2 + ξ * z)
            ≤ Real.exp (z ^ 2 / 8 + 1) * Real.exp (-z ^ 2 / 2 + ξ * z) :=
              mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
          _ = Real.exp (z ^ 2 / 8 + 1 + (-z ^ 2 / 2 + ξ * z)) := by rw [← Real.exp_add]
          _ ≤ Real.exp (2 * ξ ^ 2 + 1 + -(1 / 4) * z ^ 2) :=
              Real.exp_le_exp.mpr (by nlinarith [sq_nonneg (z - 4 * ξ)])
      calc |z| * (Real.exp (-z ^ 2 / 2 + ξ * z) * abs (Real.log |z|))
          = (|z| * Real.exp (-z ^ 2 / 2 + ξ * z)) * abs (Real.log |z|) := by ring
        _ ≤ (Real.exp (2 * ξ ^ 2 + 1) * Real.exp (-(1 / 4) * z ^ 2)) *
              (2 * |z| ^ (-(1 / 2 : ℝ)) + |z|) :=
            mul_le_mul hexp hlog (abs_nonneg _) (by positivity)
        _ = Real.exp (2 * ξ ^ 2 + 1) * ((2 * |z| ^ (-(1 / 2 : ℝ)) + |z|) *
              Real.exp (-(1 / 4) * z ^ 2)) := by ring

/-- `∫ z e^{−z²/2 + ξz} dz = √(2π) ξ e^{ξ²/2}` (shift `z = u + ξ` and oddness). -/
theorem integral_mul_exp_quadratic_half (ξ : ℝ) :
    ∫ z : ℝ, z * Real.exp (-z ^ 2 / 2 + ξ * z) =
      Real.sqrt (2 * Real.pi) * ξ * Real.exp (ξ ^ 2 / 2) := by
  have hshift := integral_add_right_eq_self (μ := volume)
    (fun z : ℝ => z * Real.exp (-z ^ 2 / 2 + ξ * z)) ξ
  rw [← hshift]
  have e : (fun u : ℝ => (u + ξ) * Real.exp (-(u + ξ) ^ 2 / 2 + ξ * (u + ξ))) =
      fun u => Real.exp (ξ ^ 2 / 2) * (u * Real.exp (-u ^ 2 / 2)) +
        Real.exp (ξ ^ 2 / 2) * ξ * Real.exp (-u ^ 2 / 2) := by
    funext u
    rw [show -(u + ξ) ^ 2 / 2 + ξ * (u + ξ) = ξ ^ 2 / 2 + -u ^ 2 / 2 by ring, Real.exp_add]
    ring
  have hodd : ∫ u : ℝ, u * Real.exp (-u ^ 2 / 2) = 0 := by
    have h := integral_neg_eq_self (fun u : ℝ => u * Real.exp (-u ^ 2 / 2)) volume
    simp only [neg_sq, neg_mul] at h
    rw [integral_neg] at h
    linarith
  have hg : ∫ u : ℝ, Real.exp (-u ^ 2 / 2) = Real.sqrt (2 * Real.pi) := by
    have := integral_gaussian (1 / 2 : ℝ)
    rw [show (fun u : ℝ => Real.exp (-u ^ 2 / 2)) = fun u => Real.exp (-(1 / 2) * u ^ 2) by
      funext u; ring_nf, this]
    congr 1; ring
  have hint1 : Integrable fun u : ℝ => u * Real.exp (-u ^ 2 / 2) := by
    have := integrable_rpow_mul_exp_neg_mul_sq (b := 1 / 2) (by norm_num) (s := 1) (by norm_num)
    refine this.congr (Filter.Eventually.of_forall fun u => ?_)
    simp only [Real.rpow_one]; ring_nf
  have hint2 : Integrable fun u : ℝ => Real.exp (-u ^ 2 / 2) := by
    have := integrable_exp_neg_mul_sq (b := 1 / 2) (by norm_num)
    refine this.congr (Filter.Eventually.of_forall fun u => ?_)
    simp only; ring_nf
  rw [e, integral_add (hint1.const_mul _) (hint2.const_mul _), integral_const_mul,
    integral_const_mul, hodd, hg]
  ring

/-- The signed reduction: for an integrable insertion `f(w₁w₂)` on the square. -/
theorem integral_crossing_flat {f : ℝ → ℝ} (hf : Measurable f)
    (hint : IntegrableOn (fun t => f t * (2 * Real.log (1 / |t|))) (Ioo (-1 : ℝ) 1)) :
    ∫ w in Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1, f (w.1 * w.2) =
      ∫ t in Ioo (-1 : ℝ) 1, f t * (2 * Real.log (1 / |t|)) := by
  have hnn : ∀ t ∈ Ioo (-1 : ℝ) 1, 0 ≤ 2 * Real.log (1 / |t|) := by
    intro t ht
    refine mul_nonneg zero_le_two ?_
    rcases eq_or_ne t 0 with rfl | h0
    · simp
    · refine Real.log_nonneg ((le_one_div one_pos (abs_pos.mpr h0)).mpr ?_)
      rw [one_div_one]
      exact (abs_lt.mpr ht).le
  -- the two lintegral identities for the positive and negative parts
  have hpos := lintegral_crossing_flat (Ψ := fun t => ENNReal.ofReal (f t)) hf.ennreal_ofReal
  have hneg := lintegral_crossing_flat (Ψ := fun t => ENNReal.ofReal (-f t))
    hf.neg.ennreal_ofReal
  have habs := lintegral_crossing_flat (Ψ := fun t => ENNReal.ofReal |f t|)
    hf.abs.ennreal_ofReal
  have hbox : IntegrableOn (fun w : ℝ × ℝ => f (w.1 * w.2)) (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1) := by
    refine ⟨(hf.comp (by fun_prop)).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    have e1 : ∫⁻ w in Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1, ‖f (w.1 * w.2)‖ₑ =
        ∫⁻ w in Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1, ENNReal.ofReal |f (w.1 * w.2)| :=
      lintegral_congr fun w => by rw [Real.enorm_eq_ofReal_abs]
    rw [e1, habs]
    have e2 : ∫⁻ t in Ioo (-1 : ℝ) 1,
      ENNReal.ofReal |f t| * ENNReal.ofReal (2 * Real.log (1 / |t|)) =
        ∫⁻ t in Ioo (-1 : ℝ) 1, ‖f t * (2 * Real.log (1 / |t|))‖ₑ :=
      setLIntegral_congr_fun measurableSet_Ioo fun t ht => by
        rw [Real.enorm_eq_ofReal_abs, abs_mul, abs_of_nonneg (hnn t ht),
          ENNReal.ofReal_mul (abs_nonneg _)]
    rw [e2]
    exact hint.2
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hbox,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hint]
  congr 2
  · rw [hpos]
    refine setLIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
    rw [ENNReal.ofReal_mul' (hnn t ht)]
  · rw [hneg]
    refine setLIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
    rw [← neg_mul, ENNReal.ofReal_mul' (hnn t ht)]

/-- `z e^{−z²/2 + ξz}` is integrable on `ℝ` (shift of `(u + ξ) e^{−u²/2}`). -/
theorem integrable_mul_exp_quadratic' (ξ : ℝ) :
    Integrable fun z : ℝ => z * Real.exp (-z ^ 2 / 2 + ξ * z) := by
  have hint1 : Integrable fun u : ℝ => u * Real.exp (-u ^ 2 / 2) := by
    have := integrable_rpow_mul_exp_neg_mul_sq (b := 1 / 2) (by norm_num) (s := 1) (by norm_num)
    refine this.congr (Filter.Eventually.of_forall fun u => ?_)
    simp only [Real.rpow_one]; ring_nf
  have hint2 : Integrable fun u : ℝ => Real.exp (-u ^ 2 / 2) := by
    have := integrable_exp_neg_mul_sq (b := 1 / 2) (by norm_num)
    refine this.congr (Filter.Eventually.of_forall fun u => ?_)
    simp only; ring_nf
  have hf : Integrable fun u : ℝ =>
      Real.exp (ξ ^ 2 / 2) * (u * Real.exp (-u ^ 2 / 2)) + Real.exp (ξ ^ 2 / 2) * ξ *
        Real.exp (-u ^ 2 / 2) :=
    (hint1.const_mul _).add (hint2.const_mul _)
  refine (hf.comp_add_right (-ξ)).congr (Filter.Eventually.of_forall fun z => ?_)
  simp only
  rw [show -(z + -ξ) ^ 2 / 2 = (-z ^ 2 / 2 + ξ * z) - ξ ^ 2 / 2 by ring, Real.exp_sub]
  field_simp
  ring

/-- The polar-distribution integrand `e^{−Nt²/2 + √N ξ t}·2 log(1/|t|)` is integrable on `(−1,1)`
(read off from the finiteness of the box integral). -/
theorem integrableOn_crossing_field_density (N ξ : ℝ) :
    IntegrableOn (fun t : ℝ =>
      Real.exp (-N * t ^ 2 / 2 + Real.sqrt N * ξ * t) * (2 * Real.log (1 / |t|))) (Ioo (-1) 1) := by
  set h : ℝ → ℝ := fun t =>
    Real.exp (-N * t ^ 2 / 2 + Real.sqrt N * ξ * t) * (2 * Real.log (1 / |t|)) with hh
  have hl := lintegral_crossing_flat_field N ξ (f := fun _ => (1 : ℝ)) measurable_const
  simp only [one_mul] at hl
  have hbox : IntegrableOn (fun w : ℝ × ℝ =>
      Real.exp (-N * (w.1 * w.2) ^ 2 / 2 + Real.sqrt N * ξ * (w.1 * w.2)))
      (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1) :=
    (by fun_prop : Continuous fun w : ℝ × ℝ =>
      Real.exp (-N * (w.1 * w.2) ^ 2 / 2 + Real.sqrt N * ξ * (w.1 * w.2))).continuousOn
      |>.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
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
  refine ⟨hhm.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have : ∫⁻ t in Ioo (-1 : ℝ) 1, ‖h t‖ₑ = ∫⁻ t in Ioo (-1 : ℝ) 1, ENNReal.ofReal (h t) :=
    lintegral_congr_ae ((ae_restrict_of_forall_mem measurableSet_Ioo hhnn).mono
      fun t ht => Real.enorm_eq_ofReal ht)
  rw [this, ← hl, ← ofReal_integral_eq_lintegral_ofReal hbox
    (ae_of_all _ fun w => (Real.exp_pos _).le)]
  exact ENNReal.ofReal_lt_top

/-- ★★ **The output observable under the frozen field**: the posterior numerator of `w₁w₂` is
`N^{−1}[√(2π) ξ e^{ξ²/2} log N − 2 m₁⁽¹⁾(ξ) − tail]`, so that
`E[w₁w₂ | ξ] → ξ/√N` with a `1/log N` relative correction. -/
theorem crossing_flat_field_mean {N : ℝ} (hN : 0 < N) (ξ : ℝ) :
    ∫ w in Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1,
        (w.1 * w.2) * Real.exp (-N * (w.1 * w.2) ^ 2 / 2 + Real.sqrt N * ξ * (w.1 * w.2)) =
      N⁻¹ * (Real.sqrt (2 * Real.pi) * ξ * Real.exp (ξ ^ 2 / 2) * Real.log N -
        2 * logMomentShift₁ ξ -
        ∫ z in (Ioc (-Real.sqrt N) (Real.sqrt N))ᶜ,
          z * (Real.exp (-z ^ 2 / 2 + ξ * z) * (Real.log N - 2 * Real.log |z|))) := by
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN
  have hsq : Real.sqrt N ^ 2 = N := Real.sq_sqrt hN.le
  have hae : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ 0 := by rw [ae_iff]; simp
  set H₁ : ℝ → ℝ := fun z =>
    z * (Real.exp (-z ^ 2 / 2 + ξ * z) * (Real.log N - 2 * Real.log |z|)) with hH₁
  set h : ℝ → ℝ := fun t =>
    Real.exp (-N * t ^ 2 / 2 + Real.sqrt N * ξ * t) * (2 * Real.log (1 / |t|)) with hh
  have hH₁int : Integrable H₁ := by
    have := ((integrable_mul_exp_quadratic' ξ).const_mul (Real.log N)).sub
      ((integrable_mul_exp_quadratic_log ξ).const_mul 2)
    refine this.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only [hH₁, Pi.sub_apply]; ring
  -- C1: the signed reduction with the insertion `f(t) = t e^{…}`
  have hred : ∫ w in Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1,
      (w.1 * w.2) * Real.exp (-N * (w.1 * w.2) ^ 2 / 2 + Real.sqrt N * ξ * (w.1 * w.2)) =
      ∫ t in Ioo (-1 : ℝ) 1, t * h t := by
    have hint : IntegrableOn (fun t : ℝ =>
        (t * Real.exp (-N * t ^ 2 / 2 + Real.sqrt N * ξ * t)) * (2 * Real.log (1 / |t|)))
        (Ioo (-1) 1) := by
      refine (integrableOn_crossing_field_density N ξ).mono' ?_ ?_
      · exact (by fun_prop : Measurable fun t : ℝ =>
          (t * Real.exp (-N * t ^ 2 / 2 + Real.sqrt N * ξ * t)) *
            (2 * Real.log (1 / |t|))).aestronglyMeasurable
      · refine ae_restrict_of_forall_mem measurableSet_Ioo fun t ht => ?_
        have hnn : 0 ≤ 2 * Real.log (1 / |t|) := by
          refine mul_nonneg zero_le_two ?_
          rcases eq_or_ne t 0 with rfl | h0
          · simp
          · refine Real.log_nonneg ((le_one_div one_pos (abs_pos.mpr h0)).mpr ?_)
            rw [one_div_one]
            exact (abs_lt.mpr ht).le
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_nonneg hnn]
        have : |t| ≤ 1 := (abs_lt.mpr ht).le
        have := Real.exp_pos (-N * t ^ 2 / 2 + Real.sqrt N * ξ * t)
        nlinarith [mul_nonneg this.le hnn]
    rw [integral_crossing_flat (f := fun t => t * Real.exp (-N * t ^ 2 / 2 + Real.sqrt N * ξ * t))
      (by fun_prop) hint]
    refine setIntegral_congr_fun measurableSet_Ioo fun t _ => ?_
    simp only [hh]; ring
  -- C2: scaling `t = z/√N`: `t h t = (√N)⁻¹ H₁(√N t)` off `t = 0`
  have hscale : ∫ t in Ioo (-1 : ℝ) 1, t * h t =
      (Real.sqrt N)⁻¹ * ((Real.sqrt N)⁻¹ * ∫ z in Ioc (-Real.sqrt N) (Real.sqrt N), H₁ z) := by
    have e : ∀ t ≠ (0 : ℝ), t * h t = (Real.sqrt N)⁻¹ * H₁ (Real.sqrt N * t) := by
      intro t ht
      simp only [hh, hH₁]
      rw [mul_pow, hsq, abs_mul, abs_of_pos hsN, Real.log_mul hsN.ne' (abs_ne_zero.mpr ht),
        Real.log_sqrt hN.le, one_div, Real.log_inv]
      field_simp
      ring
    have hae' : (fun t => t * h t) =ᵐ[volume.restrict (Ioo (-1 : ℝ) 1)]
        fun t => (Real.sqrt N)⁻¹ * H₁ (Real.sqrt N * t) :=
      (ae_restrict_of_ae hae).mono fun t ht => e t ht
    rw [integral_congr_ae hae', integral_const_mul, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by norm_num), intervalIntegral.integral_comp_mul_left
        (fun z => H₁ z) hsN.ne', smul_eq_mul, intervalIntegral.integral_of_le (by linarith),
      mul_neg, mul_one]
  -- C3: the full-line integral of `H₁`
  have hfull : ∫ z, H₁ z = Real.sqrt (2 * Real.pi) * ξ * Real.exp (ξ ^ 2 / 2) * Real.log N -
      2 * logMomentShift₁ ξ := by
    have e : (fun z => H₁ z) = fun z => Real.log N * (z * Real.exp (-z ^ 2 / 2 + ξ * z)) -
        2 * (z * (Real.exp (-z ^ 2 / 2 + ξ * z) * Real.log |z|)) := by
      funext z; simp only [hH₁]; ring
    rw [e, integral_sub ((integrable_mul_exp_quadratic' ξ).const_mul _)
      ((integrable_mul_exp_quadratic_log ξ).const_mul 2), integral_const_mul, integral_const_mul,
      integral_mul_exp_quadratic_half, logMomentShift₁]
    ring
  have hsplit : ∫ z in Ioc (-Real.sqrt N) (Real.sqrt N), H₁ z =
      (∫ z, H₁ z) - ∫ z in (Ioc (-Real.sqrt N) (Real.sqrt N))ᶜ, H₁ z := by
    rw [← integral_add_compl measurableSet_Ioc hH₁int]; ring
  rw [hred, hscale, hsplit, hfull, ← mul_assoc, ← mul_inv, Real.mul_self_sqrt hN.le]

end Grammar
