/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.BlowUpPolar

/-!
# The blow-up zeta function in closed form: `ζ(w) = 2^{3w+1} Γ(w + ½)²`

`lintegral_blowK_gauss` factorised the zeta function of the blow-up example `K = x²(x² + y²)/2`
against the Gaussian prior into a radial Gamma integral and the angular integral
`∫_{−π}^{π} |cos θ|^{2w} dθ`.  Here the angular integral is evaluated by the Gaussian trick: the
integral `∫_{ℝ²} |x|^{2w} e^{−|z|²/2} dz` is a product of one-dimensional Gamma integrals in
Cartesian coordinates and a radial Gamma integral times the angular integral in polar
coordinates, so

  `∫_{−π}^{π} |cos θ|^{2w} dθ = 2√π Γ(w + ½)/Γ(w + 1)`   (★★ `lintegral_abs_cos_rpow`),

and with Legendre's duplication formula (`Real.Gamma_mul_Gamma_add_half`)

  `∫_{ℝ²} K^w e^{−|z|²/2} dz = 2^{3w+1} Γ(w + ½)²`   (★★★ `lintegral_blowK_gauss_closed`),

for `w > −1/2`: the double poles of `Γ(w + ½)²` at the negative half-integers are the tied walls
of the blow-up (examples_slop §3).  Zero `sorry`/`axiom`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Grammar

/-- The radial Gamma integral `∫_0^∞ r^{2w+1} e^{−r²/2} dr = 2^w Γ(w + 1)` for `w > −1`. -/
theorem integral_radial_gamma' {w : ℝ} (hw : -1 < w) :
    ∫ r in Ioi (0 : ℝ), r ^ (2 * w + 1) * Real.exp (-r ^ 2 / 2) =
      (2 : ℝ) ^ w * Real.Gamma (w + 1) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 2 * w + 1) (b := 1 / 2) two_pos
    (by linarith) (by norm_num)
  have hfun : (fun r : ℝ => r ^ (2 * w + 1) * Real.exp (-r ^ 2 / 2)) =
      fun r => r ^ (2 * w + 1) * Real.exp (-(1 / 2) * r ^ (2 : ℝ)) := by
    funext r
    rw [Real.rpow_two]
    ring_nf
  rw [hfun, h, show (2 * w + 1 + 1) / 2 = w + 1 by ring]
  have h2 : ((1 / 2 : ℝ) ^ (-(2 * w + 1 + 1) / 2)) = (2 : ℝ) ^ (w + 1) := by
    rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.inv_rpow (by norm_num),
      ← Real.rpow_neg (by norm_num)]
    congr 1
    ring
  rw [h2, Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
  ring

/-- The half-line Gamma integral `∫_0^∞ x^{2w} e^{−x²/2} dx = 2^{w−½} Γ(w + ½)` for `w > −1/2`. -/
theorem integral_rpow_gauss_Ioi {w : ℝ} (hw : -1 / 2 < w) :
    ∫ x in Ioi (0 : ℝ), x ^ (2 * w) * Real.exp (-x ^ 2 / 2) =
      (2 : ℝ) ^ (w - 1 / 2) * Real.Gamma (w + 1 / 2) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 2 * w) (b := 1 / 2) two_pos
    (by linarith) (by norm_num)
  have hfun : (fun x : ℝ => x ^ (2 * w) * Real.exp (-x ^ 2 / 2)) =
      fun x => x ^ (2 * w) * Real.exp (-(1 / 2) * x ^ (2 : ℝ)) := by
    funext x
    rw [Real.rpow_two]
    ring_nf
  rw [hfun, h, show (2 * w + 1) / 2 = w + 1 / 2 by ring]
  have h2 : ((1 / 2 : ℝ) ^ (-(2 * w + 1) / 2)) = (2 : ℝ) ^ (w + 1 / 2) := by
    rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.inv_rpow (by norm_num),
      ← Real.rpow_neg (by norm_num)]
    congr 1
    ring
  rw [h2]
  have h3 : (2 : ℝ) ^ (w - 1 / 2) = 2 ^ (w + 1 / 2) * 2⁻¹ := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  rw [h3]
  ring

/-- `∫_ℝ |x|^{2w} e^{−x²/2} dx = 2^{w+½} Γ(w + ½)` as a lower integral, `w > −1/2`. -/
theorem lintegral_abs_rpow_gauss {w : ℝ} (hw : -1 / 2 < w) :
    ∫⁻ x : ℝ, ENNReal.ofReal (|x| ^ (2 * w) * Real.exp (-x ^ 2 / 2)) =
      ENNReal.ofReal ((2 : ℝ) ^ (w + 1 / 2) * Real.Gamma (w + 1 / 2)) := by
  set f : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (|x| ^ (2 * w) * Real.exp (-x ^ 2 / 2)) with hf
  have hfm : Measurable f := by rw [hf]; fun_prop
  have hneg : ∀ x, f (-x) = f x := by intro x; simp [hf]
  have h1 : ∫⁻ x in Iio (0 : ℝ), f x = ∫⁻ x in Ioi (0 : ℝ), f x := by
    have := (Measure.measurePreserving_neg (volume : Measure ℝ)).setLIntegral_comp_preimage
      (s := Ioi (0 : ℝ)) measurableSet_Ioi hfm
    rw [show (fun x : ℝ => -x) ⁻¹' Ioi 0 = Iio 0 by ext; simp] at this
    simp_rw [hneg] at this
    exact this
  have h2 : ∫⁻ x in Ici (0 : ℝ), f x = ∫⁻ x in Ioi (0 : ℝ), f x := by
    rw [Measure.restrict_congr_set Ioi_ae_eq_Ici.symm]
  have hIoi : ∫⁻ x in Ioi (0 : ℝ), f x =
      ENNReal.ofReal ((2 : ℝ) ^ (w - 1 / 2) * Real.Gamma (w + 1 / 2)) := by
    have e : ∫⁻ x in Ioi (0 : ℝ), f x =
        ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (x ^ (2 * w) * Real.exp (-x ^ 2 / 2)) :=
      setLIntegral_congr_fun measurableSet_Ioi fun x hx => by
        rw [hf]; simp only; rw [abs_of_pos hx]
    have hint : IntegrableOn (fun x : ℝ => x ^ (2 * w) * Real.exp (-x ^ 2 / 2)) (Ioi 0) := by
      have := (integrable_rpow_mul_exp_neg_mul_sq (b := 1 / 2) (by norm_num) (s := 2 * w)
        (by linarith)).integrableOn (s := Ioi (0 : ℝ))
      refine this.congr_fun (fun x _ => ?_) measurableSet_Ioi
      simp only; ring_nf
    rw [e, ← ofReal_integral_eq_lintegral_ofReal hint (ae_restrict_of_forall_mem measurableSet_Ioi
      fun x hx => mul_nonneg (Real.rpow_nonneg (le_of_lt hx) _) (Real.exp_pos _).le),
      integral_rpow_gauss_Ioi hw]
  have hG : 0 ≤ (2 : ℝ) ^ (w - 1 / 2) * Real.Gamma (w + 1 / 2) :=
    mul_nonneg (by positivity) (Real.Gamma_pos_of_pos (by linarith)).le
  calc ∫⁻ x : ℝ, f x = (∫⁻ x in Iio (0 : ℝ), f x) + ∫⁻ x in Ici (0 : ℝ), f x := by
        rw [← lintegral_add_compl f measurableSet_Iio, compl_Iio]
    _ = ENNReal.ofReal ((2 : ℝ) ^ (w - 1 / 2) * Real.Gamma (w + 1 / 2)) +
        ENNReal.ofReal ((2 : ℝ) ^ (w - 1 / 2) * Real.Gamma (w + 1 / 2)) :=
        congrArg₂ (· + ·) (h1.trans hIoi) (h2.trans hIoi)
    _ = _ := by
        rw [← ENNReal.ofReal_add hG hG]
        congr 1
        rw [show w + 1 / 2 = (w - 1 / 2) + 1 by ring, Real.rpow_add (by norm_num : (0 : ℝ) < 2),
          Real.rpow_one]
        ring

/-- The Gaussian integral `∫_ℝ e^{−y²/2} dy = √(2π)` as a lower integral. -/
theorem lintegral_gauss_half :
    ∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-y ^ 2 / 2)) =
      ENNReal.ofReal (Real.sqrt (2 * Real.pi)) := by
  have hint : Integrable fun y : ℝ => Real.exp (-y ^ 2 / 2) := by
    have := integrable_exp_neg_mul_sq (b := 1 / 2) (by norm_num)
    refine this.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only; ring_nf
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun y => (Real.exp_pos _).le)]
  congr 1
  have := integral_gaussian (1 / 2 : ℝ)
  rw [show (fun y : ℝ => Real.exp (-y ^ 2 / 2)) = fun y => Real.exp (-(1 / 2) * y ^ 2) by
    funext y; ring_nf, this]
  congr 1
  ring

/-- The two-dimensional Gaussian factorises. -/
theorem gauss2_eq (z : ℝ × ℝ) :
    gauss2 z = Real.exp (-z.1 ^ 2 / 2) * Real.exp (-z.2 ^ 2 / 2) := by
  rw [gauss2, ← Real.exp_add]; congr 1; ring

/-- `∫_{ℝ²} |x|^{2w} e^{−|z|²/2} dz` in Cartesian coordinates: a product of two one-dimensional
integrals. -/
theorem lintegral_abs_rpow_gauss2_prod {w : ℝ} (hw : -1 / 2 < w) :
    ∫⁻ z : ℝ × ℝ, ENNReal.ofReal (|z.1| ^ (2 * w) * gauss2 z) =
      ENNReal.ofReal ((2 : ℝ) ^ (w + 1 / 2) * Real.Gamma (w + 1 / 2)) *
        ENNReal.ofReal (Real.sqrt (2 * Real.pi)) := by
  set f : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (|x| ^ (2 * w) * Real.exp (-x ^ 2 / 2)) with hf
  set g : ℝ → ℝ≥0∞ := fun y => ENNReal.ofReal (Real.exp (-y ^ 2 / 2)) with hg
  have hfm : Measurable f := by rw [hf]; fun_prop
  have hgm : Measurable g := by rw [hg]; fun_prop
  have e : ∀ z : ℝ × ℝ, ENNReal.ofReal (|z.1| ^ (2 * w) * gauss2 z) = f z.1 * g z.2 := by
    intro z
    rw [hf, hg]
    simp only
    rw [gauss2_eq, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  calc ∫⁻ z : ℝ × ℝ, ENNReal.ofReal (|z.1| ^ (2 * w) * gauss2 z)
      = ∫⁻ z : ℝ × ℝ, f z.1 * g z.2 ∂((volume : Measure ℝ).prod volume) := by
        rw [← Measure.volume_eq_prod]; exact lintegral_congr e
    _ = (∫⁻ x, f x) * ∫⁻ y, g y := lintegral_prod_mul hfm.aemeasurable hgm.aemeasurable
    _ = _ := by rw [hf, hg, lintegral_abs_rpow_gauss hw, lintegral_gauss_half]

/-- `∫_{ℝ²} |x|^{2w} e^{−|z|²/2} dz` in polar coordinates: the radial Gamma integral times the
angular integral. -/
theorem lintegral_abs_rpow_gauss2_polar {w : ℝ} (hw : -1 / 2 < w) :
    ∫⁻ z : ℝ × ℝ, ENNReal.ofReal (|z.1| ^ (2 * w) * gauss2 z) =
      ENNReal.ofReal ((2 : ℝ) ^ w * Real.Gamma (w + 1)) *
        ∫⁻ θ in Ioo (-Real.pi) Real.pi, ENNReal.ofReal (|Real.cos θ| ^ (2 * w)) := by
  have hf : Measurable fun z : ℝ × ℝ => ENNReal.ofReal (|z.1| ^ (2 * w) * gauss2 z) :=
    ((measurable_fst.abs.pow_const _).mul measurable_gauss2).ennreal_ofReal
  rw [lintegral_polar _ hf]
  have hpt : ∀ r ∈ Ioi (0 : ℝ), ∫⁻ θ in Ioo (-Real.pi) Real.pi, ENNReal.ofReal r *
      ENNReal.ofReal (|(r * Real.cos θ, r * Real.sin θ).1| ^ (2 * w) *
        gauss2 (r * Real.cos θ, r * Real.sin θ)) =
      ENNReal.ofReal (r ^ (2 * w + 1) * Real.exp (-r ^ 2 / 2)) *
        ∫⁻ θ in Ioo (-Real.pi) Real.pi, ENNReal.ofReal (|Real.cos θ| ^ (2 * w)) := by
    intro r hr
    have hr' : (0 : ℝ) < r := hr
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_congr_fun measurableSet_Ioo fun θ _ => ?_
    simp only
    rw [gauss2_polar, abs_mul, abs_of_pos hr', Real.mul_rpow hr'.le (abs_nonneg _),
      ← ENNReal.ofReal_mul hr'.le, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [Real.rpow_add hr', Real.rpow_one]
    ring
  rw [setLIntegral_congr_fun measurableSet_Ioi hpt]
  have hmeas : Measurable fun r : ℝ =>
      ENNReal.ofReal (r ^ (2 * w + 1) * Real.exp (-r ^ 2 / 2)) := by fun_prop
  rw [lintegral_mul_const _ hmeas]
  congr 1
  have hint : IntegrableOn (fun r : ℝ => r ^ (2 * w + 1) * Real.exp (-r ^ 2 / 2)) (Ioi 0) := by
    have := (integrable_rpow_mul_exp_neg_mul_sq (b := 1 / 2) (by norm_num) (s := 2 * w + 1)
      (by linarith)).integrableOn (s := Ioi (0 : ℝ))
    refine this.congr_fun (fun x _ => ?_) measurableSet_Ioi
    simp only; ring_nf
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_restrict_of_forall_mem measurableSet_Ioi
    fun x hx => mul_nonneg (Real.rpow_nonneg (le_of_lt hx) _) (Real.exp_pos _).le),
    integral_radial_gamma' (by linarith)]

/-- ★★ The angular Beta integral: `∫_{−π}^{π} |cos θ|^{2w} dθ = 2√π Γ(w + ½)/Γ(w + 1)` for
`w > −1/2`. -/
theorem lintegral_abs_cos_rpow {w : ℝ} (hw : -1 / 2 < w) :
    ∫⁻ θ in Ioo (-Real.pi) Real.pi, ENNReal.ofReal (|Real.cos θ| ^ (2 * w)) =
      ENNReal.ofReal (2 * Real.sqrt Real.pi * Real.Gamma (w + 1 / 2) / Real.Gamma (w + 1)) := by
  have hΓ₁ : 0 < Real.Gamma (w + 1 / 2) := Real.Gamma_pos_of_pos (by linarith)
  have hΓ₂ : 0 < Real.Gamma (w + 1) := Real.Gamma_pos_of_pos (by linarith)
  have hA : 0 < (2 : ℝ) ^ w * Real.Gamma (w + 1) := mul_pos (by positivity) hΓ₂
  have h := (lintegral_abs_rpow_gauss2_polar hw).symm.trans (lintegral_abs_rpow_gauss2_prod hw)
  rw [← ENNReal.ofReal_mul (mul_nonneg (by positivity) hΓ₁.le)] at h
  rw [(ENNReal.eq_div_iff (ENNReal.ofReal_pos.mpr hA).ne' ENNReal.ofReal_ne_top).mpr h,
    ← ENNReal.ofReal_div_of_pos hA]
  congr 1
  have h2 : (2 : ℝ) ^ (w + 1 / 2) = 2 ^ w * Real.sqrt 2 := by
    rw [Real.rpow_add two_pos, Real.sqrt_eq_rpow]
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  rw [h2, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), div_eq_div_iff hA.ne' hΓ₂.ne']
  linear_combination ((2 : ℝ) ^ w * Real.Gamma (w + 1 / 2) * Real.sqrt Real.pi *
    Real.Gamma (w + 1)) * hs

/-- ★★★ **The zeta function of the blow-up example in closed form**: for `w > −1/2`,
`∫_{ℝ²} K^w e^{−|z|²/2} dz = 2^{3w+1} Γ(w + ½)²`. -/
theorem lintegral_blowK_gauss_closed {w : ℝ} (hw : -1 / 2 < w) :
    ∫⁻ z : ℝ × ℝ, ENNReal.ofReal (blowK z ^ w * gauss2 z) =
      ENNReal.ofReal ((2 : ℝ) ^ (3 * w + 1) * Real.Gamma (w + 1 / 2) ^ 2) := by
  have hΓ₁ : 0 < Real.Gamma (w + 1 / 2) := Real.Gamma_pos_of_pos (by linarith)
  have hΓ₂ : 0 < Real.Gamma (w + 1) := Real.Gamma_pos_of_pos (by linarith)
  have hΓ₃ : 0 < Real.Gamma (2 * w + 1) := Real.Gamma_pos_of_pos (by linarith)
  have hπ : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  rw [lintegral_blowK_gauss hw, lintegral_abs_cos_rpow hw,
    ← ENNReal.ofReal_mul (mul_nonneg (by positivity) hΓ₃.le)]
  congr 1
  have hdup := Real.Gamma_mul_Gamma_add_half (w + 1 / 2)
  rw [show w + 1 / 2 + 1 / 2 = w + 1 by ring, show 2 * (w + 1 / 2) = 2 * w + 1 by ring,
    show 1 - (2 * w + 1) = -(2 * w) by ring, Real.rpow_neg (by norm_num)] at hdup
  -- hdup : Γ(w+½) Γ(w+1) = Γ(2w+1) (2^{2w})⁻¹ √π
  have hD : Real.Gamma (2 * w + 1) =
      Real.Gamma (w + 1 / 2) * Real.Gamma (w + 1) * 2 ^ (2 * w) / Real.sqrt Real.pi := by
    rw [eq_div_iff hπ.ne', hdup]
    field_simp
  rw [hD, show 3 * w + 1 = w + 2 * w + 1 by ring, Real.rpow_add two_pos, Real.rpow_add two_pos,
    Real.rpow_one]
  field_simp

end Grammar
