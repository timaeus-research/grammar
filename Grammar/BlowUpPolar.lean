/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.ConeGaussian

/-!
# The blow-up example `K = x²(x² + y²)/2`: polar coordinates and the zeta factorisation

The two-output model `(x², xy)` with unit Gaussian noise and zero target has divergence
`K = x²(x² + y²)/2` (examples_slop §3), the paper's blow-up example.  In polar coordinates
`(x, y) = (r cos θ, r sin θ)` the phase is `r⁴ cos²θ / 2`: the polar coordinates are the real
oriented blow-up of the origin, and the phase is the crossing `w² s²` in the coordinates
`w = cos θ`, `s = r²` up to a unit.  This module records the two formal facts behind that reduction:

* `lintegral_polar` — Tonelli form of Mathlib's polar coordinates: for measurable `f`,
  `∫_{ℝ²} f = ∫_0^∞ ∫_{−π}^{π} r f(r cos θ, r sin θ) dθ dr`;
* ★★ `lintegral_blowK_gauss` — the zeta function of the model against the Gaussian prior
  factorises into a radial Gamma integral and an angular integral: for `w > −1/2`,

    `∫_{ℝ²} K^w e^{−|z|²/2} dz = 2^w Γ(2w + 1) · ∫_{−π}^{π} |cos θ|^{2w} dθ`.

The angular integral is the Beta function `2√π Γ(w + ½)/Γ(w + 1)`, giving
`ζ(w) = 2^{3w+1} Γ(w + ½)²` with double poles at the half-integers; its evaluation is an analytic
derivation (not in Mathlib) and the note records it as such.  Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Grammar

/-- The phase of the two-output model: `x²(x² + y²)/2`. -/
noncomputable def blowK (z : ℝ × ℝ) : ℝ := z.1 ^ 2 * (z.1 ^ 2 + z.2 ^ 2) / 2

/-- The Gaussian weight `e^{−|z|²/2}` on `ℝ²`. -/
noncomputable def gauss2 (z : ℝ × ℝ) : ℝ := Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 2)

theorem blowK_nonneg (z : ℝ × ℝ) : 0 ≤ blowK z := by unfold blowK; positivity

theorem measurable_blowK : Measurable blowK := by unfold blowK; fun_prop

theorem measurable_gauss2 : Measurable gauss2 := by unfold gauss2; fun_prop

/-- ★ **Polar coordinates, Tonelli form.** -/
theorem lintegral_polar (f : ℝ × ℝ → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ z, f z = ∫⁻ r in Ioi (0 : ℝ), ∫⁻ θ in Ioo (-Real.pi) Real.pi,
      ENNReal.ofReal r * f (r * Real.cos θ, r * Real.sin θ) := by
  rw [← lintegral_comp_polarCoord_symm f, polarCoord_target, Measure.volume_eq_prod,
    ← Measure.prod_restrict]
  have hm : Measurable fun p : ℝ × ℝ => ENNReal.ofReal p.1 • f (polarCoord.symm p) :=
    measurable_fst.ennreal_ofReal.smul (hf.comp (by
      change Measurable fun p : ℝ × ℝ => (p.1 * Real.cos p.2, p.1 * Real.sin p.2)
      fun_prop))
  rw [lintegral_prod _ hm.aemeasurable]
  rfl

/-- The phase in polar coordinates. -/
theorem blowK_polar (r θ : ℝ) :
    blowK (r * Real.cos θ, r * Real.sin θ) = r ^ 4 * Real.cos θ ^ 2 / 2 := by
  unfold blowK
  have := Real.cos_sq_add_sin_sq θ
  simp only
  rw [show (r * Real.cos θ) ^ 2 * ((r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2) =
    r ^ 4 * Real.cos θ ^ 2 * (Real.cos θ ^ 2 + Real.sin θ ^ 2) by ring, this, mul_one]

theorem gauss2_polar (r θ : ℝ) :
    gauss2 (r * Real.cos θ, r * Real.sin θ) = Real.exp (-r ^ 2 / 2) := by
  unfold gauss2
  simp only
  congr 1
  have := Real.cos_sq_add_sin_sq θ
  nlinarith [this]

/-- The pointwise factorisation of `K^w e^{−|z|²/2}` in polar coordinates, `r > 0`. -/
theorem blowK_rpow_gauss_polar {r : ℝ} (hr : 0 < r) (θ w : ℝ) :
    blowK (r * Real.cos θ, r * Real.sin θ) ^ w * gauss2 (r * Real.cos θ, r * Real.sin θ) =
      (2 : ℝ) ^ (-w) * r ^ (4 * w) * Real.exp (-r ^ 2 / 2) * |Real.cos θ| ^ (2 * w) := by
  rw [blowK_polar, gauss2_polar]
  have h1 : r ^ 4 * Real.cos θ ^ 2 / 2 = (r ^ 4 * Real.cos θ ^ 2) * (2 : ℝ)⁻¹ := by ring
  rw [h1, Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity),
    Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num), ← sq_abs (Real.cos θ),
    ← Real.rpow_natCast r 4, ← Real.rpow_natCast |Real.cos θ| 2, ← Real.rpow_mul hr.le,
    ← Real.rpow_mul (abs_nonneg _)]
  push_cast
  ring

/-- The radial Gamma integral: `∫_0^∞ r^{4w+1} e^{−r²/2} dr = 2^{2w} Γ(2w + 1)` for `w > −1/2`. -/
theorem integral_radial_gamma {w : ℝ} (hw : -1 / 2 < w) :
    ∫ r in Ioi (0 : ℝ), r ^ (4 * w + 1) * Real.exp (-r ^ 2 / 2) =
      (2 : ℝ) ^ (2 * w) * Real.Gamma (2 * w + 1) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 4 * w + 1) (b := 1 / 2) two_pos
    (by linarith) (by norm_num)
  have hfun : (fun r : ℝ => r ^ (4 * w + 1) * Real.exp (-r ^ 2 / 2)) =
      fun r => r ^ (4 * w + 1) * Real.exp (-(1 / 2) * r ^ (2 : ℝ)) := by
    funext r
    rw [Real.rpow_two]
    ring_nf
  rw [hfun, h, show (4 * w + 1 + 1) / 2 = 2 * w + 1 by ring]
  have h2 : ((1 / 2 : ℝ) ^ (-(4 * w + 1 + 1) / 2)) = (2 : ℝ) ^ (2 * w + 1) := by
    rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num)]
    congr 1
    ring
  rw [h2, Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
  ring

/-- ★★ **The zeta function of the blow-up example against the Gaussian prior factorises**: for
`w > −1/2`, `∫_{ℝ²} K^w e^{−|z|²/2} dz = 2^w Γ(2w + 1) ∫_{−π}^{π} |cos θ|^{2w} dθ`. -/
theorem lintegral_blowK_gauss {w : ℝ} (hw : -1 / 2 < w) :
    ∫⁻ z : ℝ × ℝ, ENNReal.ofReal (blowK z ^ w * gauss2 z) =
      ENNReal.ofReal ((2 : ℝ) ^ w * Real.Gamma (2 * w + 1)) *
        ∫⁻ θ in Ioo (-Real.pi) Real.pi, ENNReal.ofReal (|Real.cos θ| ^ (2 * w)) := by
  have hf : Measurable fun z : ℝ × ℝ => ENNReal.ofReal (blowK z ^ w * gauss2 z) :=
    ((measurable_blowK.pow_const w).mul measurable_gauss2).ennreal_ofReal
  rw [lintegral_polar _ hf]
  have hpt : ∀ r ∈ Ioi (0 : ℝ), ∫⁻ θ in Ioo (-Real.pi) Real.pi, ENNReal.ofReal r *
      ENNReal.ofReal (blowK (r * Real.cos θ, r * Real.sin θ) ^ w *
        gauss2 (r * Real.cos θ, r * Real.sin θ)) =
      ENNReal.ofReal ((2 : ℝ) ^ (-w) * r ^ (4 * w + 1) * Real.exp (-r ^ 2 / 2)) *
        ∫⁻ θ in Ioo (-Real.pi) Real.pi, ENNReal.ofReal (|Real.cos θ| ^ (2 * w)) := by
    intro r hr
    have hr' : (0 : ℝ) < r := hr
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_congr_fun measurableSet_Ioo fun θ _ => ?_
    rw [blowK_rpow_gauss_polar hr' θ w, ← ENNReal.ofReal_mul hr'.le,
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [Real.rpow_add hr', Real.rpow_one]
    ring
  rw [setLIntegral_congr_fun measurableSet_Ioi hpt]
  have hgroup : ∀ r : ℝ, (2 : ℝ) ^ (-w) * r ^ (4 * w + 1) * Real.exp (-r ^ 2 / 2) =
      (2 : ℝ) ^ (-w) * (r ^ (4 * w + 1) * Real.exp (-r ^ 2 / 2)) := fun r => by ring
  simp_rw [hgroup]
  have hmeas : Measurable fun r : ℝ =>
      ENNReal.ofReal ((2 : ℝ) ^ (-w) * (r ^ (4 * w + 1) * Real.exp (-r ^ 2 / 2))) := by
    fun_prop
  rw [lintegral_mul_const _ hmeas]
  congr 1
  have hint : Integrable (fun r : ℝ => r ^ (4 * w + 1) * Real.exp (-r ^ 2 / 2)) := by
    have := integrable_rpow_mul_exp_neg_mul_sq (b := 1 / 2) (by norm_num) (s := 4 * w + 1)
      (by linarith)
    refine this.congr (Eventually.of_forall fun r => ?_)
    simp only
    congr 2
    ring
  rw [← ofReal_integral_eq_lintegral_ofReal (hint.const_mul _).integrableOn
    (ae_restrict_of_forall_mem measurableSet_Ioi fun r hr => by
      have hr' : (0 : ℝ) < r := hr
      positivity)]
  congr 1
  rw [integral_const_mul, integral_radial_gamma hw, ← mul_assoc,
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  congr 2
  ring

end Grammar
