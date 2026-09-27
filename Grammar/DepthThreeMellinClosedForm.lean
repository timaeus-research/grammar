/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.DepthThreeMellinBridge

/-!
# The closed form of the Mellin transform of the depth-two Gaussian DLN

`M(z) = ∫₀^∞ v^{z−1} Z₂(v²) dv = 2^{−1−z/2} Γ(z/2) Γ((1−z)/2)² / π` for `0 < z < 1`
(★★★ `depthThreeMellin_eq`).  Route: the scalar reduction `Z₂(v²) = ∫ γ(g)(1 + v²g²)^{−1/2} dg`
(DCXIX), Tonelli, the substitution `u = |g| v` giving `|g|^{−z} A(z)` with

  `A(z) = ∫₀^∞ u^{z−1}(1 + u²)^{−1/2} du = Γ(z/2) Γ((1−z)/2)/(2√π)`   (★★ `mellinHalfBeta_eq`),

itself by the Gamma representation `(1 + u²)^{−1/2} = π^{−1/2} ∫₀^∞ w^{−1/2} e^{−(1+u²)w} dw` and
onemore Tonelli (no Beta-function API), and the negative Gaussian moment

  `∫ |g|^{−z} γ(g) dg = 2^{−z/2} Γ((1−z)/2)/√π`   (`integral_abs_rpow_neg_mul_gaussDensity`).

Both Tonelli steps use `integrable_prod_iff'` with the inner integrals evaluated by
`integral_rpow_mul_exp_neg_mul_rpow`.  With DCXLII–DCXLIII this identifies the depth-three
constant `Q` (next unit; examples_slop §2; Astra round-13).  Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

/-! ### Two Gamma-type integrals -/

/-- `∫₀^∞ u^{z−1} e^{−w u²} du = w^{−z/2} Γ(z/2)/2` for `z, w > 0`. -/
theorem integral_rpow_mul_exp_neg_mul_sq' {z w : ℝ} (hz : 0 < z) (hw : 0 < w) :
    ∫ u in Ioi (0 : ℝ), u ^ (z - 1) * Real.exp (-w * u ^ 2) =
      w ^ (-z / 2) * (1 / 2) * Real.Gamma (z / 2) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := z - 1) (b := w) two_pos
    (by linarith) hw
  have e : ∀ u ∈ Ioi (0 : ℝ), u ^ (z - 1) * Real.exp (-w * u ^ (2 : ℝ)) =
      u ^ (z - 1) * Real.exp (-w * u ^ 2) := by
    intro u _; rw [Real.rpow_two]
  rw [setIntegral_congr_fun measurableSet_Ioi e] at h
  rw [h, show -(z - 1 + 1) / 2 = -z / 2 by ring, show (z - 1 + 1) / 2 = z / 2 by ring]

/-- `∫₀^∞ w^{a−1} e^{−b w} dw = b^{−a} Γ(a)` for `a, b > 0`. -/
theorem integral_rpow_mul_exp_neg_mul' {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ w in Ioi (0 : ℝ), w ^ (a - 1) * Real.exp (-b * w) = b ^ (-a) * Real.Gamma a := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 1) (q := a - 1) (b := b) one_pos
    (by linarith) hb
  have e : ∀ w ∈ Ioi (0 : ℝ), w ^ (a - 1) * Real.exp (-b * w ^ (1 : ℝ)) =
      w ^ (a - 1) * Real.exp (-b * w) := by
    intro w _; rw [Real.rpow_one]
  rw [setIntegral_congr_fun measurableSet_Ioi e] at h
  rw [h, show -(a - 1 + 1) / 1 = -a by ring, show (a - 1 + 1) / 1 = a by ring]
  ring

/-- The Gamma representation `(1 + t)^{−1/2} = π^{−1/2} ∫₀^∞ w^{−1/2} e^{−(1+t)w} dw` for
`t ≥ 0`. -/
theorem inv_sqrt_one_add_eq_integral {t : ℝ} (ht : 0 ≤ t) :
    1 / Real.sqrt (1 + t) =
      1 / Real.sqrt Real.pi * ∫ w in Ioi (0 : ℝ), w ^ (-(1 / 2 : ℝ)) * Real.exp (-(1 + t) * w) := by
  have h := integral_rpow_mul_exp_neg_mul' (a := 1 / 2) (b := 1 + t) (by norm_num) (by linarith)
  rw [show (1 / 2 : ℝ) - 1 = -(1 / 2) by norm_num] at h
  rw [h, Real.Gamma_one_half_eq, Real.sqrt_eq_rpow, Real.rpow_neg (by linarith)]
  have hs : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  field_simp

/-! ### `A(z) = ∫₀^∞ u^{z−1}(1+u²)^{−1/2} du` -/

/-- `A(z) = ∫₀^∞ u^{z−1}(1 + u²)^{−1/2} du`. -/
noncomputable def mellinHalfBeta (z : ℝ) : ℝ :=
  ∫ u in Ioi (0 : ℝ), u ^ (z - 1) / Real.sqrt (1 + u ^ 2)

/-- The two-variable integrand `w^{−1/2} e^{−w} u^{z−1} e^{−w u²}` is integrable on `(0,∞)²`. -/
theorem integrable_halfBeta_prod {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    Integrable (Function.uncurry fun u w : ℝ =>
      w ^ (-(1 / 2 : ℝ)) * Real.exp (-w) * (u ^ (z - 1) * Real.exp (-w * u ^ 2)))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hmeas : AEStronglyMeasurable (Function.uncurry fun u w : ℝ =>
      w ^ (-(1 / 2 : ℝ)) * Real.exp (-w) * (u ^ (z - 1) * Real.exp (-w * u ^ 2)))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    refine Measurable.aestronglyMeasurable ?_
    have : Function.uncurry (fun u w : ℝ =>
        w ^ (-(1 / 2 : ℝ)) * Real.exp (-w) * (u ^ (z - 1) * Real.exp (-w * u ^ 2))) =
        fun p : ℝ × ℝ => p.2 ^ (-(1 / 2 : ℝ)) * Real.exp (-p.2) *
          (p.1 ^ (z - 1) * Real.exp (-p.2 * p.1 ^ 2)) := by
      funext p; rfl
    rw [this]
    exact ((measurable_snd.pow_const _).mul (Real.measurable_exp.comp measurable_snd.neg)).mul
      ((measurable_fst.pow_const _).mul (Real.measurable_exp.comp
        (measurable_snd.neg.mul (measurable_fst.pow_const 2))))
  rw [integrable_prod_iff' hmeas]
  constructor
  · rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun w hw => ?_
    have hw' : (0 : ℝ) < w := hw
    have hI : IntegrableOn (fun u : ℝ => u ^ (z - 1) * Real.exp (-w * u ^ 2)) (Ioi 0) := by
      have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 2) (s := z - 1) (b := w)
        (by linarith) two_pos hw'
      refine this.congr_fun (fun u _ => ?_) measurableSet_Ioi
      change u ^ (z - 1) * Real.exp (-w * u ^ (2 : ℝ)) = _
      rw [Real.rpow_two]
    exact (hI.const_mul (w ^ (-(1 / 2 : ℝ)) * Real.exp (-w))).congr
      (Eventually.of_forall fun u => rfl)
  · have e : ∀ w ∈ Ioi (0 : ℝ), (∫ u in Ioi (0 : ℝ), ‖Function.uncurry (fun u w : ℝ =>
        w ^ (-(1 / 2 : ℝ)) * Real.exp (-w) * (u ^ (z - 1) * Real.exp (-w * u ^ 2))) (u, w)‖) =
        (1 / 2) * Real.Gamma (z / 2) * (w ^ (-(1 + z) / 2) * Real.exp (-w)) := by
      intro w hw
      have hw' : (0 : ℝ) < w := hw
      have e' : ∀ u ∈ Ioi (0 : ℝ), ‖Function.uncurry (fun u w : ℝ =>
          w ^ (-(1 / 2 : ℝ)) * Real.exp (-w) * (u ^ (z - 1) * Real.exp (-w * u ^ 2))) (u, w)‖ =
          w ^ (-(1 / 2 : ℝ)) * Real.exp (-w) * (u ^ (z - 1) * Real.exp (-w * u ^ 2)) := by
        intro u hu
        have hu' : (0 : ℝ) < u := hu
        rw [Function.uncurry_apply_pair, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      rw [setIntegral_congr_fun measurableSet_Ioi e', integral_const_mul,
        integral_rpow_mul_exp_neg_mul_sq' hz0 hw']
      have hp : w ^ (-(1 / 2 : ℝ)) * w ^ (-z / 2) = w ^ (-(1 + z) / 2) := by
        rw [← Real.rpow_add hw']; congr 1; ring
      rw [← hp]
      ring
    have hI : IntegrableOn (fun w : ℝ => (1 / 2) * Real.Gamma (z / 2) *
        (w ^ (-(1 + z) / 2) * Real.exp (-w))) (Ioi 0) := by
      have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := -(1 + z) / 2) (b := 1)
        (by linarith) one_pos one_pos
      refine IntegrableOn.congr_fun (this.const_mul ((1 / 2) * Real.Gamma (z / 2)))
        (fun w _ => ?_) measurableSet_Ioi
      simp only [Real.rpow_one, neg_mul, one_mul]
    exact hI.congr_fun (fun w hw => (e w hw).symm) measurableSet_Ioi

/-- ★★ `A(z) = Γ(z/2) Γ((1−z)/2)/(2√π)` for `0 < z < 1`. -/
theorem mellinHalfBeta_eq {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    mellinHalfBeta z = Real.Gamma (z / 2) * Real.Gamma ((1 - z) / 2) / (2 * Real.sqrt Real.pi) := by
  unfold mellinHalfBeta
  have hs : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  -- rewrite the integrand through the Gamma representation
  have e : ∀ u ∈ Ioi (0 : ℝ), u ^ (z - 1) / Real.sqrt (1 + u ^ 2) =
      1 / Real.sqrt Real.pi * ∫ w in Ioi (0 : ℝ),
        w ^ (-(1 / 2 : ℝ)) * Real.exp (-w) * (u ^ (z - 1) * Real.exp (-w * u ^ 2)) := by
    intro u hu
    have hu' : (0 : ℝ) < u := hu
    rw [div_eq_mul_one_div, inv_sqrt_one_add_eq_integral (sq_nonneg u), ← mul_assoc,
      mul_comm (u ^ (z - 1)), mul_assoc, ← integral_const_mul]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun w _ => ?_
    rw [show -(1 + u ^ 2) * w = -w + -w * u ^ 2 by ring, Real.exp_add]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi e, integral_const_mul,
    integral_integral_swap (integrable_halfBeta_prod hz0 hz1)]
  have e2 : ∀ w ∈ Ioi (0 : ℝ), (∫ u in Ioi (0 : ℝ),
      w ^ (-(1 / 2 : ℝ)) * Real.exp (-w) * (u ^ (z - 1) * Real.exp (-w * u ^ 2))) =
      (1 / 2) * Real.Gamma (z / 2) * (w ^ ((1 - z) / 2 - 1) * Real.exp (-1 * w)) := by
    intro w hw
    have hw' : (0 : ℝ) < w := hw
    rw [integral_const_mul, integral_rpow_mul_exp_neg_mul_sq' hz0 hw']
    have hp : w ^ (-(1 / 2 : ℝ)) * w ^ (-z / 2) = w ^ ((1 - z) / 2 - 1) := by
      rw [← Real.rpow_add hw']; congr 1; ring
    rw [← hp, neg_one_mul]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi e2, integral_const_mul,
    integral_rpow_mul_exp_neg_mul' (by linarith) one_pos, Real.one_rpow]
  field_simp

/-! ### The negative Gaussian moment -/

theorem gaussDensity_abs (g : ℝ) : gaussDensity |g| = gaussDensity g := by
  unfold gaussDensity; rw [sq_abs]

/-- `∫ |g|^{−z} γ(g) dg = 2^{−z/2} Γ((1−z)/2)/√π` for `z < 1`. -/
theorem integral_abs_rpow_neg_mul_gaussDensity {z : ℝ} (hz : z < 1) :
    ∫ g : ℝ, |g| ^ (-z) * gaussDensity g =
      (2 : ℝ) ^ (-z / 2) * Real.Gamma ((1 - z) / 2) / Real.sqrt Real.pi := by
  have h := integral_comp_abs (f := fun g : ℝ => g ^ (-z) * gaussDensity g)
  simp only [gaussDensity_abs] at h
  rw [h]
  have e : ∀ g ∈ Ioi (0 : ℝ), g ^ (-z) * gaussDensity g =
      1 / Real.sqrt (2 * Real.pi) * (g ^ ((1 - z) - 1) * Real.exp (-(1 / 2) * g ^ 2)) := by
    intro g _
    unfold gaussDensity
    rw [show (1 - z) - 1 = -z by ring, show -g ^ 2 / 2 = -(1 / 2) * g ^ 2 by ring]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi e, integral_const_mul,
    integral_rpow_mul_exp_neg_mul_sq' (by linarith) (by norm_num)]
  have hs : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have h2 : Real.sqrt (2 * Real.pi) = Real.sqrt 2 * Real.sqrt Real.pi :=
    Real.sqrt_mul (by norm_num) _
  have h3 : (1 / 2 : ℝ) ^ (-(1 - z) / 2) = (2 : ℝ) ^ ((1 - z) / 2) := by
    rw [one_div, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num)]
    congr 1; ring
  have h4 : (2 : ℝ) ^ ((1 - z) / 2) = Real.sqrt 2 * (2 : ℝ) ^ (-z / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add (by norm_num)]
    congr 1; ring
  have h5 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  rw [h2, h3, h4]
  field_simp

/-! ### The closed form -/

/-- For `g ≠ 0`: `∫₀^∞ v^{z−1}(1 + v²g²)^{−1/2} dv = |g|^{−z} A(z)` (the substitution
`u = |g| v`). -/
theorem integral_rpow_div_sqrt_one_add_mul_sq {z g : ℝ} (hg : g ≠ 0) :
    ∫ v in Ioi (0 : ℝ), v ^ (z - 1) / Real.sqrt (1 + v ^ 2 * g ^ 2) =
      |g| ^ (-z) * mellinHalfBeta z := by
  have hg0 : 0 < |g| := abs_pos.2 hg
  unfold mellinHalfBeta
  have h := integral_comp_mul_left_Ioi (fun u : ℝ => u ^ (z - 1) / Real.sqrt (1 + u ^ 2)) 0 hg0
  rw [mul_zero, smul_eq_mul] at h
  have e : ∀ v ∈ Ioi (0 : ℝ), v ^ (z - 1) / Real.sqrt (1 + v ^ 2 * g ^ 2) =
      |g| ^ (-(z - 1)) * ((|g| * v) ^ (z - 1) / Real.sqrt (1 + (|g| * v) ^ 2)) := by
    intro v hv
    have hv' : (0 : ℝ) < v := hv
    rw [Real.mul_rpow hg0.le hv'.le, mul_pow, sq_abs, Real.rpow_neg hg0.le,
      mul_comm (g ^ 2) (v ^ 2)]
    have : (0 : ℝ) < |g| ^ (z - 1) := Real.rpow_pos_of_pos hg0 _
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi e, integral_const_mul, h]
  have hinv : |g|⁻¹ = |g| ^ (-1 : ℝ) := by rw [Real.rpow_neg hg0.le, Real.rpow_one]
  have hpow : |g| ^ (-(z - 1)) * |g| ^ (-1 : ℝ) = |g| ^ (-z) := by
    rw [← Real.rpow_add hg0]; congr 1; ring
  rw [hinv, ← mul_assoc, hpow]

/-- The integrand `v^{z−1} γ(g)(1 + v²g²)^{−1/2}` is integrable on `(0,∞) × ℝ` for `0 < z < 1`
(the `v`-marginal of its norm is `v^{z−1} Z₂(v²)`, integrable by DCXLII). -/
theorem integrable_mellin_prod {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    Integrable (Function.uncurry fun v g : ℝ =>
      v ^ (z - 1) * (gaussDensity g / Real.sqrt (1 + v ^ 2 * g ^ 2)))
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
  have hmeas : AEStronglyMeasurable (Function.uncurry fun v g : ℝ =>
      v ^ (z - 1) * (gaussDensity g / Real.sqrt (1 + v ^ 2 * g ^ 2)))
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
    refine Measurable.aestronglyMeasurable ?_
    have : Function.uncurry (fun v g : ℝ =>
        v ^ (z - 1) * (gaussDensity g / Real.sqrt (1 + v ^ 2 * g ^ 2))) =
        fun p : ℝ × ℝ =>
          p.1 ^ (z - 1) * (gaussDensity p.2 / Real.sqrt (1 + p.1 ^ 2 * p.2 ^ 2)) := by
      funext p; rfl
    rw [this]
    exact (measurable_fst.pow_const _).mul
      ((continuous_gaussDensity.measurable.comp measurable_snd).div
      (Real.continuous_sqrt.measurable.comp (measurable_const.add
        ((measurable_fst.pow_const 2).mul (measurable_snd.pow_const 2)))))
  rw [integrable_prod_iff hmeas]
  constructor
  · rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun v hv => ?_
    have hv' : (0 : ℝ) < v := hv
    have hm : Measurable fun g : ℝ =>
        v ^ (z - 1) * (gaussDensity g / Real.sqrt (1 + v ^ 2 * g ^ 2)) :=
      measurable_const.mul (continuous_gaussDensity.measurable.div
        (Real.continuous_sqrt.measurable.comp (measurable_const.add
          (measurable_const.mul (measurable_id.pow_const 2)))))
    simp only [Function.uncurry_apply_pair]
    refine (integrable_gaussDensity.const_mul (v ^ (z - 1))).mono' hm.aestronglyMeasurable
      (Eventually.of_forall fun g => ?_)
    have h1 : 1 ≤ Real.sqrt (1 + v ^ 2 * g ^ 2) :=
      Real.one_le_sqrt.2 (by linarith [mul_nonneg (sq_nonneg v) (sq_nonneg g)])
    rw [Real.norm_eq_abs, abs_of_nonneg (by
      have := gaussDensity_nonneg g; positivity)]
    have hγ := gaussDensity_nonneg g
    have hvp : 0 ≤ v ^ (z - 1) := by positivity
    calc v ^ (z - 1) * (gaussDensity g / Real.sqrt (1 + v ^ 2 * g ^ 2))
        ≤ v ^ (z - 1) * (gaussDensity g / 1) := by gcongr
      _ = v ^ (z - 1) * gaussDensity g := by rw [div_one]
  · have e : ∀ v ∈ Ioi (0 : ℝ), (∫ g : ℝ, ‖Function.uncurry (fun v g : ℝ =>
        v ^ (z - 1) * (gaussDensity g / Real.sqrt (1 + v ^ 2 * g ^ 2))) (v, g)‖) =
        v ^ (z - 1) * gaussLaplace2 (v ^ 2) := by
      intro v hv
      have hv' : (0 : ℝ) < v := hv
      rw [gaussLaplace2_eq_density_integral (sq_nonneg v), ← integral_const_mul]
      congr 1
      funext g
      rw [Function.uncurry_apply_pair, Real.norm_eq_abs, abs_of_nonneg (by
        have := gaussDensity_nonneg g; positivity)]
    exact (integrableOn_rpow_mul_gaussLaplace2 hz0 hz1).congr_fun (fun v hv => (e v hv).symm)
      measurableSet_Ioi

/-- ★★★ **The closed form**: `M(z) = 2^{−1−z/2} Γ(z/2) Γ((1−z)/2)² / π` for `0 < z < 1`. -/
theorem depthThreeMellin_eq {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    depthThreeMellin z =
      (2 : ℝ) ^ (-1 - z / 2) * Real.Gamma (z / 2) * Real.Gamma ((1 - z) / 2) ^ 2 / Real.pi := by
  unfold depthThreeMellin
  have e : ∀ v ∈ Ioi (0 : ℝ), v ^ (z - 1) * gaussLaplace2 (v ^ 2) =
      ∫ g : ℝ, v ^ (z - 1) * (gaussDensity g / Real.sqrt (1 + v ^ 2 * g ^ 2)) := by
    intro v _
    rw [gaussLaplace2_eq_density_integral (sq_nonneg v), ← integral_const_mul]
  rw [setIntegral_congr_fun measurableSet_Ioi e,
    integral_integral_swap (integrable_mellin_prod hz0 hz1)]
  have hae : ∀ᵐ g : ℝ, g ≠ 0 := by
    rw [ae_iff]
    simp only [not_not, Set.ofPred_eq_eq_singleton, measure_singleton]
  have e2 : ∀ g : ℝ, g ≠ 0 →
      (∫ v in Ioi (0 : ℝ), v ^ (z - 1) * (gaussDensity g / Real.sqrt (1 + v ^ 2 * g ^ 2))) =
        mellinHalfBeta z * (|g| ^ (-z) * gaussDensity g) := by
    intro g hg
    have : (fun v : ℝ => v ^ (z - 1) * (gaussDensity g / Real.sqrt (1 + v ^ 2 * g ^ 2))) =
        fun v => gaussDensity g * (v ^ (z - 1) / Real.sqrt (1 + v ^ 2 * g ^ 2)) := by
      funext v; ring
    rw [this, integral_const_mul, integral_rpow_div_sqrt_one_add_mul_sq hg]
    ring
  rw [integral_congr_ae (hae.mono fun g hg => e2 g hg), integral_const_mul,
    integral_abs_rpow_neg_mul_gaussDensity hz1, mellinHalfBeta_eq hz0 hz1]
  have hs : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have h2 : (2 : ℝ) ^ (-1 - z / 2) = (2 : ℝ) ^ (-z / 2) / 2 := by
    rw [show (-1 - z / 2 : ℝ) = -z / 2 - 1 by ring, Real.rpow_sub_one two_ne_zero]
  rw [h2]
  field_simp
  simp only [Real.sq_sqrt Real.pi_pos.le]

end Grammar
