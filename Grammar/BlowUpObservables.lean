/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.BlowUpLaplaceExpansion
import Grammar.ConeAveragedPosterior

/-!
# The blow-up model: the leading numerators of the observables `x²` and `y²`

For the model `K = x²(x² + y²)/2` with the raw Gaussian prior `e^{−|w|²/2}` (examples_slop §4),
the inserted integrals `X_N = ∫ x² e^{−NK} φ` and `Y_N = ∫ y² e^{−NK} φ` have the leading
behaviour

  `N X_N → π`  and  `√N Y_N → 2√(2π)`

(★★★ `tendsto_mul_blowupX`, `tendsto_sqrt_mul_blowupY`): the Gaussian integral in `y` at fixed `x`
(`blowupX_eq_integral`, `blowupY_eq_integral`, with the second moment
`∫ y² e^{−cy²/2} = √(2π)/c^{3/2}`),
the scalings `x = u/m` at `N = m⁴` (`blowupX_scaled`:
`m⁴ X = √(2π) ∫ u² e^{−u⁴/2 − u²/2m²}/√(u² + 1/m²)`)
and `x = t/m` at `N = m²` (`blowupY_scaled`: `m Y = √(2π) ∫ e^{−(t⁴+t²)/2m²}/(1 + t²)^{3/2}`),
dominated
convergence, and the two values `∫ |u| e^{−u⁴/2} = √(2π)/2` and `∫ (1 + t²)^{−3/2} = 2` (primitive
`t/√(1 + t²)`).  The observable `x²` removes the logarithm (order `N^{−1}` against the partition
function's `N^{−1/2} log N`); `y²` keeps the `N^{−1/2}` order with the kernel `(1 + Nx²)^{−3/2}`
(Astra round-11 target 1).  Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

/-- `X_N = ∫ x² e^{−N x²(x²+y²)/2} e^{−|w|²/2}`. -/
noncomputable def blowupX (N : ℝ) : ℝ :=
  ∫ w : ℝ × ℝ, w.1 ^ 2 * (Real.exp (-N * (w.1 ^ 2 * (w.1 ^ 2 + w.2 ^ 2)) / 2) *
    Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / 2))

/-- `Y_N = ∫ y² e^{−N x²(x²+y²)/2} e^{−|w|²/2}`. -/
noncomputable def blowupY (N : ℝ) : ℝ :=
  ∫ w : ℝ × ℝ, w.2 ^ 2 * (Real.exp (-N * (w.1 ^ 2 * (w.1 ^ 2 + w.2 ^ 2)) / 2) *
    Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / 2))

/-! ### Gaussian moments -/

theorem integrable_sq_mul_exp_neg_half_sq :
    Integrable (fun x : ℝ => x ^ 2 * Real.exp (-x ^ 2 / 2)) := by
  have := integrable_rpow_mul_exp_neg_mul_sq (b := 1 / 2) (by norm_num) (s := 2) (by norm_num)
  refine this.congr (Eventually.of_forall fun x => ?_)
  simp only
  rw [Real.rpow_two]
  congr 2
  ring

/-- `∫ y² e^{−c y²/2} dy = √(2π)/(c √c)` for `c > 0`. -/
theorem integral_sq_exp_cond {c : ℝ} (hc : 0 < c) :
    ∫ y : ℝ, y ^ 2 * Real.exp (-c * y ^ 2 / 2) = Real.sqrt (2 * Real.pi) / (c * Real.sqrt c) := by
  have h := integral_comp_abs (f := fun y : ℝ => y ^ 2 * Real.exp (-c * y ^ 2 / 2))
  simp only [sq_abs] at h
  rw [h]
  have hg := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 2) (b := c / 2) (by norm_num)
    (by norm_num) (by positivity)
  have e : ∀ y ∈ Ioi (0 : ℝ), y ^ (2 : ℝ) * Real.exp (-(c / 2) * y ^ (2 : ℝ)) =
      y ^ 2 * Real.exp (-c * y ^ 2 / 2) := by
    intro y _
    rw [Real.rpow_two]
    congr 2
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi e] at hg
  rw [hg, show (-(2 + 1) / 2 : ℝ) = -(3 / 2) by norm_num,
    show ((2 : ℝ) + 1) / 2 = 1 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
    Real.Gamma_one_half_eq, Real.rpow_neg (by positivity)]
  have h32 : (c / 2) ^ (3 / 2 : ℝ) = (c / 2) * Real.sqrt (c / 2) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (by positivity), Real.rpow_one,
      Real.sqrt_eq_rpow]
  rw [h32, Real.sqrt_div' _ (by norm_num)]
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hsc : Real.sqrt c * Real.sqrt c = c := Real.mul_self_sqrt hc.le
  have hsq2 : 0 < Real.sqrt 2 := by positivity
  have hsqc : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  rw [Real.sqrt_mul (by norm_num)]
  field_simp

/-! ### The conditional reductions -/

theorem integrable_blowupX (N : ℝ) (hN : 0 ≤ N) :
    Integrable fun w : ℝ × ℝ => w.1 ^ 2 * (Real.exp (-N * (w.1 ^ 2 * (w.1 ^ 2 + w.2 ^ 2)) / 2) *
      Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / 2)) := by
  have hg : Integrable fun x : ℝ => Real.exp (-x ^ 2 / 2) := by
    have := integrable_exp_neg_mul_sq (b := 1 / 2) (by norm_num)
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only
    congr 1
    ring
  have hprod : Integrable (fun w : ℝ × ℝ => w.1 ^ 2 * Real.exp (-w.1 ^ 2 / 2) *
      Real.exp (-w.2 ^ 2 / 2)) (volume.prod volume) := integrable_sq_mul_exp_neg_half_sq.mul_prod hg
  rw [Measure.volume_eq_prod]
  refine hprod.mono' (Measurable.aestronglyMeasurable (by fun_prop))
    (Eventually.of_forall fun w => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h1 : Real.exp (-N * (w.1 ^ 2 * (w.1 ^ 2 + w.2 ^ 2)) / 2) ≤ 1 :=
    Real.exp_le_one_iff.2 (by
      nlinarith [mul_nonneg hN (by positivity : 0 ≤ w.1 ^ 2 * (w.1 ^ 2 + w.2 ^ 2))])
  have h2 : Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / 2) =
      Real.exp (-w.1 ^ 2 / 2) * Real.exp (-w.2 ^ 2 / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [h2]
  have h3 : 0 ≤ w.1 ^ 2 * (Real.exp (-w.1 ^ 2 / 2) * Real.exp (-w.2 ^ 2 / 2)) := by positivity
  calc w.1 ^ 2 * (Real.exp (-N * (w.1 ^ 2 * (w.1 ^ 2 + w.2 ^ 2)) / 2) *
        (Real.exp (-w.1 ^ 2 / 2) * Real.exp (-w.2 ^ 2 / 2)))
      = Real.exp (-N * (w.1 ^ 2 * (w.1 ^ 2 + w.2 ^ 2)) / 2) *
        (w.1 ^ 2 * (Real.exp (-w.1 ^ 2 / 2) * Real.exp (-w.2 ^ 2 / 2))) := by ring
    _ ≤ 1 * (w.1 ^ 2 * (Real.exp (-w.1 ^ 2 / 2) * Real.exp (-w.2 ^ 2 / 2))) :=
        mul_le_mul_of_nonneg_right h1 h3
    _ = w.1 ^ 2 * Real.exp (-w.1 ^ 2 / 2) * Real.exp (-w.2 ^ 2 / 2) := by ring

theorem integrable_blowupY (N : ℝ) (hN : 0 ≤ N) :
    Integrable fun w : ℝ × ℝ => w.2 ^ 2 * (Real.exp (-N * (w.1 ^ 2 * (w.1 ^ 2 + w.2 ^ 2)) / 2) *
      Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / 2)) := by
  have hg : Integrable fun x : ℝ => Real.exp (-x ^ 2 / 2) := by
    have := integrable_exp_neg_mul_sq (b := 1 / 2) (by norm_num)
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only
    congr 1
    ring
  have hprod : Integrable (fun w : ℝ × ℝ => Real.exp (-w.1 ^ 2 / 2) *
      (w.2 ^ 2 * Real.exp (-w.2 ^ 2 / 2))) (volume.prod volume) :=
    hg.mul_prod integrable_sq_mul_exp_neg_half_sq
  rw [Measure.volume_eq_prod]
  refine hprod.mono' (Measurable.aestronglyMeasurable (by fun_prop))
    (Eventually.of_forall fun w => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h1 : Real.exp (-N * (w.1 ^ 2 * (w.1 ^ 2 + w.2 ^ 2)) / 2) ≤ 1 :=
    Real.exp_le_one_iff.2 (by
      nlinarith [mul_nonneg hN (by positivity : 0 ≤ w.1 ^ 2 * (w.1 ^ 2 + w.2 ^ 2))])
  have h2 : Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / 2) =
      Real.exp (-w.1 ^ 2 / 2) * Real.exp (-w.2 ^ 2 / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [h2]
  have h3 : 0 ≤ w.2 ^ 2 * (Real.exp (-w.1 ^ 2 / 2) * Real.exp (-w.2 ^ 2 / 2)) := by positivity
  calc w.2 ^ 2 * (Real.exp (-N * (w.1 ^ 2 * (w.1 ^ 2 + w.2 ^ 2)) / 2) *
        (Real.exp (-w.1 ^ 2 / 2) * Real.exp (-w.2 ^ 2 / 2)))
      = Real.exp (-N * (w.1 ^ 2 * (w.1 ^ 2 + w.2 ^ 2)) / 2) *
        (w.2 ^ 2 * (Real.exp (-w.1 ^ 2 / 2) * Real.exp (-w.2 ^ 2 / 2))) := by ring
    _ ≤ 1 * (w.2 ^ 2 * (Real.exp (-w.1 ^ 2 / 2) * Real.exp (-w.2 ^ 2 / 2))) :=
        mul_le_mul_of_nonneg_right h1 h3
    _ = Real.exp (-w.1 ^ 2 / 2) * (w.2 ^ 2 * Real.exp (-w.2 ^ 2 / 2)) := by ring

/-- ★★ `X_N = √(2π) ∫ x² e^{−N x⁴/2} e^{−x²/2}/√(1 + N x²) dx` for `N ≥ 0`. -/
theorem blowupX_eq_integral {N : ℝ} (hN : 0 ≤ N) :
    blowupX N = Real.sqrt (2 * Real.pi) *
      ∫ x : ℝ, x ^ 2 * (Real.exp (-N * x ^ 4 / 2) * Real.exp (-x ^ 2 / 2)) /
        Real.sqrt (1 + N * x ^ 2) := by
  unfold blowupX
  rw [Measure.volume_eq_prod, integral_prod _ (by
    have := integrable_blowupX N hN
    rwa [Measure.volume_eq_prod] at this), ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  have hc : 0 < 1 + N * x ^ 2 := by positivity
  have hexp : ∀ y : ℝ, Real.exp (-N * (x ^ 2 * (x ^ 2 + y ^ 2)) / 2) *
      Real.exp (-(x ^ 2 + y ^ 2) / 2) =
      Real.exp (-N * x ^ 4 / 2) * Real.exp (-x ^ 2 / 2) *
        Real.exp (-(1 + N * x ^ 2) * y ^ 2 / 2) := by
    intro y
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hpt : ∀ y : ℝ, x ^ 2 * (Real.exp (-N * (x ^ 2 * (x ^ 2 + y ^ 2)) / 2) *
      Real.exp (-(x ^ 2 + y ^ 2) / 2)) =
      (x ^ 2 * (Real.exp (-N * x ^ 4 / 2) * Real.exp (-x ^ 2 / 2))) *
        Real.exp (-(1 + N * x ^ 2) * y ^ 2 / 2) := by
    intro y
    rw [hexp]
    ring
  simp_rw [hpt]
  rw [integral_const_mul, integral_exp_cond hc, Real.sqrt_div' _ hc.le]
  ring

/-- ★★ `Y_N = √(2π) ∫ e^{−N x⁴/2} e^{−x²/2}/((1 + N x²)√(1 + N x²)) dx` for `N ≥ 0`. -/
theorem blowupY_eq_integral {N : ℝ} (hN : 0 ≤ N) :
    blowupY N = Real.sqrt (2 * Real.pi) *
      ∫ x : ℝ, Real.exp (-N * x ^ 4 / 2) * Real.exp (-x ^ 2 / 2) /
        ((1 + N * x ^ 2) * Real.sqrt (1 + N * x ^ 2)) := by
  unfold blowupY
  rw [Measure.volume_eq_prod, integral_prod _ (by
    have := integrable_blowupY N hN
    rwa [Measure.volume_eq_prod] at this), ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  have hc : 0 < 1 + N * x ^ 2 := by positivity
  have hexp : ∀ y : ℝ, Real.exp (-N * (x ^ 2 * (x ^ 2 + y ^ 2)) / 2) *
      Real.exp (-(x ^ 2 + y ^ 2) / 2) =
      Real.exp (-N * x ^ 4 / 2) * Real.exp (-x ^ 2 / 2) *
        Real.exp (-(1 + N * x ^ 2) * y ^ 2 / 2) := by
    intro y
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hpt : ∀ y : ℝ, y ^ 2 * (Real.exp (-N * (x ^ 2 * (x ^ 2 + y ^ 2)) / 2) *
      Real.exp (-(x ^ 2 + y ^ 2) / 2)) =
      (Real.exp (-N * x ^ 4 / 2) * Real.exp (-x ^ 2 / 2)) *
        (y ^ 2 * Real.exp (-(1 + N * x ^ 2) * y ^ 2 / 2)) := by
    intro y
    rw [hexp]
    ring
  simp_rw [hpt]
  rw [integral_const_mul, integral_sq_exp_cond hc]
  ring

/-! ### Scaling -/

/-- `m⁴ X_{m⁴} = √(2π) ∫ u² e^{−u⁴/2} e^{−u²/2m²}/√(u² + 1/m²) du` for `m > 0` (`x = u/m`). -/
theorem blowupX_scaled {m : ℝ} (hm : 0 < m) :
    m ^ 4 * blowupX (m ^ 4) = Real.sqrt (2 * Real.pi) *
      ∫ u : ℝ, u ^ 2 * (Real.exp (-u ^ 4 / 2) * Real.exp (-u ^ 2 / (2 * m ^ 2))) /
        Real.sqrt (u ^ 2 + 1 / m ^ 2) := by
  rw [blowupX_eq_integral (by positivity)]
  set g : ℝ → ℝ := fun x => x ^ 2 * (Real.exp (-m ^ 4 * x ^ 4 / 2) * Real.exp (-x ^ 2 / 2)) /
    Real.sqrt (1 + m ^ 4 * x ^ 2) with hg
  have e : ∀ u : ℝ, m ^ 3 * g (1 / m * u) =
      u ^ 2 * (Real.exp (-u ^ 4 / 2) * Real.exp (-u ^ 2 / (2 * m ^ 2))) /
        Real.sqrt (u ^ 2 + 1 / m ^ 2) := by
    intro u
    simp only [hg]
    have h1 : -m ^ 4 * (1 / m * u) ^ 4 / 2 = -u ^ 4 / 2 := by field_simp
    have h2 : -(1 / m * u) ^ 2 / 2 = -u ^ 2 / (2 * m ^ 2) := by field_simp
    have h3 : Real.sqrt (1 + m ^ 4 * (1 / m * u) ^ 2) = m * Real.sqrt (u ^ 2 + 1 / m ^ 2) := by
      rw [show 1 + m ^ 4 * (1 / m * u) ^ 2 = m ^ 2 * (u ^ 2 + 1 / m ^ 2) by field_simp; ring,
        Real.sqrt_mul (by positivity), Real.sqrt_sq hm.le]
    rw [h1, h2, h3]
    have hs : 0 < Real.sqrt (u ^ 2 + 1 / m ^ 2) := Real.sqrt_pos.2 (by positivity)
    field_simp
  have h := Measure.integral_comp_mul_left g (1 / m)
  rw [smul_eq_mul, show |(1 / m)⁻¹| = m by rw [inv_div, div_one, abs_of_pos hm]] at h
  have h' : ∫ y, g y = 1 / m * ∫ x, g (1 / m * x) := by rw [h]; field_simp
  rw [h', show m ^ 4 * (Real.sqrt (2 * Real.pi) * (1 / m * ∫ x, g (1 / m * x))) =
    Real.sqrt (2 * Real.pi) * ∫ x, m ^ 3 * g (1 / m * x) by
      rw [integral_const_mul]; field_simp]
  congr 1
  exact integral_congr_ae (Eventually.of_forall e)

/-- `m Y_{m²} = √(2π) ∫ e^{−t⁴/2m²} e^{−t²/2m²}/((1 + t²)√(1 + t²)) dt` for `m > 0` (`x = t/m`). -/
theorem blowupY_scaled {m : ℝ} (hm : 0 < m) :
    m * blowupY (m ^ 2) = Real.sqrt (2 * Real.pi) *
      ∫ t : ℝ, Real.exp (-t ^ 4 / (2 * m ^ 2)) * Real.exp (-t ^ 2 / (2 * m ^ 2)) /
        ((1 + t ^ 2) * Real.sqrt (1 + t ^ 2)) := by
  rw [blowupY_eq_integral (by positivity)]
  set g : ℝ → ℝ := fun x => Real.exp (-m ^ 2 * x ^ 4 / 2) * Real.exp (-x ^ 2 / 2) /
    ((1 + m ^ 2 * x ^ 2) * Real.sqrt (1 + m ^ 2 * x ^ 2)) with hg
  have e : ∀ t : ℝ, g (1 / m * t) =
      Real.exp (-t ^ 4 / (2 * m ^ 2)) * Real.exp (-t ^ 2 / (2 * m ^ 2)) /
      ((1 + t ^ 2) * Real.sqrt (1 + t ^ 2)) := by
    intro t
    simp only [hg]
    have h1 : -m ^ 2 * (1 / m * t) ^ 4 / 2 = -t ^ 4 / (2 * m ^ 2) := by field_simp
    have h2 : -(1 / m * t) ^ 2 / 2 = -t ^ 2 / (2 * m ^ 2) := by field_simp
    have h3 : 1 + m ^ 2 * (1 / m * t) ^ 2 = 1 + t ^ 2 := by field_simp
    rw [h1, h2, h3]
  have h := Measure.integral_comp_mul_left g (1 / m)
  rw [smul_eq_mul, show |(1 / m)⁻¹| = m by rw [inv_div, div_one, abs_of_pos hm]] at h
  have h' : ∫ y, g y = 1 / m * ∫ x, g (1 / m * x) := by rw [h]; field_simp
  rw [h', show m * (Real.sqrt (2 * Real.pi) * (1 / m * ∫ x, g (1 / m * x))) =
    Real.sqrt (2 * Real.pi) * ∫ x, g (1 / m * x) by field_simp]
  congr 1
  exact integral_congr_ae (Eventually.of_forall e)

/-! ### The two values -/

/-- `∫ |u| e^{−u⁴/2} du = √(2π)/2`. -/
theorem integral_abs_mul_exp_neg_quartic :
    ∫ u : ℝ, |u| * Real.exp (-u ^ 4 / 2) = Real.sqrt (2 * Real.pi) / 2 := by
  have e4 : ∀ x : ℝ, |x| ^ 4 = x ^ 4 := fun x => by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs, ← pow_mul]
  have h := integral_comp_abs (f := fun u : ℝ => u * Real.exp (-u ^ 4 / 2))
  simp only [e4] at h
  rw [h]
  have hg := integral_rpow_mul_exp_neg_mul_rpow (p := 4) (q := 1) (b := 1 / 2) (by norm_num)
    (by norm_num) (by norm_num)
  have e : ∀ x ∈ Ioi (0 : ℝ), x ^ (1 : ℝ) * Real.exp (-(1 / 2) * x ^ (4 : ℝ)) =
      x * Real.exp (-x ^ 4 / 2) := by
    intro x _
    rw [Real.rpow_one, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    congr 2
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi e] at hg
  rw [hg, show (-(1 + 1) / 4 : ℝ) = -(1 / 2) by norm_num,
    show ((1 : ℝ) + 1) / 4 = 1 / 2 by norm_num,
    Real.Gamma_one_half_eq, Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow,
    Real.sqrt_div' _ (by norm_num), Real.sqrt_one, Real.sqrt_mul (by norm_num)]
  have hs2 : 0 < Real.sqrt 2 := by positivity
  field_simp
  norm_num

/-- `∫ (1 + t²)^{−3/2} dt = 2`, by the primitive `t/√(1 + t²)`. -/
theorem integral_one_add_sq_pow_three_half :
    ∫ t : ℝ, 1 / ((1 + t ^ 2) * Real.sqrt (1 + t ^ 2)) = 2 := by
  have hderiv : ∀ t : ℝ, HasDerivAt (fun t => t / Real.sqrt (1 + t ^ 2))
      (1 / ((1 + t ^ 2) * Real.sqrt (1 + t ^ 2))) t := by
    intro t
    have hpos : 0 < 1 + t ^ 2 := by positivity
    have hs : 0 < Real.sqrt (1 + t ^ 2) := Real.sqrt_pos.2 hpos
    have h1 : HasDerivAt (fun t : ℝ => 1 + t ^ 2) (2 * t) t := by
      simpa using ((hasDerivAt_pow 2 t).const_add 1)
    have h2 := h1.sqrt hpos.ne'
    have h3 := (hasDerivAt_id' t).div h2 hs.ne'
    refine h3.congr_deriv ?_
    have hsq : Real.sqrt (1 + t ^ 2) ^ 2 = 1 + t ^ 2 := Real.sq_sqrt hpos.le
    field_simp
    linear_combination (t ^ 2) * hsq
  have hint : Integrable fun t : ℝ => 1 / ((1 + t ^ 2) * Real.sqrt (1 + t ^ 2)) := by
    have hcont : Continuous fun t : ℝ => 1 / ((1 + t ^ 2) * Real.sqrt (1 + t ^ 2)) :=
      continuous_const.div (by fun_prop) fun t => by positivity
    refine integrable_inv_one_add_sq.mono' hcont.aestronglyMeasurable
      (Eventually.of_forall fun t => ?_)
    have hpos : 0 < 1 + t ^ 2 := by positivity
    have hs1 : 1 ≤ Real.sqrt (1 + t ^ 2) :=
      Real.one_le_sqrt.2 (le_add_of_nonneg_right (sq_nonneg t))
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), one_div, inv_le_inv₀ (by positivity) hpos]
    nlinarith
  have hsq_id : ∀ t : ℝ, 0 ≤ t → t / Real.sqrt (1 + t ^ 2) = Real.sqrt (1 - 1 / (1 + t ^ 2)) := by
    intro t ht
    have hpos : 0 < 1 + t ^ 2 := by positivity
    rw [show 1 - 1 / (1 + t ^ 2) = t ^ 2 / (1 + t ^ 2) by field_simp; ring,
      Real.sqrt_div' _ hpos.le,
      Real.sqrt_sq ht]
  have hlim : Tendsto (fun t : ℝ => Real.sqrt (1 - 1 / (1 + t ^ 2))) atTop (𝓝 1) := by
    have h1 : Tendsto (fun t : ℝ => 1 / (1 + t ^ 2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        (tendsto_atTop_add_const_left _ 1 (tendsto_pow_atTop two_ne_zero))
    have h2 : Tendsto (fun t : ℝ => 1 - 1 / (1 + t ^ 2)) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h1
    have := (Real.continuous_sqrt.tendsto 1).comp h2
    rw [Real.sqrt_one] at this
    exact this
  have htop : Tendsto (fun t : ℝ => t / Real.sqrt (1 + t ^ 2)) atTop (𝓝 1) := by
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact (hsq_id t ht).symm
  have hbot : Tendsto (fun t : ℝ => t / Real.sqrt (1 + t ^ 2)) atBot (𝓝 (-1)) := by
    have hneg : Tendsto (fun t : ℝ => -((-t) / Real.sqrt (1 + (-t) ^ 2))) atBot (𝓝 (-1)) := by
      have := (htop.comp tendsto_neg_atBot_atTop).neg
      simpa [Function.comp] using this
    refine hneg.congr fun t => ?_
    rw [neg_sq]
    ring
  rw [integral_of_hasDerivAt_of_tendsto hderiv hint hbot htop]
  norm_num

/-! ### The limits -/

theorem tendsto_one_div_sq_atTop : Tendsto (fun m : ℝ => 1 / m ^ 2) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop (tendsto_pow_atTop two_ne_zero)

/-- `m⁴ X_{m⁴} → π` as `m → ∞`. -/
theorem tendsto_blowupX_scaled :
    Tendsto (fun m : ℝ => m ^ 4 * blowupX (m ^ 4)) atTop (𝓝 Real.pi) := by
  have hval : Real.pi = Real.sqrt (2 * Real.pi) * ∫ u : ℝ, |u| * Real.exp (-u ^ 4 / 2) := by
    rw [integral_abs_mul_exp_neg_quartic, ← mul_div_assoc, Real.mul_self_sqrt (by positivity)]
    ring
  rw [hval]
  refine ((tendsto_integral_filter_of_dominated_convergence
    (F := fun m u => u ^ 2 * (Real.exp (-u ^ 4 / 2) * Real.exp (-u ^ 2 / (2 * m ^ 2))) /
      Real.sqrt (u ^ 2 + 1 / m ^ 2))
    (f := fun u => |u| * Real.exp (-u ^ 4 / 2))
    (fun u => Real.exp (1 / 8) * Real.exp (-(1 / 4) * u ^ 2))
    (Eventually.of_forall fun m => (by fun_prop : Measurable fun u : ℝ =>
      u ^ 2 * (Real.exp (-u ^ 4 / 2) * Real.exp (-u ^ 2 / (2 * m ^ 2))) /
        Real.sqrt (u ^ 2 + 1 / m ^ 2)).aestronglyMeasurable)
    ?_ ((integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 4)).const_mul _)
    (Eventually.of_forall fun u => ?_)).const_mul (Real.sqrt (2 * Real.pi))).congr' ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with m hm
    refine Eventually.of_forall fun u => ?_
    have hE : Real.exp (-u ^ 2 / (2 * m ^ 2)) ≤ 1 :=
      Real.exp_le_one_iff.2 (by
        have : 0 ≤ u ^ 2 / (2 * m ^ 2) := by positivity
        rw [neg_div]; linarith)
    have hE0 : 0 < Real.exp (-u ^ 2 / (2 * m ^ 2)) := Real.exp_pos _
    have hq : 0 < Real.exp (-u ^ 4 / 2) := Real.exp_pos _
    have hs : 0 < Real.sqrt (u ^ 2 + 1 / m ^ 2) := Real.sqrt_pos.2 (by positivity)
    have hsu : |u| ≤ Real.sqrt (u ^ 2 + 1 / m ^ 2) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt (by linarith [show 0 ≤ 1 / m ^ 2 by positivity])
    have hab : |u| ^ 2 = u ^ 2 := sq_abs u
    have h1 : u ^ 2 * (Real.exp (-u ^ 4 / 2) * Real.exp (-u ^ 2 / (2 * m ^ 2))) /
        Real.sqrt (u ^ 2 + 1 / m ^ 2) ≤ |u| * Real.exp (-u ^ 4 / 2) := by
      rw [div_le_iff₀ hs]
      have := mul_le_mul_of_nonneg_left hsu (by positivity : 0 ≤ |u| * Real.exp (-u ^ 4 / 2))
      nlinarith [mul_le_mul_of_nonneg_left hE (by positivity : 0 ≤ u ^ 2 * Real.exp (-u ^ 4 / 2)),
        abs_nonneg u]
    have h2 : |u| * Real.exp (-u ^ 4 / 2) ≤ Real.exp (1 / 8) * Real.exp (-(1 / 4) * u ^ 2) := by
      have hu : |u| ≤ Real.exp (u ^ 2 / 4) := by
        have := Real.add_one_le_exp (u ^ 2 / 4)
        nlinarith [sq_nonneg (|u| - 2), sq_abs u]
      have hq' : Real.exp (-u ^ 4 / 2) ≤ Real.exp (1 / 8) * Real.exp (-u ^ 2 / 2) := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.2 (by nlinarith [sq_nonneg (u ^ 2 - 1 / 2)])
      calc |u| * Real.exp (-u ^ 4 / 2)
          ≤ Real.exp (u ^ 2 / 4) * (Real.exp (1 / 8) * Real.exp (-u ^ 2 / 2)) :=
            mul_le_mul hu hq' hq.le (Real.exp_pos _).le
        _ = Real.exp (1 / 8) * Real.exp (-(1 / 4) * u ^ 2) := by
            have e : Real.exp (u ^ 2 / 4) * Real.exp (-u ^ 2 / 2) =
                Real.exp (-(1 / 4) * u ^ 2) := by
              rw [← Real.exp_add]; congr 1; ring
            rw [mul_left_comm, e]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact h1.trans h2
  · by_cases hu : u = 0
    · subst hu
      simp
    · have h1 : Tendsto (fun m : ℝ => Real.exp (-u ^ 2 / (2 * m ^ 2))) atTop (𝓝 1) := by
        have h0 : Tendsto (fun m : ℝ => -u ^ 2 / 2 * (1 / m ^ 2)) atTop (𝓝 0) := by
          simpa using tendsto_one_div_sq_atTop.const_mul (-u ^ 2 / 2)
        have := (Real.continuous_exp.tendsto 0).comp h0
        rw [Real.exp_zero] at this
        refine this.congr fun m => ?_
        simp only [Function.comp]
        congr 1
        ring
      have h2 : Tendsto (fun m : ℝ => Real.sqrt (u ^ 2 + 1 / m ^ 2)) atTop (𝓝 |u|) := by
        have h0 : Tendsto (fun m : ℝ => u ^ 2 + 1 / m ^ 2) atTop (𝓝 (u ^ 2)) := by
          simpa using (tendsto_const_nhds (x := u ^ 2)).add tendsto_one_div_sq_atTop
        have := (Real.continuous_sqrt.tendsto (u ^ 2)).comp h0
        rw [Real.sqrt_sq_eq_abs] at this
        exact this
      have hu' : |u| ≠ 0 := abs_ne_zero.2 hu
      have := ((tendsto_const_nhds (x := u ^ 2)).mul
        ((tendsto_const_nhds (x := Real.exp (-u ^ 4 / 2))).mul h1)).div h2 hu'
      rw [mul_one, show u ^ 2 * Real.exp (-u ^ 4 / 2) / |u| = |u| * Real.exp (-u ^ 4 / 2) by
        rw [← sq_abs u]; field_simp] at this
      exact this
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with m hm
    exact (blowupX_scaled hm).symm

/-- `m Y_{m²} → 2√(2π)` as `m → ∞`. -/
theorem tendsto_blowupY_scaled :
    Tendsto (fun m : ℝ => m * blowupY (m ^ 2)) atTop (𝓝 (2 * Real.sqrt (2 * Real.pi))) := by
  have hval : 2 * Real.sqrt (2 * Real.pi) = Real.sqrt (2 * Real.pi) *
      ∫ t : ℝ, 1 / ((1 + t ^ 2) * Real.sqrt (1 + t ^ 2)) := by
    rw [integral_one_add_sq_pow_three_half]; ring
  rw [hval]
  have hint : Integrable fun t : ℝ => 1 / ((1 + t ^ 2) * Real.sqrt (1 + t ^ 2)) := by
    have hcont : Continuous fun t : ℝ => 1 / ((1 + t ^ 2) * Real.sqrt (1 + t ^ 2)) :=
      continuous_const.div (by fun_prop) fun t => by positivity
    refine integrable_inv_one_add_sq.mono' hcont.aestronglyMeasurable
      (Eventually.of_forall fun t => ?_)
    have hpos : 0 < 1 + t ^ 2 := by positivity
    have hs1 : 1 ≤ Real.sqrt (1 + t ^ 2) :=
      Real.one_le_sqrt.2 (le_add_of_nonneg_right (sq_nonneg t))
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), one_div, inv_le_inv₀ (by positivity) hpos]
    nlinarith
  refine ((tendsto_integral_filter_of_dominated_convergence
    (F := fun m t => Real.exp (-t ^ 4 / (2 * m ^ 2)) * Real.exp (-t ^ 2 / (2 * m ^ 2)) /
      ((1 + t ^ 2) * Real.sqrt (1 + t ^ 2)))
    (f := fun t => 1 / ((1 + t ^ 2) * Real.sqrt (1 + t ^ 2)))
    (fun t => 1 / ((1 + t ^ 2) * Real.sqrt (1 + t ^ 2)))
    (Eventually.of_forall fun m => (by fun_prop : Measurable fun t : ℝ =>
      Real.exp (-t ^ 4 / (2 * m ^ 2)) * Real.exp (-t ^ 2 / (2 * m ^ 2)) /
        ((1 + t ^ 2) * Real.sqrt (1 + t ^ 2))).aestronglyMeasurable)
    (Eventually.of_forall fun m => Eventually.of_forall fun t => ?_) hint
    (Eventually.of_forall fun t => ?_)).const_mul (Real.sqrt (2 * Real.pi))).congr' ?_
  · have hpos : 0 < (1 + t ^ 2) * Real.sqrt (1 + t ^ 2) := by positivity
    have hE1 : Real.exp (-t ^ 4 / (2 * m ^ 2)) ≤ 1 := Real.exp_le_one_iff.2 (by
      have : 0 ≤ t ^ 4 / (2 * m ^ 2) := by positivity
      rw [neg_div]; linarith)
    have hE2 : Real.exp (-t ^ 2 / (2 * m ^ 2)) ≤ 1 := Real.exp_le_one_iff.2 (by
      have : 0 ≤ t ^ 2 / (2 * m ^ 2) := by positivity
      rw [neg_div]; linarith)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_div_iff_of_pos_right hpos]
    exact mul_le_one₀ hE1 (Real.exp_pos _).le hE2
  · have h1 : Tendsto (fun m : ℝ => Real.exp (-t ^ 4 / (2 * m ^ 2))) atTop (𝓝 1) := by
      have h0 : Tendsto (fun m : ℝ => -t ^ 4 / 2 * (1 / m ^ 2)) atTop (𝓝 0) := by
        simpa using tendsto_one_div_sq_atTop.const_mul (-t ^ 4 / 2)
      have := (Real.continuous_exp.tendsto 0).comp h0
      rw [Real.exp_zero] at this
      refine this.congr fun m => ?_
      simp only [Function.comp]
      congr 1
      ring
    have h2 : Tendsto (fun m : ℝ => Real.exp (-t ^ 2 / (2 * m ^ 2))) atTop (𝓝 1) := by
      have h0 : Tendsto (fun m : ℝ => -t ^ 2 / 2 * (1 / m ^ 2)) atTop (𝓝 0) := by
        simpa using tendsto_one_div_sq_atTop.const_mul (-t ^ 2 / 2)
      have := (Real.continuous_exp.tendsto 0).comp h0
      rw [Real.exp_zero] at this
      refine this.congr fun m => ?_
      simp only [Function.comp]
      congr 1
      ring
    have := (h1.mul h2).div_const ((1 + t ^ 2) * Real.sqrt (1 + t ^ 2))
    rw [mul_one] at this
    exact this
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with m hm
    exact (blowupY_scaled hm).symm

/-- ★★★ `N X_N → π`: the observable `x²` removes the logarithm. -/
theorem tendsto_mul_blowupX : Tendsto (fun N : ℝ => N * blowupX N) atTop (𝓝 Real.pi) := by
  have hm : Tendsto (fun N : ℝ => Real.sqrt (Real.sqrt N)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp Real.tendsto_sqrt_atTop
  refine (tendsto_blowupX_scaled.comp hm).congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with N hN
  simp only [Function.comp]
  rw [show Real.sqrt (Real.sqrt N) ^ 4 = N by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt hN]]

/-- ★★★ `√N Y_N → 2√(2π)`. -/
theorem tendsto_sqrt_mul_blowupY :
    Tendsto (fun N : ℝ => Real.sqrt N * blowupY N) atTop (𝓝 (2 * Real.sqrt (2 * Real.pi))) := by
  refine (tendsto_blowupY_scaled.comp Real.tendsto_sqrt_atTop).congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with N hN
  simp only [Function.comp]
  rw [Real.sq_sqrt hN]

end Grammar
