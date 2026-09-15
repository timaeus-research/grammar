/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.Fluctuation
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Regressions for the empirical leading term in one dimension

Two hand computations fixing the conventions of the empirical stratum measure.

* **Two-sided `K = x²` with a constant signed field.** Watanabe's standard form
  `K_N = x² − x a/√N` has the signed monomial `u^k = x`, so the root field
  `ψ = √N(K − K_N)/√K = sgn(x)·a` has branch traces `±a` on the two normal sides of the wall
  `{x = 0}`. The leading term is
  `√N ∫ φ e^{−Nx² + √N x a} → √π φ(0) e^{a²/4} = φ(0)(S_{1/2}(a) + S_{1/2}(−a))/2`
  (`twoSided_constant_field_limit`, `fluctuation_half_add_neg`): the average of the fluctuation
  density over the two branches, not `S_{1/2}(a)` of a single field.
* **A boundary-layer field.** For `ξ_N(x) = h(√N x)` with `h(0) = 0` the trace of the field on the
  zero set vanishes identically, yet `√N ∫ φ e^{−Nx² + √N x h(√N x)} → φ(0) ∫ e^{−y² + y h(y)} dy`
  (`boundaryLayer_field_limit`), which differs from the zero-field limit `√π φ(0)` in general:
  convergence of the field on the zero fibre alone does not determine the empirical leading term;
  convergence on a neighbourhood does. Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Filter Topology

namespace Grammar

/-- The Gaussian integral with a linear term: `∫ e^{−v² + av} dv = √π e^{a²/4}`. -/
theorem integral_exp_neg_sq_add_mul (a : ℝ) :
    ∫ v : ℝ, Real.exp (-v ^ 2 + a * v) = √π * Real.exp (a ^ 2 / 4) := by
  have h : ∀ v : ℝ, Real.exp (-v ^ 2 + a * v) =
      Real.exp (a ^ 2 / 4) * Real.exp (-(1 : ℝ) * (v - a / 2) ^ 2) := fun v => by
    rw [← Real.exp_add]
    congr 1
    ring
  simp_rw [h]
  rw [integral_const_mul,
    integral_sub_right_eq_self (fun v : ℝ => Real.exp (-(1 : ℝ) * v ^ 2)) (a / 2),
    integral_gaussian, div_one, mul_comm]

theorem integrable_exp_neg_sq_add_mul (a : ℝ) :
    Integrable fun v : ℝ => Real.exp (-v ^ 2 + a * v) := by
  have h : (fun v : ℝ => Real.exp (-v ^ 2 + a * v)) =
      fun v => Real.exp (a ^ 2 / 4) * Real.exp (-(1 : ℝ) * (v - a / 2) ^ 2) := by
    funext v
    rw [← Real.exp_add]
    congr 1
    ring
  rw [h]
  exact ((integrable_exp_neg_mul_sq one_pos).comp_sub_right (a / 2)).const_mul _

/-- `S_{1/2}(a) = 2 ∫₀^∞ e^{−v² + av} dv` (temperature one; substitution `t = v²`). -/
theorem fluctuation_half_eq (a : ℝ) :
    fluctuation 1 (1 / 2) a = 2 * ∫ v in Ioi (0 : ℝ), Real.exp (-v ^ 2 + a * v) := by
  unfold fluctuation
  have himg : (fun v : ℝ => v ^ 2) '' Ioi 0 = Ioi 0 := by
    ext t
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact pow_pos (show (0 : ℝ) < v from hv) 2
    · intro ht
      exact ⟨√t, Real.sqrt_pos.2 ht, Real.sq_sqrt ht.le⟩
  have hinj : InjOn (fun v : ℝ => v ^ 2) (Ioi 0) := fun x hx y hy hxy =>
    (pow_left_inj₀ (le_of_lt hx) (le_of_lt hy) two_ne_zero).1 hxy
  have hsub := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun v (_ : v ∈ Ioi (0 : ℝ)) => (hasDerivAt_pow 2 v).hasDerivWithinAt) hinj
    (fun t : ℝ => t ^ ((1 : ℝ) / 2 - 1) * Real.exp (-1 * t + 1 * a * √t))
  rw [himg] at hsub
  rw [hsub, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun v hv => ?_
  have hv0 : (0 : ℝ) < v := hv
  have hsq : (v ^ 2) ^ ((1 : ℝ) / 2 - 1) = v⁻¹ := by
    rw [show (1 : ℝ) / 2 - 1 = -(1 / 2) by norm_num, Real.rpow_neg (sq_nonneg v),
      ← Real.sqrt_eq_rpow, Real.sqrt_sq hv0.le]
  simp only [smul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one, hsq, Real.sqrt_sq hv0.le, one_mul,
    neg_one_mul]
  rw [abs_of_pos (by linarith : (0 : ℝ) < 2 * v)]
  field_simp

/-- The two-branch sum: `S_{1/2}(a) + S_{1/2}(−a) = 2√π e^{a²/4}`. -/
theorem fluctuation_half_add_neg (a : ℝ) :
    fluctuation 1 (1 / 2) a + fluctuation 1 (1 / 2) (-a) = 2 * (√π * Real.exp (a ^ 2 / 4)) := by
  rw [fluctuation_half_eq, fluctuation_half_eq, ← mul_add, ← integral_exp_neg_sq_add_mul a]
  congr 1
  have hneg : ∫ v in Ioi (0 : ℝ), Real.exp (-v ^ 2 + -a * v) =
      ∫ v in Iic (0 : ℝ), Real.exp (-v ^ 2 + a * v) := by
    have h := integral_comp_neg_Ioi (0 : ℝ) (fun v : ℝ => Real.exp (-v ^ 2 + a * v))
    rw [neg_zero] at h
    rw [← h]
    refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
    simp only [neg_sq]
    ring_nf
  rw [hneg, add_comm, ← compl_Iic, integral_add_compl measurableSet_Iic
    (integrable_exp_neg_sq_add_mul a)]

/-! ### The two-sided `x²` regression with a constant signed field -/

/-- **Two-sided `K = x²`, constant signed field `a`**: the leading term averages the fluctuation
density over the two normal sides. -/
theorem twoSided_constant_field_limit {φ : ℝ → ℝ} (hφ : Continuous φ) {B : ℝ}
    (hφB : ∀ x, |φ x| ≤ B) (a : ℝ) :
    Tendsto (fun N : ℝ => √N * ∫ x, φ x * Real.exp (-N * x ^ 2 + √N * x * a)) atTop
      (𝓝 (√π * Real.exp (a ^ 2 / 4) * φ 0)) := by
  -- the rescaled integrand
  set g : ℝ → ℝ → ℝ := fun N y => φ ((y + a / 2) / √N) * Real.exp (-y ^ 2) with hg
  have hrew : ∀ N : ℝ, 0 < N → √N * ∫ x, φ x * Real.exp (-N * x ^ 2 + √N * x * a) =
      Real.exp (a ^ 2 / 4) * ∫ y, g N y := by
    intro N hN
    have hsN : 0 < √N := Real.sqrt_pos.2 hN
    have hN2 : √N ^ 2 = N := Real.sq_sqrt hN.le
    have hpt : ∀ x : ℝ, φ x * Real.exp (-N * x ^ 2 + √N * x * a) =
        Real.exp (a ^ 2 / 4) * (fun u => g N (u - a / 2)) (√N * x) := fun x => by
      simp only [hg]
      rw [show √N * x - a / 2 + a / 2 = √N * x by ring, mul_div_cancel_left₀ _ hsN.ne',
        mul_left_comm, ← Real.exp_add]
      congr 2
      linear_combination (x ^ 2) * hN2
    simp_rw [hpt]
    rw [integral_const_mul, Measure.integral_comp_mul_left (fun u => g N (u - a / 2)) (√N),
      integral_sub_right_eq_self (g N) (a / 2), abs_of_pos (inv_pos.2 hsN), smul_eq_mul]
    field_simp
  have hlim : Tendsto (fun N : ℝ => ∫ y, g N y) atTop (𝓝 (∫ y : ℝ, φ 0 * Real.exp (-y ^ 2))) := by
    have hdom : Integrable fun y : ℝ => B * Real.exp (-y ^ 2) := by
      have := (integrable_exp_neg_mul_sq one_pos).const_mul B
      simpa using this
    refine tendsto_integral_filter_of_dominated_convergence (fun y => B * Real.exp (-y ^ 2)) ?_ ?_
      hdom ?_
    · exact Eventually.of_forall fun N =>
        ((hφ.comp (by fun_prop)).mul (Real.continuous_exp.comp (by fun_prop))).aestronglyMeasurable
    · exact Eventually.of_forall fun N => Eventually.of_forall fun y => by
        simp only [hg, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
        exact mul_le_mul_of_nonneg_right (hφB _) (Real.exp_pos _).le
    · refine Eventually.of_forall fun y => ?_
      simp only [hg]
      refine ((hφ.tendsto 0).comp ?_).mul_const _
      have : Tendsto (fun N : ℝ => (y + a / 2) / √N) atTop (𝓝 0) := by
        have h1 : Tendsto (fun N : ℝ => (y + a / 2) * (√N)⁻¹) atTop (𝓝 ((y + a / 2) * 0)) :=
          (tendsto_inv_atTop_zero.comp tendsto_sqrt_atTop).const_mul _
        rw [mul_zero] at h1
        exact h1.congr fun N => (div_eq_mul_inv _ _).symm
      simpa using this
  rw [integral_const_mul] at hlim
  have hgauss : ∫ y : ℝ, Real.exp (-y ^ 2) = √π := by
    have := integral_gaussian 1
    simpa [div_one] using this
  rw [hgauss] at hlim
  have h2 := hlim.const_mul (Real.exp (a ^ 2 / 4))
  rw [show √π * Real.exp (a ^ 2 / 4) * φ 0 = Real.exp (a ^ 2 / 4) * (φ 0 * √π) by ring]
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with N hN
  exact (hrew N hN).symm

/-! ### The boundary-layer regression -/

/-- **A boundary-layer field `h(√N x)` changes the limit**: with `h` bounded continuous,
`√N ∫ φ e^{−Nx² + √N x h(√N x)} → φ(0) ∫ e^{−y² + y h(y)} dy`; for `h(0) = 0` the field has zero
trace on the zero set while the limit differs from the zero-field value `√π φ(0)` in general. -/
theorem boundaryLayer_field_limit {φ h : ℝ → ℝ} (hφ : Continuous φ) {B : ℝ}
    (hφB : ∀ x, |φ x| ≤ B) (hh : Continuous h) {M : ℝ} (hhM : ∀ y, |h y| ≤ M) :
    Tendsto (fun N : ℝ => √N * ∫ x, φ x * Real.exp (-N * x ^ 2 + √N * x * h (√N * x))) atTop
      (𝓝 (φ 0 * ∫ y : ℝ, Real.exp (-y ^ 2 + y * h y))) := by
  set g : ℝ → ℝ → ℝ := fun N y => φ (y / √N) * Real.exp (-y ^ 2 + y * h y) with hg
  have hrew : ∀ N : ℝ, 0 < N →
      √N * ∫ x, φ x * Real.exp (-N * x ^ 2 + √N * x * h (√N * x)) = ∫ y, g N y := by
    intro N hN
    have hsN : 0 < √N := Real.sqrt_pos.2 hN
    have hN2 : √N ^ 2 = N := Real.sq_sqrt hN.le
    have hpt : ∀ x : ℝ, φ x * Real.exp (-N * x ^ 2 + √N * x * h (√N * x)) = g N (√N * x) :=
      fun x => by
        simp only [hg]
        rw [mul_div_cancel_left₀ _ hsN.ne']
        congr 2
        linear_combination (x ^ 2) * hN2
    simp_rw [hpt]
    rw [Measure.integral_comp_mul_left (g N) (√N), abs_of_pos (inv_pos.2 hsN), smul_eq_mul]
    field_simp
  -- the dominating function `B e^{M²/4}(e^{−(y−M/2)²} + e^{−(y+M/2)²}) ≥ B e^{−y² + M|y|}`
  set dom : ℝ → ℝ := fun y => B * (Real.exp (M ^ 2 / 4) *
    (Real.exp (-(1 : ℝ) * (y - M / 2) ^ 2) + Real.exp (-(1 : ℝ) * (y + M / 2) ^ 2))) with hdomdef
  have hdom : Integrable dom :=
    ((((integrable_exp_neg_mul_sq one_pos).comp_sub_right (M / 2)).add
      ((integrable_exp_neg_mul_sq one_pos).comp_add_right (M / 2))).const_mul
        (Real.exp (M ^ 2 / 4))).const_mul B
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hφB 0)
  have hexp : ∀ y : ℝ, Real.exp (-y ^ 2 + M * |y|) ≤ Real.exp (M ^ 2 / 4) *
      (Real.exp (-(1 : ℝ) * (y - M / 2) ^ 2) + Real.exp (-(1 : ℝ) * (y + M / 2) ^ 2)) := by
    intro y
    rcases le_or_gt 0 y with hy | hy
    · rw [abs_of_nonneg hy]
      have : Real.exp (-y ^ 2 + M * y) =
          Real.exp (M ^ 2 / 4) * Real.exp (-(1 : ℝ) * (y - M / 2) ^ 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [this]
      exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (Real.exp_pos _).le)
        (Real.exp_pos _).le
    · rw [abs_of_neg hy]
      have : Real.exp (-y ^ 2 + M * -y) =
          Real.exp (M ^ 2 / 4) * Real.exp (-(1 : ℝ) * (y + M / 2) ^ 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [this]
      exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (Real.exp_pos _).le)
        (Real.exp_pos _).le
  have hlim : Tendsto (fun N : ℝ => ∫ y, g N y) atTop
      (𝓝 (∫ y : ℝ, φ 0 * Real.exp (-y ^ 2 + y * h y))) := by
    refine tendsto_integral_filter_of_dominated_convergence dom ?_ ?_ hdom ?_
    · exact Eventually.of_forall fun N =>
        ((hφ.comp (by fun_prop)).mul (Real.continuous_exp.comp (by fun_prop))).aestronglyMeasurable
    · refine Eventually.of_forall fun N => Eventually.of_forall fun y => ?_
      simp only [hg, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), hdomdef]
      have hyh : y * h y ≤ M * |y| := by
        calc y * h y ≤ |y * h y| := le_abs_self _
          _ = |y| * |h y| := abs_mul _ _
          _ ≤ |y| * M := mul_le_mul_of_nonneg_left (hhM y) (abs_nonneg _)
          _ = M * |y| := mul_comm _ _
      calc |φ (y / √N)| * Real.exp (-y ^ 2 + y * h y)
          ≤ B * Real.exp (-y ^ 2 + M * |y|) :=
            mul_le_mul (hφB _) (Real.exp_le_exp.2 (by linarith)) (Real.exp_pos _).le hB0
        _ ≤ B * (Real.exp (M ^ 2 / 4) * (Real.exp (-(1 : ℝ) * (y - M / 2) ^ 2) +
            Real.exp (-(1 : ℝ) * (y + M / 2) ^ 2))) :=
            mul_le_mul_of_nonneg_left (hexp y) hB0
    · refine Eventually.of_forall fun y => ?_
      simp only [hg]
      refine ((hφ.tendsto 0).comp ?_).mul_const _
      have : Tendsto (fun N : ℝ => y / √N) atTop (𝓝 0) := by
        have h1 : Tendsto (fun N : ℝ => y * (√N)⁻¹) atTop (𝓝 (y * 0)) :=
          (tendsto_inv_atTop_zero.comp tendsto_sqrt_atTop).const_mul _
        rw [mul_zero] at h1
        exact h1.congr fun N => (div_eq_mul_inv _ _).symm
      simpa using this
  rw [integral_const_mul] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with N hN
  exact (hrew N hN).symm

end Grammar
