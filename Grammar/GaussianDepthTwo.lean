/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.GaussianProductZeta

/-!
# The Gaussian-prior deep linear network at depth two: the exact conditional reduction

For the normalised Gaussian prior on `ℝ²` and the phase `K = (xy)²/2`, the partition function

  `Z_N = (2π)^{−1} ∫_{ℝ²} e^{−N(xy)²/2} e^{−(x²+y²)/2} dx dy`

reduces exactly, by the Gaussian integral in `y` at fixed `x`, to the one-dimensional integral

  `Z_N = (2π)^{−1/2} ∫_ℝ e^{−x²/2} / √(1 + N x²) dx`  (★★★ `gaussLaplace2_eq_integral`),

with no Bessel functions and no product-density theorem (examples_slop §2, eq. dln_gauss at `L = 2`;
Astra round-4 target 1).  The two-term expansion
`Z_N = (log N + 3 log 2 − γ)/√(2πN) + O(N^{−3/2} log N)` follows from this representation by the
`J(ε)` route of the consult in `Grammar.GaussianDepthTwoExpansion`.
Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

/-- The depth-two Gaussian partition function with the normalised prior. -/
noncomputable def gaussLaplace2 (N : ℝ) : ℝ :=
  ∫ w : ℝ × ℝ, Real.exp (-N * (w.1 * w.2) ^ 2 / 2) *
    (Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / 2) / (2 * Real.pi))

/-- The conditional Gaussian integral: `∫ e^{−(1 + N x²) y²/2} dy = √(2π/(1 + N x²))`. -/
theorem integral_exp_cond {c : ℝ} (hc : 0 < c) :
    ∫ y : ℝ, Real.exp (-c * y ^ 2 / 2) = Real.sqrt (2 * Real.pi / c) := by
  have h := integral_gaussian (c / 2)
  have e : (fun y : ℝ => Real.exp (-c * y ^ 2 / 2)) = fun y => Real.exp (-(c / 2) * y ^ 2) := by
    funext y; congr 1; ring
  rw [e, h]
  congr 1
  field_simp

theorem integrable_gaussLaplace2 (N : ℝ) (hN : 0 ≤ N) :
    Integrable fun w : ℝ × ℝ => Real.exp (-N * (w.1 * w.2) ^ 2 / 2) *
      (Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / 2) / (2 * Real.pi)) := by
  have hg : Integrable fun x : ℝ => Real.exp (-x ^ 2 / 2) := by
    have := integrable_exp_neg_mul_sq (b := 1 / 2) (by norm_num)
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only
    congr 1
    ring
  have hprod : Integrable (fun w : ℝ × ℝ => Real.exp (-w.1 ^ 2 / 2) * Real.exp (-w.2 ^ 2 / 2))
      (volume.prod volume) := hg.mul_prod hg
  rw [Measure.volume_eq_prod]
  refine (hprod.const_mul (1 / (2 * Real.pi))).mono' ?_ ?_
  · exact (Measurable.aestronglyMeasurable (by fun_prop))
  · refine Eventually.of_forall fun w => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h1 : Real.exp (-N * (w.1 * w.2) ^ 2 / 2) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg (w.1 * w.2)])
    have h2 : Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / 2) =
        Real.exp (-w.1 ^ 2 / 2) * Real.exp (-w.2 ^ 2 / 2) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [h2]
    have h3 : 0 ≤ Real.exp (-w.1 ^ 2 / 2) * Real.exp (-w.2 ^ 2 / 2) / (2 * Real.pi) := by positivity
    calc Real.exp (-N * (w.1 * w.2) ^ 2 / 2) *
          (Real.exp (-w.1 ^ 2 / 2) * Real.exp (-w.2 ^ 2 / 2) / (2 * Real.pi))
        ≤ 1 * (Real.exp (-w.1 ^ 2 / 2) * Real.exp (-w.2 ^ 2 / 2) / (2 * Real.pi)) :=
          mul_le_mul_of_nonneg_right h1 h3
      _ = 1 / (2 * Real.pi) * (Real.exp (-w.1 ^ 2 / 2) * Real.exp (-w.2 ^ 2 / 2)) := by ring

/-- ★★★ **The exact conditional reduction at depth two**:
`Z_N = (2π)^{−1/2} ∫_ℝ e^{−x²/2}/√(1 + N x²) dx` for `N ≥ 0`. -/
theorem gaussLaplace2_eq_integral {N : ℝ} (hN : 0 ≤ N) :
    gaussLaplace2 N = (Real.sqrt (2 * Real.pi))⁻¹ *
      ∫ x : ℝ, Real.exp (-x ^ 2 / 2) / Real.sqrt (1 + N * x ^ 2) := by
  unfold gaussLaplace2
  rw [Measure.volume_eq_prod, integral_prod _ (by
    have := integrable_gaussLaplace2 N hN
    rwa [Measure.volume_eq_prod] at this), ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  have hc : 0 < 1 + N * x ^ 2 := by positivity
  have hpt : ∀ y : ℝ, Real.exp (-N * (x * y) ^ 2 / 2) *
      (Real.exp (-(x ^ 2 + y ^ 2) / 2) / (2 * Real.pi)) =
      (Real.exp (-x ^ 2 / 2) / (2 * Real.pi)) * Real.exp (-(1 + N * x ^ 2) * y ^ 2 / 2) := by
    intro y
    have e1 : Real.exp (-N * (x * y) ^ 2 / 2) * (Real.exp (-(x ^ 2 + y ^ 2) / 2) / (2 * Real.pi)) =
        Real.exp (-N * (x * y) ^ 2 / 2 + -(x ^ 2 + y ^ 2) / 2) / (2 * Real.pi) := by
      rw [Real.exp_add]; ring
    have e2 : (Real.exp (-x ^ 2 / 2) / (2 * Real.pi)) * Real.exp (-(1 + N * x ^ 2) * y ^ 2 / 2) =
        Real.exp (-x ^ 2 / 2 + -(1 + N * x ^ 2) * y ^ 2 / 2) / (2 * Real.pi) := by
      rw [Real.exp_add]; ring
    rw [e1, e2]
    congr 2
    ring
  simp_rw [hpt]
  rw [integral_const_mul, integral_exp_cond hc]
  have hsq : Real.sqrt (2 * Real.pi / (1 + N * x ^ 2)) =
      Real.sqrt (2 * Real.pi) / Real.sqrt (1 + N * x ^ 2) := Real.sqrt_div' _ hc.le
  rw [hsq]
  have h2π : Real.sqrt (2 * Real.pi) * Real.sqrt (2 * Real.pi) = 2 * Real.pi :=
    Real.mul_self_sqrt (by positivity)
  have hs0 : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
  have hs1 : Real.sqrt (1 + N * x ^ 2) ≠ 0 := by positivity
  field_simp
  linear_combination h2π

end Grammar
