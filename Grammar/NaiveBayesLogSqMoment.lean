/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.CrossingFlatDepth
import Grammar.GammaSecondDerivHalf

/-!
# The Gaussian second log moment `m₂ = ∫ e^{−z²/2} log²|z| dz = √(2π)(g²/4 + π²/8)`, `g = γ + log 2`

The naive-Bayes surrogate's `N^{−3/2}log²N` data (examples_slop §6) involve
`m₂ = ∫_ℝ e^{−z²/2} (log |z|)² dz`.  By evenness and the substitution `z = √(2t)`,

  `m₂ = (1/(2√2)) ∫₀^∞ e^{−t} t^{−1/2} (log 2 + log t)² dt
      = (1/(2√2)) [log²2 · H₀ + 2 log 2 · H₁ + H₂]`,

with the Gamma log-moments `H_j = ∫₀^∞ e^{−t}t^{−1/2}log^j t = Γ^{(j)}(½)` of `CrossingFlatDepth`
(`H₀ = √π`, `H₁ = −√π(γ + 2 log 2)`) and DCVIII (`H₂ = √π((γ + 2 log 2)² + π²/2)`), whence

  `m₂ = √(2π) ((γ + log 2)²/4 + π²/8)`   (★★★ `integral_gaussian_log_abs_sq`).

Astra round-15 target 2.  Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

/-- The half-line integral `∫₀^∞ e^{−z²/2} (log z)² dz = (1/(4√2))[log²2 H₀ + 2 log 2 H₁ + H₂]`. -/
theorem integral_Ioi_exp_neg_half_sq_mul_log_sq :
    ∫ z in Ioi (0 : ℝ), Real.exp (-z ^ 2 / 2) * Real.log z ^ 2 =
      1 / (4 * Real.sqrt 2) * (Real.log 2 ^ 2 * gammaLogMoment 0 +
        2 * Real.log 2 * gammaLogMoment 1 + gammaLogMoment 2) := by
  -- `z ↦ z²`: the integrand is `2z · g(z²)` with `g(y) = e^{−y/2}(log y)²/(8√y)`
  set g : ℝ → ℝ := fun y => Real.exp (-y / 2) * Real.log y ^ 2 / (8 * Real.sqrt y) with hg
  have h1 : ∫ z in Ioi (0 : ℝ), Real.exp (-z ^ 2 / 2) * Real.log z ^ 2 =
      ∫ y in Ioi (0 : ℝ), g y := by
    rw [← integral_comp_rpow_Ioi_of_pos (g := g) (p := 2) two_pos]
    refine setIntegral_congr_fun measurableSet_Ioi fun z hz => ?_
    have hz' : (0 : ℝ) < z := hz
    simp only [hg, smul_eq_mul, Real.rpow_two]
    rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.log_pow, Nat.cast_ofNat,
      Real.sqrt_sq hz'.le]
    field_simp
    ring
  -- `y = 2t`
  have h2 : ∫ y in Ioi (0 : ℝ), g y = 2 * ∫ t in Ioi (0 : ℝ), g (2 * t) := by
    rw [integral_comp_mul_left_Ioi g 0 two_pos, mul_zero, smul_eq_mul]
    ring
  have e : ∀ t ∈ Ioi (0 : ℝ), g (2 * t) =
      1 / (8 * Real.sqrt 2) *
        (Real.log 2 ^ 2 * (Real.exp (-t) * t ^ (-(1 / 2 : ℝ)) * Real.log t ^ 0) +
        2 * Real.log 2 * (Real.exp (-t) * t ^ (-(1 / 2 : ℝ)) * Real.log t ^ 1) +
        Real.exp (-t) * t ^ (-(1 / 2 : ℝ)) * Real.log t ^ 2) := by
    intro t ht
    have ht' : (0 : ℝ) < t := ht
    simp only [hg]
    rw [Real.log_mul two_ne_zero ht'.ne', show -(2 * t) / 2 = -t by ring,
      Real.sqrt_mul (by norm_num) t, Real.sqrt_eq_rpow t, Real.rpow_neg ht'.le]
    have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    have hr : 0 < t ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos ht' _
    field_simp
    ring
  rw [h1, h2, setIntegral_congr_fun measurableSet_Ioi e, integral_const_mul]
  have hI : ∀ j : ℕ, IntegrableOn
      (fun t : ℝ => Real.exp (-t) * t ^ (-(1 / 2 : ℝ)) * Real.log t ^ j) (Ioi 0) :=
    integrableOn_wt_log_pow
  have h01 : Integrable (fun t : ℝ =>
      Real.log 2 ^ 2 * (Real.exp (-t) * t ^ (-(1 / 2 : ℝ)) * Real.log t ^ 0) +
        2 * Real.log 2 * (Real.exp (-t) * t ^ (-(1 / 2 : ℝ)) * Real.log t ^ 1))
      (volume.restrict (Ioi 0)) := ((hI 0).const_mul _).add ((hI 1).const_mul _)
  rw [integral_add h01 (hI 2), integral_add ((hI 0).const_mul _) ((hI 1).const_mul _),
    integral_const_mul, integral_const_mul]
  unfold gammaLogMoment
  ring

theorem gaussian_log_abs_sq_even (z : ℝ) :
    Real.exp (-z ^ 2 / 2) * Real.log |z| ^ 2 =
      (fun t : ℝ => Real.exp (-t ^ 2 / 2) * Real.log t ^ 2) |z| := by
  simp only [sq_abs]

/-- ★★★ **The Gaussian second log moment**:
`∫ e^{−z²/2} (log |z|)² dz = √(2π)((γ + log 2)²/4 + π²/8)`. -/
theorem integral_gaussian_log_abs_sq :
    ∫ z : ℝ, Real.exp (-z ^ 2 / 2) * Real.log |z| ^ 2 =
      Real.sqrt (2 * Real.pi) *
        ((Real.eulerMascheroniConstant + Real.log 2) ^ 2 / 4 + Real.pi ^ 2 / 8) := by
  have h := integral_comp_abs (f := fun t : ℝ => Real.exp (-t ^ 2 / 2) * Real.log t ^ 2)
  simp only [sq_abs] at h
  rw [h, integral_Ioi_exp_neg_half_sq_mul_log_sq]
  have hS : Real.log 2 ^ 2 * gammaLogMoment 0 + 2 * Real.log 2 * gammaLogMoment 1 +
      gammaLogMoment 2 = Real.sqrt Real.pi *
        ((Real.eulerMascheroniConstant + Real.log 2) ^ 2 + Real.pi ^ 2 / 2) := by
    rw [gammaLogMoment_zero, gammaLogMoment_one, gammaLogMoment_two]
    ring
  rw [hS]
  have h2 : Real.sqrt (2 * Real.pi) = Real.sqrt 2 * Real.sqrt Real.pi :=
    Real.sqrt_mul (by norm_num) _
  have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsq2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  rw [h2]
  set T := Real.sqrt 2 with hT
  clear_value T
  have key : 1 / (4 * T) * 2 = T / 4 := by
    field_simp
    first
      | linear_combination (-4) * hsq2
      | linear_combination 4 * hsq2
      | nlinarith [hsq2]
  calc 2 * (1 / (4 * T) * (Real.sqrt Real.pi *
        ((Real.eulerMascheroniConstant + Real.log 2) ^ 2 + Real.pi ^ 2 / 2)))
      = (1 / (4 * T) * 2) * (Real.sqrt Real.pi *
        ((Real.eulerMascheroniConstant + Real.log 2) ^ 2 + Real.pi ^ 2 / 2)) := by ring
    _ = T / 4 * (Real.sqrt Real.pi *
        ((Real.eulerMascheroniConstant + Real.log 2) ^ 2 + Real.pi ^ 2 / 2)) := by rw [key]
    _ = T * Real.sqrt Real.pi *
        ((Real.eulerMascheroniConstant + Real.log 2) ^ 2 / 4 + Real.pi ^ 2 / 8) := by ring

end Grammar
