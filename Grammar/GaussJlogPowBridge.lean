/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.GammaOneLogMoments
import Grammar.PolynomialEngineCoefficients

/-!
# The Gaussian log moments through the Gamma log moments

`J_k = ∫₀^∞ h(x) log^k x/x dx` (`gaussJlogPow k`, `h = e^{−x²/2} − 1_{(0,1]}`) for every `k`
(Astra round 21, the `J_k` bridge, stage 2): the substitution `x² = 2y` gives
`J_k = 2^{−(k+1)} ∫₀^∞ (e^{−y} − 1_{(0,½]}(y)) (log 2 + log y)^k/y dy` (`gaussJlogPow_eq_half_cut`,
DCXXXVIII's route for every power), the cutoff moves from `½` to `1` at the cost of
`∫_{½}^1 (log 2 + log y)^k/y = log^{k+1}2/(k+1)`, and the binomial expansion against DCLXVIII's
renormalised integrals gives
★★★ `gaussJlogPow_eq_gammaOneLogMoment (k) :
J_k = 2^{−(k+1)} [Σ_{r ≤ k} C(k,r) log^{k−r}2 · G_{r+1}/(r+1) + log^{k+1}2/(k+1)]`.
Regressions: `k = 0, 1` reproduce `R₀ = (log 2 − γ)/2` and `J = R₀²/2 + π²/48`
(`gaussJlogPow_zero_eq`, `gaussJlogPow_one_eq`), and `J₂`, `J₃` are explicit in `G₃`, `G₄`
(`gaussJlog2_eq_gammaOneLogMoment`, `gaussJlog3_eq_gammaOneLogMoment`): every lower coefficient
of `enginePoly L` is now a polynomial in `log 2, γ, π², G₃, G₄, …` and the residual masses.
Examples_slop §2.
Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology
open Finset (range)

namespace Grammar

/-! ### The substitution `x² = 2y` -/

/-- `J_k = 2^{−(k+1)} ∫₀^∞ (e^{−y} − 1_{(0,½]}(y)) (log 2 + log y)^k/y dy`. -/
theorem gaussJlogPow_eq_half_cut (k : ℕ) :
    gaussJlogPow k = (∫ y in Ioi (0 : ℝ),
      (Real.exp (-y) - (Ioc 0 (1 / 2)).indicator 1 y) * (Real.log 2 + Real.log y) ^ k / y) /
        2 ^ (k + 1) := by
  set g : ℝ → ℝ := fun w =>
    (Real.exp (-w / 2) - (Ioc 0 1).indicator 1 w) * Real.log w ^ k / (2 ^ (k + 1) * w) with hg
  have h1 : gaussJlogPow k = ∫ w in Ioi (0 : ℝ), g w := by
    unfold gaussJlogPow
    rw [← integral_comp_rpow_Ioi_of_pos (g := g) (p := 2) two_pos]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx' : (0 : ℝ) < x := hx
    simp only [hg, smul_eq_mul, Real.rpow_two]
    rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]
    have hind : (Ioc (0 : ℝ) 1).indicator (1 : ℝ → ℝ) (x ^ 2) =
        (Ioc (0 : ℝ) 1).indicator 1 x := by
      by_cases h : x ≤ 1
      · rw [indicator_of_mem (mem_Ioc.2 ⟨by positivity, by nlinarith⟩ : x ^ 2 ∈ Ioc (0 : ℝ) 1),
          indicator_of_mem (mem_Ioc.2 ⟨hx', h⟩ : x ∈ Ioc (0 : ℝ) 1)]
        rfl
      · rw [indicator_of_notMem (fun hm : x ^ 2 ∈ Ioc (0 : ℝ) 1 => h (by nlinarith [hm.2])),
          indicator_of_notMem (fun hm : x ∈ Ioc (0 : ℝ) 1 => h hm.2)]
    unfold gaussH
    rw [hind, Real.log_pow, Nat.cast_ofNat, mul_pow, pow_succ]
    field_simp
    ring
  have h2 : ∫ w in Ioi (0 : ℝ), g w = 2 * ∫ y in Ioi (0 : ℝ), g (2 * y) := by
    rw [integral_comp_mul_left_Ioi g 0 two_pos, mul_zero, smul_eq_mul]
    ring
  have e : ∀ y ∈ Ioi (0 : ℝ), g (2 * y) =
      ((Real.exp (-y) - (Ioc 0 (1 / 2)).indicator 1 y) * (Real.log 2 + Real.log y) ^ k / y) /
        (2 * 2 ^ (k + 1)) := by
    intro y hy
    have hy' : (0 : ℝ) < y := hy
    simp only [hg]
    have hind : (Ioc (0 : ℝ) 1).indicator (1 : ℝ → ℝ) (2 * y) =
        (Ioc (0 : ℝ) (1 / 2)).indicator 1 y := by
      by_cases h : y ≤ 1 / 2
      · rw [indicator_of_mem (mem_Ioc.2 ⟨by positivity, by linarith⟩ : 2 * y ∈ Ioc (0 : ℝ) 1),
          indicator_apply, if_pos (mem_Ioc.2 ⟨hy', h⟩ : y ∈ Ioc (0 : ℝ) (1 / 2))]
        rfl
      · rw [indicator_of_notMem (fun hm : 2 * y ∈ Ioc (0 : ℝ) 1 => h (by linarith [hm.2])),
          indicator_of_notMem (fun hm : y ∈ Ioc (0 : ℝ) (1 / 2) => h hm.2)]
    rw [hind, Real.log_mul two_ne_zero hy'.ne', show -(2 * y) / 2 = -y by ring]
    field_simp
  rw [h1, h2, setIntegral_congr_fun measurableSet_Ioi e, integral_div]
  field_simp

/-! ### The cutoff shift and the binomial expansion -/

/-- The half-cut integrand splits into the unit-cut one and the piece on `(½, 1]`. -/
theorem half_cut_split_pow (k : ℕ) {y : ℝ} (hy : 0 < y) :
    (Real.exp (-y) - (Ioc 0 (1 / 2)).indicator 1 y) * (Real.log 2 + Real.log y) ^ k / y =
      (Real.exp (-y) - (Ioc 0 1).indicator 1 y) * (Real.log 2 + Real.log y) ^ k / y +
        (Ioc (1 / 2 : ℝ) 1).indicator (fun y => (Real.log 2 + Real.log y) ^ k / y) y := by
  rcases le_or_gt y (1 / 2) with h | h
  · have hm₁ : y ∈ Ioc (0 : ℝ) (1 / 2) := mem_Ioc.2 ⟨hy, h⟩
    have hm₂ : y ∈ Ioc (0 : ℝ) 1 := mem_Ioc.2 ⟨hy, by linarith⟩
    rw [indicator_of_mem hm₁, indicator_of_mem hm₂,
      indicator_of_notMem (fun hm : y ∈ Ioc (1 / 2 : ℝ) 1 => absurd h (not_le.2 hm.1)), add_zero]
  · have hm₁ : y ∉ Ioc (0 : ℝ) (1 / 2) := fun hm => absurd hm.2 (not_le.2 h)
    rw [indicator_of_notMem hm₁]
    rcases le_or_gt y 1 with h1 | h1
    · rw [indicator_of_mem (mem_Ioc.2 ⟨hy, h1⟩ : y ∈ Ioc (0 : ℝ) 1),
        indicator_of_mem (mem_Ioc.2 ⟨h, h1⟩ : y ∈ Ioc (1 / 2 : ℝ) 1), Pi.one_apply]
      ring
    · rw [indicator_of_notMem (fun hm : y ∈ Ioc (0 : ℝ) 1 => absurd hm.2 (not_le.2 h1)),
        indicator_of_notMem (fun hm : y ∈ Ioc (1 / 2 : ℝ) 1 => absurd hm.2 (not_le.2 h1))]
      simp

/-- The binomial expansion of the unit-cut integrand. -/
theorem unit_cut_binomial (k : ℕ) (y : ℝ) :
    (Real.exp (-y) - (Ioc 0 1).indicator 1 y) * (Real.log 2 + Real.log y) ^ k / y =
      ∑ r ∈ range (k + 1), (k.choose r : ℝ) * Real.log 2 ^ (k - r) *
        ((Real.exp (-y) - (Ioc 0 1).indicator 1 y) * Real.log y ^ r / y) := by
  rw [add_comm (Real.log 2), add_pow, Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun r _ => ?_
  ring

theorem integrableOn_unit_cut_pow (k : ℕ) :
    IntegrableOn (fun y : ℝ =>
      (Real.exp (-y) - (Ioc 0 1).indicator 1 y) * (Real.log 2 + Real.log y) ^ k / y) (Ioi 0) := by
  have h : IntegrableOn (fun y : ℝ => ∑ r ∈ range (k + 1), (k.choose r : ℝ) * Real.log 2 ^ (k - r) *
      ((Real.exp (-y) - (Ioc 0 1).indicator 1 y) * Real.log y ^ r / y)) (Ioi 0) :=
    integrable_finsetSum _ fun r _ => (integrableOn_renormalised_log_pow r).const_mul _
  exact h.congr_fun (fun y _ => (unit_cut_binomial k y).symm) measurableSet_Ioi

/-- `∫₀^∞ (e^{−y} − 1_{(0,1]}) (log 2 + log y)^k/y = Σ_r C(k,r) log^{k−r}2 · G_{r+1}/(r+1)`. -/
theorem integral_unit_cut_pow (k : ℕ) :
    ∫ y in Ioi (0 : ℝ),
        (Real.exp (-y) - (Ioc 0 1).indicator 1 y) * (Real.log 2 + Real.log y) ^ k / y =
      ∑ r ∈ range (k + 1), (k.choose r : ℝ) * Real.log 2 ^ (k - r) *
        (gammaOneLogMoment (r + 1) / (r + 1)) := by
  rw [setIntegral_congr_fun measurableSet_Ioi fun y _ => unit_cut_binomial k y,
    integral_finsetSum _ fun r _ => (integrableOn_renormalised_log_pow r).const_mul _]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [integral_const_mul, integral_renormalised_exp_log_pow]

theorem hasDerivAt_log_two_add_log_pow (k : ℕ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun y : ℝ => (Real.log 2 + Real.log y) ^ (k + 1) / (k + 1))
      ((Real.log 2 + Real.log y) ^ k / y) y := by
  have hl : HasDerivAt (fun y : ℝ => Real.log 2 + Real.log y) y⁻¹ y :=
    (Real.hasDerivAt_log hy.ne').const_add _
  refine ((hl.pow (k + 1)).div_const ((k : ℝ) + 1)).congr_deriv ?_
  simp only [Nat.add_sub_cancel]
  push_cast
  field_simp

theorem integrableOn_log_two_add_log_pow_div (k : ℕ) :
    IntegrableOn (fun y : ℝ => (Real.log 2 + Real.log y) ^ k / y) (Ioc (1 / 2) 1) := by
  rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
  refine ContinuousOn.intervalIntegrable ?_
  refine ContinuousOn.div
    ((continuousOn_const.add (Real.continuousOn_log.mono fun y hy => ?_)).pow k)
    continuousOn_id fun y hy => ?_
  · rw [uIcc_of_le (by norm_num)] at hy
    exact mem_compl_singleton_iff.2 (ne_of_gt (lt_of_lt_of_le (by norm_num) hy.1))
  · rw [uIcc_of_le (by norm_num)] at hy
    exact ne_of_gt (lt_of_lt_of_le (by norm_num) hy.1)

/-- `∫_{½}^1 (log 2 + log y)^k/y dy = log^{k+1}2/(k+1)`. -/
theorem integral_log_two_add_log_pow_div (k : ℕ) :
    ∫ y in Ioc (1 / 2 : ℝ) 1, (Real.log 2 + Real.log y) ^ k / y =
      Real.log 2 ^ (k + 1) / (k + 1) := by
  have hpos : ∀ y ∈ uIcc (1 / 2 : ℝ) 1, 0 < y := fun y hy => by
    rw [uIcc_of_le (by norm_num)] at hy
    exact lt_of_lt_of_le (by norm_num) hy.1
  rw [← intervalIntegral.integral_of_le (by norm_num),
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun y hy => hasDerivAt_log_two_add_log_pow k (hpos y hy))
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).2
        (integrableOn_log_two_add_log_pow_div k))]
  rw [Real.log_one, add_zero, one_div, Real.log_inv, add_neg_cancel, zero_pow (Nat.succ_ne_zero k),
    zero_div, sub_zero]

/-- ★★★ **The bridge**: for every `k`,
`J_k = 2^{−(k+1)} [Σ_{r ≤ k} C(k,r) log^{k−r}2 · G_{r+1}/(r+1) + log^{k+1}2/(k+1)]`. -/
theorem gaussJlogPow_eq_gammaOneLogMoment (k : ℕ) :
    gaussJlogPow k = (1 / (2 : ℝ) ^ (k + 1)) *
      ((∑ r ∈ range (k + 1), (k.choose r : ℝ) * Real.log 2 ^ (k - r) *
        (gammaOneLogMoment (r + 1) / (r + 1))) + Real.log 2 ^ (k + 1) / (k + 1)) := by
  rw [gaussJlogPow_eq_half_cut]
  have hind : IntegrableOn ((Ioc (1 / 2 : ℝ) 1).indicator
      (fun y : ℝ => (Real.log 2 + Real.log y) ^ k / y)) (Ioi 0) :=
    ((integrableOn_log_two_add_log_pow_div k).integrable_indicator measurableSet_Ioc).integrableOn
  rw [setIntegral_congr_fun measurableSet_Ioi fun y (hy : (0 : ℝ) < y) => half_cut_split_pow k hy,
    integral_add (integrableOn_unit_cut_pow k) hind, integral_unit_cut_pow,
    setIntegral_indicator measurableSet_Ioc,
    show Ioi (0 : ℝ) ∩ Ioc (1 / 2) 1 = Ioc (1 / 2) 1 from
      inter_eq_right.2 fun y (hy : y ∈ Ioc (1 / 2 : ℝ) 1) => (show (0 : ℝ) < y by linarith [hy.1]),
    integral_log_two_add_log_pow_div]
  ring

/-! ### Regressions and the new moments -/

/-- `k = 0` reproduces `R₀ = (log 2 − γ)/2`. -/
theorem gaussJlogPow_zero_eq :
    gaussJlogPow 0 = (Real.log 2 - Real.eulerMascheroniConstant) / 2 := by
  rw [gaussJlogPow_eq_gammaOneLogMoment]
  simp only [Finset.sum_range_one, Nat.choose_self, Nat.cast_one, zero_add, Nat.sub_zero, pow_zero,
    one_mul, gammaOneLogMoment_one, Nat.cast_zero, div_one, pow_one]
  ring

/-- `k = 1` reproduces `J = R₀²/2 + π²/48`. -/
theorem gaussJlogPow_one_eq :
    gaussJlogPow 1 =
      ((Real.log 2 - Real.eulerMascheroniConstant) / 2) ^ 2 / 2 + Real.pi ^ 2 / 48 := by
  rw [gaussJlogPow_eq_gammaOneLogMoment]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose_zero_right, Nat.choose_self,
    Nat.cast_one, zero_add, Nat.sub_zero, Nat.sub_self, pow_zero, pow_one, one_mul, mul_one,
    Nat.reduceAdd, gammaOneLogMoment_one, gammaOneLogMoment_two, Nat.cast_zero, div_one]
  ring

/-- `J₂ = [log³2 + 3 log²2 · G₁ + (3/2) log 2 · G₂ + G₃/3]/8 + log³2/24` — explicit in `G₃`. -/
theorem gaussJlog2_eq_gammaOneLogMoment :
    gaussJlog2 = (1 / 8) * ((Real.log 2 ^ 2 * gammaOneLogMoment 1 +
      2 * Real.log 2 * (gammaOneLogMoment 2 / 2) + gammaOneLogMoment 3 / 3) +
      Real.log 2 ^ 3 / 3) := by
  rw [← gaussJlogPow_two, gaussJlogPow_eq_gammaOneLogMoment]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose_zero_right, Nat.choose_self,
    Nat.choose_one_right, Nat.cast_one, Nat.cast_ofNat, zero_add, Nat.sub_zero, Nat.sub_self,
    pow_zero, one_mul, mul_one]
  norm_num

/-- `J₃` explicit in `G₃`, `G₄`. -/
theorem gaussJlog3_eq_gammaOneLogMoment :
    gaussJlog3 = (1 / 16) * ((Real.log 2 ^ 3 * gammaOneLogMoment 1 +
      3 * Real.log 2 ^ 2 * (gammaOneLogMoment 2 / 2) + 3 * Real.log 2 * (gammaOneLogMoment 3 / 3) +
      gammaOneLogMoment 4 / 4) + Real.log 2 ^ 4 / 4) := by
  rw [← gaussJlogPow_three, gaussJlogPow_eq_gammaOneLogMoment]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose_zero_right, Nat.choose_self,
    Nat.choose_one_right, Nat.cast_one, Nat.cast_ofNat, zero_add, Nat.sub_zero, Nat.sub_self,
    pow_zero, one_mul, mul_one]
  norm_num

end Grammar
