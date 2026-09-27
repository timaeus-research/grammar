/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.GaussianDepthTwoExpansion

/-!
# The crossing `x²y²` with the Gaussian prior: the two-term expansion

The paper's running example `K = x²y²/2` with the unnormalised Gaussian prior `e^{−|w|²/2}` on `ℝ²`
is the depth-two Gaussian deep linear network up to the prior's mass `2π`
(`crossingLaplace_eq_gaussLaplace2`), so its partition function has the two-term expansion

  `|Z_N − √(2π)(log N + 3 log 2 − γ)/√N| ≤ √(2π)(log(2N) + 3)/(2N√N)`  for `N ≥ 1/2`
  (★★ `crossingLaplace_two_term_bound`), hence
  `Z_N = √(2π)(log N + 3 log 2 − γ)/√N + O(N^{−3/2} log N)` (`crossingLaplace_two_term`),

a normalisation checkpoint against the blow-up model of `Grammar.BlowUpLaplaceExpansion`, whose
constant `5 log 2 − γ` differs by the `2 log 2` of the extra factor `e^{−Nx⁴/2}` (Astra round-7
target 1).  Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

/-- The crossing's partition function with the prior `e^{−|w|²/2}`. -/
noncomputable def crossingLaplace (N : ℝ) : ℝ :=
  ∫ w : ℝ × ℝ, Real.exp (-N * (w.1 * w.2) ^ 2 / 2) * Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / 2)

/-- ★ The crossing is the depth-two Gaussian network times the prior's mass `2π`. -/
theorem crossingLaplace_eq_gaussLaplace2 (N : ℝ) :
    crossingLaplace N = 2 * Real.pi * gaussLaplace2 N := by
  unfold crossingLaplace gaussLaplace2
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  simp only
  field_simp

/-- ★★ **The two-term expansion of the crossing with the Gaussian prior**: for `N ≥ 1/2`,
`|Z_N − √(2π)(log N + 3 log 2 − γ)/√N| ≤ √(2π)(log(2N) + 3)/(2N√N)`. -/
theorem crossingLaplace_two_term_bound {N : ℝ} (hN : 1 / 2 ≤ N) :
    |crossingLaplace N - Real.sqrt (2 * Real.pi) *
      (Real.log N + 3 * Real.log 2 - Real.eulerMascheroniConstant) / Real.sqrt N| ≤
      Real.sqrt (2 * Real.pi) * (Real.log (2 * N) + 3) / (2 * N * Real.sqrt N) := by
  have hN0 : 0 < N := by linarith
  have h := gaussLaplace2_two_term_bound hN
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have hsq : Real.sqrt (2 * Real.pi) * Real.sqrt (2 * Real.pi) = 2 * Real.pi :=
    Real.mul_self_sqrt (by positivity)
  rw [Real.sqrt_mul (by positivity) N] at h
  rw [crossingLaplace_eq_gaussLaplace2]
  generalize hsdef : Real.sqrt (2 * Real.pi) = s at h hs hsq ⊢
  rw [← hsq]
  have e : s * s * gaussLaplace2 N - s *
      (Real.log N + 3 * Real.log 2 - Real.eulerMascheroniConstant) / Real.sqrt N =
      s * s * (gaussLaplace2 N -
        (Real.log N + 3 * Real.log 2 - Real.eulerMascheroniConstant) / (s * Real.sqrt N)) := by
    field_simp
  rw [e, abs_mul, abs_of_pos (by positivity)]
  calc s * s * |gaussLaplace2 N -
        (Real.log N + 3 * Real.log 2 - Real.eulerMascheroniConstant) / (s * Real.sqrt N)|
      ≤ s * s * ((Real.log (2 * N) + 3) / (2 * N * (s * Real.sqrt N))) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = s * (Real.log (2 * N) + 3) / (2 * N * Real.sqrt N) := by
        field_simp

/-- ★★ `Z_N = √(2π)(log N + 3 log 2 − γ)/√N + O(N^{−3/2} log N)`. -/
theorem crossingLaplace_two_term :
    (fun N : ℝ => crossingLaplace N - Real.sqrt (2 * Real.pi) *
      (Real.log N + 3 * Real.log 2 - Real.eulerMascheroniConstant) / Real.sqrt N)
      =O[atTop] fun N => N ^ (-(3 / 2 : ℝ)) * Real.log N := by
  refine Asymptotics.IsBigO.of_bound (Real.sqrt (2 * Real.pi) * (5 / 2)) ?_
  filter_upwards [eventually_ge_atTop (3 : ℝ)] with N hN3
  have hN : 0 < N := by linarith
  have hlog : 1 ≤ Real.log N := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos _) (by linarith [Real.exp_one_lt_d9])
  have hb := crossingLaplace_two_term_bound (by linarith : 1 / 2 ≤ N)
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hN.le _) (by linarith))]
  refine hb.trans ?_
  have hlog2 : Real.log (2 * N) = Real.log 2 + Real.log N := Real.log_mul two_ne_zero hN.ne'
  have h2 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hpow : N ^ (-(3 / 2 : ℝ)) = 1 / (N * Real.sqrt N) := by
    rw [Real.rpow_neg hN.le, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hN,
      Real.rpow_one, Real.sqrt_eq_rpow, inv_eq_one_div]
  rw [hpow]
  calc Real.sqrt (2 * Real.pi) * (Real.log (2 * N) + 3) / (2 * N * Real.sqrt N)
      ≤ Real.sqrt (2 * Real.pi) * (5 * Real.log N) / (2 * N * Real.sqrt N) := by
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        have : 0 ≤ Real.sqrt (2 * Real.pi) := Real.sqrt_nonneg _
        nlinarith
    _ = Real.sqrt (2 * Real.pi) * (5 / 2) * (1 / (N * Real.sqrt N) * Real.log N) := by
        field_simp

end Grammar
