/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.DepthThreeConstExact
import Grammar.GaussianDepthAllThirdCoeff

/-!
# The third logarithmic coefficient of the Gaussian DLN in closed form at every depth

DCXXXVI proved `√N Z_L = A_L ℓ^{L−1} + B_L ℓ^{L−2} + C_L ℓ^{L−3} + O((1+ℓ)^{L−4})` with `C_L`
given by the recursion `thirdCoeff` (`thirdCoeff m = C_{m+4}`); DCXLV made `C₃` exact.  Here the
recursion is solved (★★★ `thirdCoeff_eq_closed`):

  `C_L = [D_L² + (L+3)π²/6] / (2 (L−3)! s^{L−1})`,  `D_L = (L+1) log 2 − (L−1)γ`,  `s = √(2π)`,

i.e. with `T_L = (L−3)! s^{L−1} C_L`, `T_{L+1} − T_L = 2 D_L R₀ + 4J` and `4J = 2R₀² + π²/12`,
`D_{L+1} = D_L + 2R₀` (the Mellin-jet coefficient of `ε²` in `Γ(½−ε)2^{(L−1)ε}Γ(1+ε)^L`).  Hence
the three leading coefficients of `P_{L−1}` in the note's eq. dln_gauss are explicit at every
depth `L ≥ 3` (examples_slop §2; Astra round-14 target 1).  Zero `sorry`/`axiom`.
-/

namespace Grammar

/-- `D_L = (L+1) log 2 − (L−1) γ` at `L = m + 4`. -/
noncomputable def thirdCoeffD (m : ℕ) : ℝ :=
  ((m : ℝ) + 5) * Real.log 2 - ((m : ℝ) + 3) * Real.eulerMascheroniConstant

/-- The closed form at `L = m + 4`: `[D² + (m+7)π²/6] / (2 (m+1)! s^{m+3})`. -/
noncomputable def thirdCoeffClosed (m : ℕ) : ℝ :=
  (thirdCoeffD m ^ 2 + ((m : ℝ) + 7) * Real.pi ^ 2 / 6) /
    (2 * ((m + 1).factorial : ℝ) * Real.sqrt (2 * Real.pi) ^ (m + 3))

theorem thirdCoeffD_succ (m : ℕ) : thirdCoeffD (m + 1) = thirdCoeffD m + 2 * gaussR₀ := by
  unfold thirdCoeffD gaussR₀
  push_cast
  ring

/-- The base `C₄ = [D₄² + 7π²/6]/(2 s³)` from the exact `C₃`, `J`, `R₀`. -/
theorem thirdCoeff_zero_eq : thirdCoeff 0 = thirdCoeffClosed 0 := by
  unfold thirdCoeffClosed thirdCoeffD
  rw [thirdCoeff, depthThreeConst_eq, gaussJlog_eq]
  unfold gaussR₀
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  set S := Real.sqrt (2 * Real.pi) with hS
  have hpi : Real.pi = S ^ 2 / 2 := by rw [hS, Real.sq_sqrt (by positivity)]; ring
  clear_value S
  rw [hpi]
  simp only [Nat.factorial, Nat.cast_zero]
  field_simp
  ring

/-- The step: the recursion preserves the closed form. -/
theorem thirdCoeffClosed_succ (m : ℕ) :
    (thirdCoeffClosed m / (m + 2) + 2 * gaussCoeffB m * gaussR₀ +
      4 * (m + 3) * gaussCoeffA m * gaussJlog) / Real.sqrt (2 * Real.pi) =
      thirdCoeffClosed (m + 1) := by
  unfold thirdCoeffClosed gaussCoeffA gaussCoeffB
  rw [thirdCoeffD_succ, gaussJlog_eq]
  unfold thirdCoeffD gaussR₀
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hf1 : ((m + 1).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hf2 : ((m + 2).factorial : ℝ) = (m + 2) * ((m + 1).factorial : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hf3 : ((m + 3).factorial : ℝ) = (m + 3) * ((m + 2) * ((m + 1).factorial : ℝ)) := by
    rw [Nat.factorial_succ, Nat.factorial_succ]; push_cast; ring
  rw [hf3, hf2]
  set S := Real.sqrt (2 * Real.pi) with hS
  have hpi : Real.pi = S ^ 2 / 2 := by rw [hS, Real.sq_sqrt (by positivity)]; ring
  clear_value S
  rw [hpi]
  have hm2 : ((m : ℝ) + 2) ≠ 0 := by positivity
  have hm3 : ((m : ℝ) + 3) ≠ 0 := by positivity
  push_cast
  rw [pow_succ S (m + 3)]
  field_simp
  ring

/-- ★★★ **The third coefficient in closed form at every depth**:
`C_{m+4} = [((m+5) log 2 − (m+3)γ)² + (m+7)π²/6] / (2 (m+1)! √(2π)^{m+3})`. -/
theorem thirdCoeff_eq_closed (m : ℕ) : thirdCoeff m = thirdCoeffClosed m := by
  induction m with
  | zero => exact thirdCoeff_zero_eq
  | succ m ih =>
    rw [thirdCoeff, ih, thirdCoeffClosed_succ]

end Grammar
