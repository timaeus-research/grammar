/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.DepthJetRecurrence

/-!
# Depth five in closed form: `D₅`, `E₅`, `Q₅` modulo the digamma symbols

The acceptance test of the digamma machinery.  At depth five the recurrence of `DepthJetRecurrence`
has `q_{5,0} = a := 6 log 2 − 4γ`, `q_{5,1} = 4π²/3`, `q_{5,2} = −λ₃`, `q_{5,3} = 20ψ₃`,
`q_{5,4} = −26ψ₄`, and gives (`depthJetCoeff_five_one … five`)

  `h₁ = a`, `h₂ = a²/2 + 2π²/3`, `h₃ = a³/6 + 2π²a/3 − λ₃/3`,
  `h₄ = a⁴/24 + π²a²/3 − aλ₃/3 + 2π⁴/9 + 5λ₄/6`,
  `h₅ = a⁵/120 + π²a³/9 − a²λ₃/6 + 2π⁴a/9 − 2π²λ₃/9 + 5aλ₄/6 − 13λ₅/60`,

with the real symbols `λ₄ = 6ψ₃ = (log Γ)''''(1)`, `λ₅ = 24ψ₄` (`gammaLogFourthOne`,
`gammaLogFifthOne`).  Through `enginePoly 5 = depthFivePoly` (`enginePoly_four/five`) and DCLXXV:

  ★★★ `depthFiveLinCoeff_eq : D₅ = h₃/(4π²)`, ★★★ `depthFiveConst_eq : E₅ = h₄/(4π²)`,
  ★★★ `residualMass_five_eq : Q₅ = h₅/(8π²)`,

and the regression `coeff_enginePoly_five_two` reproduces the all-depth `C₅`.  With
`λ₃ = −2ζ(3)`, `λ₄ = π⁴/15`, `λ₅ = −24ζ(5)`: `D₅ = 0.3553669`, `E₅ = 1.0205207`,
`Q₅ = 0.8766618` (`gauss_depth_recurrence_check.py`).  Astra round 26 target (iv).
Zero `sorry`/`axiom`.
-/

open Filter Topology Finset Polynomial

namespace Grammar

/-- `λ₄ = (log Γ)''''(1) = 6ψ₃` (real symbol). -/
noncomputable def gammaLogFourthOne : ℝ := (6 * psiOneCoeff 3).re

/-- `λ₅ = (log Γ)^{(5)}(1) = 24ψ₄` (real symbol). -/
noncomputable def gammaLogFifthOne : ℝ := (24 * psiOneCoeff 4).re

/-- The depth-five centring `a = 6 log 2 − 4γ`. -/
noncomputable def depthFiveCentring : ℝ := 6 * Real.log 2 - 4 * Real.eulerMascheroniConstant

/-! ### The logarithmic-derivative jet at depth five -/

theorem depthLogDerivCoeff_five_zero :
    depthLogDerivCoeff 5 0 = ((depthFiveCentring : ℝ) : ℂ) := by
  have hlog : Complex.log 2 = ((Real.log 2 : ℝ) : ℂ) := (Complex.ofNat_log).symm
  rw [depthLogDerivCoeff_zero, hlog]
  unfold depthFiveCentring
  push_cast
  ring

theorem depthLogDerivCoeff_five_one :
    depthLogDerivCoeff 5 1 = ((4 * Real.pi ^ 2 / 3 : ℝ) : ℂ) := by
  rw [depthLogDerivCoeff_eq_one, psiOneCoeff_one, if_neg one_ne_zero]
  push_cast
  ring

theorem depthLogDerivCoeff_five_two :
    depthLogDerivCoeff 5 2 = -((gammaLogThirdOne : ℝ) : ℂ) := by
  rw [depthLogDerivCoeff_eq_one, psiOneCoeff_two, if_neg (by norm_num)]
  push_cast
  ring

theorem depthLogDerivCoeff_five_three : depthLogDerivCoeff 5 3 = 20 * psiOneCoeff 3 := by
  rw [depthLogDerivCoeff_eq_one, if_neg (by norm_num)]
  push_cast
  ring

theorem depthLogDerivCoeff_five_four : depthLogDerivCoeff 5 4 = -26 * psiOneCoeff 4 := by
  rw [depthLogDerivCoeff_eq_one, if_neg (by norm_num)]
  push_cast
  ring

/-! ### The jet of `H₅` -/

theorem depthJetCoeff_five_one : depthJetCoeff 5 1 = ((depthFiveCentring : ℝ) : ℂ) := by
  have h := depthJetCoeff_one 4
  norm_num at h
  rw [h, depthLogDerivCoeff_five_zero]

theorem depthJetCoeff_five_two :
    depthJetCoeff 5 2 = ((depthFiveCentring ^ 2 / 2 + 2 * Real.pi ^ 2 / 3 : ℝ) : ℂ) := by
  have h := depthJetCoeff_succ_mul 4 1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [depthJetCoeff_five_one, depthLogDerivCoeff_five_zero, depthLogDerivCoeff_five_one,
    depthJetCoeff_zero] at h
  push_cast at h ⊢
  linear_combination h / 2

theorem depthJetCoeff_five_three :
    depthJetCoeff 5 3 = ((depthFiveCentring ^ 3 / 6 + 2 * Real.pi ^ 2 * depthFiveCentring / 3 -
      gammaLogThirdOne / 3 : ℝ) : ℂ) := by
  have h := depthJetCoeff_succ_mul 4 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [depthJetCoeff_five_one, depthJetCoeff_five_two, depthLogDerivCoeff_five_zero,
    depthLogDerivCoeff_five_one, depthLogDerivCoeff_five_two, depthJetCoeff_zero] at h
  push_cast at h ⊢
  linear_combination h / 3

theorem depthJetCoeff_five_four :
    depthJetCoeff 5 4 = ((depthFiveCentring ^ 4 / 24 + Real.pi ^ 2 * depthFiveCentring ^ 2 / 3 -
      depthFiveCentring * gammaLogThirdOne / 3 + 2 * Real.pi ^ 4 / 9 : ℝ) : ℂ) +
      ((5 / 6 : ℝ) : ℂ) * (6 * psiOneCoeff 3) := by
  have h := depthJetCoeff_succ_mul 4 3
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [depthJetCoeff_five_one, depthJetCoeff_five_two, depthJetCoeff_five_three,
    depthLogDerivCoeff_five_zero, depthLogDerivCoeff_five_one, depthLogDerivCoeff_five_two,
    depthLogDerivCoeff_five_three, depthJetCoeff_zero] at h
  push_cast at h ⊢
  linear_combination h / 4

theorem depthJetCoeff_five_five :
    depthJetCoeff 5 5 = ((depthFiveCentring ^ 5 / 120 + Real.pi ^ 2 * depthFiveCentring ^ 3 / 9 -
      depthFiveCentring ^ 2 * gammaLogThirdOne / 6 + 2 * Real.pi ^ 4 * depthFiveCentring / 9 -
      2 * Real.pi ^ 2 * gammaLogThirdOne / 9 : ℝ) : ℂ) +
      ((5 * depthFiveCentring / 6 : ℝ) : ℂ) * (6 * psiOneCoeff 3) -
      ((13 / 60 : ℝ) : ℂ) * (24 * psiOneCoeff 4) := by
  have h := depthJetCoeff_succ_mul 4 4
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [depthJetCoeff_five_one, depthJetCoeff_five_two, depthJetCoeff_five_three,
    depthJetCoeff_five_four, depthLogDerivCoeff_five_zero, depthLogDerivCoeff_five_one,
    depthLogDerivCoeff_five_two, depthLogDerivCoeff_five_three, depthLogDerivCoeff_five_four,
    depthJetCoeff_zero] at h
  push_cast at h ⊢
  linear_combination h / 5

/-! ### The engine at depth five -/

theorem enginePoly_four : enginePoly 4 = depthFourPoly := by
  change enginePoly (3 + 1) = _
  rw [enginePoly_succ 3 (by norm_num), enginePoly_three, stepPoly_three]

theorem enginePoly_five : enginePoly 5 = depthFivePoly := by
  change enginePoly (4 + 1) = _
  rw [enginePoly_succ 4 (by norm_num), enginePoly_four, stepPoly_four]

theorem coeff_depthFivePoly_zero : depthFivePoly.coeff 0 = depthFiveConst := by
  simp only [depthFivePoly, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]
  norm_num

theorem coeff_depthFivePoly_one : depthFivePoly.coeff 1 = depthFiveLinCoeff := by
  simp only [depthFivePoly, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]
  norm_num

theorem sqrt_two_pi_pow_four : (Real.sqrt 2 * Real.sqrt Real.pi) ^ 4 = 4 * Real.pi ^ 2 := by
  rw [mul_pow, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, Real.sq_sqrt (by positivity),
    Real.sq_sqrt (by positivity)]
  ring

/-- ★★★ **`D₅ = [a³/6 + 2π²a/3 − λ₃/3]/(4π²)`**, `a = 6 log 2 − 4γ`. -/
theorem depthFiveLinCoeff_eq :
    depthFiveLinCoeff = (depthFiveCentring ^ 3 / 6 + 2 * Real.pi ^ 2 * depthFiveCentring / 3 -
      gammaLogThirdOne / 3) / (4 * Real.pi ^ 2) := by
  have h := coeff_enginePoly_eq_depthJetCoeff 4 (by norm_num) (k := 1) (by norm_num)
  rw [enginePoly_five, coeff_depthFivePoly_one] at h
  norm_num at h
  rw [h, depthJetCoeff_five_three, Complex.ofReal_re, sqrt_two_pi_pow_four]

/-- ★★★ **`E₅ = [a⁴/24 + π²a²/3 − aλ₃/3 + 2π⁴/9 + 5λ₄/6]/(4π²)`.** -/
theorem depthFiveConst_eq :
    depthFiveConst = (depthFiveCentring ^ 4 / 24 + Real.pi ^ 2 * depthFiveCentring ^ 2 / 3 -
      depthFiveCentring * gammaLogThirdOne / 3 + 2 * Real.pi ^ 4 / 9 +
      5 * gammaLogFourthOne / 6) / (4 * Real.pi ^ 2) := by
  have h := coeff_enginePoly_eq_depthJetCoeff 4 (by norm_num) (k := 0) (by norm_num)
  rw [enginePoly_five, coeff_depthFivePoly_zero] at h
  norm_num at h
  rw [h, depthJetCoeff_five_four, Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul,
    sqrt_two_pi_pow_four]
  unfold gammaLogFourthOne
  ring

/-- ★★★ **`Q₅ = [a⁵/120 + π²a³/9 − a²λ₃/6 + 2π⁴a/9 − 2π²λ₃/9 + 5aλ₄/6 − 13λ₅/60]/(8π²)`.** -/
theorem residualMass_five_eq :
    residualMass 5 (enginePoly 5) = (depthFiveCentring ^ 5 / 120 +
      Real.pi ^ 2 * depthFiveCentring ^ 3 / 9 - depthFiveCentring ^ 2 * gammaLogThirdOne / 6 +
      2 * Real.pi ^ 4 * depthFiveCentring / 9 - 2 * Real.pi ^ 2 * gammaLogThirdOne / 9 +
      5 * depthFiveCentring * gammaLogFourthOne / 6 - 13 * gammaLogFifthOne / 60) /
      (8 * Real.pi ^ 2) := by
  have h := residualMass_eq_depthJetCoeff 4 (by norm_num)
  norm_num at h
  rw [h, depthJetCoeff_five_five, Complex.sub_re, Complex.add_re, Complex.ofReal_re,
    Complex.re_ofReal_mul, Complex.re_ofReal_mul, sqrt_two_pi_pow_four]
  unfold gammaLogFourthOne gammaLogFifthOne
  ring

/-- Regression: the jet's `C₅ = (a² + 4π²/3)/(16π²)` is the all-depth third coefficient. -/
theorem coeff_enginePoly_five_two :
    (enginePoly 5).coeff 2 =
      (depthFiveCentring ^ 2 + 4 * Real.pi ^ 2 / 3) / (16 * Real.pi ^ 2) := by
  have h := coeff_enginePoly_eq_depthJetCoeff 4 (by norm_num) (k := 2) (by norm_num)
  norm_num at h
  rw [h, depthJetCoeff_five_two, Complex.ofReal_re, sqrt_two_pi_pow_four]
  have hpi : 0 < Real.pi := Real.pi_pos
  field_simp
  ring

/-- The jet's `C₅` agrees with the all-depth closed form `coeff_enginePoly_third` at `L = 5`
(both are `(enginePoly 5).coeff 2`; here the two closed forms are shown equal directly). -/
theorem coeff_enginePoly_five_two_regression :
    (depthFiveCentring ^ 2 + 4 * Real.pi ^ 2 / 3) / (16 * Real.pi ^ 2) =
      ((((5 : ℝ) + 1) * Real.log 2 - ((5 : ℝ) - 1) * Real.eulerMascheroniConstant) ^ 2 +
        ((5 : ℝ) + 3) * Real.pi ^ 2 / 6) /
        (2 * ((5 - 3).factorial : ℝ) * Real.sqrt (2 * Real.pi) ^ (5 - 1)) := by
  have hs : Real.sqrt (2 * Real.pi) ^ (5 - 1) = 4 * Real.pi ^ 2 := by
    rw [Real.sqrt_mul (by norm_num), show (5 - 1 : ℕ) = 4 from rfl, sqrt_two_pi_pow_four]
  rw [hs, show (5 - 3 : ℕ) = 2 from rfl, Nat.factorial_two]
  unfold depthFiveCentring
  have hpi : 0 < Real.pi := Real.pi_pos
  push_cast
  field_simp
  ring

end Grammar
