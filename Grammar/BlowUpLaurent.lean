/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.GammaSecondDerivHalf
import Grammar.ChartZetaPolar

/-!
# The Laurent data of the blow-up zeta function at its double pole

The zeta function of the blow-up example `K = x²(x² + y²)/2` against the Gaussian prior is
`ζ(w) = 2^{3w+1} Γ(w + ½)²` (`Grammar.BlowUpZeta`, `lintegral_blowK_gauss_closed`).  At the leading
pole `w = −½`, with `t = w + ½`, the regularisation `t² ζ(−½ + t) = 2^{3t−½} Γ(1 + t)²` is
analytic at `t = 0` (`blowupZetaReg`), and its value and derivative at `0` give the Laurent data

  `ζ(−½ + t) = (1/√2)/t² + ((3 log 2 − 2γ)/√2)/t + O(1)`  (★★★ `blowupZeta_laurent`),

i.e. the population polar data `A_{½,2} = 1/√2`, `A_{½,1} = (3 log 2 − 2γ)/√2` of the blow-up
example (examples_slop §4, the finite parts along the two walls; Astra round 5), from `Γ(1) = 1` and
`Γ'(1) = −γ` (Mathlib) only — no derivative of `Γ` at its pole.  The paper's Laplace polynomial
`√(π/2)[log N + 5 log 2 − γ]` at `N^{−1/2}` follows by the Gamma transform (a derivation until the
transfer theorem is formal).  Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology Asymptotics

namespace Grammar

/-- The closed-form zeta function of the blow-up example. -/
noncomputable def blowupZeta (w : ℂ) : ℂ := (2 : ℂ) ^ (3 * w + 1) * Complex.Gamma (w + 1 / 2) ^ 2

/-- The regularised function `t² ζ(−½ + t) = 2^{3t − ½} Γ(1 + t)²`, analytic at `0`. -/
noncomputable def blowupZetaReg (t : ℂ) : ℂ :=
  Complex.exp ((3 * t - 1 / 2) * Real.log 2) * Complex.Gamma (1 + t) ^ 2

/-- `ζ(−½ + t) = blowupZetaReg t / t²` for `t ≠ 0`. -/
theorem blowupZeta_eq_reg {t : ℂ} (ht : t ≠ 0) :
    blowupZeta (-1 / 2 + t) = blowupZetaReg t / t ^ 2 := by
  unfold blowupZeta blowupZetaReg
  have hG := Complex.Gamma_add_one t ht
  rw [show (-1 / 2 + t + 1 / 2 : ℂ) = t by ring,
    show (3 * (-1 / 2 + t) + 1 : ℂ) = 3 * t - 1 / 2 by ring,
    Complex.cpow_def_of_ne_zero (by norm_num) _, ← Complex.ofNat_log]
  rw [mul_comm ((Real.log 2 : ℝ) : ℂ) _, show (1 + t : ℂ) = t + 1 by ring, hG]
  field_simp

theorem differentiableOn_blowupZetaReg :
    DifferentiableOn ℂ blowupZetaReg {t : ℂ | -1 < t.re} := by
  intro t ht
  have ht' : 0 < (1 + t).re := by simp; linarith [show -1 < t.re from ht]
  refine DifferentiableAt.differentiableWithinAt ?_
  unfold blowupZetaReg
  refine DifferentiableAt.mul (by fun_prop) ?_
  exact ((Complex.differentiableAt_Gamma _ (ne_neg_nat_of_re_pos ht')).comp t
    (differentiableAt_const _ |>.add differentiableAt_id)).pow 2

/-- `exp(−½ log 2) = 1/√2`. -/
theorem exp_neg_half_log_two :
    Complex.exp ((-1 / 2 : ℂ) * Real.log 2) = ((1 / Real.sqrt 2 : ℝ) : ℂ) := by
  have h : Real.exp (-1 / 2 * Real.log 2) = 1 / Real.sqrt 2 := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by norm_num), one_div, ← Real.exp_neg]
    congr 1
    ring
  rw [← h, Complex.ofReal_exp]
  push_cast
  rfl

theorem blowupZetaReg_zero : blowupZetaReg 0 = ((1 / Real.sqrt 2 : ℝ) : ℂ) := by
  unfold blowupZetaReg
  rw [show (3 * (0 : ℂ) - 1 / 2) = -1 / 2 by ring, exp_neg_half_log_two, add_zero,
    Complex.Gamma_one]
  ring

/-- The derivative of the regularised function at `0`: `(3 log 2 − 2γ)/√2`. -/
theorem hasDerivAt_blowupZetaReg_zero :
    HasDerivAt blowupZetaReg
      (((3 * Real.log 2 - 2 * Real.eulerMascheroniConstant) / Real.sqrt 2 : ℝ) : ℂ) 0 := by
  have hE : HasDerivAt (fun t : ℂ => Complex.exp ((3 * t - 1 / 2) * Real.log 2))
      (Complex.exp ((3 * (0 : ℂ) - 1 / 2) * Real.log 2) * (3 * Real.log 2)) 0 := by
    have hl : HasDerivAt (fun t : ℂ => (3 * t - 1 / 2) * Real.log 2) (3 * Real.log 2) 0 := by
      have := (((hasDerivAt_id (0 : ℂ)).const_mul (3 : ℂ)).sub_const (1 / 2)).mul_const
        ((Real.log 2 : ℝ) : ℂ)
      refine this.congr_deriv ?_
      simp
    exact (Complex.hasDerivAt_exp _).comp 0 hl
  have hG : HasDerivAt (fun t : ℂ => Complex.Gamma (1 + t)) (-Real.eulerMascheroniConstant) 0 := by
    have hg : HasDerivAt Complex.Gamma (-(Real.eulerMascheroniConstant : ℂ)) (1 + 0) := by
      simpa using Complex.hasDerivAt_Gamma_one
    exact hg.comp_const_add 1
  have hprod := hE.mul (hG.mul hG)
  refine (hprod.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)).congr_deriv ?_
  · first
    | rfl
    | simp only [blowupZetaReg, Pi.mul_apply, sq]
  simp only [Pi.mul_apply]
  rw [show (3 * (0 : ℂ) - 1 / 2) = -1 / 2 by ring, exp_neg_half_log_two, add_zero,
    Complex.Gamma_one]
  push_cast
  have hs2 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (by norm_num)).ne'
  field_simp
  ring

/-- ★★★ **The Laurent data of the blow-up zeta function at `w = −½`**:
`ζ(−½ + t) = (1/√2)/t² + ((3 log 2 − 2γ)/√2)/t + O(1)`, i.e. `A_{½,2} = 1/√2`,
`A_{½,1} = (3 log 2 − 2γ)/√2`. -/
theorem blowupZeta_laurent :
    (fun t : ℂ => blowupZeta (-1 / 2 + t) - ((1 / Real.sqrt 2 : ℝ) : ℂ) / t ^ 2 -
      (((3 * Real.log 2 - 2 * Real.eulerMascheroniConstant) / Real.sqrt 2 : ℝ) : ℂ) / t)
      =O[𝓝[≠] (0 : ℂ)] fun _ => (1 : ℂ) := by
  have hU : {t : ℂ | -1 < t.re} ∈ 𝓝 (0 : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp)
  have h := pole_taylor_isBigO_one hU differentiableOn_blowupZetaReg 2
  refine h.congr' ?_ EventuallyEq.rfl
  refine eventually_nhdsWithin_of_forall fun t ht => ?_
  have ht0 : t ≠ 0 := ht
  beta_reduce
  rw [blowupZeta_eq_reg ht0]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [iteratedDeriv_one, iteratedDeriv_zero, hasDerivAt_blowupZetaReg_zero.deriv,
    blowupZetaReg_zero]
  field_simp
  ring

end Grammar
