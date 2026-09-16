/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.GaussianThreshold

/-!
# Even and odd moments of a centred Gaussian (§20, the Wick weights)

`∫ x^{2j} dN(0,v) = (2j−1)‼ v^j = (2j)!/(2^j j!) v^j` and `∫ x^{2j+1} dN(0,v) = 0`
(`integral_pow_even_gaussianReal`, `integral_pow_odd_gaussianReal`,
`doubleFactorial_odd_eq_factorial_div`): the pointwise Wick weights that turn the annealed
generating series `Σ_r (1/r!) E C^pop_{μ+r/2,q}[η Y^r]` of a centred Gaussian field into
`Σ_j (1/(2^j j!)) C^pop_{μ+j,q}[η V^j]` (`AnnealedGeneratingSeries`, consult #159 A2–A3).

Route for the even moments: the density is even, `integral_comp_abs` halves the line, and the
half-line integral is `integral_rpow_mul_exp_neg_mul_sq` (`GaussianThreshold`) with
`Γ(j + 1/2) = (2j−1)‼ √π / 2^j`.

Zero `sorry`/`axiom`.
-/

open MeasureTheory ProbabilityTheory Real Set
open scoped NNReal Nat

namespace Grammar

/-- `(2j−1)‼ = (2j)!/(2^j j!)` in `ℝ`. -/
theorem doubleFactorial_odd_eq_factorial_div (j : ℕ) :
    ((2 * j - 1)‼ : ℝ) = ((2 * j).factorial : ℝ) / (2 ^ j * (j.factorial : ℝ)) := by
  rw [eq_div_iff (by positivity)]
  rcases j with _ | j
  · simp
  · have h2 : (2 * (j + 1)).factorial = (2 * (j + 1))‼ * (2 * j + 1)‼ := by
      rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring]
      exact Nat.factorial_eq_mul_doubleFactorial (2 * j + 1)
    have h : (2 * (j + 1) - 1)‼ * (2 ^ (j + 1) * (j + 1).factorial) = (2 * (j + 1)).factorial := by
      rw [show 2 * (j + 1) - 1 = 2 * j + 1 by omega, h2, Nat.doubleFactorial_two_mul]
      ring
    exact_mod_cast h

/-- The odd moments of a centred Gaussian vanish. -/
theorem integral_pow_odd_gaussianReal (v : ℝ≥0) (j : ℕ) :
    ∫ x, x ^ (2 * j + 1) ∂gaussianReal 0 v = 0 := by
  rcases eq_or_ne v 0 with hv | hv
  · subst hv
    simp [gaussianReal_zero_var]
  · rw [integral_gaussianReal_eq_integral_smul hv]
    have hodd : ∀ x : ℝ, gaussianPDFReal 0 v (-x) • (-x) ^ (2 * j + 1) =
        -(gaussianPDFReal 0 v x • x ^ (2 * j + 1)) := by
      intro x
      simp only [smul_eq_mul, gaussianPDFReal_def, sub_zero, neg_sq, Odd.neg_pow ⟨j, rfl⟩, mul_neg]
    have h1 := integral_neg_eq_self (fun x => gaussianPDFReal 0 v x • x ^ (2 * j + 1)) volume
    simp only [hodd, integral_neg] at h1
    linarith

/-- ★ **The even moments of a centred Gaussian**: `∫ x^{2j} dN(0,v) = (2j−1)‼ v^j`. -/
theorem integral_pow_even_gaussianReal (v : ℝ≥0) (j : ℕ) :
    ∫ x, x ^ (2 * j) ∂gaussianReal 0 v = ((2 * j - 1)‼ : ℝ) * (v : ℝ) ^ j := by
  rcases eq_or_ne v 0 with hv | hv
  · subst hv
    rcases j with _ | j
    · simp [gaussianReal_zero_var]
    · simp [gaussianReal_zero_var]
  · have hv0 : (0 : ℝ) < v := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hv)
    rw [integral_gaussianReal_eq_integral_smul hv]
    obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ,
        g = fun y => (√(2 * π * v))⁻¹ * (y ^ (2 * j) * exp (-(1 / (2 * v)) * y ^ 2)) := ⟨_, rfl⟩
    have hfun : (fun x : ℝ => gaussianPDFReal 0 v x • x ^ (2 * j)) = fun x => g |x| := by
      funext x
      simp only [hg, smul_eq_mul, gaussianPDFReal_def, sub_zero, Even.pow_abs (even_two_mul j),
        sq_abs]
      rw [show -x ^ 2 / (2 * (v : ℝ)) = -(1 / (2 * v)) * x ^ 2 by ring]
      ring
    rw [hfun, integral_comp_abs (f := g), hg, integral_const_mul]
    have hpow : ∀ x ∈ Ioi (0 : ℝ), x ^ (2 * j) * exp (-(1 / (2 * v)) * x ^ 2) =
        x ^ ((2 * j + 1 : ℝ) - 1) * exp (-(1 / (2 * v)) * x ^ 2) := by
      intro x _
      rw [show (2 * j + 1 : ℝ) - 1 = ((2 * j : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    rw [setIntegral_congr_fun measurableSet_Ioi hpow,
      integral_rpow_mul_exp_neg_mul_sq (1 / (2 * v)) (2 * j + 1) (by positivity) (by positivity)]
    -- the scalar algebra
    have hgamma : Real.Gamma ((2 * j + 1 : ℝ) / 2) = ((2 * j - 1)‼ : ℝ) * √π / 2 ^ j := by
      rw [show (2 * j + 1 : ℝ) / 2 = (j : ℝ) + 1 / 2 by ring, Real.Gamma_nat_add_half]
    have hrpow : (1 / (2 * (v : ℝ))) ^ (-(2 * j + 1 : ℝ) / 2) = (2 * v) ^ j * √(2 * v) := by
      rw [one_div, Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity), neg_div, neg_neg,
        show (2 * j + 1 : ℝ) / 2 = (j : ℝ) + 1 / 2 by ring, Real.rpow_add (by positivity),
        Real.rpow_natCast, Real.sqrt_eq_rpow]
    rw [hgamma, hrpow]
    have hs : √(2 * π * v) = √(2 * v) * √π := by
      rw [← Real.sqrt_mul (by positivity)]
      congr 1
      ring
    rw [hs]
    have ht : √(2 * (v : ℝ)) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
    have hp : √π ≠ 0 := (Real.sqrt_pos.2 Real.pi_pos).ne'
    field_simp
    ring

/-- The even moments in the Wick form `(2j)!/(2^j j!) v^j`. -/
theorem integral_pow_even_gaussianReal' (v : ℝ≥0) (j : ℕ) :
    ∫ x, x ^ (2 * j) ∂gaussianReal 0 v =
      ((2 * j).factorial : ℝ) / (2 ^ j * (j.factorial : ℝ)) * (v : ℝ) ^ j := by
  rw [integral_pow_even_gaussianReal, doubleFactorial_odd_eq_factorial_div]

end Grammar
