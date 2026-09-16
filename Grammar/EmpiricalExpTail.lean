/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.EmpiricalFamilyLinear

/-!
# Exponential tails (§20, generating identity)

`expTail n x = e^x − Σ_{s<n} x^s/s!`, with `(expTail n)' = expTail (n−1)` (natural subtraction),
smoothness, and the two bounds

* `abs_expTail_le : |expTail n x| ≤ |x|^n/n! · e^{|x|}`,
* `abs_expTail_le_half : |expTail n x| ≤ (1/2)^n · e^{3|x|}`,

the second being the geometric decay used to sum the population coefficients.

Zero `sorry`/`axiom`.
-/

open Real Finset Filter Topology

namespace Grammar

namespace SmoothEngine

/-- `expTail n x = e^x − Σ_{s<n} x^s/s!`. -/
noncomputable def expTail (n : ℕ) (x : ℝ) : ℝ :=
  Real.exp x - ∑ s ∈ range n, x ^ s / (s.factorial : ℝ)

theorem expTail_zero (x : ℝ) : expTail 0 x = Real.exp x := by
  simp [expTail]

theorem expTail_succ (n : ℕ) (x : ℝ) :
    expTail (n + 1) x = expTail n x - x ^ n / (n.factorial : ℝ) := by
  simp only [expTail, Finset.sum_range_succ]
  ring

theorem hasDerivAt_expTail (n : ℕ) (x : ℝ) : HasDerivAt (expTail n) (expTail (n - 1) x) x := by
  induction n with
  | zero =>
    have h : expTail 0 = Real.exp := funext expTail_zero
    rw [h]
    exact Real.hasDerivAt_exp x
  | succ n ih =>
    have h1 : expTail (n + 1) = fun y => expTail n y - y ^ n / (n.factorial : ℝ) :=
      funext (expTail_succ n)
    rw [h1]
    refine (ih.fun_sub ((hasDerivAt_pow n x).div_const (n.factorial : ℝ))).congr_deriv ?_
    cases n with
    | zero => simp
    | succ m =>
      simp only [Nat.add_sub_cancel]
      rw [expTail_succ m x, Nat.factorial_succ]
      push_cast
      congr 1
      field_simp

theorem contDiff_expTail (n : ℕ) : ContDiff ℝ ⊤ (expTail n) :=
  Real.contDiff_exp.sub (ContDiff.sum fun s _ => (contDiff_id.pow s).div_const _)

theorem differentiable_expTail (n : ℕ) : Differentiable ℝ (expTail n) := fun x =>
  (hasDerivAt_expTail n x).differentiableAt

/-- The tail is the shifted exponential series. -/
theorem expTail_eq_tsum (n : ℕ) (x : ℝ) :
    expTail n x = ∑' s : ℕ, x ^ (s + n) / ((s + n).factorial : ℝ) := by
  have hs : Summable fun s : ℕ => x ^ s / (s.factorial : ℝ) := Real.summable_pow_div_factorial x
  have hexp : Real.exp x = ∑' s : ℕ, x ^ s / (s.factorial : ℝ) := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  have hshift : Summable fun s : ℕ => x ^ (s + n) / ((s + n).factorial : ℝ) :=
    (summable_nat_add_iff n).2 hs
  have h : ∑ s ∈ range n, x ^ s / (s.factorial : ℝ) +
      ∑' s : ℕ, x ^ (s + n) / ((s + n).factorial : ℝ) = ∑' s : ℕ, x ^ s / (s.factorial : ℝ) :=
    Summable.sum_add_tsum_nat_add' hshift
  unfold expTail
  rw [hexp]
  linarith

/-- ★ `|expTail n x| ≤ |x|^n/n! · e^{|x|}`. -/
theorem abs_expTail_le (n : ℕ) (x : ℝ) :
    |expTail n x| ≤ |x| ^ n / (n.factorial : ℝ) * Real.exp |x| := by
  rw [expTail_eq_tsum]
  have hs : Summable fun s : ℕ => |x| ^ s / (s.factorial : ℝ) :=
    Real.summable_pow_div_factorial |x|
  have hshift : Summable fun s : ℕ => x ^ (s + n) / ((s + n).factorial : ℝ) :=
    (summable_nat_add_iff n).2 (Real.summable_pow_div_factorial x)
  have hexp : Real.exp |x| = ∑' s : ℕ, |x| ^ s / (s.factorial : ℝ) := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  have hterm : ∀ s : ℕ, |x ^ (s + n) / ((s + n).factorial : ℝ)| ≤
      |x| ^ n / (n.factorial : ℝ) * (|x| ^ s / (s.factorial : ℝ)) := by
    intro s
    rw [abs_div, abs_pow, Nat.abs_cast, pow_add]
    have hf : ((n.factorial : ℝ) * s.factorial) ≤ ((s + n).factorial : ℝ) := by
      have hd : n.factorial * s.factorial ∣ (s + n).factorial := by
        rw [add_comm]
        exact Nat.factorial_mul_factorial_dvd_factorial_add n s
      exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos _) hd
    calc |x| ^ s * |x| ^ n / ((s + n).factorial : ℝ)
        ≤ |x| ^ s * |x| ^ n / ((n.factorial : ℝ) * s.factorial) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hf
      _ = _ := by
          field_simp
  calc |∑' s : ℕ, x ^ (s + n) / ((s + n).factorial : ℝ)|
      ≤ ∑' s : ℕ, |x ^ (s + n) / ((s + n).factorial : ℝ)| := by
        have := norm_tsum_le_tsum_norm (f := fun s : ℕ => x ^ (s + n) / ((s + n).factorial : ℝ))
          (by simpa only [Real.norm_eq_abs] using hshift.abs)
        simpa only [Real.norm_eq_abs] using this
    _ ≤ ∑' s : ℕ, |x| ^ n / (n.factorial : ℝ) * (|x| ^ s / (s.factorial : ℝ)) :=
        Summable.tsum_le_tsum hterm hshift.abs (hs.mul_left _)
    _ = |x| ^ n / (n.factorial : ℝ) * Real.exp |x| := by
        rw [tsum_mul_left, hexp]

/-- `y^n / n! ≤ e^{2y} / 2^n` for `y ≥ 0`. -/
theorem pow_div_factorial_le_exp_two_mul {y : ℝ} (hy : 0 ≤ y) (n : ℕ) :
    y ^ n / (n.factorial : ℝ) ≤ (1 / 2) ^ n * Real.exp (2 * y) := by
  have h := Real.pow_div_factorial_le_exp (2 * y) (by positivity) n
  have h2 : (2 * y) ^ n = 2 ^ n * y ^ n := mul_pow 2 y n
  rw [h2] at h
  have hpos : (0 : ℝ) < 2 ^ n := by positivity
  rw [one_div_pow]
  calc y ^ n / (n.factorial : ℝ) = (2 ^ n * y ^ n / (n.factorial : ℝ)) / 2 ^ n := by
        field_simp
    _ ≤ Real.exp (2 * y) / 2 ^ n := div_le_div_of_nonneg_right h hpos.le
    _ = 1 / 2 ^ n * Real.exp (2 * y) := by ring

/-- ★ **Geometric decay of the tails**: `|expTail n x| ≤ (1/2)^n e^{3|x|}`. -/
theorem abs_expTail_le_half (n : ℕ) (x : ℝ) :
    |expTail n x| ≤ (1 / 2) ^ n * Real.exp (3 * |x|) := by
  calc |expTail n x| ≤ |x| ^ n / (n.factorial : ℝ) * Real.exp |x| := abs_expTail_le n x
    _ ≤ (1 / 2) ^ n * Real.exp (2 * |x|) * Real.exp |x| :=
        mul_le_mul_of_nonneg_right (pow_div_factorial_le_exp_two_mul (abs_nonneg x) n)
          (Real.exp_nonneg _)
    _ = (1 / 2) ^ n * Real.exp (3 * |x|) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring

/-- `(1/2)^{R−j} ≤ 2^W (1/2)^R` for `j ≤ W` (natural subtraction). -/
theorem half_pow_sub_le {j W : ℕ} (hj : j ≤ W) (R : ℕ) :
    ((1 : ℝ) / 2) ^ (R - j) ≤ 2 ^ W * (1 / 2) ^ R := by
  have h1 : ((1 : ℝ) / 2) ^ (R - j) = (1 / 2) ^ (R - j + j) * 2 ^ j := by
    rw [pow_add, mul_assoc, ← mul_pow]
    norm_num
  have h2 : ((1 : ℝ) / 2) ^ (R - j + j) ≤ (1 / 2) ^ R :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) le_tsub_add
  have h3 : (2 : ℝ) ^ j ≤ 2 ^ W := pow_le_pow_right₀ (by norm_num) hj
  rw [h1]
  calc ((1 : ℝ) / 2) ^ (R - j + j) * 2 ^ j ≤ (1 / 2) ^ R * 2 ^ W :=
        mul_le_mul h2 h3 (by positivity) (by positivity)
    _ = _ := by ring

end SmoothEngine

end Grammar
