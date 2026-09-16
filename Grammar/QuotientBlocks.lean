/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-!
# Quotient blocks (§20, posterior expectations beyond the first correction)

Formal division of two coefficient sequences `A, B : ℕ → K` over a field `K` with `B 0 ≠ 0`: the
**quotient blocks** `R = quotientBlocks A B` are the coefficients of the power series
`(Σ A_j x^j)/(Σ B_j x^j)`, so that `Σ_{i ≤ j} B_i R_{j−i} = A_j` for every `j`
(`sum_mul_quotientBlocks`) and `R` satisfies the recursion `R_0 = A_0/B_0`,
`R_{j+1} = (A_{j+1} − Σ_{i ≤ j} B_{i+1} R_{j−i})/B_0`
(`quotientBlocks_zero`, `quotientBlocks_succ`).

For the posterior expectation `E_N[φ]/E_N[1]` the field is the rational functions of `log N`, or
the reals pointwise in `N`: `x = N^{−1/Q}` and `A_j, B_j` are the polynomials in `log N` attached
to the `j`-th lattice exponent (consult #158, item 3: keep the rational-log blocks exact for
power accuracy; expand a block in `1/log N` separately).

Zero `sorry`/`axiom`.
-/

open PowerSeries Finset

namespace Grammar

variable {K : Type*} [Field K]

/-- The quotient blocks of `A` by `B`: the coefficients of `(Σ A_j x^j) · (Σ B_j x^j)⁻¹`. -/
noncomputable def quotientBlocks (A B : ℕ → K) (j : ℕ) : K :=
  PowerSeries.coeff j (PowerSeries.mk A * (PowerSeries.mk B)⁻¹)

/-- ★ **Exact finite division**: `Σ_{i ≤ j} B_i R_{j−i} = A_j`. -/
theorem sum_mul_quotientBlocks (A B : ℕ → K) (hB : B 0 ≠ 0) (j : ℕ) :
    ∑ i ∈ range (j + 1), B i * quotientBlocks A B (j - i) = A j := by
  have hc : PowerSeries.constantCoeff (PowerSeries.mk B) ≠ 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]
    exact hB
  have h1 : PowerSeries.mk B * (PowerSeries.mk A * (PowerSeries.mk B)⁻¹) = PowerSeries.mk A := by
    rw [mul_left_comm, PowerSeries.mul_inv_cancel _ hc, mul_one]
  have h2 := congrArg (PowerSeries.coeff j) h1
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mk,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i l => PowerSeries.coeff i (PowerSeries.mk B) *
        PowerSeries.coeff l (PowerSeries.mk A * (PowerSeries.mk B)⁻¹)) j] at h2
  simpa only [PowerSeries.coeff_mk, quotientBlocks] using h2

theorem quotientBlocks_zero (A B : ℕ → K) (hB : B 0 ≠ 0) : quotientBlocks A B 0 = A 0 / B 0 := by
  have h := sum_mul_quotientBlocks A B hB 0
  simp only [zero_add, Finset.sum_range_one, Nat.sub_zero] at h
  rw [eq_div_iff hB, mul_comm]
  exact h

theorem quotientBlocks_succ (A B : ℕ → K) (hB : B 0 ≠ 0) (j : ℕ) :
    quotientBlocks A B (j + 1) =
      (A (j + 1) - ∑ i ∈ range (j + 1), B (i + 1) * quotientBlocks A B (j - i)) / B 0 := by
  have h := sum_mul_quotientBlocks A B hB (j + 1)
  rw [Finset.sum_range_succ', Nat.sub_zero] at h
  have hs : ∑ i ∈ range (j + 1), B (i + 1) * quotientBlocks A B (j + 1 - (i + 1)) =
      ∑ i ∈ range (j + 1), B (i + 1) * quotientBlocks A B (j - i) :=
    Finset.sum_congr rfl fun i _ => by rw [Nat.add_sub_add_right]
  rw [hs] at h
  rw [eq_div_iff hB]
  linear_combination h

end Grammar
