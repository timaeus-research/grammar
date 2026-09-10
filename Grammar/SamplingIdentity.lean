/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# The sampling identity: `N = n` and the sign of the fluctuation

In the standard form `f(x,u) = φ(u) a(x,u)` with `E a(X,u) = φ(u)` (so
`K(u) = E f(X,u) = φ(u)²`), the empirical log-likelihood ratio of an i.i.d. sample is, identically
for every dataset,

  `(1/n) ∑_i f(X_i,u) = φ(u)² + φ(u) ζ_n(u)/√n`,   `ζ_n(u) := n^{−1/2} ∑_i (a(X_i,u) − φ(u))`,

so that `e^{−β ∑_i f(X_i,u)} = e^{−β n φ(u)² − β √n φ(u) ζ_n(u)}` (`exp_neg_sum_eq`).  Read against
the standard integral `e^{−βN u^{2k} + β√N u^k ξ(u)}` this identifies the asymptotic scale `N = n`
and the fluctuation `ξ_n = −ζ_n`: the standard integral's phase is **minus** the centred empirical
process of the coefficient `a`.  These are pure algebraic identities of the sampling model (no
probability); they are the sign audit requested in consult #56 for the companion note.
-/

namespace Grammar

/-- The centred empirical process of the coefficient `a` at `u`: `n^{−1/2} ∑_{i<n} (a(x_i) − φ)`. -/
noncomputable def zetaEmp (n : ℕ) (a : ℕ → ℝ) (φ : ℝ) : ℝ :=
  (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, (a i - φ)

/-- **The empirical mean of the standard form**: `(1/n) ∑ φ a_i = φ² + φ ζ_n/√n`. -/
theorem sum_mul_eq (n : ℕ) (hn : 0 < n) (a : ℕ → ℝ) (φ : ℝ) :
    (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, φ * a i = φ ^ 2 + φ * zetaEmp n a φ / Real.sqrt n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set s := Real.sqrt n with hsdef
  have hs : 0 < s := Real.sqrt_pos.2 hn'
  have hsq : s * s = n := Real.mul_self_sqrt hn'.le
  unfold zetaEmp
  rw [← hsdef, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    ← Finset.mul_sum, ← hsq]
  field_simp
  ring

/-- **`N = n` and `ξ_n = −ζ_n`**: the sampling exponent `−β ∑ f(X_i,u)` is the standard-integral
exponent `−βN φ² + β√N φ ξ` with `N = n` and `ξ = −ζ_n`. -/
theorem sampling_exponent_eq (n : ℕ) (hn : 0 < n) (a : ℕ → ℝ) (φ β : ℝ) :
    -β * ∑ i ∈ Finset.range n, φ * a i =
      -β * n * φ ^ 2 + β * Real.sqrt n * φ * (-zetaEmp n a φ) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h := sum_mul_eq n hn a φ
  set s := Real.sqrt n with hsdef
  have hs : 0 < s := Real.sqrt_pos.2 hn'
  have hsq : s * s = n := Real.mul_self_sqrt hn'.le
  have hsum : ∑ i ∈ Finset.range n, φ * a i = n * (φ ^ 2 + φ * zetaEmp n a φ / s) := by
    rw [← h]; field_simp
  rw [hsum, ← hsq]
  field_simp
  ring

/-- **The exponential form of the sampling identity**:
`e^{−β ∑ φ a_i} = e^{−β n φ² − β √n φ ζ_n}`. -/
theorem exp_neg_sum_eq (n : ℕ) (hn : 0 < n) (a : ℕ → ℝ) (φ β : ℝ) :
    Real.exp (-β * ∑ i ∈ Finset.range n, φ * a i) =
      Real.exp (-β * n * φ ^ 2 - β * Real.sqrt n * φ * zetaEmp n a φ) := by
  rw [sampling_exponent_eq n hn a φ β]
  ring_nf

end Grammar
