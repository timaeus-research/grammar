/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.RingTheory.PowerSeries.Derivative
import Grammar.QuotientBlocks

/-!
# The formal source logarithm and the connected coefficients (§20, posterior cumulants)

For a fixed sample the posterior expectation `Z_N[ηf]/Z_N[η]` is the formal quotient of two
expansions (`quotientBlocks`).  The clean organisation is through a **source**: with
`Z(ε) = Z_N[η e^{εf}] = Σ_r (ε^r/r!) Z_N[η f^r]`, the posterior cumulants of `f` are the
`ε`-derivatives at `0` of `log (Z(ε)/Z(0))`.  Anchoring by `Z(0)` makes the constant term `0`,
so Mathlib's formal logarithm `PowerSeries.logOf` applies without choosing a logarithm of the
leading evidence coefficient (consult #162, §3).

Over a commutative `ℚ`-algebra `A` and `U : A⟦ε⟧` with constant coefficient `1`:

* ★ `mul_derivative_logOf`: `U · (log U)' = U'`, the formal identity behind
  `∂_ε log Z = Z⁻¹ ∂_ε Z`;
* `coeff_succ_mul_eq_sum_logOf`: its coefficientwise form, the moment–cumulant recurrence
  `(n+1) U_{n+1} = Σ_{i+l=n} U_i (l+1) (log U)_{l+1}`;
* `coeff_one_logOf`, `two_mul_coeff_two_logOf`: `κ₁ = U₁`, `κ₂ = 2U₂ − U₁²` (exponential
  normalisation `U = 1 + εκ₁ + ε²κ₂/2 + …`).

Specialised to `Z = B + εA + ε²C/2 + O(ε³)` with `B` invertible and `U = B⁻¹Z`:
`κ₁ = B⁻¹A` and `κ₂ = B⁻¹C − (B⁻¹A)²` (`coeff_one_logOf_source`,
`two_mul_coeff_two_logOf_source`).  Over the block field `K⟦x⟧` (`x = N^{−1/Q}`, blocks
`a, b, c : ℕ → K`) this reads, at the block level,

★ `coeff_two_mul_coeff_two_logOf_blocks`:
`κ₂(j) = quotientBlocks c b j − Σ_{i ≤ j} quotientBlocks a b i · quotientBlocks a b (j − i)`
(`varianceBlocks`), the all-orders blocks of the posterior variance, and
`κ₁(j) = quotientBlocks a b j` (`coeff_coeff_one_logOf_blocks`).

Zero `sorry`/`axiom`.
-/

open PowerSeries Finset

namespace Grammar

section FormalLog

variable {A : Type*} [CommRing A] [Algebra ℚ A]

/-- The alternating geometric series `Σ (−1)^n X^n = 1/(1+X)`, the derivative of `log (1+X)`. -/
noncomputable def geomAlt (A : Type*) [CommRing A] [Algebra ℚ A] : A⟦X⟧ :=
  mk fun n => algebraMap ℚ A ((-1 : ℚ) ^ n)

theorem geomAlt_mul_one_add_X : geomAlt A * (1 + X) = 1 := by
  ext n
  rcases n with _ | n
  · simp [geomAlt, mul_add]
  · rw [mul_add, mul_one, map_add, coeff_succ_mul_X, coeff_one, if_neg (Nat.succ_ne_zero n)]
    simp only [geomAlt, coeff_mk]
    rw [← map_add, show ((-1 : ℚ) ^ (n + 1) + (-1) ^ n) = 0 by ring, map_zero]

theorem derivative_log_eq_geomAlt : d⁄dX A (log A) = geomAlt A := deriv_log

omit [Algebra ℚ A] in
theorem hasSubst_sub_one {U : A⟦X⟧} (hU : constantCoeff U = 1) : HasSubst (U - 1) :=
  HasSubst.of_constantCoeff_zero' (by rw [map_sub, map_one, hU, sub_self])

/-- `(1/(1+X)) ∘ (U − 1) · U = 1`. -/
theorem geomAlt_subst_mul {U : A⟦X⟧} (hU : constantCoeff U = 1) :
    (geomAlt A).subst (U - 1) * U = 1 := by
  have hs := hasSubst_sub_one hU
  have h : (geomAlt A * (1 + X)).subst (U - 1) = (1 : A⟦X⟧).subst (U - 1) := by
    rw [geomAlt_mul_one_add_X]
  have h1 : (1 : A⟦X⟧).subst (U - 1) = 1 := by
    rw [← coe_substAlgHom hs]
    exact map_one _
  rw [subst_mul hs, subst_add hs, subst_X hs, h1, add_sub_cancel] at h
  exact h

/-- ★ **The formal source identity** `U · (log U)' = U'` for `U` with constant coefficient `1`:
the derivative of the anchored logarithm is `U⁻¹ U'`. -/
theorem mul_derivative_logOf {U : A⟦X⟧} (hU : constantCoeff U = 1) :
    U * d⁄dX A (logOf U) = d⁄dX A U := by
  have hs := hasSubst_sub_one hU
  rw [logOf_eq, derivative_subst hs, derivative_log_eq_geomAlt, map_sub, derivative_one,
    sub_zero, ← mul_assoc, mul_comm U, geomAlt_subst_mul hU, one_mul]

/-- The moment–cumulant recurrence: `(n+1) U_{n+1} = Σ_{i+l=n} U_i · (l+1) (log U)_{l+1}`. -/
theorem coeff_succ_mul_eq_sum_logOf {U : A⟦X⟧} (hU : constantCoeff U = 1) (n : ℕ) :
    coeff (n + 1) U * (n + 1) =
      ∑ p ∈ antidiagonal n, coeff p.1 U * (coeff (p.2 + 1) (logOf U) * (p.2 + 1)) := by
  have h := congrArg (coeff n) (mul_derivative_logOf hU)
  rw [coeff_mul, coeff_derivative] at h
  simp only [coeff_derivative] at h
  exact h.symm

/-- `κ₁ = U₁`. -/
theorem coeff_one_logOf {U : A⟦X⟧} (hU : constantCoeff U = 1) :
    coeff 1 (logOf U) = coeff 1 U := by
  have h := coeff_succ_mul_eq_sum_logOf hU 0
  have h0 : coeff 0 U = 1 := by rw [coeff_zero_eq_constantCoeff_apply, hU]
  simp only [Nat.antidiagonal_zero, sum_singleton, h0, Nat.cast_zero, zero_add, mul_one,
    one_mul] at h
  exact h.symm

/-- `κ₂ = 2U₂ − U₁²` (exponential normalisation `U = 1 + εκ₁ + ε²κ₂/2 + …`). -/
theorem two_mul_coeff_two_logOf {U : A⟦X⟧} (hU : constantCoeff U = 1) :
    2 * coeff 2 (logOf U) = 2 * coeff 2 U - coeff 1 U ^ 2 := by
  have h := coeff_succ_mul_eq_sum_logOf hU 1
  have h0 : coeff 0 U = 1 := by rw [coeff_zero_eq_constantCoeff_apply, hU]
  rw [Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i l => coeff i U * (coeff (l + 1) (logOf U) * (l + 1))) 1, sum_range_succ,
    sum_range_one, h0, coeff_one_logOf hU] at h
  simp only [Nat.cast_one, Nat.cast_zero, zero_add, one_mul, Nat.sub_zero, Nat.sub_self,
    mul_one] at h
  linear_combination -h

end FormalLog

section Source

variable {A : Type*} [CommRing A] [Algebra ℚ A] {Z : A⟦X⟧} {Bi : A}

omit [Algebra ℚ A] in
theorem constantCoeff_C_mul_of_inv (hB : Bi * constantCoeff Z = 1) :
    constantCoeff (C Bi * Z) = 1 := by
  rw [map_mul, constantCoeff_C, hB]

/-- `κ₁ = B⁻¹ A` for `Z = B + εA + …`. -/
theorem coeff_one_logOf_source (hB : Bi * constantCoeff Z = 1) :
    coeff 1 (logOf (C Bi * Z)) = Bi * coeff 1 Z := by
  rw [coeff_one_logOf (constantCoeff_C_mul_of_inv hB), coeff_C_mul]

/-- `κ₂ = B⁻¹ C − (B⁻¹ A)²` for `Z = B + εA + ε²C/2 + …`. -/
theorem two_mul_coeff_two_logOf_source (hB : Bi * constantCoeff Z = 1) :
    2 * coeff 2 (logOf (C Bi * Z)) = Bi * (2 * coeff 2 Z) - (Bi * coeff 1 Z) ^ 2 := by
  rw [two_mul_coeff_two_logOf (constantCoeff_C_mul_of_inv hB), coeff_C_mul, coeff_C_mul]
  ring

end Source

section Blocks

variable {K : Type*} [Field K] [CharZero K]

/-- The **variance blocks**: `κ₂(j) = (c/b)_j − Σ_{i ≤ j} (a/b)_i (a/b)_{j−i}`, the all-orders
blocks of the posterior variance when `a, b, c` are the blocks of `Z_N[ηf], Z_N[η], Z_N[ηf²]`. -/
noncomputable def varianceBlocks (a b c : ℕ → K) (j : ℕ) : K :=
  quotientBlocks c b j -
    ∑ i ∈ range (j + 1), quotientBlocks a b i * quotientBlocks a b (j - i)

omit [CharZero K] in
theorem coeff_sq_mk_mul_inv (a b : ℕ → K) (j : ℕ) :
    coeff j ((mk a * (mk b)⁻¹) ^ 2) =
      ∑ i ∈ range (j + 1), quotientBlocks a b i * quotientBlocks a b (j - i) := by
  rw [sq, coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i l => coeff i (mk a * (mk b)⁻¹) * coeff l (mk a * (mk b)⁻¹)) j]
  simp only [quotientBlocks]

variable {a b c : ℕ → K} {Z : K⟦X⟧⟦X⟧}

omit [CharZero K] in
theorem inv_mk_mul_constantCoeff (hb : b 0 ≠ 0) (hZ0 : constantCoeff Z = mk b) :
    (mk b)⁻¹ * constantCoeff Z = 1 := by
  rw [hZ0]
  exact PowerSeries.inv_mul_cancel _ (by rwa [← coeff_zero_eq_constantCoeff_apply, coeff_mk])

/-- ★ `κ₁(j) = quotientBlocks a b j`: the first connected coefficient is the quotient block. -/
theorem coeff_coeff_one_logOf_blocks (hb : b 0 ≠ 0) (hZ0 : constantCoeff Z = mk b)
    (hZ1 : coeff 1 Z = mk a) (j : ℕ) :
    coeff j (coeff 1 (logOf (C (mk b)⁻¹ * Z))) = quotientBlocks a b j := by
  have hB := inv_mk_mul_constantCoeff hb hZ0
  have h1 := coeff_one_logOf_source hB
  rw [h1, hZ1, mul_comm]
  simp only [quotientBlocks]

/-- ★ **The variance blocks are the second connected coefficients**:
`κ₂(j) = quotientBlocks c b j − Σ_{i ≤ j} quotientBlocks a b i · quotientBlocks a b (j − i)`
for `Z = B + εA + ε²C/2 + …` with blocks `a, b, c`. -/
theorem coeff_two_mul_coeff_two_logOf_blocks (hb : b 0 ≠ 0) (hZ0 : constantCoeff Z = mk b)
    (hZ1 : coeff 1 Z = mk a) (hZ2 : 2 * coeff 2 Z = mk c) (j : ℕ) :
    coeff j (2 * coeff 2 (logOf (C (mk b)⁻¹ * Z))) = varianceBlocks a b c j := by
  have hB := inv_mk_mul_constantCoeff hb hZ0
  have h2 := two_mul_coeff_two_logOf_source hB
  rw [h2, hZ1, hZ2, map_sub, mul_comm _ (mk c), mul_comm _ (mk a), coeff_sq_mk_mul_inv]
  simp only [varianceBlocks, quotientBlocks]

end Blocks

end Grammar
