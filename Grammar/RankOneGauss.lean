/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.BlowUpPolar

/-!
# Rank-one matrix factorisation: the column-wise Gaussian integration

For the model with output `x yᵀ` (`x : Fin M → ℝ`, `y : Fin N → ℝ`), unit Gaussian noise and the truth
`A`, the empirical divergence with a frozen field `Ξ` is
`n K − √n ⟨x yᵀ − A, Ξ⟩ = (n/2) Σ_{ij} (xᵢ yⱼ − Aᵢⱼ)² − √n Σ_{ij} (xᵢ yⱼ − Aᵢⱼ) Ξᵢⱼ`, and it is a sum over
the columns `j` of quadratics in `yⱼ`.  Against the Gaussian prior `e^{−|y|²/2}` the `y`-integral is
therefore a product of one-dimensional Gaussian integrals with linear terms (examples_slop §4):

  `∫_{ℝ^N} e^{−nK + √n⟨x yᵀ − A, Ξ⟩ − |y|²/2} dy
      = ∏_j √(2π/(n|x|²+1)) · exp( (n⟨x,A_j⟩ + √n⟨x,Ξ_j⟩)² / (2(n|x|²+1)) − n|A_j|²/2 − √n⟨A_j,Ξ_j⟩ )`

(★★ `integral_rankOne_gauss`), which reduces the `M+N`-dimensional partition function to an
`M`-dimensional integral exactly, field included.  The one-dimensional input is the real quadratic
Gaussian integral `∫ e^{−αy² + βy − γ} = √(π/α) e^{β²/4α − γ}` (`integral_exp_quadratic_real`, from
Mathlib's `integral_cexp_quadratic`).  Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology Finset
open scoped ENNReal

namespace Grammar

/-- The real Gaussian integral with a linear term: `∫ e^{−αy² + βy − γ} dy = √(π/α) e^{β²/(4α) − γ}`. -/
theorem integral_exp_quadratic_real {α : ℝ} (hα : 0 < α) (β γ : ℝ) :
    ∫ y : ℝ, Real.exp (-α * y ^ 2 + β * y - γ) =
      Real.sqrt (Real.pi / α) * Real.exp (β ^ 2 / (4 * α) - γ) := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  have h := integral_cexp_quadratic (b := -(α : ℂ)) (by simpa using hα) (β : ℂ) (-(γ : ℂ))
  have hpt : ∀ y : ℝ, ((Real.exp (-α * y ^ 2 + β * y - γ) : ℝ) : ℂ) =
      Complex.exp (-(α : ℂ) * (y : ℂ) ^ 2 + (β : ℂ) * (y : ℂ) + -(γ : ℂ)) := by
    intro y
    rw [Complex.ofReal_exp]
    push_cast
    ring_nf
  simp_rw [hpt]
  rw [h]
  have hsqrt : ((Real.pi : ℂ) / -(-(α : ℂ))) ^ (1 / 2 : ℂ) = ((Real.sqrt (Real.pi / α) : ℝ) : ℂ) := by
    rw [neg_neg, Real.sqrt_eq_rpow, Complex.ofReal_cpow (by positivity)]
    push_cast
    ring_nf
  rw [hsqrt]
  push_cast
  congr 1
  field_simp
  ring_nf

variable {M N : ℕ}

/-- The columnwise decomposition of the residual and of the field: for every column `j`,
`Σᵢ (xᵢ yⱼ − Aᵢⱼ)² = |x|² yⱼ² − 2 yⱼ ⟨x, Aⱼ⟩ + |Aⱼ|²`. -/
theorem sum_sq_column (x : Fin M → ℝ) (A : Fin M → Fin N → ℝ) (y : Fin N → ℝ) (j : Fin N) :
    ∑ i, (x i * y j - A i j) ^ 2 =
      (∑ i, x i ^ 2) * y j ^ 2 - 2 * y j * ∑ i, x i * A i j + ∑ i, A i j ^ 2 := by
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem sum_field_column (x : Fin M → ℝ) (A Ξ : Fin M → Fin N → ℝ) (y : Fin N → ℝ) (j : Fin N) :
    ∑ i, (x i * y j - A i j) * Ξ i j = y j * ∑ i, x i * Ξ i j - ∑ i, A i j * Ξ i j := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- ★★ **The column-wise Gaussian integration of the rank-one model with a frozen field.** -/
theorem integral_rankOne_gauss {n : ℝ} (hn : 0 ≤ n) (x : Fin M → ℝ) (A Ξ : Fin M → Fin N → ℝ) :
    ∫ y : Fin N → ℝ, Real.exp (-n * (∑ j, ∑ i, (x i * y j - A i j) ^ 2) / 2 +
        Real.sqrt n * (∑ j, ∑ i, (x i * y j - A i j) * Ξ i j) - (∑ j, y j ^ 2) / 2) =
      ∏ j, (Real.sqrt (2 * Real.pi / (n * (∑ i, x i ^ 2) + 1)) *
        Real.exp ((n * (∑ i, x i * A i j) + Real.sqrt n * (∑ i, x i * Ξ i j)) ^ 2 /
          (2 * (n * (∑ i, x i ^ 2) + 1)) - n * (∑ i, A i j ^ 2) / 2 -
            Real.sqrt n * ∑ i, A i j * Ξ i j)) := by
  set S := ∑ i, x i ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hα : 0 < (n * S + 1) / 2 := by positivity
  -- the integrand is a product over the columns
  have hpt : ∀ y : Fin N → ℝ, Real.exp (-n * (∑ j, ∑ i, (x i * y j - A i j) ^ 2) / 2 +
      Real.sqrt n * (∑ j, ∑ i, (x i * y j - A i j) * Ξ i j) - (∑ j, y j ^ 2) / 2) =
      ∏ j, Real.exp (-((n * S + 1) / 2) * y j ^ 2 +
        (n * (∑ i, x i * A i j) + Real.sqrt n * (∑ i, x i * Ξ i j)) * y j -
          (n * (∑ i, A i j ^ 2) / 2 + Real.sqrt n * ∑ i, A i j * Ξ i j)) := by
    intro y
    rw [← Real.exp_sum]
    congr 1
    simp_rw [sum_sq_column, sum_field_column]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hS]
    ring
  simp_rw [hpt]
  rw [integral_fintype_prod_volume_eq_prod (fun j (t : ℝ) => Real.exp (-((n * S + 1) / 2) * t ^ 2 +
    (n * (∑ i, x i * A i j) + Real.sqrt n * (∑ i, x i * Ξ i j)) * t -
      (n * (∑ i, A i j ^ 2) / 2 + Real.sqrt n * ∑ i, A i j * Ξ i j)))]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [integral_exp_quadratic_real hα]
  have h1 : Real.pi / ((n * S + 1) / 2) = 2 * Real.pi / (n * S + 1) := by
    field_simp
  rw [h1]
  congr 2
  field_simp
  ring

end Grammar
