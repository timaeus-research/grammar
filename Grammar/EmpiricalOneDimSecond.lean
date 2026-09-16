/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.EmpiricalOneDim

/-!
# The second one-dimensional empirical coefficient (§20, consult #146 item 2)

The coefficients of the one-dimensional empirical expansion are
`C_j = ∂_u^j[η(u) S_{μ_j}(ξ(u))]|_{u=0} / (j!·2k)`, `μ_j = (h+j+1)/2k` (`empOneDimCoeff`). Expanding
the derivatives with the ladder `∂_a S_μ = S_{μ+1/2}` gives the closed forms of the old Taylor-tree
draft: `C_0 = η S_{μ_0}/2k`, `C_1 = (η' S_{μ_1} + η ξ' S_{μ_1+1/2})/2k` (`EmpiricalOneDim`), and
★ `empOneDimCoeff_two`:
`C_2 = (η'' S_μ + 2η'ξ' S_{μ+1/2} + η(ξ'' S_{μ+1/2} + ξ'^2 S_{μ+1}))(0) / (2·2k)`,
`μ = μ_2 = (h+3)/2k`.
No logarithmic weights appear in one dimension. Zero `sorry`/`axiom`.
-/

open Real
open scoped ContDiff

namespace Grammar

namespace SmoothEngine

variable {η ξ : ℝ → ℝ}

/-- The derivative of `η · S_μ(ξ)` as a function: `η' S_μ(ξ) + η ξ' S_{μ+1/2}(ξ)`. -/
theorem deriv_mul_fluctuation (hη : ContDiff ℝ ∞ η) (hξ : ContDiff ℝ ∞ ξ) {μ : ℝ} (hμ : 0 < μ) :
    deriv (fun v => η v * fluctuation 1 μ (ξ v)) = fun v =>
      deriv η v * fluctuation 1 μ (ξ v) + η v * deriv ξ v * fluctuation 1 (μ + 1 / 2) (ξ v) := by
  funext v
  have hd : HasDerivAt (fun v => η v * fluctuation 1 μ (ξ v))
      (deriv η v * fluctuation 1 μ (ξ v) +
        η v * (1 * fluctuation 1 (μ + 1 / 2) (ξ v) * deriv ξ v)) v :=
    ((hη.differentiable (by simp)) v).hasDerivAt.mul
      ((hasDerivAt_fluctuation 1 _ one_pos hμ (ξ v)).comp v
        ((hξ.differentiable (by simp)) v).hasDerivAt)
  rw [hd.deriv]
  ring

/-- ★ **The second one-dimensional coefficient**: with `μ = μ_2 = (h+3)/2k`,
`C_2 = (η''(0) S_μ(ξ0) + 2η'(0)ξ'(0) S_{μ+1/2}(ξ0) +
η(0)(ξ''(0) S_{μ+1/2}(ξ0) + ξ'(0)² S_{μ+1}(ξ0))) / (2·2k)`. -/
theorem empOneDimCoeff_two (hη : ContDiff ℝ ∞ η) (hξ : ContDiff ℝ ∞ ξ) (h : ℕ) {k : ℕ}
    (hk : 0 < k) :
    empOneDimCoeff η ξ h k 2 =
      (iteratedDeriv 2 η 0 * fluctuation 1 (lam k (2 + h)) (ξ 0) +
        2 * deriv η 0 * deriv ξ 0 * fluctuation 1 (lam k (2 + h) + 1 / 2) (ξ 0) +
        η 0 * (iteratedDeriv 2 ξ 0 * fluctuation 1 (lam k (2 + h) + 1 / 2) (ξ 0) +
          deriv ξ 0 ^ 2 * fluctuation 1 (lam k (2 + h) + 1) (ξ 0))) / (2 * (2 * k)) := by
  unfold empOneDimCoeff
  have hμ : 0 < lam k (2 + h) := lam_pos hk _
  have hη' : ContDiff ℝ ∞ (deriv η) := hη.iterate_deriv 1
  have hξ' : ContDiff ℝ ∞ (deriv ξ) := hξ.iterate_deriv 1
  rw [iteratedDeriv_succ, iteratedDeriv_one, deriv_mul_fluctuation hη hξ hμ]
  have h1 : HasDerivAt (fun v => deriv η v * fluctuation 1 (lam k (2 + h)) (ξ v))
      (deriv (deriv η) 0 * fluctuation 1 (lam k (2 + h)) (ξ 0) +
        deriv η 0 * (1 * fluctuation 1 (lam k (2 + h) + 1 / 2) (ξ 0) * deriv ξ 0)) 0 :=
    ((hη'.differentiable (by simp)) 0).hasDerivAt.mul
      ((hasDerivAt_fluctuation 1 _ one_pos hμ (ξ 0)).comp 0
        ((hξ.differentiable (by simp)) 0).hasDerivAt)
  have h2 : HasDerivAt (fun v => η v * deriv ξ v * fluctuation 1 (lam k (2 + h) + 1 / 2) (ξ v))
      ((deriv η 0 * deriv ξ 0 + η 0 * deriv (deriv ξ) 0) *
          fluctuation 1 (lam k (2 + h) + 1 / 2) (ξ 0) +
        η 0 * deriv ξ 0 *
          (1 * fluctuation 1 (lam k (2 + h) + 1 / 2 + 1 / 2) (ξ 0) * deriv ξ 0)) 0 :=
    (((hη.differentiable (by simp)) 0).hasDerivAt.mul
      ((hξ'.differentiable (by simp)) 0).hasDerivAt).mul
      ((hasDerivAt_fluctuation 1 _ one_pos (by linarith) (ξ 0)).comp 0
        ((hξ.differentiable (by simp)) 0).hasDerivAt)
  have h12 : HasDerivAt (fun v => deriv η v * fluctuation 1 (lam k (2 + h)) (ξ v) +
      η v * deriv ξ v * fluctuation 1 (lam k (2 + h) + 1 / 2) (ξ v))
      ((deriv (deriv η) 0 * fluctuation 1 (lam k (2 + h)) (ξ 0) +
        deriv η 0 * (1 * fluctuation 1 (lam k (2 + h) + 1 / 2) (ξ 0) * deriv ξ 0)) +
      ((deriv η 0 * deriv ξ 0 + η 0 * deriv (deriv ξ) 0) *
          fluctuation 1 (lam k (2 + h) + 1 / 2) (ξ 0) +
        η 0 * deriv ξ 0 *
          (1 * fluctuation 1 (lam k (2 + h) + 1 / 2 + 1 / 2) (ξ 0) * deriv ξ 0))) 0 := h1.add h2
  rw [h12.deriv]
  have hS : fluctuation 1 (lam k (2 + h) + 1 / 2 + 1 / 2) (ξ 0) =
      fluctuation 1 (lam k (2 + h) + 1) (ξ 0) := by
    congr 1
    ring
  rw [hS, iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_succ, iteratedDeriv_one]
  simp only [Nat.factorial_two, Nat.cast_ofNat]
  ring

end SmoothEngine

end Grammar
