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

/-- The derivative of `A · S_ν(ξ)` at a point, for smooth `A`. -/
theorem hasDerivAt_mul_fluctuation {A : ℝ → ℝ} (hA : ContDiff ℝ ∞ A) (hξ : ContDiff ℝ ∞ ξ)
    {ν : ℝ} (hν : 0 < ν) (v : ℝ) :
    HasDerivAt (fun v => A v * fluctuation 1 ν (ξ v))
      (deriv A v * fluctuation 1 ν (ξ v) + A v * deriv ξ v * fluctuation 1 (ν + 1 / 2) (ξ v))
      v := by
  have hd : HasDerivAt (fun v => A v * fluctuation 1 ν (ξ v))
      (deriv A v * fluctuation 1 ν (ξ v) +
        A v * (1 * fluctuation 1 (ν + 1 / 2) (ξ v) * deriv ξ v)) v :=
    ((hA.differentiable (by simp)) v).hasDerivAt.mul
      ((hasDerivAt_fluctuation 1 _ one_pos hν (ξ v)).comp v
        ((hξ.differentiable (by simp)) v).hasDerivAt)
  refine hd.congr_deriv ?_
  ring

/-- ★ **The third one-dimensional coefficient**: with `μ = μ_3 = (h+4)/2k`, the seven-term formula
`C_3 = (η⁗ S_μ + 3η″ξ′ S_{μ+1/2} + 3η′(ξ″ S_{μ+1/2} + ξ′² S_{μ+1}) +
η(ξ⁗ S_{μ+1/2} + 3ξ′ξ″ S_{μ+1} + ξ′³ S_{μ+3/2}))(0) / (6·2k)` (primes denote `u`-derivatives at `0`,
`η⁗ = η'''`). -/
theorem empOneDimCoeff_three (hη : ContDiff ℝ ∞ η) (hξ : ContDiff ℝ ∞ ξ) (h : ℕ) {k : ℕ}
    (hk : 0 < k) :
    empOneDimCoeff η ξ h k 3 =
      (iteratedDeriv 3 η 0 * fluctuation 1 (lam k (3 + h)) (ξ 0) +
        3 * iteratedDeriv 2 η 0 * deriv ξ 0 * fluctuation 1 (lam k (3 + h) + 1 / 2) (ξ 0) +
        3 * deriv η 0 * (iteratedDeriv 2 ξ 0 * fluctuation 1 (lam k (3 + h) + 1 / 2) (ξ 0) +
          deriv ξ 0 ^ 2 * fluctuation 1 (lam k (3 + h) + 1) (ξ 0)) +
        η 0 * (iteratedDeriv 3 ξ 0 * fluctuation 1 (lam k (3 + h) + 1 / 2) (ξ 0) +
          3 * deriv ξ 0 * iteratedDeriv 2 ξ 0 * fluctuation 1 (lam k (3 + h) + 1) (ξ 0) +
          deriv ξ 0 ^ 3 * fluctuation 1 (lam k (3 + h) + 3 / 2) (ξ 0))) / (6 * (2 * k)) := by
  unfold empOneDimCoeff
  set μ := lam k (3 + h) with hμdef
  have hμ : 0 < μ := lam_pos hk _
  have hη' : ContDiff ℝ ∞ (deriv η) := hη.iterate_deriv 1
  have hη'' : ContDiff ℝ ∞ (deriv (deriv η)) := hη'.iterate_deriv 1
  have hξ' : ContDiff ℝ ∞ (deriv ξ) := hξ.iterate_deriv 1
  have hξ'' : ContDiff ℝ ∞ (deriv (deriv ξ)) := hξ'.iterate_deriv 1
  rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one, deriv_mul_fluctuation hη hξ hμ]
  have h2 : deriv (fun v => deriv η v * fluctuation 1 μ (ξ v) +
      η v * deriv ξ v * fluctuation 1 (μ + 1 / 2) (ξ v)) = fun v =>
      deriv (deriv η) v * fluctuation 1 μ (ξ v) +
        deriv η v * deriv ξ v * fluctuation 1 (μ + 1 / 2) (ξ v) +
        (deriv η v * deriv ξ v + η v * deriv (deriv ξ) v) * fluctuation 1 (μ + 1 / 2) (ξ v) +
        η v * deriv ξ v * deriv ξ v * fluctuation 1 (μ + 1 / 2 + 1 / 2) (ξ v) := by
    funext v
    have ha := hasDerivAt_mul_fluctuation hη' hξ hμ v
    have hb := hasDerivAt_mul_fluctuation (hη.mul hξ') hξ (by linarith : 0 < μ + 1 / 2) v
    have hab : HasDerivAt (fun v => deriv η v * fluctuation 1 μ (ξ v) +
        η v * deriv ξ v * fluctuation 1 (μ + 1 / 2) (ξ v))
        ((deriv (deriv η) v * fluctuation 1 μ (ξ v) +
          deriv η v * deriv ξ v * fluctuation 1 (μ + 1 / 2) (ξ v)) +
        (deriv (fun v => η v * deriv ξ v) v * fluctuation 1 (μ + 1 / 2) (ξ v) +
          η v * deriv ξ v * deriv ξ v * fluctuation 1 (μ + 1 / 2 + 1 / 2) (ξ v))) v := ha.add hb
    rw [hab.deriv]
    have hprod : deriv (fun v => η v * deriv ξ v) v =
        deriv η v * deriv ξ v + η v * deriv (deriv ξ) v :=
      (((hη.differentiable (by simp)) v).hasDerivAt.mul
        ((hξ'.differentiable (by simp)) v).hasDerivAt).deriv
    rw [hprod]
    ring
  rw [h2]
  have hc1 := hasDerivAt_mul_fluctuation hη'' hξ hμ 0
  have hc2 := hasDerivAt_mul_fluctuation (hη'.mul hξ') hξ (by linarith : 0 < μ + 1 / 2) 0
  have hc3 := hasDerivAt_mul_fluctuation ((hη'.mul hξ').add (hη.mul hξ'')) hξ
    (by linarith : 0 < μ + 1 / 2) 0
  have hc4 := hasDerivAt_mul_fluctuation ((hη.mul hξ').mul hξ') hξ
    (by linarith : 0 < μ + 1 / 2 + 1 / 2) 0
  have hsum : HasDerivAt (fun v => deriv (deriv η) v * fluctuation 1 μ (ξ v) +
      deriv η v * deriv ξ v * fluctuation 1 (μ + 1 / 2) (ξ v) +
      (deriv η v * deriv ξ v + η v * deriv (deriv ξ) v) * fluctuation 1 (μ + 1 / 2) (ξ v) +
      η v * deriv ξ v * deriv ξ v * fluctuation 1 (μ + 1 / 2 + 1 / 2) (ξ v))
      ((deriv (deriv (deriv η)) 0 * fluctuation 1 μ (ξ 0) +
          deriv (deriv η) 0 * deriv ξ 0 * fluctuation 1 (μ + 1 / 2) (ξ 0)) +
        (deriv (fun v => deriv η v * deriv ξ v) 0 * fluctuation 1 (μ + 1 / 2) (ξ 0) +
          deriv η 0 * deriv ξ 0 * deriv ξ 0 * fluctuation 1 (μ + 1 / 2 + 1 / 2) (ξ 0)) +
        (deriv (fun v => deriv η v * deriv ξ v + η v * deriv (deriv ξ) v) 0 *
            fluctuation 1 (μ + 1 / 2) (ξ 0) +
          (deriv η 0 * deriv ξ 0 + η 0 * deriv (deriv ξ) 0) * deriv ξ 0 *
            fluctuation 1 (μ + 1 / 2 + 1 / 2) (ξ 0)) +
        (deriv (fun v => η v * deriv ξ v * deriv ξ v) 0 *
            fluctuation 1 (μ + 1 / 2 + 1 / 2) (ξ 0) +
          η 0 * deriv ξ 0 * deriv ξ 0 * deriv ξ 0 *
            fluctuation 1 (μ + 1 / 2 + 1 / 2 + 1 / 2) (ξ 0))) 0 :=
    ((hc1.add hc2).add hc3).add hc4
  rw [hsum.deriv]
  have hd1 : deriv (fun v => deriv η v * deriv ξ v) 0 =
      deriv (deriv η) 0 * deriv ξ 0 + deriv η 0 * deriv (deriv ξ) 0 :=
    (((hη'.differentiable (by simp)) 0).hasDerivAt.mul
      ((hξ'.differentiable (by simp)) 0).hasDerivAt).deriv
  have hd2 : deriv (fun v => deriv η v * deriv ξ v + η v * deriv (deriv ξ) v) 0 =
      (deriv (deriv η) 0 * deriv ξ 0 + deriv η 0 * deriv (deriv ξ) 0) +
        (deriv η 0 * deriv (deriv ξ) 0 + η 0 * deriv (deriv (deriv ξ)) 0) :=
    ((((hη'.differentiable (by simp)) 0).hasDerivAt.mul
      ((hξ'.differentiable (by simp)) 0).hasDerivAt).add
      (((hη.differentiable (by simp)) 0).hasDerivAt.mul
        ((hξ''.differentiable (by simp)) 0).hasDerivAt)).deriv
  have hd3 : deriv (fun v => η v * deriv ξ v * deriv ξ v) 0 =
      (deriv η 0 * deriv ξ 0 + η 0 * deriv (deriv ξ) 0) * deriv ξ 0 +
        η 0 * deriv ξ 0 * deriv (deriv ξ) 0 :=
    ((((hη.differentiable (by simp)) 0).hasDerivAt.mul
      ((hξ'.differentiable (by simp)) 0).hasDerivAt).mul
      ((hξ'.differentiable (by simp)) 0).hasDerivAt).deriv
  rw [hd1, hd2, hd3]
  have hS1 : fluctuation 1 (μ + 1 / 2 + 1 / 2) (ξ 0) = fluctuation 1 (μ + 1) (ξ 0) := by
    congr 1
    ring
  have hS2 : fluctuation 1 (μ + 1 / 2 + 1 / 2 + 1 / 2) (ξ 0) =
      fluctuation 1 (μ + 3 / 2) (ξ 0) := by
    congr 1
    ring
  rw [hS1, hS2]
  simp only [iteratedDeriv_succ, iteratedDeriv_zero]
  have h3 : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
  rw [h3]
  ring

end SmoothEngine

end Grammar
