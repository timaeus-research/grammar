/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.PolynomialRateUnique

/-!
# The coefficient recursion of the engine

The step `stepPoly` acts on coefficients explicitly (Astra round 20, target (a)):
`(step P Q)₀ = (2/s)[Σ_j 2^j J_j P_j + Q]` (`coeff_stepPoly_zero`) and
`(step P Q)_{k+1} = P_k/(s(k+1)) + (2/s) Σ_j 2^j J_j C(k+1+j, j) P_{k+1+j}` (`coeff_stepPoly_succ`),
from `coeff_primZero_succ` and Mathlib's `hasseDeriv_coeff`.  Hence the degree grows by exactly
one (`natDegree_stepPoly`) with leading coefficient divided by `s(deg P + 1)`
(`leadingCoeff_stepPoly`), so at every depth `L ≥ 2`
`natDegree (enginePoly L) = L − 1` and the leading coefficient is `1/((L−1)! s^{L−1})`
(★★ `leadingCoeff_enginePoly`, `coeff_enginePoly_top`): the engine re-derives the all-depth leading
asymptotic of DCXXIV.  Also the moment aliases `gaussJlogPow_zero/one/two/three`
(`= gaussR₀, gaussJlog, gaussJlog2, gaussJlog3`).  Examples_slop §2.
Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology Polynomial Finset

namespace Grammar

/-! ### The moment aliases -/

theorem gaussJlogPow_zero : gaussJlogPow 0 = gaussR₀ := by
  unfold gaussJlogPow gaussR₀
  simp only [pow_zero, mul_one]
  exact integral_gaussH_div

theorem gaussJlogPow_one : gaussJlogPow 1 = gaussJlog := by
  unfold gaussJlogPow gaussJlog; simp only [pow_one]

theorem gaussJlogPow_two : gaussJlogPow 2 = gaussJlog2 := rfl

theorem gaussJlogPow_three : gaussJlogPow 3 = gaussJlog3 := rfl

/-! ### Coefficients of the primitive -/

theorem coeff_primZero_zero (P : ℝ[X]) : (primZero P).coeff 0 = 0 := by
  rw [coeff_zero_eq_eval_zero, eval_primZero_zero]

theorem coeff_primZero_succ (P : ℝ[X]) (k : ℕ) :
    (primZero P).coeff (k + 1) = P.coeff k / (k + 1) := by
  unfold primZero
  rw [finsetSum_coeff]
  simp only [coeff_monomial, add_left_inj]
  rw [Finset.sum_ite_eq' (range (P.natDegree + 1)) k]
  split_ifs with hk
  · rfl
  · rw [coeff_eq_zero_of_natDegree_lt (by
      rw [Finset.mem_range] at hk; omega), zero_div]

theorem natDegree_primZero_le (P : ℝ[X]) : (primZero P).natDegree ≤ P.natDegree + 1 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [coeff_primZero_succ, coeff_eq_zero_of_natDegree_lt (by omega), zero_div]

theorem natDegree_primZero {P : ℝ[X]} (hP : P ≠ 0) :
    (primZero P).natDegree = P.natDegree + 1 := by
  refine natDegree_eq_of_le_of_coeff_ne_zero (natDegree_primZero_le P) ?_
  rw [coeff_primZero_succ, coeff_natDegree]
  exact div_ne_zero (leadingCoeff_ne_zero.2 hP) (by positivity)

/-! ### The Hasse sum and the step -/

/-- The Hasse part of the step, `Σ_{j ≤ deg P} 2^j J_j H_j P`. -/
noncomputable def hasseSum (P : ℝ[X]) : ℝ[X] :=
  ∑ j ∈ range (P.natDegree + 1), C (2 ^ j * gaussJlogPow j) * hasseDeriv j P

theorem stepPoly_eq (P : ℝ[X]) (Q : ℝ) :
    stepPoly P Q = C (1 / Real.sqrt (2 * Real.pi)) * primZero P +
      C (2 / Real.sqrt (2 * Real.pi)) * hasseSum P + C (2 * Q / Real.sqrt (2 * Real.pi)) := rfl

theorem coeff_hasseSum (P : ℝ[X]) (k : ℕ) :
    (hasseSum P).coeff k = ∑ j ∈ range (P.natDegree + 1),
      2 ^ j * gaussJlogPow j * ((k + j).choose j : ℝ) * P.coeff (k + j) := by
  unfold hasseSum
  rw [finsetSum_coeff]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coeff_C_mul, hasseDeriv_coeff]
  ring

/-- ★★ The constant term of the step: `(2/s)[Σ_j 2^j J_j P_j + Q]`. -/
theorem coeff_stepPoly_zero (P : ℝ[X]) (Q : ℝ) :
    (stepPoly P Q).coeff 0 = 2 / Real.sqrt (2 * Real.pi) *
      ((∑ j ∈ range (P.natDegree + 1), 2 ^ j * gaussJlogPow j * P.coeff j) + Q) := by
  rw [stepPoly_eq, coeff_add, coeff_add, coeff_C_mul, coeff_C_mul, coeff_primZero_zero,
    coeff_hasseSum, coeff_C_zero]
  simp only [zero_add, Nat.choose_self, Nat.cast_one, mul_one]
  ring

/-- ★★ The higher coefficients of the step:
`(step P Q)_{k+1} = P_k/(s(k+1)) + (2/s) Σ_j 2^j J_j C(k+1+j, j) P_{k+1+j}`. -/
theorem coeff_stepPoly_succ (P : ℝ[X]) (Q : ℝ) (k : ℕ) :
    (stepPoly P Q).coeff (k + 1) = P.coeff k / (Real.sqrt (2 * Real.pi) * (k + 1)) +
      2 / Real.sqrt (2 * Real.pi) * ∑ j ∈ range (P.natDegree + 1),
        2 ^ j * gaussJlogPow j * ((k + 1 + j).choose j : ℝ) * P.coeff (k + 1 + j) := by
  rw [stepPoly_eq, coeff_add, coeff_add, coeff_C_mul, coeff_C_mul, coeff_primZero_succ,
    coeff_hasseSum, coeff_C_of_ne_zero (Nat.succ_ne_zero k)]
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  field_simp
  ring

theorem natDegree_stepPoly_le (P : ℝ[X]) (Q : ℝ) :
    (stepPoly P Q).natDegree ≤ P.natDegree + 1 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [coeff_stepPoly_succ, coeff_eq_zero_of_natDegree_lt (by omega), zero_div, zero_add,
    Finset.sum_eq_zero fun j _ => by
      rw [coeff_eq_zero_of_natDegree_lt (by omega)]; ring, mul_zero]

theorem coeff_stepPoly_top {P : ℝ[X]} (Q : ℝ) :
    (stepPoly P Q).coeff (P.natDegree + 1) =
      P.leadingCoeff / (Real.sqrt (2 * Real.pi) * (P.natDegree + 1)) := by
  rw [coeff_stepPoly_succ, coeff_natDegree, Finset.sum_eq_zero fun j _ => by
    rw [coeff_eq_zero_of_natDegree_lt (by omega)]; ring, mul_zero, add_zero]

/-- ★★ The degree grows by exactly one. -/
theorem natDegree_stepPoly {P : ℝ[X]} (hP : P ≠ 0) (Q : ℝ) :
    (stepPoly P Q).natDegree = P.natDegree + 1 := by
  refine natDegree_eq_of_le_of_coeff_ne_zero (natDegree_stepPoly_le P Q) ?_
  rw [coeff_stepPoly_top]
  exact div_ne_zero (leadingCoeff_ne_zero.2 hP) (by positivity)

theorem stepPoly_ne_zero {P : ℝ[X]} (hP : P ≠ 0) (Q : ℝ) : stepPoly P Q ≠ 0 := by
  intro h
  have := natDegree_stepPoly hP Q
  rw [h, natDegree_zero] at this
  omega

theorem leadingCoeff_stepPoly {P : ℝ[X]} (hP : P ≠ 0) (Q : ℝ) :
    (stepPoly P Q).leadingCoeff =
      P.leadingCoeff / (Real.sqrt (2 * Real.pi) * (P.natDegree + 1)) := by
  rw [leadingCoeff, natDegree_stepPoly hP Q, coeff_stepPoly_top]

/-! ### The engine's degree and leading coefficient at every depth -/

theorem leadingCoeff_depthTwoPoly :
    depthTwoPoly.leadingCoeff = 1 / Real.sqrt (2 * Real.pi) := by
  rw [leadingCoeff, natDegree_depthTwoPoly]
  unfold depthTwoPoly
  simp

theorem depthTwoPoly_ne_zero : depthTwoPoly ≠ 0 := by
  intro h
  have := natDegree_depthTwoPoly
  rw [h, natDegree_zero] at this
  omega

theorem enginePoly_ne_zero_and_natDegree :
    ∀ L : ℕ, 2 ≤ L → enginePoly L ≠ 0 ∧ (enginePoly L).natDegree = L - 1 := by
  refine Nat.le_induction ⟨depthTwoPoly_ne_zero, natDegree_depthTwoPoly⟩ fun n hn ih => ?_
  rw [enginePoly_succ n hn]
  refine ⟨stepPoly_ne_zero ih.1 _, ?_⟩
  rw [natDegree_stepPoly ih.1, ih.2]
  omega

theorem enginePoly_ne_zero (L : ℕ) (hL : 2 ≤ L) : enginePoly L ≠ 0 :=
  (enginePoly_ne_zero_and_natDegree L hL).1

/-- ★★ `natDegree (enginePoly L) = L − 1`. -/
theorem natDegree_enginePoly (L : ℕ) (hL : 2 ≤ L) : (enginePoly L).natDegree = L - 1 :=
  (enginePoly_ne_zero_and_natDegree L hL).2

/-- ★★ The leading coefficient at every depth: `1/((L−1)! s^{L−1})` (DCXXIV's `A_L`). -/
theorem leadingCoeff_enginePoly :
    ∀ L : ℕ, 2 ≤ L → (enginePoly L).leadingCoeff =
      1 / (((L - 1).factorial : ℝ) * Real.sqrt (2 * Real.pi) ^ (L - 1)) := by
  refine Nat.le_induction ?_ fun n hn ih => ?_
  · rw [enginePoly_two, leadingCoeff_depthTwoPoly]
    simp
  · rw [enginePoly_succ n hn, leadingCoeff_stepPoly (enginePoly_ne_zero n hn), ih,
      natDegree_enginePoly n hn]
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    simp only [show k + 2 + 1 - 1 = k + 2 from rfl, show k + 2 - 1 = k + 1 from rfl,
      Nat.factorial_succ (k + 1), pow_succ]
    push_cast
    field_simp

/-- ★★ `(enginePoly L).coeff (L − 1) = 1/((L−1)! s^{L−1})`. -/
theorem coeff_enginePoly_top (L : ℕ) (hL : 2 ≤ L) :
    (enginePoly L).coeff (L - 1) =
      1 / (((L - 1).factorial : ℝ) * Real.sqrt (2 * Real.pi) ^ (L - 1)) := by
  rw [← natDegree_enginePoly L hL, coeff_natDegree, leadingCoeff_enginePoly L hL,
    natDegree_enginePoly L hL]

end Grammar
