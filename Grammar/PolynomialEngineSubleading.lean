/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.PolynomialEngineCoefficients
import Grammar.DepthThreeConstExact

/-!
# The second and third coefficients from the engine

The coefficient recursion of DCLXVI, with only the `j = 0` (resp. `j = 0, 1`) Hasse terms
surviving at the top, gives the subleading coefficients of `enginePoly L` in closed form at
every depth: ★★ `coeff_enginePoly_second : (enginePoly L)_{L−2} = [(L+1) log 2 − (L−1)γ]/((L−2)! s^{L−1})`
for `L ≥ 2` (DCXXVI's `B_L`; recursion `B_{L+1} = B_L/(s(L−1)) + 2R₀A_L/s`) and
★★ `coeff_enginePoly_third : (enginePoly L)_{L−3} = [D_L² + (L+3)π²/6]/(2(L−3)! s^{L−1})`,
`D_L = (L+1) log 2 − (L−1)γ`, for `L ≥ 3` (DCXLVI's `C_L`, seeded by DCXLV's exact `C₃`;
recursion `C_{L+1} = C_L/(s(L−2)) + (2/s)[R₀B_L + 2(L−1)JA_L]` with `J = R₀²/2 + π²/48`).
The engine therefore re-derives the three closed leading coefficients of eq. dln_gauss from the
depth-two base case alone.  Astra round 20, target (a) (stretch).  Examples_slop §2.
Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology Polynomial Finset

namespace Grammar

theorem enginePoly_three : enginePoly 3 = depthThreePoly := by
  rw [enginePoly_succ 2 le_rfl, enginePoly_two, stepPoly_two]

theorem coeff_depthTwoPoly_zero :
    depthTwoPoly.coeff 0 = (3 * Real.log 2 - Real.eulerMascheroniConstant) / Real.sqrt (2 * Real.pi) := by
  unfold depthTwoPoly; simp

theorem coeff_depthThreePoly_zero : depthThreePoly.coeff 0 = depthThreeConst := by
  unfold depthThreePoly; simp

/-- The coefficients of `enginePoly L` above the degree vanish. -/
theorem coeff_enginePoly_eq_zero {L n : ℕ} (hL : 2 ≤ L) (hn : L - 1 < n) :
    (enginePoly L).coeff n = 0 :=
  coeff_eq_zero_of_natDegree_lt (by rw [natDegree_enginePoly L hL]; exact hn)

/-- ★★ The second coefficient at every depth `L ≥ 2`: `B_L = [(L+1) log 2 − (L−1)γ]/((L−2)! s^{L−1})`. -/
theorem coeff_enginePoly_second :
    ∀ L : ℕ, 2 ≤ L → (enginePoly L).coeff (L - 2) =
      (((L : ℝ) + 1) * Real.log 2 - ((L : ℝ) - 1) * Real.eulerMascheroniConstant) /
        (((L - 2).factorial : ℝ) * Real.sqrt (2 * Real.pi) ^ (L - 1)) := by
  refine Nat.le_induction ?_ fun n hn ih => ?_
  · rw [enginePoly_two, coeff_depthTwoPoly_zero]
    norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
    have hA := coeff_enginePoly_top (m + 2) hn
    rw [show m + 2 - 1 = m + 1 from rfl] at hA
    rw [show m + 2 - 2 = m from rfl] at ih
    rw [enginePoly_succ (m + 2) hn, show m + 2 + 1 - 2 = m + 1 from rfl, coeff_stepPoly_succ,
      natDegree_enginePoly (m + 2) hn, show m + 2 - 1 = m + 1 from rfl, Finset.sum_range_succ',
      Finset.sum_eq_zero (fun j _ => by
        rw [coeff_enginePoly_eq_zero hn (by omega)]; ring), zero_add]
    simp only [add_zero, pow_zero, Nat.choose_zero_right, Nat.cast_one, one_mul, mul_one]
    rw [ih, hA, gaussJlogPow_zero]
    unfold gaussR₀
    simp only [show m + 2 + 1 - 1 = m + 2 from rfl, Nat.factorial_succ m]
    push_cast
    field_simp
    ring

/-- ★★ The third coefficient at every depth `L ≥ 3`:
`C_L = [((L+1) log 2 − (L−1)γ)² + (L+3)π²/6]/(2(L−3)! s^{L−1})`. -/
theorem coeff_enginePoly_third :
    ∀ L : ℕ, 3 ≤ L → (enginePoly L).coeff (L - 3) =
      ((((L : ℝ) + 1) * Real.log 2 - ((L : ℝ) - 1) * Real.eulerMascheroniConstant) ^ 2 +
        ((L : ℝ) + 3) * Real.pi ^ 2 / 6) /
        (2 * ((L - 3).factorial : ℝ) * Real.sqrt (2 * Real.pi) ^ (L - 1)) := by
  refine Nat.le_induction ?_ fun n hn ih => ?_
  · rw [enginePoly_three, coeff_depthThreePoly_zero, depthThreeConst_eq]
    have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
    set S := Real.sqrt (2 * Real.pi) with hS
    have hpi : Real.pi = S ^ 2 / 2 := by rw [hS, Real.sq_sqrt (by positivity)]; ring
    clear_value S
    rw [hpi]
    norm_num
    field_simp
    ring
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    have hn2 : 2 ≤ m + 3 := by omega
    have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
    have hA := coeff_enginePoly_top (m + 3) hn2
    rw [show m + 3 - 1 = m + 2 from rfl] at hA
    have hB := coeff_enginePoly_second (m + 3) hn2
    rw [show m + 3 - 2 = m + 1 from rfl] at hB
    rw [show m + 3 - 3 = m from rfl] at ih
    rw [enginePoly_succ (m + 3) hn2, show m + 3 + 1 - 3 = m + 1 from rfl, coeff_stepPoly_succ,
      natDegree_enginePoly (m + 3) hn2, show m + 3 - 1 = m + 2 from rfl, Finset.sum_range_succ',
      Finset.sum_range_succ', Finset.sum_eq_zero (fun j _ => by
        rw [coeff_enginePoly_eq_zero hn2 (by omega)]; ring), zero_add]
    simp only [add_zero, zero_add, add_assoc, Nat.reduceAdd, pow_zero, pow_one,
      Nat.choose_zero_right, Nat.choose_one_right, Nat.cast_one, one_mul, mul_one]
    rw [ih, hB, hA, gaussJlogPow_zero, gaussJlogPow_one, gaussJlog_eq]
    unfold gaussR₀
    simp only [show m + 4 - 1 = m + 3 from rfl, Nat.factorial_succ (m + 1), Nat.factorial_succ m]
    push_cast
    field_simp
    ring

end Grammar
