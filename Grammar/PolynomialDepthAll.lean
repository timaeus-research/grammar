/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.PolynomialDepthStep
import Grammar.GaussianDepthFiveConst

/-!
# The all-depth theorem and the acceptance tests

Iterating the depth step from the depth-two base case gives the full polynomial with the
linear-log rate at EVERY depth: `enginePoly 2 = P₂ = (X + 3 log 2 − γ)/s` (from DCXII's two-term
bound), `enginePoly (L+1) = stepPoly (enginePoly L) (residualMass L (enginePoly L))`, and
★★★ `hasPolyRate_enginePoly : ∀ L ≥ 2, HasPolyRate L (enginePoly L)`, i.e.
`|√N Z_L(N) − (enginePoly L)(log N)| ≤ K_L(1 + log N)/√N` for `N ≥ 1`.

The acceptance tests (Astra round 19) certify the engine against the hand-built depths:
`stepPoly P₂ Q₂ = P₃` (`stepPoly_two`, so `enginePoly 3 = P₃` with DCXXXI's `depthThreeConst`),
`stepPoly P₃ Q₃ = P₄` (`stepPoly_three`, DCLI's `depthFourConst`), `stepPoly P₄ Q₄ = P₅`
(`stepPoly_four`, DCLVI's `depthFiveLinCoeff`, `depthFiveConst`), the residual masses being
identified with `depthThreeQint`, `depthFourQint`, `depthFiveQint`.  Examples_slop §2.
Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology Polynomial Finset

namespace Grammar

/-! ### The explicit low-depth polynomials -/

/-- `P₂(u) = (u + 3 log 2 − γ)/s`. -/
noncomputable def depthTwoPoly : ℝ[X] :=
  C (1 / Real.sqrt (2 * Real.pi)) * X +
    C ((3 * Real.log 2 - Real.eulerMascheroniConstant) / Real.sqrt (2 * Real.pi))

/-- `P₃(u) = A₃u² + B₃u + C₃`. -/
noncomputable def depthThreePoly : ℝ[X] :=
  C (1 / (4 * Real.pi)) * X ^ 2 +
    C ((2 * Real.log 2 - Real.eulerMascheroniConstant) / Real.pi) * X + C depthThreeConst

/-- `P₄(u) = A₄u³ + B₄u² + C₄u + D₄`. -/
noncomputable def depthFourPoly : ℝ[X] :=
  C (gaussCoeffA 0) * X ^ 3 + C (gaussCoeffB 0) * X ^ 2 + C (thirdCoeff 0) * X + C depthFourConst

/-- `P₅(u) = A₅u⁴ + B₅u³ + C₅u² + D₅u + E₅`. -/
noncomputable def depthFivePoly : ℝ[X] :=
  C (gaussCoeffA 1) * X ^ 4 + C (gaussCoeffB 1) * X ^ 3 + C (thirdCoeff 1) * X ^ 2 +
    C depthFiveLinCoeff * X + C depthFiveConst

theorem eval_depthTwoPoly (u : ℝ) : depthTwoPoly.eval u =
    (u + (3 * Real.log 2 - Real.eulerMascheroniConstant)) / Real.sqrt (2 * Real.pi) := by
  simp only [depthTwoPoly, eval_add, eval_mul, eval_C, eval_X]; ring

theorem eval_depthThreePoly (u : ℝ) : depthThreePoly.eval u = depthThreeJet u := by
  simp only [depthThreePoly, depthThreeJet, eval_add, eval_mul, eval_C, eval_X, eval_pow]; ring

theorem eval_depthFourPoly (u : ℝ) : depthFourPoly.eval u = depthFourJet u := by
  simp only [depthFourPoly, depthFourJet, eval_add, eval_mul, eval_C, eval_X, eval_pow]

theorem eval_depthFivePoly (u : ℝ) : depthFivePoly.eval u =
    gaussCoeffA 1 * u ^ 4 + gaussCoeffB 1 * u ^ 3 + thirdCoeff 1 * u ^ 2 + depthFiveLinCoeff * u +
      depthFiveConst := by
  simp only [depthFivePoly, eval_add, eval_mul, eval_C, eval_X, eval_pow]

/-! ### The base case at depth two -/

/-- ★★ `HasPolyRate 2 P₂` from the depth-two two-term bound. -/
theorem hasPolyRate_two : HasPolyRate 2 depthTwoPoly := by
  set s := Real.sqrt (2 * Real.pi) with hs_def
  have hs : 0 < s := Real.sqrt_pos.2 (by positivity)
  refine ⟨2 / s, by positivity, fun N hN => ?_⟩
  have hN0 : 0 < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have hℓ : 0 ≤ Real.log N := Real.log_nonneg hN
  have h := gaussLaplace2_two_term_bound (by linarith : 1 / 2 ≤ N)
  have hsq : Real.sqrt (2 * Real.pi * N) = s * Real.sqrt N := by
    rw [hs_def, Real.sqrt_mul (by positivity)]
  rw [hsq] at h
  rw [gaussLaplaceL_two, eval_depthTwoPoly]
  have e : Real.sqrt N * gaussLaplace2 N -
      (Real.log N + (3 * Real.log 2 - Real.eulerMascheroniConstant)) / s =
      Real.sqrt N * (gaussLaplace2 N -
        (Real.log N + 3 * Real.log 2 - Real.eulerMascheroniConstant) / (s * Real.sqrt N)) := by
    field_simp
    ring
  have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hNs : Real.sqrt N ≤ N := by nlinarith [Real.sq_sqrt hN0.le]
  rw [e, abs_mul, abs_of_pos hsN]
  calc Real.sqrt N * |gaussLaplace2 N -
        (Real.log N + 3 * Real.log 2 - Real.eulerMascheroniConstant) / (s * Real.sqrt N)|
      ≤ Real.sqrt N * ((Real.log (2 * N) + 3) / (2 * N * (s * Real.sqrt N))) :=
        mul_le_mul_of_nonneg_left h hsN.le
    _ = (Real.log 2 + Real.log N + 3) / (2 * s * N) := by
        rw [Real.log_mul two_ne_zero hN0.ne']
        field_simp
    _ ≤ 4 * (1 + Real.log N) / (2 * s * N) := by
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        linarith
    _ = 2 * (1 + Real.log N) / s * (1 / N) := by ring
    _ ≤ 2 * (1 + Real.log N) / s * (1 / Real.sqrt N) := by
        gcongr
    _ = 2 / s * (1 + Real.log N) / Real.sqrt N := by ring

/-! ### The depth polynomials by iteration -/

/-- The polynomial at every depth: `enginePoly 2 = P₂`, `enginePoly (L+1) = stepPoly …`. -/
noncomputable def enginePoly : ℕ → ℝ[X]
  | 0 => 0
  | 1 => 0
  | 2 => depthTwoPoly
  | L + 3 => stepPoly (enginePoly (L + 2)) (residualMass (L + 2) (enginePoly (L + 2)))

theorem enginePoly_two : enginePoly 2 = depthTwoPoly := rfl

theorem enginePoly_succ (L : ℕ) (hL : 2 ≤ L) :
    enginePoly (L + 1) = stepPoly (enginePoly L) (residualMass L (enginePoly L)) := by
  obtain ⟨k, rfl⟩ : ∃ k, L = k + 2 := ⟨L - 2, by omega⟩
  rfl

/-- ★★★ **The all-depth theorem**: at every depth `L ≥ 2`,
`|√N Z_L(N) − (enginePoly L)(log N)| ≤ K_L (1 + log N)/√N` for `N ≥ 1`. -/
theorem hasPolyRate_enginePoly : ∀ L : ℕ, 2 ≤ L → HasPolyRate L (enginePoly L) := by
  intro L hL
  induction L with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge n 2 with h | h
    · have hn : n = 1 := by omega
      subst hn
      exact hasPolyRate_two
    · rw [enginePoly_succ n h]
      exact (ih h).step

/-! ### Evaluating Hasse derivatives and the primitive -/

theorem eval_hasseDeriv_zero (P : ℝ[X]) (u : ℝ) : (hasseDeriv 0 P).eval u = P.eval u := by
  rw [hasseDeriv_zero']

theorem eval_hasseDeriv_one (P : ℝ[X]) (u : ℝ) :
    (hasseDeriv 1 P).eval u = (derivative P).eval u := by
  rw [hasseDeriv_one']

theorem eval_hasseDeriv_two (P : ℝ[X]) (u : ℝ) :
    (hasseDeriv 2 P).eval u = (derivative (derivative P)).eval u / 2 := by
  have h := congrFun (factorial_smul_hasseDeriv (R := ℝ) (k := 2)) P
  simp only [LinearMap.smul_apply, Nat.factorial, Function.iterate_succ, Function.iterate_zero,
    Function.comp_apply, id] at h
  have h' := congrArg (fun q : ℝ[X] => q.eval u) h
  simp only [nsmul_eq_mul, eval_mul, eval_natCast] at h'
  norm_num at h'
  linarith

theorem eval_hasseDeriv_three (P : ℝ[X]) (u : ℝ) :
    (hasseDeriv 3 P).eval u = (derivative (derivative (derivative P))).eval u / 6 := by
  have h := congrFun (factorial_smul_hasseDeriv (R := ℝ) (k := 3)) P
  simp only [LinearMap.smul_apply, Nat.factorial, Function.iterate_succ, Function.iterate_zero,
    Function.comp_apply, id] at h
  have h' := congrArg (fun q : ℝ[X] => q.eval u) h
  simp only [nsmul_eq_mul, eval_mul, eval_natCast] at h'
  norm_num at h'
  linarith

/-- The primitive is characterised by its derivative and its value at `0`. -/
theorem primZero_eq_of {P G : ℝ[X]} (hG : derivative G = P) (h0 : G.eval 0 = 0) :
    primZero P = G := by
  have hd : derivative (primZero P - G) = 0 := by
    rw [derivative_sub, derivative_primZero, hG, sub_self]
  have h1 : primZero P - G = C ((primZero P - G).coeff 0) := eq_C_of_derivative_eq_zero hd
  have h2 : (primZero P - G).coeff 0 = 0 := by
    have := congrArg (fun q : ℝ[X] => q.eval 0) h1
    simp only [eval_sub, eval_primZero_zero, h0, sub_self, eval_C] at this
    exact this.symm
  rw [h2, C_0] at h1
  exact sub_eq_zero.1 h1

/-! ### The acceptance tests -/

theorem polyResidual_two_eq : polyResidual 2 depthTwoPoly = depthThreeQ := by
  funext v
  unfold polyResidual depthThreeQ
  rw [gaussLaplaceL_two]
  congr 1
  refine congrArg₂ _ ?_ rfl
  funext v
  rw [eval_depthTwoPoly]
  ring

theorem residualMass_two : residualMass 2 depthTwoPoly = depthThreeQint := by
  unfold residualMass depthThreeQint
  rw [polyResidual_two_eq]

theorem polyResidual_three_eq : polyResidual 3 depthThreePoly = depthFourQ := by
  funext v
  unfold polyResidual depthFourQ
  congr 1
  refine congrArg₂ _ ?_ rfl
  funext v
  rw [eval_depthThreePoly]

theorem residualMass_three : residualMass 3 depthThreePoly = depthFourQint := by
  unfold residualMass depthFourQint
  rw [polyResidual_three_eq]

theorem polyResidual_four_eq : polyResidual 4 depthFourPoly = depthFiveQ := by
  funext v
  unfold polyResidual depthFiveQ
  congr 1
  refine congrArg₂ _ ?_ rfl
  funext v
  rw [eval_depthFourPoly]

theorem residualMass_four : residualMass 4 depthFourPoly = depthFiveQint := by
  unfold residualMass depthFiveQint
  rw [polyResidual_four_eq]

theorem natDegree_depthTwoPoly : depthTwoPoly.natDegree = 1 :=
  natDegree_linear (by positivity)

theorem natDegree_depthThreePoly : depthThreePoly.natDegree = 2 :=
  natDegree_quadratic (by positivity)

theorem natDegree_depthFourPoly : depthFourPoly.natDegree = 3 :=
  natDegree_cubic (by unfold gaussCoeffA; positivity)

theorem primZero_depthTwoPoly : primZero depthTwoPoly =
    C (1 / (2 * Real.sqrt (2 * Real.pi))) * X ^ 2 +
      C ((3 * Real.log 2 - Real.eulerMascheroniConstant) / Real.sqrt (2 * Real.pi)) * X := by
  refine primZero_eq_of (Polynomial.funext fun u => ?_) (by simp)
  simp only [derivative_add, derivative_C_mul_X_pow, derivative_C_mul_X, eval_add, eval_mul,
    eval_C, eval_X, depthTwoPoly, Nat.reduceSub, pow_one, Nat.cast_ofNat]
  field_simp

theorem primZero_depthThreePoly : primZero depthThreePoly =
    C (1 / (12 * Real.pi)) * X ^ 3 +
      C ((2 * Real.log 2 - Real.eulerMascheroniConstant) / (2 * Real.pi)) * X ^ 2 +
      C depthThreeConst * X := by
  refine primZero_eq_of (Polynomial.funext fun u => ?_) (by simp)
  simp only [derivative_add, derivative_C_mul_X_pow, derivative_C_mul_X, eval_add, eval_mul,
    eval_C, eval_X, eval_pow, depthThreePoly, Nat.reduceSub, pow_one, Nat.cast_ofNat]
  field_simp
  ring

theorem primZero_depthFourPoly : primZero depthFourPoly =
    C (gaussCoeffA 0 / 4) * X ^ 4 + C (gaussCoeffB 0 / 3) * X ^ 3 + C (thirdCoeff 0 / 2) * X ^ 2 +
      C depthFourConst * X := by
  refine primZero_eq_of (Polynomial.funext fun u => ?_) (by simp)
  simp only [derivative_add, derivative_C_mul_X_pow, derivative_C_mul_X, eval_add, eval_mul,
    eval_C, eval_X, eval_pow, depthFourPoly, Nat.reduceSub, pow_one, Nat.cast_ofNat]
  ring

/-- The step from depth two reproduces `P₃` (DCXXXI's constant). -/
theorem stepPoly_two : stepPoly depthTwoPoly (residualMass 2 depthTwoPoly) = depthThreePoly := by
  rw [residualMass_two]
  refine Polynomial.funext fun u => ?_
  rw [eval_stepPoly, eval_depthThreePoly, natDegree_depthTwoPoly, primZero_depthTwoPoly]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, eval_hasseDeriv_zero,
    eval_hasseDeriv_one, eval_depthTwoPoly, eval_add, eval_mul, eval_C, eval_X, eval_pow]
  rw [show derivative depthTwoPoly = C (1 / Real.sqrt (2 * Real.pi)) by
    unfold depthTwoPoly; rw [derivative_add, derivative_C_mul_X, derivative_C, add_zero]]
  simp only [eval_C, pow_zero, pow_one]
  unfold depthThreeJet depthThreeConst gaussJlogPow gaussJlog
  simp only [pow_zero, pow_one, mul_one]
  rw [integral_gaussH_div]
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  set S := Real.sqrt (2 * Real.pi) with hS
  have hpi : Real.pi = S ^ 2 / 2 := by rw [hS, Real.sq_sqrt (by positivity)]; ring
  set J := ∫ x in Ioi (0 : ℝ), gaussH x * Real.log x / x
  set Q := depthThreeQint
  clear_value S J Q
  rw [hpi]
  field_simp
  ring

/-- The step from depth three reproduces `P₄` (DCLI's constant). -/
theorem stepPoly_three :
    stepPoly depthThreePoly (residualMass 3 depthThreePoly) = depthFourPoly := by
  rw [residualMass_three]
  refine Polynomial.funext fun u => ?_
  rw [eval_stepPoly, eval_depthFourPoly, natDegree_depthThreePoly, primZero_depthThreePoly]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, eval_hasseDeriv_zero,
    eval_hasseDeriv_one, eval_hasseDeriv_two, depthThreePoly, depthFourJet, derivative_add,
    derivative_C_mul_X_pow, derivative_C_mul_X, derivative_C, eval_add, eval_mul, eval_C, eval_X,
    eval_pow, Nat.reduceSub, pow_zero, pow_one, Nat.cast_ofNat, add_zero]
  unfold gaussJlogPow depthFourConst
  simp only [pow_zero, pow_one, mul_one]
  rw [integral_gaussH_div, gaussCoeffA_zero_eq, gaussCoeffB_zero_eq]
  unfold thirdCoeff depthThreeConst gaussR₀ gaussJlog gaussJlog2
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  set S := Real.sqrt (2 * Real.pi) with hS
  have hpi : Real.pi = S ^ 2 / 2 := by rw [hS, Real.sq_sqrt (by positivity)]; ring
  set J := ∫ x in Ioi (0 : ℝ), gaussH x * Real.log x / x
  set J2 := ∫ x in Ioi (0 : ℝ), gaussH x * Real.log x ^ 2 / x
  set Q2 := depthThreeQint
  set Q3 := depthFourQint
  clear_value S J J2 Q2 Q3
  rw [hpi]
  field_simp
  ring

/-- The step from depth four reproduces `P₅` (DCLVI's coefficients). -/
theorem stepPoly_four :
    stepPoly depthFourPoly (residualMass 4 depthFourPoly) = depthFivePoly := by
  rw [residualMass_four]
  refine Polynomial.funext fun u => ?_
  rw [eval_stepPoly, eval_depthFivePoly, natDegree_depthFourPoly, primZero_depthFourPoly]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, eval_hasseDeriv_zero,
    eval_hasseDeriv_one, eval_hasseDeriv_two, eval_hasseDeriv_three, depthFourPoly,
    derivative_add, derivative_C_mul_X_pow, derivative_C_mul_X, derivative_C, eval_add, eval_mul,
    eval_C, eval_X, eval_pow, Nat.reduceSub, pow_zero, pow_one, Nat.cast_ofNat, add_zero]
  unfold gaussJlogPow depthFiveLinCoeff depthFiveConst
  simp only [pow_zero, pow_one, mul_one]
  rw [integral_gaussH_div, thirdCoeff_one_eq, gaussCoeffA_zero_eq, gaussCoeffB_zero_eq,
    gaussCoeffA_one_eq, gaussCoeffB_one_eq]
  unfold gaussR₀ gaussJlog gaussJlog2 gaussJlog3
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  set S := Real.sqrt (2 * Real.pi) with hS
  set J := ∫ x in Ioi (0 : ℝ), gaussH x * Real.log x / x
  set J2 := ∫ x in Ioi (0 : ℝ), gaussH x * Real.log x ^ 2 / x
  set J3 := ∫ x in Ioi (0 : ℝ), gaussH x * Real.log x ^ 3 / x
  set C4 := thirdCoeff 0
  set D4 := depthFourConst
  set Q4 := depthFiveQint
  clear_value S J J2 J3 C4 D4 Q4
  field_simp
  ring

end Grammar
