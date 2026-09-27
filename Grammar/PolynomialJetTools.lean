/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Grammar.GaussianResidualCutoffBounds

/-!
# Polynomial tools for the all-depth engine

The polynomial side of the depth step `P_L ↦ P_{L+1}` (Astra rounds 18–19), for
`P : Polynomial ℝ`:

* `eval_add_eq_sum_hasseDeriv` : Taylor's formula `P(x + y) = Σ_{j ≤ deg P} (H_j P)(x) y^j` with
  the Hasse derivatives `H_j P = P^{(j)}/j!` (Mathlib's `taylor`/`hasseDeriv`);
* `primZero` : the zero-normalised primitive, `derivative (primZero P) = P`, `(primZero P)(0) = 0`;
* `integral_eval_log_div` : the flat part `∫_a^1 P(ℓ + 2 log x)/x dx =
  [(primZero P)(ℓ) − (primZero P)(ℓ + 2 log a)]/2`;
* `abs_eval_le` : `|Q(ℓ)| ≤ (Σ_{i ≤ d}|coeff_i|)(1 + ℓ)^d` for `ℓ ≥ 0`, `deg Q ≤ d`;
* `exists_log_pow_cutoff_constant` : the absorption `(1 + ℓ)^d N^{−3/4} ≤ C(1 + ℓ)/√N` for `N ≥ 1`
  (from `log N ≤ N^ε/ε`), which is what makes the cutoff products of a polynomial of any degree
  cost `O((1 + ℓ)/√N)` after DCLVII's `a√a` moments.
Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology Polynomial Finset

namespace Grammar

/-! ### Taylor via Hasse derivatives -/

/-- `P(x + y) = Σ_{j ≤ deg P} (H_j P)(x) y^j`. -/
theorem eval_add_eq_sum_hasseDeriv (P : ℝ[X]) (x y : ℝ) :
    P.eval (x + y) = ∑ j ∈ range (P.natDegree + 1), (hasseDeriv j P).eval x * y ^ j := by
  rw [add_comm, ← taylor_eval x P y, eval_eq_sum_range, natDegree_taylor]
  simp only [taylor_coeff]

/-! ### The zero-normalised primitive -/

/-- The primitive with zero constant term: `Σ_k coeff_k X^{k+1}/(k+1)`. -/
noncomputable def primZero (P : ℝ[X]) : ℝ[X] :=
  ∑ k ∈ range (P.natDegree + 1), monomial (k + 1) (P.coeff k / (k + 1))

theorem derivative_primZero (P : ℝ[X]) : derivative (primZero P) = P := by
  unfold primZero
  rw [derivative_sum]
  conv_rhs => rw [as_sum_range P]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [derivative_monomial, Nat.add_sub_cancel]
  congr 1
  push_cast
  field_simp

theorem eval_primZero_zero (P : ℝ[X]) : (primZero P).eval 0 = 0 := by
  unfold primZero
  rw [eval_finsetSum]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [eval_monomial, zero_pow (Nat.succ_ne_zero k), mul_zero]

/-! ### The flat part for a general polynomial -/

theorem hasDerivAt_eval_log (Q : ℝ[X]) (ℓ : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun x => Q.eval (ℓ + 2 * Real.log x))
      (Q.derivative.eval (ℓ + 2 * Real.log x) * (2 * x⁻¹)) x := by
  have hl : HasDerivAt (fun x : ℝ => ℓ + 2 * Real.log x) (2 * x⁻¹) x :=
    ((Real.hasDerivAt_log hx.ne').const_mul 2).const_add ℓ
  exact (Q.hasDerivAt _).comp x hl

theorem integrableOn_eval_log_div (Q : ℝ[X]) (ℓ : ℝ) {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) :
    IntegrableOn (fun x => Q.eval (ℓ + 2 * Real.log x) / x) (Ioc a 1) := by
  rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le ha1]
  refine ContinuousOn.intervalIntegrable ?_
  refine ContinuousOn.div (ContinuousOn.comp Q.continuous.continuousOn
    (continuousOn_const.add (continuousOn_const.mul (Real.continuousOn_log.mono fun x hx => ?_)))
    (mapsTo_univ _ _)) continuousOn_id fun x hx => ?_
  · rw [uIcc_of_le ha1] at hx
    exact mem_compl_singleton_iff.2 (ne_of_gt (lt_of_lt_of_le ha0 hx.1))
  · rw [uIcc_of_le ha1] at hx
    exact ne_of_gt (lt_of_lt_of_le ha0 hx.1)

/-- ★★ The flat part: `∫_a^1 P(ℓ + 2 log x)/x dx = [(primZero P)(ℓ) − (primZero P)(ℓ + 2 log
  a)]/2`. -/
theorem integral_eval_log_div (P : ℝ[X]) (ℓ : ℝ) {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) :
    ∫ x in Ioc a 1, P.eval (ℓ + 2 * Real.log x) / x =
      ((primZero P).eval ℓ - (primZero P).eval (ℓ + 2 * Real.log a)) / 2 := by
  have hderiv : ∀ x ∈ uIcc a 1,
      HasDerivAt (fun x => (primZero P).eval (ℓ + 2 * Real.log x) / 2)
        (P.eval (ℓ + 2 * Real.log x) / x) x := by
    intro x hx
    rw [uIcc_of_le ha1] at hx
    have hx0 : 0 < x := lt_of_lt_of_le ha0 hx.1
    have := (hasDerivAt_eval_log (primZero P) ℓ hx0).div_const 2
    rw [derivative_primZero] at this
    refine this.congr_deriv ?_
    field_simp
  rw [← intervalIntegral.integral_of_le ha1, intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le ha1).2 (integrableOn_eval_log_div P ℓ ha0 ha1))]
  simp only [Real.log_one, mul_zero, add_zero]
  ring

/-! ### Coefficient bounds -/

/-- `|Q(ℓ)| ≤ (Σ_{i ≤ d} |coeff_i|)(1 + ℓ)^d` for `ℓ ≥ 0` and `deg Q ≤ d`. -/
theorem abs_eval_le (Q : ℝ[X]) {d : ℕ} (hd : Q.natDegree ≤ d) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    |Q.eval ℓ| ≤ (∑ i ∈ range (d + 1), |Q.coeff i|) * (1 + ℓ) ^ d := by
  rw [eval_eq_sum_range' (Nat.lt_succ_of_le hd), Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  rw [abs_mul, abs_pow, abs_of_nonneg hℓ]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have hi' : i ≤ d := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  calc ℓ ^ i ≤ (1 + ℓ) ^ i := pow_le_pow_left₀ hℓ (by linarith) i
    _ ≤ (1 + ℓ) ^ d := pow_le_pow_right₀ (by linarith) hi'

/-! ### Absorption of powers of `log N` -/

/-- `log N ≤ N^ε/ε` for `N > 0`, `ε > 0`. -/
theorem log_le_rpow_div {N ε : ℝ} (hN : 0 < N) (hε : 0 < ε) : Real.log N ≤ N ^ ε / ε := by
  have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hN ε)
  rw [Real.log_rpow hN] at h
  rw [le_div_iff₀ hε]
  linarith [Real.rpow_pos_of_pos hN ε]

/-- For every `d` there is `C` with `(1 + log N)^d ≤ C N^{1/4}` for `N ≥ 1`. -/
theorem exists_one_add_log_pow_le (d : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, 1 ≤ N → (1 + Real.log N) ^ d ≤ C * N ^ (1 / 4 : ℝ) := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    exact ⟨1, zero_le_one, fun N hN => by
      rw [pow_zero, one_mul]; exact Real.one_le_rpow hN (by norm_num)⟩
  · refine ⟨(1 + 4 * d) ^ d, by positivity, fun N hN => ?_⟩
    have hN0 : 0 < N := by linarith
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
    set ε : ℝ := 1 / (4 * d) with hε
    have hε0 : 0 < ε := by positivity
    have h1 : 1 ≤ N ^ ε := Real.one_le_rpow hN hε0.le
    have hlog : Real.log N ≤ 4 * d * N ^ ε := by
      have := log_le_rpow_div hN0 hε0
      have e : N ^ ε / ε = 4 * d * N ^ ε := by rw [hε]; field_simp
      linarith
    have h2 : 1 + Real.log N ≤ (1 + 4 * d) * N ^ ε := by nlinarith
    calc (1 + Real.log N) ^ d ≤ ((1 + 4 * d) * N ^ ε) ^ d :=
          pow_le_pow_left₀ (by linarith [Real.log_nonneg hN]) h2 d
      _ = (1 + 4 * d) ^ d * N ^ (1 / 4 : ℝ) := by
          rw [mul_pow, ← Real.rpow_natCast (N ^ ε) d, ← Real.rpow_mul hN0.le, hε]
          congr 2
          field_simp

/-- ★★ Absorption: `(1 + log N)^d N^{−3/4} ≤ C(1 + log N)/√N` for `N ≥ 1`. -/
theorem exists_log_pow_cutoff_constant (d : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, 1 ≤ N →
      (1 + Real.log N) ^ d * N ^ (-(3 / 4 : ℝ)) ≤ C * (1 + Real.log N) / Real.sqrt N := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    refine ⟨1, zero_le_one, fun N hN => ?_⟩
    have hN0 : 0 < N := by linarith
    have hℓ : 1 ≤ 1 + Real.log N := by linarith [Real.log_nonneg hN]
    have hs : 1 / Real.sqrt N = N ^ (-(1 / 2 : ℝ)) := by
      rw [Real.sqrt_eq_rpow, one_div, ← Real.rpow_neg hN0.le]
    rw [pow_zero, one_mul, one_mul]
    calc N ^ (-(3 / 4 : ℝ)) ≤ N ^ (-(1 / 2 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le hN (by norm_num)
      _ = 1 / Real.sqrt N := hs.symm
      _ ≤ (1 + Real.log N) / Real.sqrt N :=
          div_le_div_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)
  · obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, (Nat.sub_add_cancel hd).symm⟩
    obtain ⟨C, hC0, hC⟩ := exists_one_add_log_pow_le d'
    refine ⟨C, hC0, fun N hN => ?_⟩
    have hN0 : 0 < N := by linarith
    have hℓ : 0 ≤ 1 + Real.log N := by linarith [Real.log_nonneg hN]
    have hpow : N ^ (1 / 4 : ℝ) * N ^ (-(3 / 4 : ℝ)) = 1 / Real.sqrt N := by
      rw [← Real.rpow_add hN0, Real.sqrt_eq_rpow,
        show (1 / 4 : ℝ) + -(3 / 4) = -(1 / 2) by norm_num, Real.rpow_neg hN0.le]
      exact inv_eq_one_div _
    rw [pow_succ]
    calc (1 + Real.log N) ^ d' * (1 + Real.log N) * N ^ (-(3 / 4 : ℝ))
        ≤ C * N ^ (1 / 4 : ℝ) * (1 + Real.log N) * N ^ (-(3 / 4 : ℝ)) := by
          gcongr; exact hC N hN
      _ = C * (1 + Real.log N) * (N ^ (1 / 4 : ℝ) * N ^ (-(3 / 4 : ℝ))) := by ring
      _ = C * (1 + Real.log N) * (1 / Real.sqrt N) := by rw [hpow]
      _ = C * (1 + Real.log N) / Real.sqrt N := by ring

/-- The cutoff scale: `a√a = N^{−3/4}` for `a = 1/√N`. -/
theorem one_div_sqrt_mul_sqrt {N : ℝ} (hN : 0 < N) :
    1 / Real.sqrt N * Real.sqrt (1 / Real.sqrt N) = N ^ (-(3 / 4 : ℝ)) := by
  rw [Real.sqrt_eq_rpow, one_div, ← Real.rpow_neg hN.le, Real.sqrt_eq_rpow,
    ← Real.rpow_mul hN.le, ← Real.rpow_add hN]
  norm_num

end Grammar
