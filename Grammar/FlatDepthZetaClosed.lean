/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.DepthZetaClosedForms
import Grammar.CrossingFlatDepth

/-!
# §2 corollaries: the flat-prior polynomials in ζ-values, and the depressed form at every depth

* The half-point log-moments `H_j = ∫₀^∞ e^{−x}x^{−1/2}log^j x` are `Γ^{(j)}(½)` (DCLXXIII), so with
  DCLXXII and the ζ-bridge `H₃ = √π[−p³ − 3pπ²/2 − 14ζ(3)]`, `p = γ + 2 log 2`
  (`gammaLogMoment_three`), and DCI's flat-prior identity at depths two and three reads
  `Z_N = √(2π)/(2√N)·[(log N + γ + log 2)² + π²/2] − R`,
  `Z_N = √(2π)/(6√N)·[t³ + (3π²/2)t + 14ζ(3)] − R`, `t = log N + γ + log 2`, with
  `|R| ≤ (2/N)^{m+1}e^{−N/2}` (★★ `depthInt_two_closed`, ★★★ `depthInt_three_closed`): the note's
  `Q₂`, `Q₃`.
* The depressed form: in the centred variable `t = log N + κ_L`, `κ_L = (L+1) log 2 − (L−1)γ`, the
  engine polynomial has no `t^{L−2}` term at any depth `L ≥ 2`
  (★★ `taylor_enginePoly_coeff_sub_two`, via `Polynomial.taylor_coeff` and DCLXVII's second
  coefficient).  Astra round 29, items 2(a)–(b).  Zero `sorry`/`axiom`.
-/

open Filter Topology Polynomial

namespace Grammar

/-! ### The half-point log-moments in ζ-values -/

theorem gammaThirdOne_eq_zeta :
    gammaThirdOne = -2 * (riemannZeta 3).re - Real.eulerMascheroniConstant ^ 3 -
      Real.eulerMascheroniConstant * Real.pi ^ 2 / 2 := by
  have h := gammaLogThirdOne_eq_zeta
  unfold gammaLogThirdOne at h
  linarith

/-- `H₃ = Γ'''(½) = √π[−p³ − 3pπ²/2 − 14ζ(3)]`, `p = γ + 2 log 2`. -/
theorem gammaLogMoment_three :
    gammaLogMoment 3 = Real.sqrt Real.pi *
      (-(Real.eulerMascheroniConstant + 2 * Real.log 2) ^ 3 -
        3 * (Real.eulerMascheroniConstant + 2 * Real.log 2) * Real.pi ^ 2 / 2 -
        14 * (riemannZeta 3).re) := by
  have h := gammaLogMoment_eq_iterate 3
  rw [show deriv^[3] Complex.Gamma (1 / 2) = deriv (deriv (deriv Complex.Gamma)) (1 / 2) from rfl,
    deriv_deriv_deriv_Gamma_one_half] at h
  have hG : deriv (deriv (deriv Complex.Gamma)) 1 = ((gammaThirdOne : ℝ) : ℂ) := by
    rw [← gammaOneLogMoment_three_eq, gammaOneLogMoment_eq_iterate]
    rfl
  rw [hG] at h
  have h' := congrArg Complex.re h
  rw [Complex.ofReal_re, Complex.add_re, Complex.re_ofReal_mul, Complex.ofReal_re,
    Complex.ofReal_re, gammaThirdOne_eq_zeta] at h'
  rw [h']
  ring

/-- `P₂(X) = √π[(X + p)² + π²/2]` (`= √π Q₂`). -/
theorem depthPoly_two_eq (X : ℝ) :
    depthPoly 2 X = Real.sqrt Real.pi *
      ((X + (Real.eulerMascheroniConstant + 2 * Real.log 2)) ^ 2 + Real.pi ^ 2 / 2) := by
  simp only [depthPoly, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [gammaLogMoment_zero, gammaLogMoment_one, gammaLogMoment_two]
  ring

/-- `P₃(X) = √π[(X + p)³ + (3π²/2)(X + p) + 14ζ(3)]` (`= √π Q₃`). -/
theorem depthPoly_three_eq (X : ℝ) :
    depthPoly 3 X = Real.sqrt Real.pi *
      ((X + (Real.eulerMascheroniConstant + 2 * Real.log 2)) ^ 3 +
        3 * Real.pi ^ 2 / 2 * (X + (Real.eulerMascheroniConstant + 2 * Real.log 2)) +
        14 * (riemannZeta 3).re) := by
  simp only [depthPoly, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [gammaLogMoment_zero, gammaLogMoment_one, gammaLogMoment_two, gammaLogMoment_three]
  ring

/-- ★★ **Depth two, flat prior**: `Z_N = √(2π)/(2√N)·[(log N + γ + log 2)² + π²/2] − R₂(N)`. -/
theorem depthInt_two_closed {N : ℝ} (hN : 0 < N) :
    depthInt 2 N = Real.sqrt (2 * Real.pi) / (2 * Real.sqrt N) *
      ((Real.log N + Real.eulerMascheroniConstant + Real.log 2) ^ 2 + Real.pi ^ 2 / 2) -
      depthTail 2 N := by
  rw [depth_flat_allOrders 2 hN, depthPoly_two_eq, Real.sqrt_mul (by norm_num)]
  simp only [Nat.factorial_two, Nat.cast_ofNat]
  have : 0 < Real.sqrt N := Real.sqrt_pos.2 hN
  field_simp
  ring

/-- ★★★ **Depth three, flat prior**: `Z_N = √(2π)/(6√N)·[t³ + (3π²/2)t + 14ζ(3)] − R₃(N)`,
`t = log N + γ + log 2`. -/
theorem depthInt_three_closed {N : ℝ} (hN : 0 < N) :
    depthInt 3 N = Real.sqrt (2 * Real.pi) / (6 * Real.sqrt N) *
      ((Real.log N + Real.eulerMascheroniConstant + Real.log 2) ^ 3 +
        3 * Real.pi ^ 2 / 2 * (Real.log N + Real.eulerMascheroniConstant + Real.log 2) +
        14 * (riemannZeta 3).re) - depthTail 3 N := by
  rw [depth_flat_allOrders 3 hN, depthPoly_three_eq, Real.sqrt_mul (by norm_num)]
  simp only [Nat.factorial]
  have : 0 < Real.sqrt N := Real.sqrt_pos.2 hN
  field_simp
  ring

/-! ### The depressed form at every depth -/

/-- ★★ **No `t^{L−2}` term in the centred variable**: with `κ_L = (L+1) log 2 − (L−1)γ`,
`(enginePoly L)(t − κ_L)` has vanishing coefficient of degree `L − 2` for every `L ≥ 2`. -/
theorem taylor_enginePoly_coeff_sub_two (L : ℕ) (hL : 2 ≤ L) :
    (Polynomial.taylor
      (-(((L : ℝ) + 1) * Real.log 2 - ((L : ℝ) - 1) * Real.eulerMascheroniConstant))
      (enginePoly L)).coeff (L - 2) = 0 := by
  obtain ⟨K, rfl⟩ : ∃ K, L = K + 2 := ⟨L - 2, by omega⟩
  rw [Polynomial.taylor_coeff]
  have hdeg : (Polynomial.hasseDeriv (K + 2 - 2) (enginePoly (K + 2))).natDegree < 2 := by
    have h1 := Polynomial.natDegree_hasseDeriv_le (enginePoly (K + 2)) (K + 2 - 2)
    rw [natDegree_enginePoly (K + 2) hL] at h1
    omega
  rw [Polynomial.eval_eq_sum_range' hdeg]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Polynomial.hasseDeriv_coeff,
    Nat.add_sub_cancel, zero_add, pow_zero, pow_one, Nat.choose_self, Nat.cast_one, one_mul]
  have htop : (enginePoly (K + 2)).coeff (1 + K) =
      1 / (((K + 1).factorial : ℝ) * Real.sqrt (2 * Real.pi) ^ (K + 1)) := by
    have h := leadingCoeff_enginePoly (K + 2) hL
    rw [Polynomial.leadingCoeff, natDegree_enginePoly (K + 2) hL,
      show K + 2 - 1 = K + 1 from rfl] at h
    rw [add_comm 1 K, h]
  have hsec := coeff_enginePoly_second (K + 2) hL
  rw [show K + 2 - 2 = K from rfl, show K + 2 - 1 = K + 1 from rfl] at hsec
  rw [htop, hsec, add_comm 1 K, Nat.choose_succ_self_right, Nat.factorial_succ]
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hf : (0 : ℝ) < K.factorial := by positivity
  push_cast
  field_simp
  ring

/-- The centred evaluation: `(taylor (−κ) P)(t) = P(t − κ)`. -/
theorem taylor_enginePoly_eval (L : ℕ) (t : ℝ) :
    (Polynomial.taylor
      (-(((L : ℝ) + 1) * Real.log 2 - ((L : ℝ) - 1) * Real.eulerMascheroniConstant))
      (enginePoly L)).eval t =
      (enginePoly L).eval (t - (((L : ℝ) + 1) * Real.log 2 -
        ((L : ℝ) - 1) * Real.eulerMascheroniConstant)) := by
  rw [Polynomial.taylor_eval]
  ring_nf

end Grammar
