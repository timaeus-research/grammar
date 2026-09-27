/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.PolynomialDepthAll
import Mathlib.Analysis.Polynomial.Basic

/-!
# Canonicality of the engine's polynomial

A real polynomial whose values tend to `0` at `+∞` is zero
(`polynomial_eq_zero_of_tendsto_eval_zero`), so the rate polynomial of `HasPolyRate` is unique
(★★ `HasPolyRate.unique`), every rate polynomial at depth `L ≥ 2` is `enginePoly L`
(`HasPolyRate.eq_enginePoly`), and — the interface for the Mellin identification — any polynomial
with merely `√N Z_L(N) − P(log N) → 0` is `enginePoly L` (★★ `eq_enginePoly_of_tendsto_sub`):
an `o(1)` normalised remainder identifies the whole log-polynomial, no rate needed.  Also the
limit forms `HasPolyRate.tendsto` (in `N`) and `HasPolyRate.tendsto_exp` (in `x = log N`).
Astra round 20, target (d).  Examples_slop §2.
Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology Polynomial

namespace Grammar

/-- A real polynomial whose values tend to `0` at `+∞` is zero. -/
theorem polynomial_eq_zero_of_tendsto_eval_zero {P : ℝ[X]}
    (h : Tendsto (fun x : ℝ => P.eval x) atTop (𝓝 0)) : P = 0 := by
  by_contra hP
  rcases Nat.eq_zero_or_pos P.natDegree with hd | hd
  · have hc : P = C (P.coeff 0) := eq_C_of_natDegree_eq_zero hd
    have he : ∀ x : ℝ, P.eval x = P.coeff 0 := fun x => by
      conv_lhs => rw [hc]
      rw [eval_C]
    have h' : Tendsto (fun _ : ℝ => P.coeff 0) atTop (𝓝 0) := h.congr he
    have h0 : P.coeff 0 = 0 := tendsto_nhds_unique tendsto_const_nhds h'
    exact hP (by rw [hc, h0, C_0])
  · have hdeg : 0 < P.degree := natDegree_pos_iff_degree_pos.1 hd
    have h1 := P.abs_tendsto_atTop hdeg
    have h2 : Tendsto (fun x : ℝ => |P.eval x|) atTop (𝓝 0) := by
      have := h.abs
      rwa [abs_zero] at this
    exact not_tendsto_nhds_of_tendsto_atTop h1 0 h2

/-- `(1 + x)/√(eˣ) → 0`. -/
theorem tendsto_one_add_div_sqrt_exp :
    Tendsto (fun x : ℝ => (1 + x) / Real.sqrt (Real.exp x)) atTop (𝓝 0) := by
  have t1 := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  have t0 := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 0
  have hhalf : Tendsto (fun x : ℝ => x / 2) atTop atTop := tendsto_id.atTop_div_const two_pos
  have := ((t1.comp hhalf).const_mul 2).add (t0.comp hhalf)
  simp only [mul_zero, add_zero] at this
  refine this.congr fun x => ?_
  simp only [Function.comp_apply, pow_one, pow_zero, one_mul]
  rw [← Real.exp_half, Real.exp_neg, div_eq_mul_inv]
  ring

/-- The rate in the variable `x = log N`. -/
theorem HasPolyRate.tendsto_exp {L : ℕ} {P : ℝ[X]} (h : HasPolyRate L P) :
    Tendsto (fun x : ℝ => Real.sqrt (Real.exp x) * gaussLaplaceL L (Real.exp x) - P.eval x)
      atTop (𝓝 0) := by
  obtain ⟨K, hK0, hK⟩ := h
  have hlim : Tendsto (fun x : ℝ => K * ((1 + x) / Real.sqrt (Real.exp x))) atTop (𝓝 0) := by
    have := tendsto_one_add_div_sqrt_exp.const_mul K
    rwa [mul_zero] at this
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  have h1 := hK (Real.exp x) (Real.one_le_exp hx)
  rw [Real.log_exp] at h1
  rw [Real.norm_eq_abs]
  exact h1.trans (le_of_eq (by ring))

/-- The rate implies the limit in `N`. -/
theorem HasPolyRate.tendsto {L : ℕ} {P : ℝ[X]} (h : HasPolyRate L P) :
    Tendsto (fun N : ℝ => Real.sqrt N * gaussLaplaceL L N - P.eval (Real.log N)) atTop (𝓝 0) := by
  obtain ⟨K, hK0, hK⟩ := h
  have hlim : Tendsto (fun N : ℝ => K * (1 + Real.log N) / Real.sqrt N) atTop (𝓝 0) := by
    have := (tendsto_one_div_sqrt.add tendsto_log_div_sqrt).const_mul K
    simp only [add_zero, mul_zero] at this
    refine this.congr fun N => ?_
    ring
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with N hN
  rw [Real.norm_eq_abs]
  exact hK N hN

/-- ★★ The rate polynomial is unique. -/
theorem HasPolyRate.unique {L : ℕ} {P R : ℝ[X]} (hP : HasPolyRate L P) (hR : HasPolyRate L R) :
    P = R := by
  rw [← sub_eq_zero]
  apply polynomial_eq_zero_of_tendsto_eval_zero
  have := hR.tendsto_exp.sub hP.tendsto_exp
  rw [sub_zero] at this
  refine this.congr fun x => ?_
  rw [eval_sub]
  ring

/-- ★★ Every rate polynomial at depth `L ≥ 2` is the engine's. -/
theorem HasPolyRate.eq_enginePoly {L : ℕ} (hL : 2 ≤ L) {P : ℝ[X]} (hP : HasPolyRate L P) :
    P = enginePoly L :=
  hP.unique (hasPolyRate_enginePoly L hL)

/-- ★★ **Identification from an `o(1)` remainder**: if `√N Z_L(N) − P(log N) → 0` then
`P = enginePoly L` (`L ≥ 2`). -/
theorem eq_enginePoly_of_tendsto_sub {L : ℕ} (hL : 2 ≤ L) {P : ℝ[X]}
    (hP : Tendsto (fun N : ℝ => Real.sqrt N * gaussLaplaceL L N - P.eval (Real.log N))
      atTop (𝓝 0)) : P = enginePoly L := by
  rw [← sub_eq_zero]
  apply polynomial_eq_zero_of_tendsto_eval_zero
  have h1 := (hasPolyRate_enginePoly L hL).tendsto_exp
  have h2 : Tendsto (fun x : ℝ => Real.sqrt (Real.exp x) * gaussLaplaceL L (Real.exp x) -
      P.eval x) atTop (𝓝 0) := by
    refine (hP.comp Real.tendsto_exp_atTop).congr fun x => ?_
    simp only [Function.comp_apply, Real.log_exp]
  have := h1.sub h2
  rw [sub_zero] at this
  refine this.congr fun x => ?_
  rw [eval_sub]
  ring

end Grammar
