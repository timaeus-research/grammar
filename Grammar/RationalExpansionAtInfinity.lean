/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.QuotientBlocks
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# The expansion of a rational function at infinity (§20, posterior quotient blocks)

For real polynomials `P, Q` with degree bounds `natDegree P ≤ a`, `natDegree Q ≤ b` and
`Q.coeff b ≠ 0`, the reversed coefficient sequences `revSeq P a i = P.coeff (a − i)` (zero beyond
`a`) and `revSeq Q b` have quotient blocks `r = quotientBlocks (revSeq P a) (revSeq Q b)`
(`QuotientBlocks`), and

★ `eval_div_sub_truncQuot_isBigO`:
`P(L)/Q(L) − L^{a−b} Σ_{i<M} r_i L^{−i} = O(L^{a−b−M})` as `L → ∞`.

Route (consult #159, B(i)): put `t = 1/L`; `P(L) = L^a P#(t)`, `Q(L) = L^b Q#(t)` with the
reflected polynomials (`Polynomial.reflect`); by `sum_mul_quotientBlocks` the polynomial
`P# − Q# S_M` has vanishing coefficients below `M`, hence equals `t^M H_M(t)`;
`Q#(0) = Q.coeff b ≠ 0` bounds `1/Q#` near `0`; `H_M` is bounded on `[0,1]`.  No analytic Taylor
machinery is used.

The degree bounds `a, b` may exceed the actual degrees (random numerators may drop degree).

Zero `sorry`/`axiom`.
-/

open Polynomial Filter Topology Asymptotics Set

namespace Grammar

/-- The reversed coefficient sequence of `P` with respect to the degree bound `a`:
`revSeq P a i = P.coeff (a − i)` for `i ≤ a`, and `0` beyond `a` when `natDegree P ≤ a`. -/
noncomputable def revSeq (P : ℝ[X]) (a : ℕ) (i : ℕ) : ℝ := (reflect a P).coeff i

theorem revSeq_zero (P : ℝ[X]) (a : ℕ) : revSeq P a 0 = P.coeff a := by
  unfold revSeq
  rw [coeff_reflect, revAt_zero]

theorem revSeq_of_le (P : ℝ[X]) (a : ℕ) {i : ℕ} (hi : i ≤ a) : revSeq P a i = P.coeff (a - i) := by
  unfold revSeq
  rw [coeff_reflect, revAt_le hi]

/-- The truncated quotient `S_M = Σ_{i<M} r_i X^i`. -/
noncomputable def truncQuot (P Q : ℝ[X]) (a b M : ℕ) : ℝ[X] :=
  ∑ i ∈ Finset.range M, C (quotientBlocks (revSeq P a) (revSeq Q b) i) * X ^ i

theorem coeff_truncQuot (P Q : ℝ[X]) (a b M : ℕ) {j : ℕ} (hj : j < M) :
    (truncQuot P Q a b M).coeff j = quotientBlocks (revSeq P a) (revSeq Q b) j := by
  unfold truncQuot
  rw [finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq (Finset.range M) j, if_pos (Finset.mem_range.2 hj)]

theorem eval_truncQuot (P Q : ℝ[X]) (a b M : ℕ) (t : ℝ) :
    (truncQuot P Q a b M).eval t =
      ∑ i ∈ Finset.range M, quotientBlocks (revSeq P a) (revSeq Q b) i * t ^ i := by
  unfold truncQuot
  rw [eval_finsetSum]
  simp only [eval_mul, eval_C, eval_pow, eval_X]

/-- The coefficients of `P# − Q# S_M` below `M` vanish (`sum_mul_quotientBlocks`). -/
theorem coeff_reflect_sub_mul_truncQuot (P Q : ℝ[X]) (a b M : ℕ) (hB : Q.coeff b ≠ 0) {d : ℕ}
    (hd : d < M) : (reflect a P - reflect b Q * truncQuot P Q a b M).coeff d = 0 := by
  have hB0 : revSeq Q b 0 ≠ 0 := by
    rw [revSeq_zero]
    exact hB
  have hkey := sum_mul_quotientBlocks (revSeq P a) (revSeq Q b) hB0 d
  rw [coeff_sub, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, sub_eq_zero]
  change revSeq P a d = _
  rw [← hkey]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : d - i < M := by
    have := Finset.mem_range.1 hi
    omega
  rw [coeff_truncQuot P Q a b M hi']
  rfl

/-- `P# − Q# S_M = X^M · H_M` for a polynomial `H_M`. -/
theorem exists_reflect_sub_mul_truncQuot_eq (P Q : ℝ[X]) (a b M : ℕ) (hB : Q.coeff b ≠ 0) :
    ∃ H : ℝ[X], reflect a P - reflect b Q * truncQuot P Q a b M = X ^ M * H :=
  X_pow_dvd_iff.2 fun _ hd => coeff_reflect_sub_mul_truncQuot P Q a b M hB hd

/-- `P(L) = P#(1/L) · L^a` for `L ≠ 0` and `natDegree P ≤ a`. -/
theorem eval_eq_eval_reflect_mul_pow (P : ℝ[X]) (a : ℕ) (ha : P.natDegree ≤ a) {L : ℝ}
    (hL : L ≠ 0) : P.eval L = (reflect a P).eval L⁻¹ * L ^ a := by
  let _ := invertibleOfNonzero hL
  have h := eval₂_reflect_mul_pow (RingHom.id ℝ) L a P ha
  rw [eval₂_id, eval₂_id, invOf_eq_inv] at h
  exact h.symm

/-- ★ **The expansion of `P/Q` at infinity in powers of `1/L`**: with `r` the quotient blocks of
the reversed coefficient sequences,
`P(L)/Q(L) − L^{a−b} Σ_{i<M} r_i L^{−i} = O(L^{a−b−M})` as `L → ∞`. -/
theorem eval_div_sub_truncQuot_isBigO (P Q : ℝ[X]) (a b M : ℕ) (ha : P.natDegree ≤ a)
    (hb : Q.natDegree ≤ b) (hB : Q.coeff b ≠ 0) :
    (fun L : ℝ => P.eval L / Q.eval L - L ^ ((a : ℝ) - b) *
      ∑ i ∈ Finset.range M, quotientBlocks (revSeq P a) (revSeq Q b) i * L⁻¹ ^ i)
      =O[atTop] fun L => L ^ ((a : ℝ) - b - M) := by
  obtain ⟨H, hH⟩ := exists_reflect_sub_mul_truncQuot_eq P Q a b M hB
  obtain ⟨CH, hCH⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (H.continuous.continuousOn (s := Icc (0 : ℝ) 1))
  have hQ0 : (reflect b Q).eval 0 = Q.coeff b := by
    rw [← coeff_zero_eq_eval_zero, coeff_reflect, revAt_zero]
  have hβpos : 0 < |Q.coeff b| := abs_pos.2 hB
  obtain ⟨δ, hδ, hδQ⟩ := Metric.continuousAt_iff.1 ((reflect b Q).continuous.continuousAt (x := 0))
    (|Q.coeff b| / 2) (half_pos hβpos)
  refine IsBigO.of_bound (2 * CH / |Q.coeff b|) ?_
  filter_upwards [eventually_ge_atTop (max 1 (2 / δ))] with L hL
  have hL1 : 1 ≤ L := le_trans (le_max_left _ _) hL
  have hLpos : 0 < L := by linarith
  have hL0 : L ≠ 0 := hLpos.ne'
  have ht0 : 0 ≤ L⁻¹ := inv_nonneg.2 hLpos.le
  have ht1 : L⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hL1
  have htδ : L⁻¹ < δ := by
    have h2 : 2 / δ ≤ L := le_trans (le_max_right _ _) hL
    have : L⁻¹ ≤ δ / 2 := by
      rw [inv_le_comm₀ hLpos (half_pos hδ), inv_div]
      exact h2
    exact lt_of_le_of_lt this (half_lt_self hδ)
  -- the denominator stays away from zero
  have hQt : |Q.coeff b| / 2 < |(reflect b Q).eval L⁻¹| := by
    have h1 := hδQ (x := L⁻¹) (by rw [Real.dist_eq, sub_zero, abs_of_nonneg ht0]; exact htδ)
    rw [Real.dist_eq, hQ0] at h1
    have h2 := abs_sub_abs_le_abs_sub (Q.coeff b) ((reflect b Q).eval L⁻¹)
    rw [abs_sub_comm] at h2
    linarith
  have hQt0 : (reflect b Q).eval L⁻¹ ≠ 0 := by
    intro h
    rw [h, abs_zero] at hQt
    linarith
  -- the identity
  have hPev := eval_eq_eval_reflect_mul_pow P a ha hL0
  have hQev := eval_eq_eval_reflect_mul_pow Q b hb hL0
  have hD : (reflect a P).eval L⁻¹ - (reflect b Q).eval L⁻¹ * (truncQuot P Q a b M).eval L⁻¹ =
      L⁻¹ ^ M * H.eval L⁻¹ := by
    have := congrArg (eval L⁻¹) hH
    simpa only [eval_sub, eval_mul, eval_pow, eval_X] using this
  have hrpow : L ^ ((a : ℝ) - b) = L ^ a / L ^ b := by
    rw [Real.rpow_sub hLpos, Real.rpow_natCast, Real.rpow_natCast]
  have hrpow2 : L ^ ((a : ℝ) - b - M) = L ^ a / L ^ b * L⁻¹ ^ M := by
    rw [Real.rpow_sub hLpos, hrpow, Real.rpow_natCast, div_eq_mul_inv, inv_pow]
  have hkey : P.eval L / Q.eval L - L ^ ((a : ℝ) - b) *
      ∑ i ∈ Finset.range M, quotientBlocks (revSeq P a) (revSeq Q b) i * L⁻¹ ^ i =
      L ^ a / L ^ b * (L⁻¹ ^ M * H.eval L⁻¹ / (reflect b Q).eval L⁻¹) := by
    rw [← eval_truncQuot, hPev, hQev, hrpow, ← hD]
    simp only [div_eq_mul_inv, mul_inv]
    linear_combination (L ^ a * (L ^ b)⁻¹ * (truncQuot P Q a b M).eval L⁻¹) *
      mul_inv_cancel₀ hQt0
  -- the bound
  have hHb : |H.eval L⁻¹| ≤ CH := by
    have := hCH L⁻¹ ⟨ht0, ht1⟩
    rwa [Real.norm_eq_abs] at this
  have hab : 0 ≤ L ^ a / L ^ b := div_nonneg (pow_nonneg hLpos.le a) (pow_nonneg hLpos.le b)
  have htM : 0 ≤ L⁻¹ ^ M := pow_nonneg ht0 M
  rw [Real.norm_eq_abs, Real.norm_eq_abs, hkey, hrpow2, abs_of_nonneg (mul_nonneg hab htM),
    abs_mul, abs_of_nonneg hab, abs_div, abs_mul, abs_of_nonneg htM]
  have h1 : L⁻¹ ^ M * |H.eval L⁻¹| / |(reflect b Q).eval L⁻¹| ≤
      L⁻¹ ^ M * CH / (|Q.coeff b| / 2) :=
    div_le_div₀ (mul_nonneg htM (le_trans (abs_nonneg _) hHb))
      (mul_le_mul_of_nonneg_left hHb htM) (half_pos hβpos) hQt.le
  calc L ^ a / L ^ b * (L⁻¹ ^ M * |H.eval L⁻¹| / |(reflect b Q).eval L⁻¹|)
      ≤ L ^ a / L ^ b * (L⁻¹ ^ M * CH / (|Q.coeff b| / 2)) := mul_le_mul_of_nonneg_left h1 hab
    _ = 2 * CH / |Q.coeff b| * (L ^ a / L ^ b * L⁻¹ ^ M) := by
      field_simp

end Grammar
