/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.DigammaCompat

/-!
# The real digamma function: monotonicity, decay, and the series `ψ(1+x) − ψ(1) = Σ x/(k(k+x))`

The ζ-bridge without an integral representation (Astra round 28, route B, modules 1–2).  With
`realDigamma x = (Complex.digamma x).re`:

* `deriv_log_Gamma_eq_realDigamma`: `(log ∘ Γ)' = ψ` on `x > 0` (the complex derivative restricted
  to the real axis, `HasDerivAt.real_of_complex`, divided by `Γ(x) > 0`);
* `monotoneOn_realDigamma`: `ψ` is monotone on `(0,∞)`, from Bohr–Mollerup's
  `Real.convexOn_log_Gamma` and `ConvexOn.monotoneOn_deriv`;
* `realDigamma_add_one`: `ψ(x+1) = ψ(x) + 1/x` (Mathlib's `digamma_apply_add_one`);
* ★★ `abs_realDigamma_nat_shift_sub_le`: `|ψ(N+1+x) − ψ(N+1)| ≤ 1/N` for `−1 ≤ x ≤ 1`, `N ≥ 1`
  (monotone between the two endpoint differences `1/(N+1)` and `1/N`), hence the decay
  `tendsto_realDigamma_nat_shift_sub`;
* ★★★ `hasSum_realDigamma_sub`: `ψ(1+x) − ψ(1) = Σ_{n≥0} x/((n+1)(n+1+x))` for `−1 < x ≤ 1`, by the
  telescoped functional equation (`sum_realDigamma_telescope`) and the decay.

Zero `sorry`/`axiom`.
-/

open Filter Topology Finset

namespace Grammar

/-- `ψ(x) = (Complex.digamma x).re`. -/
noncomputable def realDigamma (x : ℝ) : ℝ := (Complex.digamma (x : ℂ)).re

/-- `Real.Gamma` is the real part of `Complex.Gamma` on the real axis. -/
theorem realGamma_eq_re : Real.Gamma = fun x : ℝ => (Complex.Gamma (x : ℂ)).re := by
  funext x
  rw [Complex.Gamma_ofReal, Complex.ofReal_re]

theorem hasDerivAt_realGamma {x : ℝ} (hx : 0 < x) :
    HasDerivAt Real.Gamma (deriv Complex.Gamma (x : ℂ)).re x := by
  have h := (hasDerivAt_Gamma_of_re_pos (z := (x : ℂ)) (by simpa using hx)).real_of_complex
  rw [realGamma_eq_re]
  exact h

theorem realDigamma_eq_div (x : ℝ) :
    realDigamma x = (deriv Complex.Gamma (x : ℂ)).re / Real.Gamma x := by
  unfold realDigamma
  rw [Complex.digamma_def, logDeriv_apply, Complex.Gamma_ofReal, Complex.div_ofReal_re]

/-- `(log ∘ Γ)' = ψ` on `x > 0`. -/
theorem hasDerivAt_log_Gamma {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => Real.log (Real.Gamma y)) (realDigamma x) x := by
  have h := (hasDerivAt_realGamma hx).log (Real.Gamma_pos_of_pos hx).ne'
  rw [realDigamma_eq_div]
  exact h

theorem deriv_log_Gamma_eq_realDigamma {x : ℝ} (hx : 0 < x) :
    deriv (fun y : ℝ => Real.log (Real.Gamma y)) x = realDigamma x :=
  (hasDerivAt_log_Gamma hx).deriv

/-- ★ `ψ` is monotone on `(0,∞)` (Bohr–Mollerup). -/
theorem monotoneOn_realDigamma : MonotoneOn realDigamma (Set.Ioi 0) := by
  have hconv : ConvexOn ℝ (Set.Ioi 0) (fun y : ℝ => Real.log (Real.Gamma y)) :=
    Real.convexOn_log_Gamma
  have hmono := hconv.monotoneOn_deriv fun x hx =>
    (hasDerivAt_log_Gamma (Set.mem_Ioi.1 hx)).differentiableAt
  intro a ha b hb hab
  have := hmono ha hb hab
  rwa [deriv_log_Gamma_eq_realDigamma (Set.mem_Ioi.1 ha),
    deriv_log_Gamma_eq_realDigamma (Set.mem_Ioi.1 hb)] at this

/-- `ψ(x+1) = ψ(x) + 1/x` for `x > 0`. -/
theorem realDigamma_add_one {x : ℝ} (hx : 0 < x) : realDigamma (x + 1) = realDigamma x + x⁻¹ := by
  unfold realDigamma
  have h := Complex.digamma_apply_add_one (x : ℂ) (ne_neg_nat_of_re_pos (by simpa using hx))
  push_cast
  rw [h, Complex.add_re, ← Complex.ofReal_inv, Complex.ofReal_re]

/-! ### Decay of the shifted differences -/

/-- ★★ `|ψ(N+1+x) − ψ(N+1)| ≤ 1/N` for `N ≥ 1`, `−1 ≤ x ≤ 1`. -/
theorem abs_realDigamma_nat_shift_sub_le (N : ℕ) (hN : 1 ≤ N) {x : ℝ} (hx0 : -1 ≤ x)
    (hx1 : x ≤ 1) :
    |realDigamma ((N : ℝ) + 1 + x) - realDigamma ((N : ℝ) + 1)| ≤ 1 / (N : ℝ) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by linarith
  have hNx : (0 : ℝ) < (N : ℝ) + 1 + x := by linarith
  have hup : realDigamma ((N : ℝ) + 1 + x) ≤ realDigamma ((N : ℝ) + 1 + 1) :=
    monotoneOn_realDigamma (Set.mem_Ioi.2 hNx) (Set.mem_Ioi.2 (by linarith)) (by linarith)
  have hlo : realDigamma (N : ℝ) ≤ realDigamma ((N : ℝ) + 1 + x) :=
    monotoneOn_realDigamma (Set.mem_Ioi.2 hNpos) (Set.mem_Ioi.2 hNx) (by linarith)
  have e1 : realDigamma ((N : ℝ) + 1 + 1) = realDigamma ((N : ℝ) + 1) + ((N : ℝ) + 1)⁻¹ :=
    realDigamma_add_one hN1
  have e2 : realDigamma ((N : ℝ) + 1) = realDigamma (N : ℝ) + (N : ℝ)⁻¹ := realDigamma_add_one hNpos
  have hinv : ((N : ℝ) + 1)⁻¹ ≤ (N : ℝ)⁻¹ := by
    rw [inv_le_inv₀ hN1 hNpos]
    linarith
  rw [abs_le, one_div]
  constructor
  · linarith
  · linarith

/-- The shifted differences tend to zero. -/
theorem tendsto_realDigamma_nat_shift_sub {x : ℝ} (hx0 : -1 ≤ x) (hx1 : x ≤ 1) :
    Tendsto (fun N : ℕ => realDigamma ((N : ℝ) + 1 + x) - realDigamma ((N : ℝ) + 1)) atTop
      (𝓝 0) := by
  refine squeeze_zero_norm' ?_ tendsto_one_div_atTop_nhds_zero_nat
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [Real.norm_eq_abs]
  exact abs_realDigamma_nat_shift_sub_le N hN hx0 hx1

/-! ### The telescoped series -/

/-- `Σ_{n<N} x/((n+1)(n+1+x)) = [ψ(1+x) − ψ(1)] − [ψ(N+1+x) − ψ(N+1)]`. -/
theorem sum_realDigamma_telescope {x : ℝ} (hx0 : -1 < x) (N : ℕ) :
    ∑ n ∈ range N, x / (((n : ℝ) + 1) * ((n : ℝ) + 1 + x)) =
      (realDigamma (1 + x) - realDigamma 1) -
        (realDigamma ((N : ℝ) + 1 + x) - realDigamma ((N : ℝ) + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have hNx : (0 : ℝ) < (N : ℝ) + 1 + x := by linarith
    have e1 : realDigamma (((N + 1 : ℕ) : ℝ) + 1 + x) =
        realDigamma ((N : ℝ) + 1 + x) + ((N : ℝ) + 1 + x)⁻¹ := by
      rw [show (((N + 1 : ℕ) : ℝ) + 1 + x) = ((N : ℝ) + 1 + x) + 1 by push_cast; ring]
      exact realDigamma_add_one hNx
    have e2 : realDigamma (((N + 1 : ℕ) : ℝ) + 1) =
        realDigamma ((N : ℝ) + 1) + ((N : ℝ) + 1)⁻¹ := by
      rw [show (((N + 1 : ℕ) : ℝ) + 1) = ((N : ℝ) + 1) + 1 by push_cast; ring]
      exact realDigamma_add_one hN1
    rw [e1, e2]
    field_simp
    ring

theorem summable_realDigamma_series {x : ℝ} (hx0 : -1 < x) :
    Summable (fun n : ℕ => x / (((n : ℝ) + 1) * ((n : ℝ) + 1 + x))) := by
  refine (summable_nat_add_iff 1).1 ?_
  have hsum : Summable (fun n : ℕ => |x| / ((n : ℝ) + 1) ^ 2) := by
    have := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (by norm_num : 1 < 2))
    refine (this.mul_left |x|).congr fun n => ?_
    push_cast
    ring
  refine Summable.of_norm_bounded hsum fun n => ?_
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hA : (n : ℝ) + 1 ≤ ((n + 1 : ℕ) : ℝ) + 1 := by push_cast; linarith
  have hB : (n : ℝ) + 1 ≤ ((n + 1 : ℕ) : ℝ) + 1 + x := by push_cast; linarith
  have hpos : (0 : ℝ) < (((n + 1 : ℕ) : ℝ) + 1) * (((n + 1 : ℕ) : ℝ) + 1 + x) :=
    mul_pos (by positivity) (by linarith)
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hpos, div_le_div_iff₀ hpos (by positivity)]
  have hprod : ((n : ℝ) + 1) ^ 2 ≤ (((n + 1 : ℕ) : ℝ) + 1) * (((n + 1 : ℕ) : ℝ) + 1 + x) := by
    rw [sq]
    exact mul_le_mul hA hB hn1.le (by positivity)
  nlinarith [abs_nonneg x]

/-- ★★★ **`ψ(1+x) − ψ(1) = Σ_{n≥0} x/((n+1)(n+1+x))`** for `−1 < x ≤ 1`. -/
theorem hasSum_realDigamma_sub {x : ℝ} (hx0 : -1 < x) (hx1 : x ≤ 1) :
    HasSum (fun n : ℕ => x / (((n : ℝ) + 1) * ((n : ℝ) + 1 + x)))
      (realDigamma (1 + x) - realDigamma 1) := by
  rw [(summable_realDigamma_series hx0).hasSum_iff_tendsto_nat]
  have h := (tendsto_realDigamma_nat_shift_sub hx0.le hx1).const_sub
    (realDigamma (1 + x) - realDigamma 1)
  rw [sub_zero] at h
  refine h.congr fun N => ?_
  rw [sum_realDigamma_telescope hx0 N]

end Grammar
