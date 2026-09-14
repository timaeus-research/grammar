/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# The face regression for smooth amplitudes (consult #114 U0)

For a continuous amplitude `f(x)` supported in `[a₀, b₀] ⊂ (0, b)` and the tied crossing phase
`x² y²` on the box `[0,b]²`,
`∫_0^b ∫_0^b f(x) e^{−N x² y²} dy dx = (√π/2) N^{−1/2} ∫_0^b f(x)/x dx + R(N)`,
`|R(N)| ≤ (∫_0^b |f(x)/x| dx)/(a₀ b) · e^{−a₀² b² N}` for `N ≥ 1` (★ `faceRegression`), while every
derivative of `f` at the corner `x = 0` vanishes (`iteratedDeriv_eq_zero_of_eventually_zero`). The
leading coefficient is a FACE integral (over the divisor component `{y = 0}`, against `dx/x`), not
a corner jet: a smooth-amplitude expansion engine must keep facewise data with their tangential
dependence (Astra #114 §1.1, §4.2). The proof is the Gaussian substitution `t = x√N y` in the inner
integral, `∫_0^∞ e^{−t²} = √π/2`, and the tail bound `∫_L^∞ e^{−t²} ≤ e^{−L²}/L`. Zero
`sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology intervalIntegral

namespace Grammar

namespace SmoothFace

/-! ### The Gaussian tail -/

theorem integrable_exp_neg_sq : Integrable fun t : ℝ => exp (-t ^ 2) := by
  simpa using integrable_exp_neg_mul_sq (one_pos : (0 : ℝ) < 1)

theorem integral_exp_neg_sq_Ioi_zero : ∫ t in Ioi (0 : ℝ), exp (-t ^ 2) = √π / 2 := by
  simpa using integral_gaussian_Ioi (1 : ℝ)

/-- The Gaussian tail `T(L) = ∫_L^∞ e^{−t²} dt`. -/
noncomputable def tail (L : ℝ) : ℝ := ∫ t in Ioi L, exp (-t ^ 2)

theorem tail_nonneg (L : ℝ) : 0 ≤ tail L :=
  setIntegral_nonneg measurableSet_Ioi fun _ _ => (exp_pos _).le

/-- `∫_L^∞ e^{−t²} dt ≤ e^{−L²}/L` for `L > 0`. -/
theorem tail_le {L : ℝ} (hL : 0 < L) : tail L ≤ exp (-L ^ 2) / L := by
  have h1 : tail L ≤ ∫ t in Ioi L, exp (-L * t) := by
    refine setIntegral_mono_on integrable_exp_neg_sq.integrableOn
      (exp_neg_integrableOn_Ioi L hL) measurableSet_Ioi fun t ht => ?_
    have ht' : L < t := ht
    exact exp_le_exp.2 (by nlinarith)
  have h2 : ∫ t in Ioi L, exp (-L * t) = exp (-L ^ 2) / L := by
    rw [integral_exp_mul_Ioi (by linarith : -L < 0) L, neg_div_neg_eq, sq, neg_mul]
  exact h1.trans_eq h2

/-- The Gaussian primitive: `∫_0^L e^{−t²} dt = √π/2 − T(L)` for `L ≥ 0`. -/
theorem integral_exp_neg_sq_eq (L : ℝ) (hL : 0 ≤ L) :
    ∫ t in (0 : ℝ)..L, exp (-t ^ 2) = √π / 2 - tail L := by
  rw [← integral_exp_neg_sq_Ioi_zero, tail]
  exact (integral_Ioi_sub_Ioi integrable_exp_neg_sq.integrableOn hL).symm

/-- The inner integral: for `x > 0`, `N > 0`,
`∫_0^b e^{−N x² y²} dy = (x√N)⁻¹ (√π/2 − T(x√N b))`. -/
theorem inner_eq {x N b : ℝ} (hx : 0 < x) (hN : 0 < N) (hb : 0 ≤ b) :
    ∫ y in (0 : ℝ)..b, exp (-N * x ^ 2 * y ^ 2) = (x * √N)⁻¹ * (√π / 2 - tail (x * √N * b)) := by
  have hc : x * √N ≠ 0 := mul_ne_zero hx.ne' (sqrt_pos.2 hN).ne'
  have h : ∀ y : ℝ, exp (-N * x ^ 2 * y ^ 2) = (fun t => exp (-t ^ 2)) (x * √N * y) := by
    intro y
    simp only
    congr 1
    rw [mul_pow, mul_pow, sq_sqrt hN.le]
    ring
  simp_rw [h]
  rw [integral_comp_mul_left (fun t => exp (-t ^ 2)) hc, mul_zero, smul_eq_mul,
    integral_exp_neg_sq_eq _ (mul_nonneg (mul_nonneg hx.le (sqrt_nonneg _)) hb)]

/-! ### Vanishing corner jets -/

/-- Every derivative at `0` of a function vanishing near `0` is zero. -/
theorem iteratedDeriv_eq_zero_of_eventually_zero {f : ℝ → ℝ} (hf : f =ᶠ[𝓝 (0 : ℝ)] 0) (n : ℕ) :
    iteratedDeriv n f 0 = 0 := by
  have key : ∀ n : ℕ, iteratedDeriv n f =ᶠ[𝓝 (0 : ℝ)] 0 := by
    intro n
    induction n with
    | zero => simpa using hf
    | succ n ih =>
      rw [iteratedDeriv_succ]
      have := ih.deriv
      rwa [show deriv (0 : ℝ → ℝ) = 0 from funext fun _ => by simp] at this
  exact (key n).eq_of_nhds

/-! ### The face regression -/

variable {f : ℝ → ℝ} {a₀ b₀ b : ℝ}

/-- A continuous amplitude supported in `[a₀, b₀] ⊂ (0, b)`: the quotient `f(x)/x` is continuous. -/
theorem continuous_div_self (hf : Continuous f) (ha₀ : 0 < a₀)
    (hsupp : ∀ x, x ∉ Icc a₀ b₀ → f x = 0) : Continuous fun x => f x / x := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  by_cases hx : x = 0
  · subst hx
    have h : (fun x => f x / x) =ᶠ[𝓝 (0 : ℝ)] 0 := by
      filter_upwards [Iio_mem_nhds ha₀] with y hy
      rw [Pi.zero_apply, hsupp y fun hy' => absurd hy'.1 (not_le.2 hy), zero_div]
    exact continuousAt_const.congr h.symm
  · exact (hf.continuousAt).div continuousAt_id hx

theorem eventually_zero (ha₀ : 0 < a₀) (hsupp : ∀ x, x ∉ Icc a₀ b₀ → f x = 0) :
    f =ᶠ[𝓝 (0 : ℝ)] 0 := by
  filter_upwards [Iio_mem_nhds ha₀] with y hy
  exact hsupp y fun hy' => absurd hy'.1 (not_le.2 hy)

theorem continuous_tail : Continuous tail := by
  have h : tail = fun L => √π / 2 - ∫ t in (0 : ℝ)..L, exp (-t ^ 2) := by
    funext L
    rcases le_or_gt 0 L with hL | hL
    · rw [integral_exp_neg_sq_eq L hL]; ring
    · -- for `L < 0` the tail exceeds the half-line integral by the integral over `(L, 0]`
      unfold tail
      rw [integral_symm, sub_neg_eq_add, ← integral_exp_neg_sq_Ioi_zero,
        ← integral_Ioi_sub_Ioi integrable_exp_neg_sq.integrableOn hL.le]
      ring
  rw [h]
  exact continuous_const.sub (intervalIntegral.continuous_primitive
    (fun _ _ => integrable_exp_neg_sq.intervalIntegrable) 0)

/-- The pointwise decomposition of the integrand of the outer integral. -/
theorem integrand_eq (hf0 : f 0 = 0) {N : ℝ} (hN : 0 < N) (hb : 0 ≤ b) (x : ℝ) (hx : 0 ≤ x) :
    f x * ∫ y in (0 : ℝ)..b, exp (-N * x ^ 2 * y ^ 2) =
      √π / 2 * (√N)⁻¹ * (f x / x) - (√N)⁻¹ * (f x / x * tail (x * √N * b)) := by
  rcases hx.eq_or_lt with hx0 | hxpos
  · subst hx0
    rw [hf0]
    simp
  · rw [inner_eq hxpos hN hb, mul_inv]
    ring

/-- ★ **The face regression**: for a continuous amplitude `f` supported in `[a₀, b₀] ⊂ (0, b)`,
`∫_0^b∫_0^b f(x) e^{−N x² y²} dy dx = (√π/2) N^{−1/2} ∫_0^b f(x)/x dx + R(N)` with
`|R(N)| ≤ (∫_0^b |f(x)/x| dx)/(a₀ b) · e^{−a₀² b² N}` for `N ≥ 1`. -/
theorem faceRegression (hf : Continuous f) (ha₀ : 0 < a₀) (hab : a₀ ≤ b₀) (hb₀ : b₀ < b)
    (hsupp : ∀ x, x ∉ Icc a₀ b₀ → f x = 0) {N : ℝ} (hN : 1 ≤ N) :
    |(∫ x in (0 : ℝ)..b, f x * ∫ y in (0 : ℝ)..b, exp (-N * x ^ 2 * y ^ 2)) -
        √π / 2 * (√N)⁻¹ * ∫ x in (0 : ℝ)..b, f x / x| ≤
      (∫ x in (0 : ℝ)..b, |f x / x|) / (a₀ * b) * exp (-(a₀ ^ 2 * b ^ 2) * N) := by
  have hNpos : 0 < N := one_pos.trans_le hN
  have hb : 0 < b := ha₀.trans_le (hab.trans hb₀.le)
  have hf0 : f 0 = 0 := hsupp 0 fun h => absurd h.1 (not_le.2 ha₀)
  have hg : Continuous fun x => f x / x := continuous_div_self hf ha₀ hsupp
  have hgT : Continuous fun x => f x / x * tail (x * √N * b) :=
    hg.mul (continuous_tail.comp ((continuous_id.mul continuous_const).mul continuous_const))
  -- the outer integrand decomposes pointwise on `[0, b]`
  have hdec : ∫ x in (0 : ℝ)..b, f x * ∫ y in (0 : ℝ)..b, exp (-N * x ^ 2 * y ^ 2) =
      √π / 2 * (√N)⁻¹ * (∫ x in (0 : ℝ)..b, f x / x) -
        (√N)⁻¹ * ∫ x in (0 : ℝ)..b, f x / x * tail (x * √N * b) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul, ← integral_sub
      (hg.intervalIntegrable _ _ |>.const_mul _) (hgT.intervalIntegrable _ _ |>.const_mul _)]
    refine integral_congr fun x hx => ?_
    rw [uIcc_of_le hb.le] at hx
    exact integrand_eq hf0 hNpos hb.le x hx.1
  rw [hdec, sub_sub_cancel_left, abs_neg, abs_mul, abs_of_pos (inv_pos.2 (sqrt_pos.2 hNpos))]
  -- the tail term: pointwise bound on the support
  set Mt : ℝ := exp (-(a₀ * √N * b) ^ 2) / (a₀ * √N * b) with hMt
  have hpt : ∀ x ∈ uIcc (0 : ℝ) b, |f x / x * tail (x * √N * b)| ≤ |f x / x| * Mt := by
    intro x hx
    rw [uIcc_of_le hb.le] at hx
    by_cases hfx : f x = 0
    · rw [hfx, zero_div, zero_mul, abs_zero, zero_mul]
    · have hxI : x ∈ Icc a₀ b₀ := by_contra fun h => hfx (hsupp x h)
      have hxpos : 0 < x := ha₀.trans_le hxI.1
      have hL : 0 < x * √N * b := mul_pos (mul_pos hxpos (sqrt_pos.2 hNpos)) hb
      have hL0 : 0 < a₀ * √N * b := mul_pos (mul_pos ha₀ (sqrt_pos.2 hNpos)) hb
      rw [abs_mul, abs_of_nonneg (tail_nonneg _)]
      refine mul_le_mul_of_nonneg_left ((tail_le hL).trans ?_) (abs_nonneg _)
      have hle : a₀ * √N * b ≤ x * √N * b :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hxI.1 (sqrt_nonneg _)) hb.le
      rw [hMt]
      refine div_le_div₀ (exp_pos _).le (exp_le_exp.2 ?_) hL0 hle
      exact neg_le_neg (pow_le_pow_left₀ hL0.le hle 2)
  have hint : |∫ x in (0 : ℝ)..b, f x / x * tail (x * √N * b)| ≤
      (∫ x in (0 : ℝ)..b, |f x / x|) * Mt := by
    rw [← intervalIntegral.integral_mul_const]
    refine (intervalIntegral.norm_integral_le_integral_norm
      (f := fun x => f x / x * tail (x * √N * b)) hb.le).trans ?_
    exact integral_mono_on hb.le (hgT.norm.intervalIntegrable _ _)
      ((hg.abs.intervalIntegrable _ _).mul_const _) fun x hx => hpt x
        (by rw [uIcc_of_le hb.le]; exact hx)
  have hC : 0 ≤ ∫ x in (0 : ℝ)..b, |f x / x| := integral_nonneg hb.le fun x _ => abs_nonneg _
  have hsq : (a₀ * √N * b) ^ 2 = a₀ ^ 2 * b ^ 2 * N := by
    rw [mul_pow, mul_pow, sq_sqrt hNpos.le]
    ring
  have hMt' : Mt = exp (-(a₀ ^ 2 * b ^ 2) * N) / (a₀ * b) * (√N)⁻¹ := by
    have hsN : √N ≠ 0 := (sqrt_pos.2 hNpos).ne'
    rw [hMt, hsq]
    field_simp
  have hN' : N⁻¹ = (√N)⁻¹ * (√N)⁻¹ := by rw [← mul_inv, mul_self_sqrt hNpos.le]
  calc (√N)⁻¹ * |∫ x in (0 : ℝ)..b, f x / x * tail (x * √N * b)|
      ≤ (√N)⁻¹ * ((∫ x in (0 : ℝ)..b, |f x / x|) * Mt) :=
        mul_le_mul_of_nonneg_left hint (inv_nonneg.2 (sqrt_nonneg _))
    _ = (∫ x in (0 : ℝ)..b, |f x / x|) / (a₀ * b) * exp (-(a₀ ^ 2 * b ^ 2) * N) * N⁻¹ := by
        rw [hMt', hN']
        ring
    _ ≤ (∫ x in (0 : ℝ)..b, |f x / x|) / (a₀ * b) * exp (-(a₀ ^ 2 * b ^ 2) * N) :=
        mul_le_of_le_one_right (mul_nonneg (div_nonneg hC (mul_pos ha₀ hb).le) (exp_pos _).le)
          (inv_le_one_of_one_le₀ hN)

end SmoothFace

end Grammar
