/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Grammar.ShallowStratumRegression

/-!
# The model finite-part distribution `F u = ∫₀¹ (u(x) − u(0))/x dx`

This module isolates, as a regression, the one-dimensional model of the tangential
(shallow-stratum) coefficient functionals of the smooth expansion at a normal crossing: the
finite-part (subtracted) integral

  `finitePart u := ∫ x in Ioc 0 1, (u x − u 0) / x`.

The subtraction of `u 0` is what makes the integral converge: for a `C¹` function the mean value
theorem gives `|u x − u 0| ≤ (sup_{[0,1]} |u'|) · x`, so the integrand is bounded on `(0,1]`
(`integrable_finitePart`). `F` is linear (`finitePart_add`, `finitePart_smul`), and the same
bound shows `|F u| ≤ sup_{[0,1]} |u'|` (`abs_finitePart_le`): `F` is a distribution of order at
most one. It is supported on `[0,1]`: `F u = 0` when `u` vanishes on `Icc 0 1`
(`finitePart_eq_zero_of_eqOn_zero`).

The order is exactly one. Cutting the constant function `1` off near `0` at scale `ε` with a
fixed smooth step (`bump ε x = χ(x/ε) · χ(2 − x)`, `χ = Real.smoothTransition`) gives smooth
functions `bump ε` with `0 ≤ bump ε ≤ 1`, `bump ε 0 = 0`, support in the fixed compact `[0,2]`,
and `F (bump ε) ≥ ∫_ε^1 dx/x = log (1/ε)` (`log_le_finitePart_bump`), unbounded as `ε → 0`.
So no estimate `|F u| ≤ C · sup |u|` holds on smooth functions supported in a fixed compact
(`no_order_zero_bound`): `F` is not a measure, and the strata coefficient functionals it models
are not integrable kernels paired with the observable.

Link to the shallow-stratum counterexample (`ShallowStratumRegression.lean`): for the phase
`x²y²` on the unit square, the `n^{-1/2}` coefficient of the observable `x^M` is `√π/(2M)`, and
`F (x^M) = ∫₀¹ x^{M−1} dx = 1/M` (`finitePart_pow`), so that coefficient is
`(√π/2) · F(x^M)` (`xM_isEquivalent_finitePart`): the tangential coefficient
`c_{1/2,0}(u(x)) = (√π/2) · F(u) + c_corner · u(0)` sees the observable along the axis `y = 0`
through the finite part, not through a finite jet at the corner. Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Asymptotics Filter Topology
open scoped ContDiff

namespace Grammar.FinitePart

/-- The model finite-part functional `F u = ∫₀¹ (u(x) − u(0))/x dx`. -/
noncomputable def finitePart (u : ℝ → ℝ) : ℝ := ∫ x in Ioc (0 : ℝ) 1, (u x - u 0) / x

variable {u v : ℝ → ℝ}

/-! ## The mean value bound and integrability -/

/-- A `C¹` function has a bounded derivative on `[0,1]`. -/
theorem exists_deriv_bound (hu : ContDiff ℝ 1 u) :
    ∃ M : ℝ, ∀ x ∈ Icc (0 : ℝ) 1, |deriv u x| ≤ M := by
  obtain ⟨M, hM⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn (hu.continuous_deriv le_rfl).continuousOn
  exact ⟨M, fun x hx => by simpa [Real.norm_eq_abs] using hM x hx⟩

/-- Mean value theorem on `[0,1]`: `|u x − u 0| ≤ M x` when `|u'| ≤ M` on `[0,1]`. -/
theorem abs_sub_le_mul (hu : ContDiff ℝ 1 u) {M : ℝ} (hM : ∀ x ∈ Icc (0 : ℝ) 1, |deriv u x| ≤ M)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : |u x - u 0| ≤ M * x := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := u) (s := Icc (0 : ℝ) 1)
    (fun y _ => (hu.differentiable one_ne_zero).differentiableAt)
    (fun y hy => by rw [Real.norm_eq_abs]; exact hM y hy) (convex_Icc 0 1)
    ⟨le_rfl, zero_le_one⟩ hx
  simpa [Real.norm_eq_abs, abs_of_nonneg hx.1] using h

/-- The subtracted integrand is bounded by the derivative bound on `(0,1]`. -/
theorem abs_integrand_le (hu : ContDiff ℝ 1 u) {M : ℝ}
    (hM : ∀ x ∈ Icc (0 : ℝ) 1, |deriv u x| ≤ M) {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) :
    |(u x - u 0) / x| ≤ M := by
  rw [abs_div, abs_of_pos hx.1, div_le_iff₀ hx.1]
  exact abs_sub_le_mul hu hM ⟨hx.1.le, hx.2⟩

theorem continuousOn_integrand (hu : ContDiff ℝ 1 u) :
    ContinuousOn (fun x => (u x - u 0) / x) (Ioc (0 : ℝ) 1) :=
  (hu.continuous.continuousOn.sub continuousOn_const).div continuousOn_id
    fun _ hx => hx.1.ne'

/-- **Integrability of the finite part**: for `C¹` `u` the subtracted integrand
`(u x − u 0)/x` is integrable on `(0,1]`. -/
theorem integrable_finitePart (hu : ContDiff ℝ 1 u) :
    IntegrableOn (fun x => (u x - u 0) / x) (Ioc (0 : ℝ) 1) := by
  obtain ⟨M, hM⟩ := exists_deriv_bound hu
  refine IntegrableOn.of_bound measure_Ioc_lt_top
    ((continuousOn_integrand hu).aestronglyMeasurable measurableSet_Ioc) M ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  rw [Real.norm_eq_abs]
  exact abs_integrand_le hu hM hx

/-! ## Linearity -/

theorem finitePart_add (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v) :
    finitePart (u + v) = finitePart u + finitePart v := by
  unfold finitePart
  rw [← integral_add (integrable_finitePart hu) (integrable_finitePart hv)]
  congr 1
  funext x
  simp only [Pi.add_apply]
  ring

theorem finitePart_const_mul (c : ℝ) (u : ℝ → ℝ) :
    finitePart (fun x => c * u x) = c * finitePart u := by
  unfold finitePart
  rw [← integral_const_mul]
  congr 1
  funext x
  ring

theorem finitePart_smul (c : ℝ) (u : ℝ → ℝ) : finitePart (c • u) = c * finitePart u :=
  finitePart_const_mul c u

theorem finitePart_neg (u : ℝ → ℝ) : finitePart (-u) = -finitePart u := by
  rw [show (-u) = fun x => -1 * u x from by funext x; simp, finitePart_const_mul, neg_one_mul]

theorem finitePart_sub (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v) :
    finitePart (u - v) = finitePart u - finitePart v := by
  have hnv : ContDiff ℝ 1 (-v) := hv.neg
  rw [sub_eq_add_neg, finitePart_add hu hnv, finitePart_neg, sub_eq_add_neg]

/-! ## The order-one estimate and the support -/

/-- **Order at most one**: `|F u| ≤ M` whenever `|u'| ≤ M` on `[0,1]`. -/
theorem abs_finitePart_le (hu : ContDiff ℝ 1 u) {M : ℝ}
    (hM : ∀ x ∈ Icc (0 : ℝ) 1, |deriv u x| ≤ M) : |finitePart u| ≤ M := by
  have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (0 : ℝ) 1)
    (f := fun x => (u x - u 0) / x) measure_Ioc_lt_top
    (fun x hx => by rw [Real.norm_eq_abs]; exact abs_integrand_le hu hM hx)
  simpa [Real.norm_eq_abs, finitePart] using h

/-- `F` only sees `u` on `[0,1]`. -/
theorem finitePart_congr (h : EqOn u v (Icc (0 : ℝ) 1)) : finitePart u = finitePart v :=
  setIntegral_congr_fun measurableSet_Ioc fun x hx => by
    rw [h ⟨hx.1.le, hx.2⟩, h ⟨le_rfl, zero_le_one⟩]

/-- **Support in `[0,1]`**: `F u = 0` when `u` vanishes on `[0,1]`. -/
theorem finitePart_eq_zero_of_eqOn_zero (h : EqOn u 0 (Icc (0 : ℝ) 1)) : finitePart u = 0 :=
  setIntegral_eq_zero_of_forall_eq_zero fun x hx => by
    rw [h ⟨hx.1.le, hx.2⟩, h ⟨le_rfl, zero_le_one⟩]
    simp

/-! ## No order-zero bound

The smooth cutoffs `bump ε x = χ(x/ε) · χ(2 − x)` with `χ = Real.smoothTransition` are `1` on
`[ε, 1]`, vanish at `0`, take values in `[0,1]` and are supported in the fixed compact `[0,2]`.
-/

/-- Smooth cutoff of the constant `1` near `0` at scale `ε`, cut off again to the right of `1`. -/
noncomputable def bump (ε x : ℝ) : ℝ :=
  Real.smoothTransition (x / ε) * Real.smoothTransition (2 - x)

theorem contDiff_bump (ε : ℝ) : ContDiff ℝ ∞ (bump ε) :=
  (Real.smoothTransition.contDiff.comp (contDiff_id.div_const ε)).mul
    (Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id))

theorem bump_nonneg (ε x : ℝ) : 0 ≤ bump ε x :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem bump_le_one (ε x : ℝ) : bump ε x ≤ 1 :=
  mul_le_one₀ (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _)
    (Real.smoothTransition.le_one _)

theorem abs_bump_le_one (ε x : ℝ) : |bump ε x| ≤ 1 := by
  rw [abs_of_nonneg (bump_nonneg ε x)]
  exact bump_le_one ε x

theorem bump_zero (ε : ℝ) : bump ε 0 = 0 := by
  simp [bump, Real.smoothTransition.zero_of_nonpos le_rfl]

theorem bump_eq_one {ε : ℝ} (hε : 0 < ε) {x : ℝ} (hx : x ∈ Icc ε 1) : bump ε x = 1 := by
  rw [bump, Real.smoothTransition.one_of_one_le ((one_le_div₀ hε).mpr hx.1),
    Real.smoothTransition.one_of_one_le (by linarith [hx.2]), mul_one]

theorem support_bump_subset {ε : ℝ} (hε : 0 < ε) : Function.support (bump ε) ⊆ Ioo 0 2 := by
  intro x hx
  rw [Function.mem_support, bump] at hx
  refine ⟨?_, ?_⟩
  · by_contra h
    exact hx (by rw [Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg
      (not_lt.mp h) hε.le), zero_mul])
  · by_contra h
    have h2 : 2 - x ≤ 0 := by linarith [not_lt.mp h]
    exact hx (by rw [Real.smoothTransition.zero_of_nonpos h2, mul_zero])

theorem tsupport_bump_subset {ε : ℝ} (hε : 0 < ε) : tsupport (bump ε) ⊆ Icc 0 2 :=
  closure_minimal ((support_bump_subset hε).trans Ioo_subset_Icc_self) isClosed_Icc

/-- **The finite part of the cutoff is at least `log (1/ε)`**: `F (bump ε) ≥ ∫_ε^1 dx/x`. -/
theorem log_le_finitePart_bump {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Real.log (1 / ε) ≤ finitePart (bump ε) := by
  have hint : IntegrableOn (fun x => bump ε x / x) (Ioc (0 : ℝ) 1) := by
    have h := integrable_finitePart ((contDiff_bump ε).of_le (mod_cast le_top))
    simpa [bump_zero] using h
  calc Real.log (1 / ε) = ∫ x in ε..1, x⁻¹ := (integral_inv_of_pos hε one_pos).symm
    _ = ∫ x in Ioc ε 1, bump ε x / x := by
      rw [intervalIntegral.integral_of_le hε1]
      refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
      rw [bump_eq_one hε ⟨hx.1.le, hx.2⟩, one_div]
    _ ≤ ∫ x in Ioc 0 1, bump ε x / x := by
      refine setIntegral_mono_set hint ?_ (Ioc_subset_Ioc_left hε.le).eventuallyLE
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact div_nonneg (bump_nonneg ε x) hx.1.le
    _ = finitePart (bump ε) := by simp [finitePart, bump_zero]

/-- **No order-zero bound**: there is no constant `C` with `|F u| ≤ C` for all smooth `u`
supported in the fixed compact `[-1,2]` with `|u| ≤ 1`. The finite part is a distribution of
order exactly one — not a measure. -/
theorem no_order_zero_bound :
    ¬ ∃ C : ℝ, ∀ u : ℝ → ℝ, ContDiff ℝ ∞ u → tsupport u ⊆ Icc (-1) 2 →
      (∀ x, |u x| ≤ 1) → |finitePart u| ≤ C := by
  rintro ⟨C, hC⟩
  set ε := Real.exp (-(|C| + 1)) with hεdef
  have hε : 0 < ε := Real.exp_pos _
  have hε1 : ε ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [abs_nonneg C])
  have h := hC (bump ε) (contDiff_bump ε)
    ((tsupport_bump_subset hε).trans (Icc_subset_Icc_left (by norm_num))) (abs_bump_le_one ε)
  have hlog := log_le_finitePart_bump hε hε1
  have hval : Real.log (1 / ε) = |C| + 1 := by
    rw [one_div, Real.log_inv, hεdef, Real.log_exp, neg_neg]
  linarith [le_abs_self (finitePart (bump ε)), le_abs_self C]

/-! ## Link to the shallow-stratum counterexample -/

/-- `F (x^M) = ∫₀¹ x^{M−1} dx = 1/M` for `M ≥ 1`. -/
theorem finitePart_pow (M : ℕ) (hM : 1 ≤ M) : finitePart (fun x => x ^ M) = 1 / M := by
  obtain ⟨m, rfl⟩ : ∃ m, M = m + 1 := ⟨M - 1, by omega⟩
  unfold finitePart
  rw [setIntegral_congr_fun measurableSet_Ioc (g := fun x : ℝ => x ^ m)
    (fun x hx => by simp only; rw [zero_pow (Nat.succ_ne_zero m), sub_zero, pow_succ,
      mul_div_cancel_right₀ _ hx.1.ne'])]
  rw [← intervalIntegral.integral_of_le zero_le_one, integral_pow]
  push_cast
  simp

/-- The `n^{-1/2}` coefficient of `x^M` on the corner `x²y² = 0` (`xM_isEquivalent`, CDX) is
`(√π/2) · F(x^M)`: the tangential coefficient functional is the finite part along the axis. -/
theorem xM_isEquivalent_finitePart (M : ℕ) (hM : 1 ≤ M) :
    (fun n : ℝ => ∫ x in Ioc (0 : ℝ) 1, ∫ y in Ioc (0 : ℝ) 1,
        x ^ M * Real.exp (-n * (x ^ 2 * y ^ 2)))
      ~[atTop] fun n : ℝ =>
        Real.sqrt Real.pi / 2 * finitePart (fun x => x ^ M) * n ^ (-(1 / 2 : ℝ)) := by
  have h := SmoothEngine.xM_isEquivalent M hM
  rw [finitePart_pow M hM]
  refine h.congr_right (Eventually.of_forall fun n => ?_)
  ring

end Grammar.FinitePart
