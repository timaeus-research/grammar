/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.GaussianDepthThree
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# The depth-two Gaussian DLN and the Bessel function `K₀`

With `K₀` defined by its integral representation for positive argument,
`K₀(z) = ∫₀^∞ e^{−z cosh t} dt` (`besselK0Integral`; no Bessel API is claimed beyond this),
the depth-two partition function is exactly

  `Z_2(N) = e^{1/(4N)} K₀(1/(4N))/√(2πN)`  for `N > 0`  (★★★ `gaussLaplace2_eq_besselK0Integral`),

by the substitution `y = sinh t/√N` in the conditional reduction
`Z_2(N) = ∫ g(y)/√(1 + N y²) dy`, `1 + sinh² t = cosh² t`, `sinh² t = (cosh 2t − 1)/2` and the
rescaling `u = 2t` (examples_slop §2, the closed form of eq. (dln_gauss) at `L = 2`; Astra round-9
target 3).  Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

/-- `K₀(z) = ∫₀^∞ e^{−z cosh t} dt` (the integral representation, `z > 0`). -/
noncomputable def besselK0Integral (z : ℝ) : ℝ := ∫ t in Ioi (0 : ℝ), Real.exp (-z * Real.cosh t)

/-- `cosh t ≥ t` for `t ≥ 0`. -/
theorem le_cosh_of_nonneg {t : ℝ} (ht : 0 ≤ t) : t ≤ Real.cosh t :=
  (Real.self_le_sinh_iff.2 ht).trans (le_of_lt (Real.sinh_lt_cosh t))

theorem integrableOn_besselK0Integral {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun t : ℝ => Real.exp (-z * Real.cosh t)) (Ioi 0) := by
  refine (exp_neg_integrableOn_Ioi 0 hz).mono' (by fun_prop : Measurable fun t : ℝ =>
    Real.exp (-z * Real.cosh t)).aestronglyMeasurable.restrict ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Eventually.of_forall fun t ht => ?_
  have ht0 : (0 : ℝ) < t := ht
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.2 (by nlinarith [le_cosh_of_nonneg ht0.le])

/-- `sinh t → ∞`. -/
theorem tendsto_sinh_atTop : Tendsto Real.sinh atTop atTop :=
  tendsto_atTop_mono' atTop (by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact Real.self_le_sinh_iff.2 ht) tendsto_id

/-- The substituted integrand:
`g(sinh t/√N)/√(1 + sinh² t) · cosh t/√N = e^{−sinh² t/(2N)}/(√(2π)√N)`. -/
theorem density_comp_sinh {N t : ℝ} (hN : 0 < N) :
    gaussDensity (Real.sinh t / Real.sqrt N) /
      Real.sqrt (1 + N * (Real.sinh t / Real.sqrt N) ^ 2) * (Real.cosh t / Real.sqrt N) =
      Real.exp (-(Real.sinh t) ^ 2 / (2 * N)) / (Real.sqrt (2 * Real.pi) * Real.sqrt N) := by
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN
  have hcosh : 0 < Real.cosh t := Real.cosh_pos t
  have h1 : 1 + N * (Real.sinh t / Real.sqrt N) ^ 2 = Real.cosh t ^ 2 := by
    rw [div_pow, Real.sq_sqrt hN.le, Real.cosh_sq]; field_simp; ring
  rw [h1, Real.sqrt_sq hcosh.le]
  unfold gaussDensity
  have h2 : -(Real.sinh t / Real.sqrt N) ^ 2 / 2 = -(Real.sinh t) ^ 2 / (2 * N) := by
    rw [div_pow, Real.sq_sqrt hN.le]; field_simp
  rw [h2]
  field_simp

/-- ★★★ **The Bessel closed form at depth two**:
`Z_2(N) = e^{1/(4N)} K₀(1/(4N))/√(2πN)`, `N > 0`. -/
theorem gaussLaplace2_eq_besselK0Integral {N : ℝ} (hN : 0 < N) :
    gaussLaplace2 N = Real.exp (1 / (4 * N)) * besselK0Integral (1 / (4 * N)) /
      Real.sqrt (2 * Real.pi * N) := by
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  rw [gaussLaplace2_eq_density_integral hN.le]
  -- evenness
  have heven : ∫ y : ℝ, gaussDensity y / Real.sqrt (1 + N * y ^ 2) =
      2 * ∫ y in Ioi (0 : ℝ), gaussDensity y / Real.sqrt (1 + N * y ^ 2) := by
    rw [← integral_comp_abs (f := fun y => gaussDensity y / Real.sqrt (1 + N * y ^ 2))]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [gaussDensity, sq_abs]
  -- the substitution `y = sinh t/√N`
  set f : ℝ → ℝ := fun t => Real.sinh t / Real.sqrt N with hf
  set f' : ℝ → ℝ := fun t => Real.cosh t / Real.sqrt N with hf'
  set G : ℝ → ℝ := fun y => gaussDensity y / Real.sqrt (1 + N * y ^ 2) with hG
  have hGcont : Continuous G := by
    rw [hG]
    exact continuous_gaussDensity.div (by fun_prop) fun y =>
      (Real.sqrt_pos.2 (by positivity)).ne'
  have hGint : Integrable G := by
    refine integrable_gaussDensity.mono' hGcont.aestronglyMeasurable
      (Eventually.of_forall fun y => ?_)
    simp only [hG]
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (gaussDensity_nonneg y) (Real.sqrt_nonneg _))]
    have h1 : 1 ≤ Real.sqrt (1 + N * y ^ 2) := Real.one_le_sqrt.2 (by nlinarith [sq_nonneg y])
    have hg0 := gaussDensity_nonneg y
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hsub := integral_comp_mul_deriv_Ioi (f := f) (f' := f') (g := G) (a := 0)
    (Real.continuous_sinh.div_const _).continuousOn
    (by
      have := tendsto_sinh_atTop
      simpa [hf, div_eq_mul_inv] using this.atTop_mul_const (inv_pos.2 hsN))
    (fun x _ => ((Real.hasDerivAt_sinh x).div_const _).hasDerivWithinAt)
    hGcont.continuousOn hGint.integrableOn ?_
  · have hf0 : f 0 = 0 := by simp [hf]
    rw [hf0] at hsub
    rw [heven, ← hsub]
    -- the substituted integrand and the half-angle formula
    have e : ∀ t ∈ Ioi (0 : ℝ), (G ∘ f) t * f' t =
        Real.exp (1 / (4 * N)) / (Real.sqrt (2 * Real.pi) * Real.sqrt N) *
          Real.exp (-(1 / (4 * N)) * Real.cosh (2 * t)) := by
      intro t _
      simp only [Function.comp, hG, hf, hf']
      rw [density_comp_sinh hN, Real.cosh_two_mul, Real.cosh_sq, div_mul_eq_mul_div,
        ← Real.exp_add]
      congr 2
      field_simp
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi e, integral_const_mul]
    have h2 := integral_comp_mul_left_Ioi (fun u : ℝ => Real.exp (-(1 / (4 * N)) * Real.cosh u)) 0
      (b := 2) two_pos
    rw [mul_zero, smul_eq_mul] at h2
    rw [h2]
    unfold besselK0Integral
    rw [Real.sqrt_mul (by positivity) N]
    field_simp
  · -- integrability of the substituted integrand on `[0, ∞)`
    have hmaj : IntegrableOn (fun t : ℝ => 1 / (Real.sqrt (2 * Real.pi) * Real.sqrt N) *
        Real.exp (-(1 / (2 * N)) * t ^ 2)) (Ici 0) :=
      ((integrable_exp_neg_mul_sq (by positivity : (0 : ℝ) < 1 / (2 * N))).const_mul _).integrableOn
    refine hmaj.mono' ?_ ?_
    · refine Continuous.aestronglyMeasurable ?_
      exact (hGcont.comp (Real.continuous_sinh.div_const _)).mul (Real.continuous_cosh.div_const _)
    · rw [ae_restrict_iff' measurableSet_Ici]
      refine Eventually.of_forall fun t ht => ?_
      have ht0 : (0 : ℝ) ≤ t := ht
      simp only [Function.comp, hG, hf, hf']
      rw [density_comp_sinh hN, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hsinh : t ≤ Real.sinh t := Real.self_le_sinh_iff.2 ht0
      have hsq : t ^ 2 ≤ Real.sinh t ^ 2 := pow_le_pow_left₀ ht0 hsinh 2
      rw [show Real.exp (-(Real.sinh t) ^ 2 / (2 * N)) /
          (Real.sqrt (2 * Real.pi) * Real.sqrt N) =
        1 / (Real.sqrt (2 * Real.pi) * Real.sqrt N) *
          Real.exp (-(Real.sinh t) ^ 2 / (2 * N)) by ring]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
      rw [show -(1 / (2 * N)) * t ^ 2 = -t ^ 2 / (2 * N) by ring]
      exact div_le_div_of_nonneg_right (by linarith) (by positivity)

end Grammar
