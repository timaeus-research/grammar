/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.BlowUpQuarticSecondOrder

/-!
# The blow-up evidence in closed form: `Z_N = (√(2π)/(2√N)) e^{1/(16N)} K₀(1/(16N))`

The substitution `u = √ε sinh(s/4)` turns the moving-amplitude integral into a Bessel integral:
`u⁴ + εu² = (ε²/8)(cosh s − 1)` and `2 du/√(u² + ε) = ds/2`, so with `z = ε²/16`

  ★★★ `ampJ_movingAmp_eq_besselK0 : J_{a_ε}(ε) = ½ e^{z} K₀(z)`,   `K₀(z) = ∫₀^∞ e^{−z cosh s} ds`,

and hence, for every `N > 0`,

  ★★★ `blowupLaplace_eq_besselK0 : Z_N = √(2π)/(2√N) · e^{1/(16N)} K₀(1/(16N))`

— the blow-up model's partition function `∫_{ℝ²} e^{−Nx²(x²+y²)/2} e^{−|w|²/2} dw` is a modified
Bessel function of the second kind, exactly (Astra round 31).  The expansion
`Z_N = √(π/2)(log N + 5log2 − γ)/√N + (√(2π)/32)(log N + 5log2 − γ)/N^{3/2} + …` is the small-`z`
series `½e^zK₀(z) = (1 + z)·½(log(2/z) − γ) + O(z²log(1/z))`.  Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

/-! ### The Bessel integral -/

/-- `K₀(z) = ∫₀^∞ e^{−z cosh s} ds` (the modified Bessel function of the second kind of order
zero, as its Schläfli integral). -/
noncomputable def besselK0 (z : ℝ) : ℝ := ∫ s in Ioi (0 : ℝ), Real.exp (-z * Real.cosh s)

theorem half_add_one_le_cosh (s : ℝ) : (s + 1) / 2 ≤ Real.cosh s := by
  rw [Real.cosh_eq]
  linarith [Real.add_one_le_exp s, Real.exp_pos (-s)]

theorem integrableOn_exp_neg_mul_cosh {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun s : ℝ => Real.exp (-z * Real.cosh s)) (Ioi 0) := by
  refine ((exp_neg_integrableOn_Ioi 0 (by positivity : 0 < z / 2)).const_mul
    (Real.exp (-z / 2))).mono'
    ((by fun_prop : Measurable fun s : ℝ => Real.exp (-z * Real.cosh s)).aestronglyMeasurable) ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Eventually.of_forall fun s _ => ?_
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
  apply Real.exp_le_exp.2
  have := mul_le_mul_of_nonneg_left (half_add_one_le_cosh s) hz.le
  linarith

theorem besselK0_pos {z : ℝ} (hz : 0 < z) : 0 < besselK0 z := by
  unfold besselK0
  refine setIntegral_pos_iff_support_of_nonneg_ae
    (Eventually.of_forall fun s => (Real.exp_pos _).le) (integrableOn_exp_neg_mul_cosh hz) |>.2 ?_
  have : Function.support (fun s : ℝ => Real.exp (-z * Real.cosh s)) = univ :=
    Function.support_eq_univ fun s => (Real.exp_pos _).ne'
  rw [this, univ_inter, Real.volume_Ioi]
  exact ENNReal.zero_lt_top

/-! ### The substitution `u = √ε sinh(s/4)` -/

/-- `φ_ε(s) = √ε sinh(s/4)`. -/
noncomputable def besselSub (ε s : ℝ) : ℝ := Real.sqrt ε * Real.sinh (s / 4)

/-- `φ_ε'(s) = (√ε/4) cosh(s/4)`. -/
noncomputable def besselSub' (ε s : ℝ) : ℝ := Real.sqrt ε / 4 * Real.cosh (s / 4)

theorem hasDerivAt_besselSub (ε s : ℝ) : HasDerivAt (besselSub ε) (besselSub' ε s) s := by
  have h1 : HasDerivAt (fun t : ℝ => t / 4) (1 / 4) s := (hasDerivAt_id s).div_const 4
  have h2 := (Real.hasDerivAt_sinh (s / 4)).comp s h1
  have h3 := h2.const_mul (Real.sqrt ε)
  unfold besselSub besselSub'
  exact h3.congr_deriv (by ring)

theorem besselSub_zero (ε : ℝ) : besselSub ε 0 = 0 := by
  simp [besselSub]

theorem besselSub_nonneg {ε s : ℝ} (hs : 0 ≤ s) : 0 ≤ besselSub ε s :=
  mul_nonneg (Real.sqrt_nonneg ε) (Real.sinh_nonneg_iff.2 (by linarith))

theorem tendsto_besselSub {ε : ℝ} (hε : 0 < ε) : Tendsto (besselSub ε) atTop atTop := by
  have hsε : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  refine tendsto_atTop_mono' atTop ?_
    ((tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 4)).const_mul_atTop hsε)
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
  unfold besselSub
  simp only [id_eq]
  exact mul_le_mul_of_nonneg_left (Real.self_le_sinh_iff.2 (by linarith)) hsε.le

/-- The transformed integrand: `g(φ(s)) φ'(s) = ½ e^{−z(cosh s − 1)}` with `z = ε²/16`. -/
theorem movingAmp_comp_besselSub {ε : ℝ} (hε : 0 < ε) (s : ℝ) :
    2 * movingAmp ε (besselSub ε s) / Real.sqrt (besselSub ε s ^ 2 + ε) * besselSub' ε s =
      Real.exp (-(ε ^ 2 / 16 * (Real.cosh s - 1))) / 2 := by
  unfold movingAmp blowAmpInf besselSub besselSub'
  set S := Real.sinh (s / 4) with hS
  set C := Real.cosh (s / 4) with hC
  have hC0 : 0 < C := Real.cosh_pos _
  have hC2 : C ^ 2 = S ^ 2 + 1 := Real.cosh_sq _
  have h1 : Real.sinh (s / 2) ^ 2 = 4 * S ^ 2 * C ^ 2 := by
    rw [show s / 2 = 2 * (s / 4) by ring, Real.sinh_two_mul]
    ring
  have h2 : Real.cosh s = 1 + 2 * Real.sinh (s / 2) ^ 2 := by
    rw [show s = 2 * (s / 2) by ring, Real.cosh_two_mul, Real.cosh_sq]
    ring
  have hsqrt : Real.sqrt ((Real.sqrt ε * S) ^ 2 + ε) = Real.sqrt ε * C := by
    rw [mul_pow, Real.sq_sqrt hε.le, show ε * S ^ 2 + ε = ε * C ^ 2 by rw [hC2]; ring,
      Real.sqrt_mul hε.le, Real.sqrt_sq hC0.le]
  rw [hsqrt, ← Real.exp_add]
  have hsε : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have e : 2 * Real.exp (-(Real.sqrt ε * S) ^ 4 / 2 + -ε * (Real.sqrt ε * S) ^ 2 / 2) /
      (Real.sqrt ε * C) * (Real.sqrt ε / 4 * C) =
      Real.exp (-(Real.sqrt ε * S) ^ 4 / 2 + -ε * (Real.sqrt ε * S) ^ 2 / 2) / 2 := by
    field_simp
    norm_num
  rw [e]
  congr 2
  have h4 : Real.sqrt ε ^ 4 = ε ^ 2 := by
    have := Real.sq_sqrt hε.le
    linear_combination (Real.sqrt ε ^ 2 + ε) * this
  rw [mul_pow, mul_pow, Real.sq_sqrt hε.le, h4, h2, h1, hC2]
  ring

/-! ### The closed form -/

theorem continuous_movingAmp_div_sqrt {ε : ℝ} (hε : 0 < ε) :
    Continuous fun u : ℝ => 2 * movingAmp ε u / Real.sqrt (u ^ 2 + ε) := by
  refine Continuous.div (by unfold movingAmp blowAmpInf; fun_prop) (by fun_prop) fun u => ?_
  exact (Real.sqrt_pos.2 (by positivity)).ne'

/-- ★★★ **The moving-amplitude integral is a Bessel function**:
`J_{a_ε}(ε) = ∫₀^∞ 2a_ε(u)/√(u²+ε) du = ½ e^{ε²/16} K₀(ε²/16)` for every `ε > 0`. -/
theorem ampJ_movingAmp_eq_besselK0 {ε : ℝ} (hε : 0 < ε) :
    ampJ (movingAmp ε) ε = Real.exp (ε ^ 2 / 16) * besselK0 (ε ^ 2 / 16) / 2 := by
  have hz : 0 < ε ^ 2 / 16 := by positivity
  set g : ℝ → ℝ := fun u => 2 * movingAmp ε u / Real.sqrt (u ^ 2 + ε) with hg
  have hgc : Continuous g := continuous_movingAmp_div_sqrt hε
  have hkey : ∀ s, (g ∘ besselSub ε) s * besselSub' ε s =
      Real.exp (ε ^ 2 / 16) / 2 * Real.exp (-(ε ^ 2 / 16) * Real.cosh s) := by
    intro s
    rw [Function.comp_apply, hg]
    beta_reduce
    rw [movingAmp_comp_besselSub hε s, show Real.exp (ε ^ 2 / 16) / 2 *
      Real.exp (-(ε ^ 2 / 16) * Real.cosh s) =
      Real.exp (ε ^ 2 / 16 + -(ε ^ 2 / 16) * Real.cosh s) / 2 by rw [Real.exp_add]; ring]
    congr 2
    ring
  have hint := integrableOn_exp_neg_mul_cosh hz
  have h := integral_comp_mul_deriv_Ioi (f := besselSub ε) (f' := besselSub' ε) (g := g) (a := 0)
    (fun s _ => (hasDerivAt_besselSub ε s).continuousAt.continuousWithinAt)
    (tendsto_besselSub hε)
    (fun s _ => (hasDerivAt_besselSub ε s).hasDerivWithinAt)
    hgc.continuousOn
    ((integrableOn_Ici_iff_integrableOn_Ioi (b := 0) |>.2
      (integrableOn_two_movingAmp_div_sqrt hε)).mono_set
      (image_subset_iff.2 fun s hs => besselSub_nonneg hs))
    ((integrableOn_Ici_iff_integrableOn_Ioi (b := 0) |>.2
      (hint.const_mul (Real.exp (ε ^ 2 / 16) / 2))).congr_fun
      (fun s _ => (hkey s).symm) measurableSet_Ici)
  rw [besselSub_zero] at h
  unfold ampJ
  rw [show (∫ u in Ioi (0 : ℝ), 2 * movingAmp ε u / Real.sqrt (u ^ 2 + ε)) = ∫ u in Ioi (0 : ℝ), g u
    from rfl, ← h, setIntegral_congr_fun measurableSet_Ioi fun s _ => hkey s, integral_const_mul]
  unfold besselK0
  ring

/-- ★★★ **The blow-up evidence in closed form**: for every `N > 0`,
`Z_N = ∫_{ℝ²} e^{−Nx²(x²+y²)/2} e^{−|w|²/2} dw = √(2π)/(2√N) · e^{1/(16N)} K₀(1/(16N))`. -/
theorem blowupLaplace_eq_besselK0 {N : ℝ} (hN : 0 < N) :
    blowupLaplace N = Real.sqrt (2 * Real.pi) / (2 * Real.sqrt N) *
      Real.exp (1 / (16 * N)) * besselK0 (1 / (16 * N)) := by
  set m := N ^ (1 / 4 : ℝ) with hm
  have hm0 : 0 < m := Real.rpow_pos_of_pos hN _
  have hm4 : m ^ 4 = N := by
    rw [hm, ← Real.rpow_natCast, ← Real.rpow_mul hN.le]; norm_num
  have hsqrt : Real.sqrt N = m ^ 2 := by
    rw [← hm4, show m ^ 4 = (m ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have hε : (1 / m ^ 2) ^ 2 / 16 = 1 / (16 * N) := by
    rw [← hm4]; field_simp
  rw [← hm4, blowupLaplace_eq_ampJ hm0, blowAmp_eq_movingAmp hm0, ampJ_movingAmp_eq_besselK0
    (by positivity), hε, hm4, hsqrt]
  field_simp

end Grammar
