/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.ConeGaussian

/-!
# The cone's frozen partition function in closed form

With the Leray density `2π² e^{−|v|}` of `Grammar.ConeGaussian`, the frozen partition function of
the cone model with a constant field `a` is a one-dimensional integral, and completing the square
on each half-line evaluates it through the Gaussian tail `T(c) = ∫_c^∞ e^{−s²/2} ds`:

  `∫_ℝ e^{−Nv²/2 + √N a v − |v|} dv
     = N^{−1/2} [ e^{(a − 1/√N)²/2} T(1/√N − a) + e^{(a + 1/√N)²/2} T(1/√N + a) ]`

(★★ `integral_cone_leray_closed`), hence ★★★ `cone_evidence_closed` for the four-dimensional
model.  Every term of the expansion in `N^{−1/2}` (examples_slop §3) is then a Taylor coefficient of
this closed form: at `a = 0`, `Z_N = 4π² N^{−1/2} e^{1/(2N)} T(1/√N)`, whose expansion
`4π²N^{−1/2}[√(π/2) − N^{−1/2} + …]` exhibits the vertex term `−4π² N^{−1}`.
Zero `sorry`/`axiom`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Grammar

/-- The Gaussian tail `T(c) = ∫_c^∞ e^{−s²/2} ds`. -/
noncomputable def gaussTailStd (c : ℝ) : ℝ := ∫ s in Ioi c, Real.exp (-s ^ 2 / 2)

/-- Translation of a half-line integral: `∫_{c}^∞ f = ∫_0^∞ f(x + c)`. -/
theorem integral_Ioi_comp_add_right (f : ℝ → ℝ) (c : ℝ) :
    ∫ x in Ioi c, f x = ∫ x in Ioi (0 : ℝ), f (x + c) := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi,
    ← integral_add_right_eq_self (fun x => (Ioi c).indicator f x) c]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [indicator_apply, mem_Ioi]
  have : c < x + c ↔ 0 < x := by constructor <;> intro h <;> linarith
  simp only [this]

/-- Reflection: `∫_{−∞}^{0} f = ∫_0^∞ f(−x)`. -/
theorem integral_Iio_zero_eq_Ioi_neg (f : ℝ → ℝ) :
    ∫ x in Iio (0 : ℝ), f x = ∫ x in Ioi (0 : ℝ), f (-x) := by
  rw [← integral_indicator measurableSet_Iio, ← integral_indicator measurableSet_Ioi,
    ← integral_neg_eq_self (fun x => (Iio (0 : ℝ)).indicator f x)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [indicator_apply, mem_Iio, mem_Ioi, neg_lt_zero]

/-- Completing the square on the half-line, `N = s²`:
`∫_0^∞ e^{−s²v²/2 + bv} dv = s⁻¹ e^{b²/(2s²)} T(−b/s)`. -/
theorem integral_Ioi_exp_quadratic {s : ℝ} (hs : 0 < s) (b : ℝ) :
    ∫ v in Ioi (0 : ℝ), Real.exp (-s ^ 2 * v ^ 2 / 2 + b * v) =
      s⁻¹ * Real.exp (b ^ 2 / (2 * s ^ 2)) * gaussTailStd (-b / s) := by
  have e1 : ∀ v : ℝ, Real.exp (-s ^ 2 * v ^ 2 / 2 + b * v) =
      Real.exp (b ^ 2 / (2 * s ^ 2)) * Real.exp (-s ^ 2 * (v - b / s ^ 2) ^ 2 / 2) := by
    intro v
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  simp_rw [e1]
  rw [integral_const_mul]
  have hshift : ∫ v in Ioi (0 : ℝ), Real.exp (-s ^ 2 * (v - b / s ^ 2) ^ 2 / 2) =
      ∫ u in Ioi (-(b / s ^ 2)), Real.exp (-s ^ 2 * u ^ 2 / 2) := by
    rw [integral_Ioi_comp_add_right (fun u => Real.exp (-s ^ 2 * u ^ 2 / 2)) (-(b / s ^ 2))]
    refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
    congr 1
  have hscale : ∫ u in Ioi (-(b / s ^ 2)), Real.exp (-s ^ 2 * u ^ 2 / 2) =
      s⁻¹ * gaussTailStd (-b / s) := by
    have h := integral_comp_mul_left_Ioi (fun t => Real.exp (-t ^ 2 / 2)) (-(b / s ^ 2)) hs
    rw [smul_eq_mul] at h
    have e2 : ∀ u : ℝ, (fun t => Real.exp (-t ^ 2 / 2)) (s * u) =
        Real.exp (-s ^ 2 * u ^ 2 / 2) := by
      intro u; simp only; congr 1; ring
    simp_rw [e2] at h
    rw [h, gaussTailStd, show s * -(b / s ^ 2) = -b / s by field_simp]
  rw [hshift, hscale]
  ring

/-- ★★ The cone's Leray integral in closed form, `N = s²`: for every field `a`,
`∫_ℝ e^{−s²v²/2 + s a v − |v|} dv
  = s⁻¹[e^{(a − 1/s)²/2} T(1/s − a) + e^{(a + 1/s)²/2} T(1/s + a)]`. -/
theorem integral_cone_leray_closed {s : ℝ} (hs : 0 < s) (a : ℝ) :
    ∫ v, Real.exp (-s ^ 2 * v ^ 2 / 2 + s * v * a - |v|) =
      s⁻¹ * (Real.exp ((a - 1 / s) ^ 2 / 2) * gaussTailStd (1 / s - a) +
        Real.exp ((a + 1 / s) ^ 2 / 2) * gaussTailStd (1 / s + a)) := by
  have hint : Integrable fun v : ℝ => Real.exp (-s ^ 2 * v ^ 2 / 2 + s * v * a - |v|) := by
    have hb : 0 < (((s ^ 2 / 2 : ℝ) : ℂ)).re := by
      rw [Complex.ofReal_re]; positivity
    have h := (integrable_cexp_quadratic hb ((s * a : ℝ) : ℂ) 0).norm
    refine h.mono' ?_ (Filter.Eventually.of_forall fun v => ?_)
    · exact (by fun_prop : Measurable fun v : ℝ =>
        Real.exp (-s ^ 2 * v ^ 2 / 2 + s * v * a - |v|)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Complex.norm_exp]
      have : -(((s ^ 2 / 2 : ℝ) : ℂ)) * (v : ℂ) ^ 2 + ((s * a : ℝ) : ℂ) * (v : ℂ) + 0 =
          ((-(s ^ 2 / 2) * v ^ 2 + s * a * v + 0 : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.ofReal_re]
      exact Real.exp_le_exp.mpr (by linarith [abs_nonneg v])
  rw [← integral_add_compl measurableSet_Iio hint, compl_Iio,
    Measure.restrict_congr_set Ioi_ae_eq_Ici.symm, integral_Iio_zero_eq_Ioi_neg]
  have hpos : ∫ v in Ioi (0 : ℝ), Real.exp (-s ^ 2 * v ^ 2 / 2 + s * v * a - |v|) =
      ∫ v in Ioi (0 : ℝ), Real.exp (-s ^ 2 * v ^ 2 / 2 + (s * a - 1) * v) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun v hv => ?_
    rw [abs_of_pos hv]; congr 1; ring
  have hneg : ∫ v in Ioi (0 : ℝ), Real.exp (-s ^ 2 * (-v) ^ 2 / 2 + s * (-v) * a - |-v|) =
      ∫ v in Ioi (0 : ℝ), Real.exp (-s ^ 2 * v ^ 2 / 2 + (-(s * a + 1)) * v) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun v hv => ?_
    rw [abs_neg, abs_of_pos hv]; congr 1; ring
  rw [hpos, hneg, integral_Ioi_exp_quadratic hs, integral_Ioi_exp_quadratic hs]
  have e1 : (s * a - 1) ^ 2 / (2 * s ^ 2) = (a - 1 / s) ^ 2 / 2 := by field_simp
  have e2 : (-(s * a + 1)) ^ 2 / (2 * s ^ 2) = (a + 1 / s) ^ 2 / 2 := by field_simp
  have e3 : -(s * a - 1) / s = 1 / s - a := by field_simp; ring
  have e4 : -(-(s * a + 1)) / s = 1 / s + a := by field_simp; ring
  rw [e1, e2, e3, e4]
  ring

/-- ★★★ **The cone's frozen partition function in closed form**: for `N > 0` and every field `a`,
`Z_N[1; a] = 2π² N^{−1/2}[e^{(a − 1/√N)²/2} T(1/√N − a) + e^{(a + 1/√N)²/2} T(1/√N + a)]`. -/
theorem cone_evidence_closed {N : ℝ} (hN : 0 < N) (a : ℝ) :
    ∫ u : (ℝ × ℝ) × (ℝ × ℝ),
        Real.exp (-N * coneQ u ^ 2 / 2 + Real.sqrt N * coneQ u * a) * gaussW u =
      2 * Real.pi ^ 2 * (Real.sqrt N)⁻¹ *
        (Real.exp ((a - 1 / Real.sqrt N) ^ 2 / 2) * gaussTailStd (1 / Real.sqrt N - a) +
          Real.exp ((a + 1 / Real.sqrt N) ^ 2 / 2) * gaussTailStd (1 / Real.sqrt N + a)) := by
  rw [cone_evidence_eq]
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN
  have hsq : Real.sqrt N ^ 2 = N := Real.sq_sqrt hN.le
  have := integral_cone_leray_closed hsN a
  rw [hsq] at this
  rw [this]
  ring

end Grammar
