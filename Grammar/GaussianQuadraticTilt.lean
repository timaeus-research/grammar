/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Mathlib.Probability.Distributions.Gaussian.Real
import Grammar.PredictiveRemainder

/-!
# Quadratic exponential tilts of a real Gaussian
(CCCLVII; companion note, consult #107 model test, part 1)

Tilting `N(m, v)` by `e^{−c w²/2 + y w}` (with `v⁻¹ + c > 0`) gives a constant multiple of
`N(m', v')`, `v' = (v⁻¹ + c)⁻¹`, `m' = v'(m/v + y)`, with constant
`Z = √(v'/v)·exp(m'²/(2v') − m²/(2v))` (★ `gaussianReal_withDensity_quadratic`: an identity of
measures, from the pointwise density identity `gaussianPDFReal_mul_exp_quadratic`). Consequences:
the tilt is integrable (`integrable_exp_quadratic_gaussianReal`), tilted integrals are `Z` times
integrals against the tilted Gaussian (`integral_mul_exp_quadratic_gaussianReal`), and the
quadratic observable `X(w) = −(w²/2 − x w)` (the negative excess loss of the normal-location model)
has `[0,1]` in the interior of its exponential-integrability set under every Gaussian
(`Icc_subset_interior_integrableExpSet_quadratic`), with tilted mean and absolute centred third
moment those of the tilted Gaussian (`tiltMean_quadratic_eq`, `tiltAbsThird_quadratic_eq`). This is
the reusable calculation behind the normal-location discharge of the predictive-remainder
certificate (part 2).
-/

open MeasureTheory ProbabilityTheory Filter Set Real Topology
open scoped ENNReal NNReal

namespace Grammar

/-! ### The tilted parameters and the density identity -/

/-- The tilted variance `(v⁻¹ + c)⁻¹` (as a nonnegative real). -/
noncomputable def tiltVar (v : ℝ≥0) (c : ℝ) : ℝ≥0 := Real.toNNReal (((v : ℝ)⁻¹ + c)⁻¹)

/-- The tilted mean `v'(m/v + y)`. -/
noncomputable def tiltMeanG (m : ℝ) (v : ℝ≥0) (c y : ℝ) : ℝ :=
  ((v : ℝ)⁻¹ + c)⁻¹ * (m / v + y)

/-- The tilt constant `√(v'/v)·exp(m'²/(2v') − m²/(2v))`. -/
noncomputable def tiltConst (m : ℝ) (v : ℝ≥0) (c y : ℝ) : ℝ :=
  Real.sqrt (((v : ℝ)⁻¹ + c)⁻¹ / v) *
    exp (tiltMeanG m v c y ^ 2 / (2 * ((v : ℝ)⁻¹ + c)⁻¹) - m ^ 2 / (2 * v))

variable {m : ℝ} {v : ℝ≥0} {c y : ℝ}

theorem coe_tiltVar (hc : 0 < (v : ℝ)⁻¹ + c) : ((tiltVar v c : ℝ≥0) : ℝ) = ((v : ℝ)⁻¹ + c)⁻¹ :=
  Real.coe_toNNReal _ (inv_pos.2 hc).le

theorem tiltVar_ne_zero (hc : 0 < (v : ℝ)⁻¹ + c) : tiltVar v c ≠ 0 := by
  intro h
  have := coe_tiltVar hc
  rw [h] at this
  simp only [NNReal.coe_zero] at this
  exact (inv_pos.2 hc).ne this

theorem tiltConst_pos (hv : v ≠ 0) (hc : 0 < (v : ℝ)⁻¹ + c) : 0 < tiltConst m v c y := by
  have hv' : (0 : ℝ) < v := by positivity
  unfold tiltConst
  exact mul_pos (Real.sqrt_pos.2 (div_pos (inv_pos.2 hc) hv')) (exp_pos _)

/-- ★ **The pointwise density identity**:
`φ_{m,v}(w) e^{−cw²/2 + yw} = Z · φ_{m',v'}(w)`. -/
theorem gaussianPDFReal_mul_exp_quadratic (hv : v ≠ 0) (hc : 0 < (v : ℝ)⁻¹ + c) (w : ℝ) :
    gaussianPDFReal m v w * exp (-(c * w ^ 2 / 2) + y * w) =
      tiltConst m v c y * gaussianPDFReal (tiltMeanG m v c y) (tiltVar v c) w := by
  have hv' : (0 : ℝ) < v := by positivity
  set vr : ℝ := (v : ℝ) with hvr
  set v' : ℝ := (vr⁻¹ + c)⁻¹ with hv'def
  have hv'pos : 0 < v' := inv_pos.2 hc
  have hcoe : ((tiltVar v c : ℝ≥0) : ℝ) = v' := coe_tiltVar hc
  set m' : ℝ := tiltMeanG m v c y with hm'
  have hm'eq : m' = v' * (m / vr + y) := rfl
  unfold gaussianPDFReal tiltConst
  rw [hcoe]
  -- the prefactors: `(√(2π v))⁻¹ = √(v'/v) · (√(2π v'))⁻¹`
  have hsq' : Real.sqrt (2 * π * v') = Real.sqrt (v' / vr) * Real.sqrt (2 * π * vr) := by
    rw [← Real.sqrt_mul (div_pos hv'pos hv').le]
    congr 1
    field_simp
  have hsqne : Real.sqrt (2 * π * vr) ≠ 0 := by positivity
  have hsqne' : Real.sqrt (2 * π * v') ≠ 0 := by positivity
  have hsqne'' : Real.sqrt (v' / vr) ≠ 0 := by positivity
  have hinv : (Real.sqrt (2 * π * vr))⁻¹ = Real.sqrt (v' / vr) * (Real.sqrt (2 * π * v'))⁻¹ := by
    rw [hsq']
    field_simp
  -- the exponents
  have hexp : -(w - m) ^ 2 / (2 * vr) + (-(c * w ^ 2 / 2) + y * w) =
      (m' ^ 2 / (2 * v') - m ^ 2 / (2 * vr)) + -(w - m') ^ 2 / (2 * v') := by
    have hv'inv : v'⁻¹ = vr⁻¹ + c := by rw [hv'def, inv_inv]
    have hm'v : m' / v' = m / vr + y := by
      rw [hm'eq]
      field_simp
    have h1 : -(w - m) ^ 2 / (2 * vr) + (-(c * w ^ 2 / 2) + y * w) =
        -(w ^ 2) * (vr⁻¹ + c) / 2 + w * (m / vr + y) - m ^ 2 / (2 * vr) := by
      field_simp
      ring
    have h2 : (m' ^ 2 / (2 * v') - m ^ 2 / (2 * vr)) + -(w - m') ^ 2 / (2 * v') =
        -(w ^ 2) * v'⁻¹ / 2 + w * (m' / v') - m ^ 2 / (2 * vr) := by
      field_simp
      ring
    rw [h1, h2, hv'inv, hm'v]
  calc (Real.sqrt (2 * π * vr))⁻¹ * exp (-(w - m) ^ 2 / (2 * vr)) * exp (-(c * w ^ 2 / 2) + y * w)
      = (Real.sqrt (2 * π * vr))⁻¹ *
          exp (-(w - m) ^ 2 / (2 * vr) + (-(c * w ^ 2 / 2) + y * w)) := by
        rw [mul_assoc, ← Real.exp_add]
    _ = (Real.sqrt (2 * π * vr))⁻¹ *
        (exp (m' ^ 2 / (2 * v') - m ^ 2 / (2 * vr)) * exp (-(w - m') ^ 2 / (2 * v'))) := by
        rw [hexp, Real.exp_add]
    _ = Real.sqrt (v' / vr) * exp (m' ^ 2 / (2 * v') - m ^ 2 / (2 * vr)) *
        ((Real.sqrt (2 * π * v'))⁻¹ * exp (-(w - m') ^ 2 / (2 * v'))) := by
        rw [hinv]
        ring

/-! ### The measure identity and its consequences -/

theorem measurable_exp_quadratic (c y : ℝ) :
    Measurable fun w : ℝ => ENNReal.ofReal (exp (-(c * w ^ 2 / 2) + y * w)) := by
  fun_prop

/-- ★ **The quadratic tilt of a Gaussian is a multiple of a Gaussian.** -/
theorem gaussianReal_withDensity_quadratic (hv : v ≠ 0) (hc : 0 < (v : ℝ)⁻¹ + c) :
    (gaussianReal m v).withDensity (fun w => ENNReal.ofReal (exp (-(c * w ^ 2 / 2) + y * w))) =
      ENNReal.ofReal (tiltConst m v c y) • gaussianReal (tiltMeanG m v c y) (tiltVar v c) := by
  rw [gaussianReal_of_var_ne_zero _ hv, gaussianReal_of_var_ne_zero _ (tiltVar_ne_zero hc),
    ← withDensity_mul _ (measurable_gaussianPDF _ _) (measurable_exp_quadratic c y),
    ← withDensity_smul _ (measurable_gaussianPDF _ _)]
  congr 1
  funext w
  simp only [Pi.mul_apply, Pi.smul_apply, gaussianPDF, smul_eq_mul]
  rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _), gaussianPDFReal_mul_exp_quadratic hv hc,
    ENNReal.ofReal_mul (tiltConst_pos hv hc).le]

theorem integrable_exp_quadratic_gaussianReal (hv : v ≠ 0) (hc : 0 < (v : ℝ)⁻¹ + c) :
    Integrable (fun w => exp (-(c * w ^ 2 / 2) + y * w)) (gaussianReal m v) := by
  have hmeas : Measurable fun w : ℝ => exp (-(c * w ^ 2 / 2) + y * w) := by fun_prop
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have : ∫⁻ w, ‖exp (-(c * w ^ 2 / 2) + y * w)‖ₑ ∂gaussianReal m v =
      ((gaussianReal m v).withDensity fun w =>
        ENNReal.ofReal (exp (-(c * w ^ 2 / 2) + y * w))) univ := by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    refine lintegral_congr fun w => ?_
    rw [Real.enorm_eq_ofReal (exp_pos _).le]
  rw [this, gaussianReal_withDensity_quadratic hv hc]
  simp

/-- Tilted integrals are `Z` times integrals against the tilted Gaussian. -/
theorem integral_mul_exp_quadratic_gaussianReal (hv : v ≠ 0) (hc : 0 < (v : ℝ)⁻¹ + c)
    (g : ℝ → ℝ) :
    ∫ w, g w * exp (-(c * w ^ 2 / 2) + y * w) ∂gaussianReal m v =
      tiltConst m v c y * ∫ w, g w ∂gaussianReal (tiltMeanG m v c y) (tiltVar v c) := by
  have h := integral_withDensity_eq_integral_toReal_smul (μ := gaussianReal m v)
    (f := fun w => ENNReal.ofReal (exp (-(c * w ^ 2 / 2) + y * w))) (g := g)
    (measurable_exp_quadratic c y) (ae_of_all _ fun w => ENNReal.ofReal_lt_top)
  rw [gaussianReal_withDensity_quadratic hv hc, integral_smul_measure,
    ENNReal.toReal_ofReal (tiltConst_pos hv hc).le, smul_eq_mul] at h
  rw [h]
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  simp only [ENNReal.toReal_ofReal (exp_pos _).le, smul_eq_mul]
  ring

/-- The tilt integrates to `Z`. -/
theorem integral_exp_quadratic_gaussianReal (hv : v ≠ 0) (hc : 0 < (v : ℝ)⁻¹ + c) :
    ∫ w, exp (-(c * w ^ 2 / 2) + y * w) ∂gaussianReal m v = tiltConst m v c y := by
  have h := integral_mul_exp_quadratic_gaussianReal (m := m) (y := y) hv hc fun _ => (1 : ℝ)
  simp only [one_mul, integral_const, probReal_univ, smul_eq_mul, mul_one] at h
  exact h

/-! ### The quadratic observable of the normal-location model -/

/-- The negative excess loss `X(w) = −(w²/2 − x w)` of the normal-location model at the data
point `x`. -/
noncomputable def negLoss (x : ℝ) (w : ℝ) : ℝ := -(w ^ 2 / 2 - x * w)

theorem continuous_negLoss (x : ℝ) : Continuous (negLoss x) := by
  unfold negLoss
  fun_prop

theorem measurable_negLoss (x : ℝ) : Measurable (negLoss x) := (continuous_negLoss x).measurable

theorem exp_mul_negLoss (x t w : ℝ) :
    exp (t * negLoss x w) = exp (-(t * w ^ 2 / 2) + (t * x) * w) := by
  unfold negLoss
  congr 1
  ring

theorem integrable_exp_mul_negLoss (hv : v ≠ 0) {x t : ℝ} (ht : 0 < (v : ℝ)⁻¹ + t) :
    Integrable (fun w => exp (t * negLoss x w)) (gaussianReal m v) := by
  simp_rw [exp_mul_negLoss]
  exact integrable_exp_quadratic_gaussianReal hv ht

/-- `[0,1]` lies in the interior of the exponential-integrability set of the negative excess loss
under every nondegenerate Gaussian. -/
theorem Icc_subset_interior_integrableExpSet_negLoss (hv : v ≠ 0) (x : ℝ) :
    Icc (0 : ℝ) 1 ⊆ interior (integrableExpSet (negLoss x) (gaussianReal m v)) := by
  have hv' : (0 : ℝ) < v := by positivity
  have hopen : Ioo (-(v : ℝ)⁻¹) 2 ⊆ integrableExpSet (negLoss x) (gaussianReal m v) := by
    intro t ht
    have : 0 < (v : ℝ)⁻¹ + t := by linarith [ht.1]
    exact integrable_exp_mul_negLoss hv this
  refine subset_trans ?_ (interior_mono hopen)
  rw [isOpen_Ioo.interior_eq]
  intro t ht
  exact ⟨by linarith [ht.1, inv_pos.2 hv'], by linarith [ht.2]⟩

/-- The tilted mean of the negative excess loss is its mean under the tilted Gaussian. -/
theorem tiltMean_negLoss_eq (hv : v ≠ 0) {x t : ℝ} (ht : 0 < (v : ℝ)⁻¹ + t) :
    tiltMean (negLoss x) (gaussianReal m v) t =
      ∫ w, negLoss x w ∂gaussianReal (tiltMeanG m v t (t * x)) (tiltVar v t) := by
  unfold tiltMean tiltMoment
  simp_rw [exp_mul_negLoss, pow_one, pow_zero, one_mul]
  have hZ := (tiltConst_pos (m := m) (y := t * x) hv ht).ne'
  rw [integral_mul_exp_quadratic_gaussianReal hv ht (negLoss x),
    integral_exp_quadratic_gaussianReal hv ht, mul_div_cancel_left₀ _ hZ]

/-- The tilted absolute centred third moment of the negative excess loss is that of the tilted
Gaussian. -/
theorem tiltAbsThird_negLoss_eq (hv : v ≠ 0) {x t : ℝ} (ht : 0 < (v : ℝ)⁻¹ + t) :
    tiltAbsThird (negLoss x) (gaussianReal m v) t =
      ∫ w, |negLoss x w - ∫ w', negLoss x w' ∂gaussianReal (tiltMeanG m v t (t * x)) (tiltVar v t)|
        ^ 3 ∂gaussianReal (tiltMeanG m v t (t * x)) (tiltVar v t) := by
  unfold tiltAbsThird
  rw [tiltMean_negLoss_eq hv ht]
  unfold tiltMoment
  simp_rw [exp_mul_negLoss, pow_zero, one_mul]
  have hZ := (tiltConst_pos (m := m) (y := t * x) hv ht).ne'
  rw [integral_mul_exp_quadratic_gaussianReal hv ht (fun w => |negLoss x w -
      ∫ w', negLoss x w' ∂gaussianReal (tiltMeanG m v t (t * x)) (tiltVar v t)| ^ 3),
    integral_exp_quadratic_gaussianReal hv ht, mul_div_cancel_left₀ _ hZ]

end Grammar
