/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.ConeSecondCoefficient

/-!
# The cone: the symmetric form of the second coefficient

`c₂ = ∫ G γ` with `G(a) = −Cov_{T∼N(a,1)}(T₊, |T|)` (DCXXXIX).  Reflecting `t ↦ −t` in the tilt
`w_{0,a}(t) = e^{−t²/2 + at}` exchanges `a ↔ −a` and `t₊ ↔ t₋`, so the positive-part moments of `a`
and `−a` add up to the absolute and second moments: `P₀(a) + P₀(−a) = M₁(a)`,
`Q₁(a) + Q₁(−a) = (a² + 1) D₀(a)`.  Hence the pointwise reflection identity

  `G(a) + G(−a) = −(a² + 1 − m(a)²)`,   `m(a) = E_a|T| = M₁/D₀`   (★★ `coneCorrectionDeriv_add_neg`)

and, integrating against the even weight `γ`,

  `c₂ = −½ ∫ (a² + 1 − m(a)²) γ(a) da`   (★★★ `coneSecondCoeff_eq_symmetric`).

The exact value `c₂ = −5/6 + √3/π` (through `m(a) = a b(a) + 2γ(a)` and three Gaussian
integrations by parts) is the next unit (examples_slop §3; Astra round-13 target 1).
Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

@[simp] theorem coneTilt_zero (a t : ℝ) : coneTilt 0 a t = Real.exp (-t ^ 2 / 2 + a * t) := by
  unfold coneTilt; simp

/-! ### The exact second tilted moment -/

/-- `∫ u e^{−u²/2} du = 0` (odd integrand). -/
theorem integral_mul_exp_neg_half_sq_eq_zero : ∫ u : ℝ, u * Real.exp (-u ^ 2 / 2) = 0 := by
  have h := integral_neg_eq_self (fun u : ℝ => u * Real.exp (-u ^ 2 / 2)) volume
  simp only [neg_sq, neg_mul] at h
  rw [integral_neg] at h
  linarith

theorem integrable_mul_exp_neg_half_sq : Integrable (fun u : ℝ => u * Real.exp (-u ^ 2 / 2)) := by
  refine integrable_abs_mul_exp_neg_half_sq.mono'
    (by fun_prop : Continuous fun u : ℝ => u * Real.exp (-u ^ 2 / 2)).aestronglyMeasurable
    (Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]

/-- `∫ t² e^{−t²/2 + at} dt = (a² + 1) √(2π) e^{a²/2}`. -/
theorem integral_sq_gaussTilt (a : ℝ) :
    ∫ t : ℝ, t ^ 2 * Real.exp (-t ^ 2 / 2 + a * t) =
      (a ^ 2 + 1) * Real.sqrt (2 * Real.pi) * Real.exp (a ^ 2 / 2) := by
  have hgauss : ∫ u : ℝ, Real.exp (-u ^ 2 / 2) = Real.sqrt (2 * Real.pi) := by
    have e : ∀ u : ℝ, Real.exp (-u ^ 2 / 2) = Real.exp (-(1 / 2) * u ^ 2) := fun u => by
      congr 1; ring
    simp_rw [e]
    rw [integral_gaussian, show Real.pi / (1 / 2) = 2 * Real.pi by ring]
  have hsq : ∫ u : ℝ, u ^ 2 * Real.exp (-u ^ 2 / 2) = Real.sqrt (2 * Real.pi) := by
    have := integral_sq_exp_cond (c := 1) one_pos
    simpa using this
  have h0 : Integrable (fun u : ℝ => Real.exp (-u ^ 2 / 2)) := by
    have := integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)
    refine this.congr (Eventually.of_forall fun u => ?_)
    simp only
    congr 1
    ring
  have e1 : (fun t : ℝ => t ^ 2 * Real.exp (-t ^ 2 / 2 + a * t)) =
      fun t => Real.exp (a ^ 2 / 2) * (t ^ 2 * Real.exp (-(t - a) ^ 2 / 2)) := by
    funext t; rw [gaussTilt_eq]; ring
  have hshift : ∫ t : ℝ, t ^ 2 * Real.exp (-(t - a) ^ 2 / 2) =
      ∫ u : ℝ, (u + a) ^ 2 * Real.exp (-u ^ 2 / 2) := by
    rw [← integral_sub_right_eq_self (fun u : ℝ => (u + a) ^ 2 * Real.exp (-u ^ 2 / 2)) a]
    congr 1
    funext t
    simp only [sub_add_cancel]
  rw [e1, integral_const_mul, hshift]
  have e3 : (fun u : ℝ => (u + a) ^ 2 * Real.exp (-u ^ 2 / 2)) =
      fun u => u ^ 2 * Real.exp (-u ^ 2 / 2) + (2 * a) * (u * Real.exp (-u ^ 2 / 2)) +
        a ^ 2 * Real.exp (-u ^ 2 / 2) := by
    funext u; ring
  have h12 : Integrable (fun u : ℝ => u ^ 2 * Real.exp (-u ^ 2 / 2) +
      (2 * a) * (u * Real.exp (-u ^ 2 / 2))) :=
    integrable_sq_mul_exp_neg_half_sq.add (integrable_mul_exp_neg_half_sq.const_mul _)
  rw [e3, integral_add h12 (h0.const_mul _), integral_add integrable_sq_mul_exp_neg_half_sq
    (integrable_mul_exp_neg_half_sq.const_mul _), integral_const_mul, integral_const_mul, hsq,
    integral_mul_exp_neg_half_sq_eq_zero, hgauss]
  ring

/-! ### Reflection `t ↦ −t`, `a ↦ −a` -/

theorem posPart_coneTilt_neg (a : ℝ) :
    ∫ t, max t 0 * coneTilt 0 (-a) t = ∫ t, max (-t) 0 * coneTilt 0 a t := by
  rw [← integral_neg_eq_self (fun t => max t 0 * coneTilt 0 (-a) t) volume]
  congr 1
  funext t
  simp only [coneTilt_zero, neg_sq, neg_mul_neg]

theorem posSq_coneTilt_neg (a : ℝ) :
    ∫ t, max t 0 * |t| * coneTilt 0 (-a) t = ∫ t, max (-t) 0 * |t| * coneTilt 0 a t := by
  rw [← integral_neg_eq_self (fun t => max t 0 * |t| * coneTilt 0 (-a) t) volume]
  congr 1
  funext t
  simp only [coneTilt_zero, neg_sq, neg_mul_neg, abs_neg]

theorem abs_gaussTilt_neg (a : ℝ) :
    ∫ t, |t| * Real.exp (-t ^ 2 / 2 + -a * t) = ∫ t, |t| * Real.exp (-t ^ 2 / 2 + a * t) := by
  rw [← integral_neg_eq_self (fun t => |t| * Real.exp (-t ^ 2 / 2 + -a * t)) volume]
  congr 1
  funext t
  simp only [neg_sq, neg_mul_neg, abs_neg]

theorem mass_coneTilt_neg (a : ℝ) : ∫ t, coneTilt 0 (-a) t = ∫ t, coneTilt 0 a t := by
  rw [← integral_neg_eq_self (fun t => coneTilt 0 (-a) t) volume]
  congr 1
  funext t
  simp only [coneTilt_zero, neg_sq, neg_mul_neg]

theorem integrable_negPart_coneTilt (a : ℝ) :
    Integrable (fun t : ℝ => max (-t) 0 * coneTilt 0 a t) := by
  have := (integrable_posPart_coneTilt le_rfl (-a)).comp_neg
  refine this.congr (Eventually.of_forall fun t => ?_)
  simp only [coneTilt_zero, neg_sq, neg_mul_neg]

theorem integrable_negSq_coneTilt (a : ℝ) :
    Integrable (fun t : ℝ => max (-t) 0 * |t| * coneTilt 0 a t) := by
  refine (integrable_sq_gaussTilt a).mono' (by
    have := continuous_coneTilt 0 a
    fun_prop : Continuous fun t : ℝ => max (-t) 0 * |t| * coneTilt 0 a t).aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by
    have := le_max_right (-t) 0; have := coneTilt_pos 0 a t; positivity), coneTilt_zero]
  have hm : max (-t) 0 ≤ |t| := max_le (neg_le_abs t) (abs_nonneg t)
  have hab : |t| * |t| = t ^ 2 := by rw [← sq, sq_abs]
  calc max (-t) 0 * |t| * Real.exp (-t ^ 2 / 2 + a * t)
      ≤ |t| * |t| * Real.exp (-t ^ 2 / 2 + a * t) := by gcongr
    _ = t ^ 2 * Real.exp (-t ^ 2 / 2 + a * t) := by rw [hab]

/-- `P₀(a) + P₀(−a) = M₁(a)`. -/
theorem posPart_add_negPart_coneTilt (a : ℝ) :
    (∫ t, max t 0 * coneTilt 0 a t) + ∫ t, max (-t) 0 * coneTilt 0 a t =
      ∫ t, |t| * Real.exp (-t ^ 2 / 2 + a * t) := by
  rw [← integral_add (integrable_posPart_coneTilt le_rfl a) (integrable_negPart_coneTilt a)]
  congr 1
  funext t
  rw [coneTilt_zero, ← add_mul, max_zero_add_max_neg_zero_eq_abs_self]

/-- `Q₁(a) + Q₁(−a) = ∫ t² w_{0,a}`. -/
theorem posSq_add_negSq_coneTilt (a : ℝ) :
    (∫ t, max t 0 * |t| * coneTilt 0 a t) + ∫ t, max (-t) 0 * |t| * coneTilt 0 a t =
      ∫ t, t ^ 2 * Real.exp (-t ^ 2 / 2 + a * t) := by
  have hQ : Integrable (fun t : ℝ => max t 0 * |t| * coneTilt 0 a t) := by
    refine (integrable_sq_gaussTilt a).mono' (by
      have := continuous_coneTilt 0 a
      fun_prop : Continuous fun t : ℝ => max t 0 * |t| * coneTilt 0 a t).aestronglyMeasurable
      (Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by
      have := le_max_right t 0; have := coneTilt_pos 0 a t; positivity), coneTilt_zero]
    have hm : max t 0 ≤ |t| := max_le (le_abs_self t) (abs_nonneg t)
    have hab : |t| * |t| = t ^ 2 := by rw [← sq, sq_abs]
    calc max t 0 * |t| * Real.exp (-t ^ 2 / 2 + a * t)
        ≤ |t| * |t| * Real.exp (-t ^ 2 / 2 + a * t) := by gcongr
      _ = t ^ 2 * Real.exp (-t ^ 2 / 2 + a * t) := by rw [hab]
  rw [← integral_add hQ (integrable_negSq_coneTilt a)]
  congr 1
  funext t
  rw [coneTilt_zero, show max t 0 * |t| * Real.exp (-t ^ 2 / 2 + a * t) +
      max (-t) 0 * |t| * Real.exp (-t ^ 2 / 2 + a * t) =
      (max t 0 + max (-t) 0) * |t| * Real.exp (-t ^ 2 / 2 + a * t) by ring,
    max_zero_add_max_neg_zero_eq_abs_self, ← sq, sq_abs]

/-! ### The reflection identity and the symmetric form -/

/-- `m(a) = E_a|T| = ∫ |t| w_{0,a} / ∫ w_{0,a}`. -/
noncomputable def coneAbsMean (a : ℝ) : ℝ :=
  (∫ t, |t| * coneTilt 0 a t) / ∫ t, coneTilt 0 a t

/-- ★★ **The reflection identity** `G(a) + G(−a) = −(a² + 1 − m(a)²)`. -/
theorem coneCorrectionDeriv_add_neg (a : ℝ) :
    coneCorrectionDeriv a + coneCorrectionDeriv (-a) = -(a ^ 2 + 1 - coneAbsMean a ^ 2) := by
  unfold coneCorrectionDeriv coneAbsMean
  rw [posPart_coneTilt_neg, posSq_coneTilt_neg, abs_gaussTilt_neg, mass_coneTilt_neg]
  have hM : ∫ t, |t| * coneTilt 0 a t = ∫ t, |t| * Real.exp (-t ^ 2 / 2 + a * t) := by
    simp only [coneTilt_zero]
  rw [hM]
  have hD₀ : ∫ t, coneTilt 0 a t = Real.sqrt (2 * Real.pi) * Real.exp (a ^ 2 / 2) := by
    simp only [coneTilt_zero]
    exact integral_gaussTilt a
  have hP := posPart_add_negPart_coneTilt a
  have hQ := posSq_add_negSq_coneTilt a
  rw [integral_sq_gaussTilt] at hQ
  set P₀ := ∫ t, max t 0 * coneTilt 0 a t with hP₀
  set Pm := ∫ t, max (-t) 0 * coneTilt 0 a t with hPm
  set Q₁ := ∫ t, max t 0 * |t| * coneTilt 0 a t with hQ₁
  set Qm := ∫ t, max (-t) 0 * |t| * coneTilt 0 a t with hQm
  set M₁ := ∫ t, |t| * Real.exp (-t ^ 2 / 2 + a * t) with hM₁
  set D₀ := ∫ t, coneTilt 0 a t with hD₀'
  have hD₀0 : 0 < D₀ := integral_coneTilt_pos le_rfl a
  clear_value P₀ Pm Q₁ Qm M₁ D₀
  have hPm' : Pm = M₁ - P₀ := by linarith
  have hQm' : Qm = (a ^ 2 + 1) * D₀ - Q₁ := by rw [hD₀]; linarith
  rw [hPm', hQm']
  field_simp
  ring

theorem gaussDensity_neg (a : ℝ) : gaussDensity (-a) = gaussDensity a := by
  unfold gaussDensity; rw [neg_sq]

theorem integrable_coneCorrectionDeriv_neg :
    Integrable (fun a : ℝ => coneCorrectionDeriv (-a) * gaussDensity a) := by
  have := integrable_coneCorrectionDeriv.comp_neg
  refine this.congr (Eventually.of_forall fun a => ?_)
  simp only [gaussDensity_neg]

/-- ★★★ **The symmetric form**: `c₂ = −½ ∫ (a² + 1 − m(a)²) γ(a) da`. -/
theorem coneSecondCoeff_eq_symmetric :
    coneSecondCoeff = -(1 / 2 : ℝ) * ∫ a, (a ^ 2 + 1 - coneAbsMean a ^ 2) * gaussDensity a := by
  unfold coneSecondCoeff
  have hrefl : ∫ a, coneCorrectionDeriv a * gaussDensity a =
      ∫ a, coneCorrectionDeriv (-a) * gaussDensity a := by
    rw [← integral_neg_eq_self (fun a => coneCorrectionDeriv a * gaussDensity a) volume]
    congr 1
    funext a
    rw [gaussDensity_neg]
  have hsum : (∫ a, coneCorrectionDeriv a * gaussDensity a) +
      ∫ a, coneCorrectionDeriv (-a) * gaussDensity a =
      -∫ a, (a ^ 2 + 1 - coneAbsMean a ^ 2) * gaussDensity a := by
    rw [← integral_add integrable_coneCorrectionDeriv integrable_coneCorrectionDeriv_neg,
      ← integral_neg]
    congr 1
    funext a
    rw [← add_mul, coneCorrectionDeriv_add_neg]
    ring
  linarith

end Grammar
