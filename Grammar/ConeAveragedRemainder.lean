/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.ConeLerayWeighted
import Grammar.BlowUpObservables

/-!
# The cone: the averaged posterior of `u₁²` to order `1/N`

DCXXIX gives `√N (E_a[Z_N[u₁²; a]/Z_N[1; a]] − ½) → 1/√π`.  Here the remainder is quantified
(★★★ `cone_averaged_remainder_bound`, `cone_averaged_remainder`):

  `|E_a[Z_N[u₁²; a]/Z_N[1; a]] − ½ − 1/(√π √N)| ≤ C₁/N`  for `N ≥ 1`,

`C₁ = ∫ B(a) γ(a) da` (`coneLipConst`), with the Lipschitz envelope
`B(a) = (s/c₀) e^{|a|} [2(a² + 1) + (|a| + 2/s)²]` (`coneLipEnvelope`): the scaled correction
`F_δ(a) = E_{δ,a}[t₊]` satisfies `|F_δ(a) − F_0(a)| ≤ δ B(a)` for `0 ≤ δ ≤ 1`
(★★ `coneScaledCorrection_sub_zero_le`), from `0 ≤ 1 − e^{−δ|t|} ≤ δ|t|` in the numerator and the
denominator, the Gaussian moments `∫ |t| e^{−t²/2 + at} ≤ e^{a²/2}(s|a| + 2)` and
`∫ t² e^{−t²/2 + at} ≤ 2s e^{a²/2}(a² + 1)`, and the denominator bound of DCXXIX.  The exact `1/N`
coefficient (a correlated absolute-Gaussian moment, `−(5/6 − √3/π)` by Astra's computation) stays a
derivation (Astra round-11 target 2).  Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

/-! ### The elementary inequality and the Gaussian moments -/

theorem one_sub_exp_neg_abs_bounds {δ : ℝ} (hδ : 0 ≤ δ) (t : ℝ) :
    0 ≤ 1 - Real.exp (-(δ * |t|)) ∧ 1 - Real.exp (-(δ * |t|)) ≤ δ * |t| := by
  have h1 := Real.add_one_le_exp (-(δ * |t|))
  have h2 : Real.exp (-(δ * |t|)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [abs_nonneg t])
  constructor <;> linarith

/-- `∫ |t| e^{−t²/2 + at} ≤ e^{a²/2}(√(2π)|a| + 2)`. -/
theorem integral_abs_gaussTilt_le (a : ℝ) :
    ∫ t : ℝ, |t| * Real.exp (-t ^ 2 / 2 + a * t) ≤
      Real.exp (a ^ 2 / 2) * (Real.sqrt (2 * Real.pi) * |a| + 2) := by
  have h := integral_posPart_coneTilt_le le_rfl a
  -- at `δ = 0` the tilt is the Gaussian tilt; but we bound `|t|` directly
  have hshift : ∫ t : ℝ, |t| * Real.exp (-(t - a) ^ 2 / 2) =
      ∫ s : ℝ, |s + a| * Real.exp (-s ^ 2 / 2) := by
    rw [← integral_add_right_eq_self (fun t : ℝ => |t| * Real.exp (-(t - a) ^ 2 / 2)) a]
    congr 1
    funext s
    congr 2
    ring
  have hI2 : Integrable (fun s : ℝ => (|s| + |a|) * Real.exp (-s ^ 2 / 2)) := by
    have h2 : Integrable (fun s : ℝ => |a| * Real.exp (-s ^ 2 / 2)) := by
      have := (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)).const_mul |a|
      refine this.congr (Eventually.of_forall fun s => ?_)
      simp only
      congr 2
      ring
    refine (integrable_abs_mul_exp_neg_half_sq.add h2).congr (Eventually.of_forall fun s => ?_)
    simp only [Pi.add_apply]
    ring
  have hI : Integrable (fun s : ℝ => |s + a| * Real.exp (-s ^ 2 / 2)) :=
    hI2.mono' (by fun_prop :
        Continuous fun s : ℝ => |s + a| * Real.exp (-s ^ 2 / 2)).aestronglyMeasurable
      (Eventually.of_forall fun s => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_right (abs_add_le s a) (Real.exp_pos _).le)
  have hgauss : ∫ s : ℝ, Real.exp (-s ^ 2 / 2) = Real.sqrt (2 * Real.pi) := by
    have e : ∀ s : ℝ, Real.exp (-s ^ 2 / 2) = Real.exp (-(1 / 2) * s ^ 2) := fun s => by
      congr 1; ring
    simp_rw [e]
    rw [integral_gaussian, show Real.pi / (1 / 2) = 2 * Real.pi by ring]
  calc ∫ t : ℝ, |t| * Real.exp (-t ^ 2 / 2 + a * t)
      = Real.exp (a ^ 2 / 2) * ∫ t, |t| * Real.exp (-(t - a) ^ 2 / 2) := by
        simp_rw [gaussTilt_eq]
        rw [← integral_const_mul]
        congr 1
        funext t
        ring
    _ = Real.exp (a ^ 2 / 2) * ∫ s, |s + a| * Real.exp (-s ^ 2 / 2) := by rw [hshift]
    _ ≤ Real.exp (a ^ 2 / 2) * ∫ s, (|s| + |a|) * Real.exp (-s ^ 2 / 2) := by
        refine mul_le_mul_of_nonneg_left (integral_mono hI hI2 fun s => ?_) (Real.exp_pos _).le
        exact mul_le_mul_of_nonneg_right (abs_add_le s a) (Real.exp_pos _).le
    _ = Real.exp (a ^ 2 / 2) * (Real.sqrt (2 * Real.pi) * |a| + 2) := by
        congr 1
        have e : (fun s : ℝ => (|s| + |a|) * Real.exp (-s ^ 2 / 2)) =
            fun s => |s| * Real.exp (-s ^ 2 / 2) + |a| * Real.exp (-s ^ 2 / 2) := by
          funext s; ring
        rw [e, integral_add integrable_abs_mul_exp_neg_half_sq
          ((integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)).const_mul |a| |>.congr
            (Eventually.of_forall fun s => by simp only; congr 2; ring)),
          integral_abs_mul_exp_neg_half_sq, integral_const_mul, hgauss]
        ring

theorem integrable_sq_gaussTilt (a : ℝ) :
    Integrable (fun t : ℝ => t ^ 2 * Real.exp (-t ^ 2 / 2 + a * t)) := by
  have h1 : Integrable (fun t : ℝ => (t - a) ^ 2 * Real.exp (-(t - a) ^ 2 / 2)) :=
    integrable_sq_mul_exp_neg_half_sq.comp_sub_right a
  have h2 : Integrable (fun t : ℝ => a ^ 2 * Real.exp (-(t - a) ^ 2 / 2)) := by
    have := ((integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)).comp_sub_right a).const_mul
      (a ^ 2)
    refine this.congr (Eventually.of_forall fun t => ?_)
    simp only
    congr 2
    ring
  have h12 : Integrable (fun t : ℝ => (t - a) ^ 2 * Real.exp (-(t - a) ^ 2 / 2) +
      a ^ 2 * Real.exp (-(t - a) ^ 2 / 2)) := h1.add h2
  refine (h12.const_mul (2 * Real.exp (a ^ 2 / 2))).mono'
    (by fun_prop :
      Continuous fun t : ℝ => t ^ 2 * Real.exp (-t ^ 2 / 2 + a * t)).aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), gaussTilt_eq]
  have hE : 0 ≤ Real.exp (a ^ 2 / 2) * Real.exp (-(t - a) ^ 2 / 2) := by positivity
  have hsq : t ^ 2 ≤ 2 * (t - a) ^ 2 + 2 * a ^ 2 := by nlinarith [sq_nonneg (t - 2 * a)]
  nlinarith [mul_le_mul_of_nonneg_right hsq hE]

/-- `∫ t² e^{−t²/2 + at} ≤ 2√(2π) e^{a²/2}(a² + 1)`. -/
theorem integral_sq_gaussTilt_le (a : ℝ) :
    ∫ t : ℝ, t ^ 2 * Real.exp (-t ^ 2 / 2 + a * t) ≤
      2 * Real.sqrt (2 * Real.pi) * Real.exp (a ^ 2 / 2) * (a ^ 2 + 1) := by
  have hsq : ∫ u : ℝ, u ^ 2 * Real.exp (-u ^ 2 / 2) = Real.sqrt (2 * Real.pi) := by
    have := integral_sq_exp_cond (c := 1) one_pos
    simpa using this
  have hgauss : ∫ u : ℝ, Real.exp (-u ^ 2 / 2) = Real.sqrt (2 * Real.pi) := by
    have e : ∀ u : ℝ, Real.exp (-u ^ 2 / 2) = Real.exp (-(1 / 2) * u ^ 2) := fun u => by
      congr 1; ring
    simp_rw [e]
    rw [integral_gaussian, show Real.pi / (1 / 2) = 2 * Real.pi by ring]
  have hI2 : Integrable (fun u : ℝ => (2 * u ^ 2 + 2 * a ^ 2) * Real.exp (-u ^ 2 / 2)) := by
    have h2 : Integrable (fun u : ℝ => 2 * a ^ 2 * Real.exp (-u ^ 2 / 2)) := by
      have := (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)).const_mul (2 * a ^ 2)
      refine this.congr (Eventually.of_forall fun u => ?_)
      simp only
      congr 2
      ring
    refine ((integrable_sq_mul_exp_neg_half_sq.const_mul 2).add h2).congr
      (Eventually.of_forall fun u => ?_)
    simp only [Pi.add_apply]
    ring
  have hI : Integrable (fun u : ℝ => (u + a) ^ 2 * Real.exp (-u ^ 2 / 2)) :=
    hI2.mono' (by fun_prop :
        Continuous fun u : ℝ => (u + a) ^ 2 * Real.exp (-u ^ 2 / 2)).aestronglyMeasurable
      (Eventually.of_forall fun u => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg (u - a)]) (Real.exp_pos _).le)
  calc ∫ t : ℝ, t ^ 2 * Real.exp (-t ^ 2 / 2 + a * t)
      = Real.exp (a ^ 2 / 2) * ∫ t, t ^ 2 * Real.exp (-(t - a) ^ 2 / 2) := by
        simp_rw [gaussTilt_eq]
        rw [← integral_const_mul]
        congr 1
        funext t
        ring
    _ = Real.exp (a ^ 2 / 2) * ∫ u, (u + a) ^ 2 * Real.exp (-u ^ 2 / 2) := by
        congr 1
        rw [← integral_add_right_eq_self (fun t : ℝ => t ^ 2 * Real.exp (-(t - a) ^ 2 / 2)) a]
        congr 1
        funext u
        congr 2
        ring
    _ ≤ Real.exp (a ^ 2 / 2) * ∫ u, (2 * u ^ 2 + 2 * a ^ 2) * Real.exp (-u ^ 2 / 2) := by
        refine mul_le_mul_of_nonneg_left (integral_mono hI hI2 fun u => ?_) (Real.exp_pos _).le
        exact mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg (u - a)]) (Real.exp_pos _).le
    _ = 2 * Real.sqrt (2 * Real.pi) * Real.exp (a ^ 2 / 2) * (a ^ 2 + 1) := by
        have e : (fun u : ℝ => (2 * u ^ 2 + 2 * a ^ 2) * Real.exp (-u ^ 2 / 2)) =
            fun u => 2 * (u ^ 2 * Real.exp (-u ^ 2 / 2)) + 2 * a ^ 2 * Real.exp (-u ^ 2 / 2) := by
          funext u; ring
        rw [e, integral_add (integrable_sq_mul_exp_neg_half_sq.const_mul 2)
          ((integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)).const_mul (2 * a ^ 2)
            |>.congr
            (Eventually.of_forall fun u => by simp only; congr 2; ring)),
          integral_const_mul, integral_const_mul, hsq, hgauss]
        ring

/-! ### The Lipschitz bound in `δ` -/

/-- `|P_0 − P_δ| ≤ δ ∫ t² w`, `P_δ = ∫ t₊ w_{δ,a}`. -/
theorem abs_integral_posPart_sub_le {δ : ℝ} (hδ : 0 ≤ δ) (a : ℝ) :
    |(∫ t, max t 0 * coneTilt 0 a t) - ∫ t, max t 0 * coneTilt δ a t| ≤
      δ * ∫ t, t ^ 2 * Real.exp (-t ^ 2 / 2 + a * t) := by
  rw [← integral_sub (integrable_posPart_coneTilt le_rfl a) (integrable_posPart_coneTilt hδ a),
    ← integral_const_mul]
  have hpt : ∀ t : ℝ, max t 0 * coneTilt 0 a t - max t 0 * coneTilt δ a t =
      max t 0 * (1 - Real.exp (-(δ * |t|))) * Real.exp (-t ^ 2 / 2 + a * t) := by
    intro t
    unfold coneTilt
    rw [show -t ^ 2 / 2 + a * t - δ * |t| = (-t ^ 2 / 2 + a * t) + -(δ * |t|) by ring, Real.exp_add]
    simp only [zero_mul, sub_zero]
    ring
  simp_rw [hpt]
  have hint : Integrable (fun t : ℝ => max t 0 * (1 - Real.exp (-(δ * |t|))) *
      Real.exp (-t ^ 2 / 2 + a * t)) := by
    have := (integrable_posPart_coneTilt le_rfl a).sub (integrable_posPart_coneTilt hδ a)
    refine this.congr (Eventually.of_forall fun t => ?_)
    simp only [Pi.sub_apply]
    exact hpt t
  rw [abs_of_nonneg (integral_nonneg fun t => by
    have := (one_sub_exp_neg_abs_bounds hδ t).1
    have := le_max_right t 0
    positivity)]
  refine integral_mono hint ((integrable_sq_gaussTilt a).const_mul δ) fun t => ?_
  have h := one_sub_exp_neg_abs_bounds hδ t
  have hm : max t 0 ≤ |t| := max_le (le_abs_self t) (abs_nonneg t)
  have hm0 : 0 ≤ max t 0 := le_max_right t 0
  have hE : 0 < Real.exp (-t ^ 2 / 2 + a * t) := Real.exp_pos _
  have hab : |t| * |t| = t ^ 2 := by rw [← sq, sq_abs]
  calc max t 0 * (1 - Real.exp (-(δ * |t|))) * Real.exp (-t ^ 2 / 2 + a * t)
      ≤ |t| * (δ * |t|) * Real.exp (-t ^ 2 / 2 + a * t) :=
        mul_le_mul_of_nonneg_right (mul_le_mul hm h.2 h.1 (abs_nonneg t)) hE.le
    _ = δ * (t ^ 2 * Real.exp (-t ^ 2 / 2 + a * t)) := by rw [← hab]; ring

/-- `|D_0 − D_δ| ≤ δ ∫ |t| w`, `D_δ = ∫ w_{δ,a}`. -/
theorem abs_integral_coneTilt_sub_le {δ : ℝ} (hδ : 0 ≤ δ) (a : ℝ) :
    |(∫ t, coneTilt 0 a t) - ∫ t, coneTilt δ a t| ≤
      δ * ∫ t, |t| * Real.exp (-t ^ 2 / 2 + a * t) := by
  rw [← integral_sub (integrable_coneTilt le_rfl a) (integrable_coneTilt hδ a),
    ← integral_const_mul]
  have hpt : ∀ t : ℝ, coneTilt 0 a t - coneTilt δ a t =
      (1 - Real.exp (-(δ * |t|))) * Real.exp (-t ^ 2 / 2 + a * t) := by
    intro t
    unfold coneTilt
    rw [show -t ^ 2 / 2 + a * t - δ * |t| = (-t ^ 2 / 2 + a * t) + -(δ * |t|) by ring, Real.exp_add]
    simp only [zero_mul, sub_zero]
    ring
  simp_rw [hpt]
  have hint : Integrable (fun t : ℝ => (1 - Real.exp (-(δ * |t|))) *
      Real.exp (-t ^ 2 / 2 + a * t)) := by
    have := (integrable_coneTilt le_rfl a).sub (integrable_coneTilt hδ a)
    refine this.congr (Eventually.of_forall fun t => ?_)
    simp only [Pi.sub_apply]
    exact hpt t
  rw [abs_of_nonneg (integral_nonneg fun t => by
    have := (one_sub_exp_neg_abs_bounds hδ t).1
    positivity)]
  refine integral_mono hint ((integrable_abs_gaussTilt a).const_mul δ) fun t => ?_
  have h := one_sub_exp_neg_abs_bounds hδ t
  have hE : 0 < Real.exp (-t ^ 2 / 2 + a * t) := Real.exp_pos _
  calc (1 - Real.exp (-(δ * |t|))) * Real.exp (-t ^ 2 / 2 + a * t)
      ≤ (δ * |t|) * Real.exp (-t ^ 2 / 2 + a * t) := mul_le_mul_of_nonneg_right h.2 hE.le
    _ = δ * (|t| * Real.exp (-t ^ 2 / 2 + a * t)) := by ring

/-- The Lipschitz envelope `B(a) = (s/c₀) e^{|a|} [2(a² + 1) + (|a| + 2/s)²]`. -/
noncomputable def coneLipEnvelope (a : ℝ) : ℝ :=
  Real.sqrt (2 * Real.pi) / coneC₀ * Real.exp |a| *
    (2 * (a ^ 2 + 1) + (|a| + 2 / Real.sqrt (2 * Real.pi)) ^ 2)

/-- ★★ **The Lipschitz bound**: `|F_δ(a) − F_0(a)| ≤ δ B(a)` for `0 ≤ δ ≤ 1`. -/
theorem coneScaledCorrection_sub_zero_le {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (a : ℝ) :
    |coneScaledCorrection δ a - coneScaledCorrection 0 a| ≤ δ * coneLipEnvelope a := by
  unfold coneScaledCorrection coneLipEnvelope
  set Pδ := ∫ t, max t 0 * coneTilt δ a t with hPδ
  set P₀ := ∫ t, max t 0 * coneTilt 0 a t with hP₀
  set Dδ := ∫ t, coneTilt δ a t with hDδ
  set D₀ := ∫ t, coneTilt 0 a t with hD₀
  set M₁ := ∫ t, |t| * Real.exp (-t ^ 2 / 2 + a * t) with hM₁
  set M₂ := ∫ t, t ^ 2 * Real.exp (-t ^ 2 / 2 + a * t) with hM₂
  set s := Real.sqrt (2 * Real.pi) with hs
  set E := Real.exp (a ^ 2 / 2) with hE
  have hs0 : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hE0 : 0 < E := Real.exp_pos _
  have hc0 := coneC₀_pos
  have hea : 0 < Real.exp |a| := Real.exp_pos _
  have hDδ0 : 0 < Dδ := integral_coneTilt_pos hδ0 a
  have hD₀0 : 0 < D₀ := integral_coneTilt_pos le_rfl a
  have hD₀eq : D₀ = s * E := by
    rw [hD₀]
    unfold coneTilt
    simp only [zero_mul, sub_zero]
    exact integral_gaussTilt a
  have hDδge : Real.exp (-|a|) * E * coneC₀ ≤ Dδ := integral_coneTilt_ge hδ0 hδ1 a
  have hP₀0 : 0 ≤ P₀ :=
    integral_nonneg fun t => mul_nonneg (le_max_right _ _) (coneTilt_pos _ a t).le
  have hP₀le : P₀ ≤ M₁ := by
    rw [hP₀, hM₁]
    refine integral_mono (integrable_posPart_coneTilt le_rfl a) (integrable_abs_gaussTilt a)
      fun t => ?_
    exact mul_le_mul (max_le (le_abs_self t) (abs_nonneg t)) (coneTilt_le le_rfl a t)
      (coneTilt_pos _ a t).le (abs_nonneg t)
  have hM₁le : M₁ ≤ E * (s * |a| + 2) := integral_abs_gaussTilt_le a
  have hM₂le : M₂ ≤ 2 * s * E * (a ^ 2 + 1) := integral_sq_gaussTilt_le a
  have hM₁0 : 0 ≤ M₁ := integral_nonneg fun t => by positivity
  have hM₂0 : 0 ≤ M₂ := integral_nonneg fun t => by positivity
  have hP := abs_integral_posPart_sub_le hδ0 a
  have hD := abs_integral_coneTilt_sub_le hδ0 a
  rw [← hPδ, ← hP₀, ← hM₂] at hP
  rw [← hDδ, ← hD₀, ← hM₁] at hD
  clear_value Pδ P₀ Dδ D₀ M₁ M₂ s E
  -- the difference of the two ratios
  have key : Pδ / Dδ - P₀ / D₀ = ((Pδ - P₀) * D₀ + P₀ * (D₀ - Dδ)) / (Dδ * D₀) := by
    field_simp
    ring
  rw [key, abs_div, abs_of_pos (mul_pos hDδ0 hD₀0)]
  have hnum : |(Pδ - P₀) * D₀ + P₀ * (D₀ - Dδ)| ≤ δ * (M₂ * D₀ + M₁ * M₁) := by
    calc |(Pδ - P₀) * D₀ + P₀ * (D₀ - Dδ)|
        ≤ |(Pδ - P₀) * D₀| + |P₀ * (D₀ - Dδ)| := abs_add_le _ _
      _ = |Pδ - P₀| * D₀ + P₀ * |D₀ - Dδ| := by
          rw [abs_mul, abs_mul, abs_of_pos hD₀0, abs_of_nonneg hP₀0]
      _ ≤ (δ * M₂) * D₀ + M₁ * (δ * M₁) := by
          have h1 : |Pδ - P₀| ≤ δ * M₂ := by rw [abs_sub_comm]; exact hP
          gcongr
      _ = δ * (M₂ * D₀ + M₁ * M₁) := by ring
  rw [div_le_iff₀ (mul_pos hDδ0 hD₀0)]
  refine hnum.trans ?_
  -- bound the bracket and the denominator
  have hbr : M₂ * D₀ + M₁ * M₁ ≤ E * E * (2 * s * s * (a ^ 2 + 1) + (s * |a| + 2) ^ 2) := by
    rw [hD₀eq]
    have h1 : M₂ * (s * E) ≤ 2 * s * E * (a ^ 2 + 1) * (s * E) :=
      mul_le_mul_of_nonneg_right hM₂le (by positivity)
    have h2 : M₁ * M₁ ≤ (E * (s * |a| + 2)) * (E * (s * |a| + 2)) :=
      mul_le_mul hM₁le hM₁le hM₁0 (by positivity)
    nlinarith
  have hden : Real.exp (-|a|) * E * coneC₀ * (s * E) ≤ Dδ * D₀ := by
    rw [hD₀eq]
    exact mul_le_mul_of_nonneg_right hDδge (by positivity)
  have hneg : Real.exp (-|a|) = (Real.exp |a|)⁻¹ := Real.exp_neg _
  calc δ * (M₂ * D₀ + M₁ * M₁)
      ≤ δ * (E * E * (2 * s * s * (a ^ 2 + 1) + (s * |a| + 2) ^ 2)) :=
        mul_le_mul_of_nonneg_left hbr hδ0
    _ = δ * (s / coneC₀ * Real.exp |a| * (2 * (a ^ 2 + 1) + (|a| + 2 / s) ^ 2)) *
          (Real.exp (-|a|) * E * coneC₀ * (s * E)) := by
        rw [hneg]
        field_simp
    _ ≤ δ * (s / coneC₀ * Real.exp |a| * (2 * (a ^ 2 + 1) + (|a| + 2 / s) ^ 2)) * (Dδ * D₀) :=
        mul_le_mul_of_nonneg_left hden (by positivity)

/-! ### The averaged remainder -/

theorem integrable_coneLipEnvelope :
    Integrable (fun a : ℝ => coneLipEnvelope a * gaussDensity a) := by
  have hK : Integrable (fun a : ℝ => Real.sqrt (2 * Real.pi) / coneC₀ * (20 * Real.exp 4) /
      Real.sqrt (2 * Real.pi) * Real.exp (-(1 / 4) * a ^ 2)) :=
    (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 4)).const_mul _
  refine hK.mono' ?_ (Eventually.of_forall fun a => ?_)
  · exact ((by unfold coneLipEnvelope; fun_prop : Continuous coneLipEnvelope).mul
      continuous_gaussDensity).aestronglyMeasurable
  · have hc := coneC₀_pos
    have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
    have hs2 : 2 ≤ Real.sqrt (2 * Real.pi) := by
      rw [Real.le_sqrt (by norm_num) (by positivity)]
      nlinarith [Real.pi_gt_three]
    have hea : 0 < Real.exp |a| := Real.exp_pos _
    have h0 : 0 ≤ coneLipEnvelope a * gaussDensity a := by
      unfold coneLipEnvelope
      have := gaussDensity_nonneg a
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    unfold coneLipEnvelope gaussDensity
    -- `2(a²+1) + (|a| + 2/s)² ≤ 4a² + 4 ≤ 20 e^{|a|}` and `e^{2|a|} e^{−a²/2} ≤ e⁴ e^{−a²/4}`
    have h1 : 2 * (a ^ 2 + 1) + (|a| + 2 / Real.sqrt (2 * Real.pi)) ^ 2 ≤ 20 * Real.exp |a| := by
      have hq : 2 / Real.sqrt (2 * Real.pi) ≤ 1 := by
        rw [div_le_one hs]; exact hs2
      have hq0 : 0 ≤ 2 / Real.sqrt (2 * Real.pi) := by positivity
      have hsq : |a| ^ 2 = a ^ 2 := sq_abs a
      have hexp : (1 + |a| / 2) ^ 2 ≤ Real.exp |a| := by
        have := Real.add_one_le_exp (|a| / 2)
        have h2 : Real.exp (|a| / 2) ^ 2 = Real.exp |a| := by
          rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
        rw [← h2]
        exact pow_le_pow_left₀ (by positivity) (by linarith) 2
      nlinarith [abs_nonneg a, mul_nonneg (abs_nonneg a) hq0]
    have h2 : Real.exp |a| * Real.exp |a| * Real.exp (-a ^ 2 / 2) ≤
        Real.exp 4 * Real.exp (-(1 / 4) * a ^ 2) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have : |a| ^ 2 = a ^ 2 := sq_abs a
      nlinarith [sq_nonneg (|a| - 4)]
    have hg : 0 < Real.exp (-a ^ 2 / 2) := Real.exp_pos _
    rw [show Real.sqrt (2 * Real.pi) / coneC₀ * Real.exp |a| *
        (2 * (a ^ 2 + 1) + (|a| + 2 / Real.sqrt (2 * Real.pi)) ^ 2) *
        (Real.exp (-a ^ 2 / 2) / Real.sqrt (2 * Real.pi)) =
        (Real.sqrt (2 * Real.pi) / coneC₀ / Real.sqrt (2 * Real.pi)) *
        ((2 * (a ^ 2 + 1) + (|a| + 2 / Real.sqrt (2 * Real.pi)) ^ 2) *
          (Real.exp |a| * Real.exp (-a ^ 2 / 2))) by ring]
    rw [show Real.sqrt (2 * Real.pi) / coneC₀ * (20 * Real.exp 4) / Real.sqrt (2 * Real.pi) *
        Real.exp (-(1 / 4) * a ^ 2) = (Real.sqrt (2 * Real.pi) / coneC₀ / Real.sqrt (2 * Real.pi)) *
        (20 * (Real.exp 4 * Real.exp (-(1 / 4) * a ^ 2))) by ring]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc (2 * (a ^ 2 + 1) + (|a| + 2 / Real.sqrt (2 * Real.pi)) ^ 2) *
          (Real.exp |a| * Real.exp (-a ^ 2 / 2))
        ≤ 20 * Real.exp |a| * (Real.exp |a| * Real.exp (-a ^ 2 / 2)) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = 20 * (Real.exp |a| * Real.exp |a| * Real.exp (-a ^ 2 / 2)) := by ring
      _ ≤ 20 * (Real.exp 4 * Real.exp (-(1 / 4) * a ^ 2)) := by gcongr

/-- `C₁ = ∫ B(a) γ(a) da`. -/
noncomputable def coneLipConst : ℝ := ∫ a, coneLipEnvelope a * gaussDensity a

/-- ★★★ **The averaged posterior to order `1/N`**: for `N ≥ 1`,
`|E_a[Z_N[u₁²; a]/Z_N[1; a]] − ½ − 1/(√π √N)| ≤ C₁/N`. -/
theorem cone_averaged_remainder_bound {N : ℝ} (hN : 1 ≤ N) :
    |(∫ a, coneNumSq N a / coneDen N a * gaussDensity a) - 1 / 2 -
      1 / (Real.sqrt Real.pi * Real.sqrt N)| ≤ coneLipConst / N := by
  have hN0 : 0 < N := by linarith
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have hδ0 : 0 ≤ 1 / Real.sqrt N := by positivity
  have hδ1 : 1 / Real.sqrt N ≤ 1 := by
    rw [div_le_one hs]; exact Real.one_le_sqrt.2 hN
  have hint : ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 →
      Integrable (fun a => coneScaledCorrection δ a * gaussDensity a) := fun δ h0 h1 =>
    integrable_coneEnvelope.mono' ((measurable_coneScaledCorrection _).mul
      continuous_gaussDensity.measurable).aestronglyMeasurable
      (Eventually.of_forall fun a => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (coneScaledCorrection_nonneg h0 a)
          (gaussDensity_nonneg a))]
        exact mul_le_mul_of_nonneg_right (coneScaledCorrection_le h0 h1 a) (gaussDensity_nonneg a))
  have hγ : ∫ a, gaussDensity a = 1 := by
    have := gaussLaplace2_zero
    rw [gaussLaplace2_eq_density_integral le_rfl] at this
    simpa using this
  simp_rw [cone_posterior_ratio_eq hN0]
  have e : ∀ a : ℝ, (1 / 2 + 1 / Real.sqrt N * coneScaledCorrection (1 / Real.sqrt N) a) *
      gaussDensity a = 1 / 2 * gaussDensity a +
        1 / Real.sqrt N * (coneScaledCorrection (1 / Real.sqrt N) a * gaussDensity a) := by
    intro a; ring
  simp_rw [e]
  rw [integral_add (integrable_gaussDensity.const_mul _) ((hint _ hδ0 hδ1).const_mul _),
    integral_const_mul, integral_const_mul, hγ]
  have hzero := integral_coneScaledCorrection_zero
  have hdiff : (∫ a, coneScaledCorrection (1 / Real.sqrt N) a * gaussDensity a) -
      ∫ a, coneScaledCorrection 0 a * gaussDensity a =
      ∫ a, (coneScaledCorrection (1 / Real.sqrt N) a - coneScaledCorrection 0 a) *
        gaussDensity a := by
    rw [← integral_sub (hint _ hδ0 hδ1) (hint 0 le_rfl zero_le_one)]
    congr 1
    funext a
    ring
  have habs : Integrable (fun a => |(coneScaledCorrection (1 / Real.sqrt N) a -
      coneScaledCorrection 0 a) * gaussDensity a|) := by
    have := ((hint _ hδ0 hδ1).sub (hint 0 le_rfl zero_le_one)).abs
    refine this.congr (Eventually.of_forall fun a => ?_)
    simp only [Pi.sub_apply]
    congr 1
    ring
  have hbound : |∫ a, (coneScaledCorrection (1 / Real.sqrt N) a - coneScaledCorrection 0 a) *
      gaussDensity a| ≤ 1 / Real.sqrt N * coneLipConst := by
    calc |∫ a, (coneScaledCorrection (1 / Real.sqrt N) a - coneScaledCorrection 0 a) *
          gaussDensity a|
        ≤ ∫ a, |(coneScaledCorrection (1 / Real.sqrt N) a - coneScaledCorrection 0 a) *
            gaussDensity a| := abs_integral_le_integral_abs
      _ ≤ ∫ a, 1 / Real.sqrt N * (coneLipEnvelope a * gaussDensity a) := by
          refine integral_mono habs (integrable_coneLipEnvelope.const_mul _) fun a => ?_
          rw [abs_mul, abs_of_nonneg (gaussDensity_nonneg a), ← mul_assoc]
          exact mul_le_mul_of_nonneg_right (coneScaledCorrection_sub_zero_le hδ0 hδ1 a)
            (gaussDensity_nonneg a)
      _ = 1 / Real.sqrt N * coneLipConst := by rw [integral_const_mul]; rfl
  have hNN : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN0.le
  calc |1 / 2 * 1 + 1 / Real.sqrt N * (∫ a, coneScaledCorrection (1 / Real.sqrt N) a *
        gaussDensity a) - 1 / 2 - 1 / (Real.sqrt Real.pi * Real.sqrt N)|
      = |1 / Real.sqrt N * ((∫ a, coneScaledCorrection (1 / Real.sqrt N) a * gaussDensity a) -
          ∫ a, coneScaledCorrection 0 a * gaussDensity a)| := by
        congr 1
        rw [hzero]
        field_simp
        ring
    _ = 1 / Real.sqrt N * |∫ a, (coneScaledCorrection (1 / Real.sqrt N) a -
          coneScaledCorrection 0 a) * gaussDensity a| := by
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / Real.sqrt N), hdiff]
    _ ≤ 1 / Real.sqrt N * (1 / Real.sqrt N * coneLipConst) :=
        mul_le_mul_of_nonneg_left hbound hδ0
    _ = coneLipConst / (Real.sqrt N * Real.sqrt N) := by field_simp
    _ = coneLipConst / N := by rw [hNN]

/-- ★★★ `E_a[Z_N[u₁²; a]/Z_N[1; a]] = ½ + 1/(√π √N) + O(1/N)`. -/
theorem cone_averaged_remainder :
    (fun N : ℝ => (∫ a, coneNumSq N a / coneDen N a * gaussDensity a) - 1 / 2 -
      1 / (Real.sqrt Real.pi * Real.sqrt N)) =O[atTop] fun N => 1 / N := by
  refine Asymptotics.IsBigO.of_bound coneLipConst ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with N hN
  have hN0 : 0 < N := by linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 1 / N)]
  refine (cone_averaged_remainder_bound hN).trans (le_of_eq ?_)
  ring

end Grammar
