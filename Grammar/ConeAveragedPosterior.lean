/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.ConeGaussian
import Grammar.GaussianDepthThree
import Grammar.MonomialFamilyLogFree

/-!
# The cone: the averaged posterior of `u₁²` and its first correction

With the Leray densities `L_φ = 2π² e^{−|v|}` and `L_{u₁²φ} = π² e^{−|v|}(1 + v + |v|)` of the cone
model under the Gaussian prior (examples_slop §3), the frozen posterior mean of `u₁²` at the field
`a` is, in the standardised variable `t = √N v` and with `δ = N^{−1/2}`,

  `Z_N[u₁²; a]/Z_N[1; a] = ½ + δ · E_{δ,a}[t₊]`,  `E_{δ,a}[t₊] = ∫ t₊ w_{δ,a} / ∫ w_{δ,a}`,
  `w_{δ,a}(t) = e^{−t²/2 + a t − δ|t|}`

(`coneScaledCorrection`, ★★ `cone_posterior_ratio_eq`).  The correction is dominated uniformly in
`0 ≤ δ ≤ 1` by the Gaussian-integrable envelope `(√(2π)|a| + 2) e^{|a|}/c₀`,
`c₀ = ∫ e^{−|s| − s²/2} ds` (★★ `coneScaledCorrection_le`: the numerator is at most
`e^{a²/2}(√(2π)|a| + 2)` and the denominator at least `e^{−|a|} e^{a²/2} c₀`, from
`|t| ≤ |a| + |t − a|`), so the average of the RATIOS over the sample field `a ∼ N(0,1)` converges by
dominated convergence, and its limit is the Gaussian double integral `E[(a + G)₊] = 1/√π`
(★★★ `cone_averaged_correction`):

  `√N (E_a[Z_N[u₁²; a]/Z_N[1; a]] − ½) → 1/√π`.

This is the domination argument the note does not give (Astra round-10 target 2: the average of
ratios, not the ratio of averages, which is the prior expectation).  The denominator is
`cone_evidence_eq`; the identification of the numerator's Leray density with the four-dimensional
integral `∫ u₁² e^{−Nq²/2 + √N q a} φ` is `ConeLerayWeighted` (`coneNumSq_eq`).
Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

/-! ### The tilted weight -/

/-- The tilted weight `w_{δ,a}(t) = e^{−t²/2 + a t − δ|t|}`. -/
noncomputable def coneTilt (δ a t : ℝ) : ℝ := Real.exp (-t ^ 2 / 2 + a * t - δ * |t|)

theorem coneTilt_pos (δ a t : ℝ) : 0 < coneTilt δ a t := Real.exp_pos _

theorem continuous_coneTilt (δ a : ℝ) : Continuous (coneTilt δ a) := by
  unfold coneTilt; fun_prop

/-- The Gaussian tilt completes the square: `e^{−t²/2 + at} = e^{a²/2} e^{−(t−a)²/2}`. -/
theorem gaussTilt_eq (a t : ℝ) :
    Real.exp (-t ^ 2 / 2 + a * t) = Real.exp (a ^ 2 / 2) * Real.exp (-(t - a) ^ 2 / 2) := by
  rw [← Real.exp_add]; congr 1; ring

theorem integrable_gaussTilt (a : ℝ) :
    Integrable (fun t : ℝ => Real.exp (-t ^ 2 / 2 + a * t)) := by
  have h : Integrable (fun t : ℝ => Real.exp (-(1 / 2) * (t - a) ^ 2)) :=
    (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)).comp_sub_right a
  refine (h.const_mul (Real.exp (a ^ 2 / 2))).congr (Eventually.of_forall fun t => ?_)
  simp only
  rw [gaussTilt_eq]
  congr 2
  ring

/-- `∫ e^{−t²/2 + at} dt = √(2π) e^{a²/2}`. -/
theorem integral_gaussTilt (a : ℝ) :
    ∫ t : ℝ, Real.exp (-t ^ 2 / 2 + a * t) = Real.sqrt (2 * Real.pi) * Real.exp (a ^ 2 / 2) := by
  simp_rw [gaussTilt_eq]
  rw [integral_const_mul]
  have e : ∀ t : ℝ, Real.exp (-(t - a) ^ 2 / 2) = Real.exp (-(1 / 2) * (t - a) ^ 2) := fun t => by
    congr 1; ring
  simp_rw [e]
  rw [integral_sub_right_eq_self (fun t : ℝ => Real.exp (-(1 / 2) * t ^ 2)) a, integral_gaussian,
    show Real.pi / (1 / 2) = 2 * Real.pi by ring]
  ring

/-- `∫ |t| e^{−t²/2} dt = 2`. -/
theorem integral_abs_mul_exp_neg_half_sq : ∫ t : ℝ, |t| * Real.exp (-t ^ 2 / 2) = 2 := by
  have h := integral_comp_abs (f := fun t : ℝ => t * Real.exp (-t ^ 2 / 2))
  simp only [sq_abs] at h
  rw [h, integral_mul_exp_neg_half_sq_Ioi]
  norm_num

theorem integrable_abs_mul_exp_neg_half_sq :
    Integrable (fun t : ℝ => |t| * Real.exp (-t ^ 2 / 2)) := by
  have h := (integrable_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)).abs
  refine h.congr (Eventually.of_forall fun t => ?_)
  simp only
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  congr 2
  ring

theorem integrable_abs_gaussTilt (a : ℝ) :
    Integrable (fun t : ℝ => |t| * Real.exp (-t ^ 2 / 2 + a * t)) := by
  have h1 : Integrable (fun t : ℝ => |t - a| * Real.exp (-(t - a) ^ 2 / 2)) :=
    integrable_abs_mul_exp_neg_half_sq.comp_sub_right a
  have h2 : Integrable (fun t : ℝ => |a| * Real.exp (-(t - a) ^ 2 / 2)) := by
    have := ((integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)).comp_sub_right a).const_mul
      |a|
    refine this.congr (Eventually.of_forall fun t => ?_)
    simp only
    congr 2
    ring
  have h12 : Integrable (fun t : ℝ => |t - a| * Real.exp (-(t - a) ^ 2 / 2) +
      |a| * Real.exp (-(t - a) ^ 2 / 2)) := h1.add h2
  refine (h12.const_mul (Real.exp (a ^ 2 / 2))).mono' ?_ (Eventually.of_forall fun t => ?_)
  · exact (by fun_prop :
      Continuous fun t : ℝ => |t| * Real.exp (-t ^ 2 / 2 + a * t)).aestronglyMeasurable
  · have key : |t| * Real.exp (-t ^ 2 / 2 + a * t) ≤ Real.exp (a ^ 2 / 2) *
        (|t - a| * Real.exp (-(t - a) ^ 2 / 2) + |a| * Real.exp (-(t - a) ^ 2 / 2)) := by
      rw [gaussTilt_eq]
      have h : |t| ≤ |t - a| + |a| := by
        calc |t| = |(t - a) + a| := by ring_nf
          _ ≤ |t - a| + |a| := abs_add_le _ _
      have hE : 0 ≤ Real.exp (a ^ 2 / 2) * Real.exp (-(t - a) ^ 2 / 2) := by positivity
      nlinarith [mul_le_mul_of_nonneg_right h hE]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact key

/-! ### Integrability and positivity of the tilted integrals -/

theorem coneTilt_le {δ : ℝ} (hδ : 0 ≤ δ) (a t : ℝ) :
    coneTilt δ a t ≤ Real.exp (-t ^ 2 / 2 + a * t) := by
  unfold coneTilt
  exact Real.exp_le_exp.2 (by nlinarith [abs_nonneg t])

theorem integrable_coneTilt {δ : ℝ} (hδ : 0 ≤ δ) (a : ℝ) : Integrable (coneTilt δ a) :=
  (integrable_gaussTilt a).mono (continuous_coneTilt δ a).aestronglyMeasurable
    (Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (coneTilt_pos δ a t),
        abs_of_pos (Real.exp_pos _)]
      exact coneTilt_le hδ a t)

theorem integrable_posPart_coneTilt {δ : ℝ} (hδ : 0 ≤ δ) (a : ℝ) :
    Integrable (fun t : ℝ => max t 0 * coneTilt δ a t) :=
  (integrable_abs_gaussTilt a).mono
    ((continuous_id.max continuous_const).mul (continuous_coneTilt δ a)).aestronglyMeasurable
    (Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (le_max_right _ _) (coneTilt_pos δ a t).le),
        abs_of_nonneg (by positivity)]
      exact mul_le_mul (max_le (le_abs_self t) (abs_nonneg t)) (coneTilt_le hδ a t)
        (coneTilt_pos δ a t).le (abs_nonneg t))

theorem integral_coneTilt_pos {δ : ℝ} (hδ : 0 ≤ δ) (a : ℝ) : 0 < ∫ t, coneTilt δ a t := by
  rw [integral_pos_iff_support_of_nonneg (fun t => (coneTilt_pos δ a t).le)
    (integrable_coneTilt hδ a), Function.support_eq_univ (fun t => (coneTilt_pos δ a t).ne')]
  simp

/-- `E_{δ,a}[t₊] = ∫ t₊ w_{δ,a} / ∫ w_{δ,a}`: the scaled first correction at the field `a`. -/
noncomputable def coneScaledCorrection (δ a : ℝ) : ℝ :=
  (∫ t, max t 0 * coneTilt δ a t) / ∫ t, coneTilt δ a t

theorem coneScaledCorrection_nonneg {δ : ℝ} (hδ : 0 ≤ δ) (a : ℝ) :
    0 ≤ coneScaledCorrection δ a :=
  div_nonneg (integral_nonneg fun t => mul_nonneg (le_max_right _ _) (coneTilt_pos δ a t).le)
    (integral_coneTilt_pos hδ a).le

/-! ### The envelope -/

/-- `c₀ = ∫ e^{−|s| − s²/2} ds`. -/
noncomputable def coneC₀ : ℝ := ∫ s : ℝ, Real.exp (-|s| - s ^ 2 / 2)

theorem integrable_coneC₀ : Integrable (fun s : ℝ => Real.exp (-|s| - s ^ 2 / 2)) :=
  (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)).mono
    (by fun_prop : Continuous fun s : ℝ => Real.exp (-|s| - s ^ 2 / 2)).aestronglyMeasurable
    (Eventually.of_forall fun s => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
        abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.2 (by nlinarith [abs_nonneg s]))

theorem coneC₀_pos : 0 < coneC₀ := by
  unfold coneC₀
  rw [integral_pos_iff_support_of_nonneg (fun s => (Real.exp_pos _).le) integrable_coneC₀,
    Function.support_eq_univ (fun s => (Real.exp_pos _).ne')]
  simp

/-- The denominator from below: `∫ w_{δ,a} ≥ e^{−|a|} e^{a²/2} c₀` for `0 ≤ δ ≤ 1`. -/
theorem integral_coneTilt_ge {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (a : ℝ) :
    Real.exp (-|a|) * Real.exp (a ^ 2 / 2) * coneC₀ ≤ ∫ t, coneTilt δ a t := by
  have hpt : ∀ t, Real.exp (-|a|) * Real.exp (a ^ 2 / 2) *
      Real.exp (-|t - a| - (t - a) ^ 2 / 2) ≤ coneTilt δ a t := by
    intro t
    unfold coneTilt
    rw [← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have h1 : |t| ≤ |a| + |t - a| := by
      calc |t| = |a + (t - a)| := by ring_nf
        _ ≤ |a| + |t - a| := abs_add_le _ _
    have h2 : δ * |t| ≤ |t| := by nlinarith [abs_nonneg t]
    have h3 : (t - a) ^ 2 = t ^ 2 - 2 * a * t + a ^ 2 := by ring
    linarith
  have hint : Integrable (fun t : ℝ => Real.exp (-|a|) * Real.exp (a ^ 2 / 2) *
      Real.exp (-|t - a| - (t - a) ^ 2 / 2)) :=
    (integrable_coneC₀.comp_sub_right a).const_mul _
  calc Real.exp (-|a|) * Real.exp (a ^ 2 / 2) * coneC₀
      = ∫ t, Real.exp (-|a|) * Real.exp (a ^ 2 / 2) * Real.exp (-|t - a| - (t - a) ^ 2 / 2) := by
        rw [integral_const_mul, coneC₀,
          ← integral_sub_right_eq_self (fun s : ℝ => Real.exp (-|s| - s ^ 2 / 2)) a]
    _ ≤ ∫ t, coneTilt δ a t := integral_mono hint (integrable_coneTilt hδ0 a) hpt

/-- The numerator from above: `∫ t₊ w_{δ,a} ≤ e^{a²/2}(√(2π)|a| + 2)` for `δ ≥ 0`. -/
theorem integral_posPart_coneTilt_le {δ : ℝ} (hδ : 0 ≤ δ) (a : ℝ) :
    ∫ t, max t 0 * coneTilt δ a t ≤ Real.exp (a ^ 2 / 2) * (Real.sqrt (2 * Real.pi) * |a| + 2) := by
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
  calc ∫ t, max t 0 * coneTilt δ a t
      ≤ ∫ t, |t| * Real.exp (-t ^ 2 / 2 + a * t) :=
        integral_mono (integrable_posPart_coneTilt hδ a) (integrable_abs_gaussTilt a) fun t =>
          mul_le_mul (max_le (le_abs_self t) (abs_nonneg t)) (coneTilt_le hδ a t)
            (coneTilt_pos δ a t).le (abs_nonneg t)
    _ = Real.exp (a ^ 2 / 2) * ∫ t, |t| * Real.exp (-(t - a) ^ 2 / 2) := by
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

/-- ★★ **The envelope**: `0 ≤ E_{δ,a}[t₊] ≤ (√(2π)|a| + 2) e^{|a|}/c₀` for `0 ≤ δ ≤ 1`. -/
theorem coneScaledCorrection_le {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (a : ℝ) :
    coneScaledCorrection δ a ≤ (Real.sqrt (2 * Real.pi) * |a| + 2) * Real.exp |a| / coneC₀ := by
  unfold coneScaledCorrection
  rw [div_le_div_iff₀ (integral_coneTilt_pos hδ0 a) coneC₀_pos]
  have hone : Real.exp |a| * Real.exp (-|a|) = 1 := by rw [← Real.exp_add]; simp
  calc (∫ t, max t 0 * coneTilt δ a t) * coneC₀
      ≤ Real.exp (a ^ 2 / 2) * (Real.sqrt (2 * Real.pi) * |a| + 2) * coneC₀ :=
        mul_le_mul_of_nonneg_right (integral_posPart_coneTilt_le hδ0 a) coneC₀_pos.le
    _ = (Real.sqrt (2 * Real.pi) * |a| + 2) * Real.exp |a| *
          (Real.exp (-|a|) * Real.exp (a ^ 2 / 2) * coneC₀) := by
        rw [show (Real.sqrt (2 * Real.pi) * |a| + 2) * Real.exp |a| *
          (Real.exp (-|a|) * Real.exp (a ^ 2 / 2) * coneC₀) = (Real.exp |a| * Real.exp (-|a|)) *
          (Real.exp (a ^ 2 / 2) * (Real.sqrt (2 * Real.pi) * |a| + 2) * coneC₀) by ring, hone,
          one_mul]
    _ ≤ (Real.sqrt (2 * Real.pi) * |a| + 2) * Real.exp |a| * ∫ t, coneTilt δ a t :=
        mul_le_mul_of_nonneg_left (integral_coneTilt_ge hδ0 hδ1 a) (by positivity)

/-! ### The frozen posterior ratio -/

/-- `v + |v| = 2 max(v, 0)`. -/
theorem add_abs_eq_two_mul_max (v : ℝ) : v + |v| = 2 * max v 0 := by
  rcases le_or_gt 0 v with h | h
  · rw [abs_of_nonneg h, max_eq_left h]; ring
  · rw [abs_of_neg h, max_eq_right h.le]; ring

/-- `Z_N[u₁²; a]` through its Leray density `π² e^{−|v|}(1 + v + |v|)` (examples_slop §3). -/
noncomputable def coneNumSq (N a : ℝ) : ℝ :=
  ∫ v, Real.exp (-N * v ^ 2 / 2 + Real.sqrt N * v * a) *
    (Real.pi ^ 2 * Real.exp (-|v|) * (1 + v + |v|))

/-- `Z_N[1; a]` through its Leray density `2π² e^{−|v|}`. -/
noncomputable def coneDen (N a : ℝ) : ℝ :=
  2 * Real.pi ^ 2 * ∫ v, Real.exp (-N * v ^ 2 / 2 + Real.sqrt N * v * a - |v|)

/-- The denominator is the four-dimensional frozen partition function (`cone_evidence_eq`). -/
theorem coneDen_eq (N a : ℝ) :
    coneDen N a = ∫ u : (ℝ × ℝ) × (ℝ × ℝ),
      Real.exp (-N * coneQ u ^ 2 / 2 + Real.sqrt N * coneQ u * a) * gaussW u :=
  (cone_evidence_eq N a).symm

/-- ★★ **The frozen ratio**: `Z_N[u₁²; a]/Z_N[1; a] = ½ + N^{−1/2} E_{δ,a}[t₊]`, `δ = N^{−1/2}`. -/
theorem cone_posterior_ratio_eq {N : ℝ} (hN : 0 < N) (a : ℝ) :
    coneNumSq N a / coneDen N a =
      1 / 2 + 1 / Real.sqrt N * coneScaledCorrection (1 / Real.sqrt N) a := by
  have hs0 : 0 < Real.sqrt N := Real.sqrt_pos.2 hN
  have hN' : N = Real.sqrt N * Real.sqrt N := (Real.mul_self_sqrt hN.le).symm
  set s := Real.sqrt N with hs
  clear_value s
  have hδ : 0 ≤ 1 / s := by positivity
  have hDpos : 0 < ∫ t, coneTilt (1 / s) a t := integral_coneTilt_pos hδ a
  have hexp : ∀ v : ℝ, coneTilt (1 / s) a (s * v) =
      Real.exp (-N * v ^ 2 / 2 + s * v * a) * Real.exp (-|v|) := by
    intro v
    unfold coneTilt
    rw [← Real.exp_add, abs_mul, abs_of_pos hs0]
    congr 1
    rw [hN']
    field_simp
    ring
  have hmax : ∀ v : ℝ, max (s * v) 0 = s * max v 0 := fun v => by
    rw [mul_max_of_nonneg _ _ hs0.le, mul_zero]
  have hnum : coneNumSq N a = s⁻¹ * (Real.pi ^ 2 * ((∫ t, coneTilt (1 / s) a t) +
      2 / s * ∫ t, max t 0 * coneTilt (1 / s) a t)) := by
    set G : ℝ → ℝ := fun t => Real.pi ^ 2 *
      (coneTilt (1 / s) a t + 2 / s * (max t 0 * coneTilt (1 / s) a t)) with hG
    have e : ∀ v : ℝ, Real.exp (-N * v ^ 2 / 2 + s * v * a) *
        (Real.pi ^ 2 * Real.exp (-|v|) * (1 + v + |v|)) = G (s * v) := by
      intro v
      rw [hG]
      simp only
      rw [hexp, hmax, add_assoc, add_abs_eq_two_mul_max]
      field_simp
    unfold coneNumSq
    rw [← hs]
    rw [show (∫ v, Real.exp (-N * v ^ 2 / 2 + s * v * a) *
        (Real.pi ^ 2 * Real.exp (-|v|) * (1 + v + |v|))) = ∫ v, G (s * v) from
        integral_congr_ae (Eventually.of_forall e),
      Measure.integral_comp_mul_left G s, smul_eq_mul, abs_of_pos (inv_pos.2 hs0), hG]
    simp only
    rw [integral_const_mul, integral_add (integrable_coneTilt hδ a)
      ((integrable_posPart_coneTilt hδ a).const_mul _), integral_const_mul]
  have hden : coneDen N a = 2 * Real.pi ^ 2 * (s⁻¹ * ∫ t, coneTilt (1 / s) a t) := by
    unfold coneDen
    rw [← hs]
    congr 1
    have e : ∀ v : ℝ, Real.exp (-N * v ^ 2 / 2 + s * v * a - |v|) = coneTilt (1 / s) a (s * v) := by
      intro v
      rw [hexp, ← Real.exp_add, sub_eq_add_neg]
    rw [show (∫ v, Real.exp (-N * v ^ 2 / 2 + s * v * a - |v|)) =
        ∫ v, coneTilt (1 / s) a (s * v) from integral_congr_ae (Eventually.of_forall e),
      Measure.integral_comp_mul_left (coneTilt (1 / s) a) s, smul_eq_mul,
      abs_of_pos (inv_pos.2 hs0)]
  rw [hnum, hden, coneScaledCorrection]
  field_simp

/-! ### Measurability and the integrable envelope -/

theorem continuous_coneTilt_pair (δ : ℝ) : Continuous fun p : ℝ × ℝ => coneTilt δ p.1 p.2 := by
  unfold coneTilt; fun_prop

theorem measurable_coneScaledCorrection (δ : ℝ) :
    Measurable fun a => coneScaledCorrection δ a := by
  unfold coneScaledCorrection
  have h1 : StronglyMeasurable (fun a : ℝ => ∫ t, max t 0 * coneTilt δ a t) :=
    ((continuous_snd.max continuous_const).mul
      (continuous_coneTilt_pair δ)).stronglyMeasurable.integral_prod_right'
  have h2 : StronglyMeasurable (fun a : ℝ => ∫ t, coneTilt δ a t) :=
    (continuous_coneTilt_pair δ).stronglyMeasurable.integral_prod_right'
  exact h1.measurable.div h2.measurable

/-- The envelope `(√(2π)|a| + 2) e^{|a|}/c₀ · γ(a)` is integrable: it is at most
`K e^{−a²/4}` with `K = (√(2π) + 2) e⁴/(√(2π) c₀)`. -/
theorem integrable_coneEnvelope :
    Integrable (fun a : ℝ =>
      (Real.sqrt (2 * Real.pi) * |a| + 2) * Real.exp |a| / coneC₀ * gaussDensity a) := by
  have hK : Integrable (fun a : ℝ => (Real.sqrt (2 * Real.pi) + 2) * Real.exp 4 /
      (Real.sqrt (2 * Real.pi) * coneC₀) * Real.exp (-(1 / 4) * a ^ 2)) :=
    (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 4)).const_mul _
  refine hK.mono' ?_ (Eventually.of_forall fun a => ?_)
  · exact ((by fun_prop : Continuous fun a : ℝ =>
      (Real.sqrt (2 * Real.pi) * |a| + 2) * Real.exp |a| / coneC₀).mul
        continuous_gaussDensity).aestronglyMeasurable
  · have hc := coneC₀_pos
    have hsq : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
    have h0 : 0 ≤ (Real.sqrt (2 * Real.pi) * |a| + 2) * Real.exp |a| / coneC₀ * gaussDensity a := by
      have := gaussDensity_nonneg a
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    unfold gaussDensity
    -- `√(2π)|a| + 2 ≤ (√(2π) + 2) e^{|a|}` and `e^{2|a|} e^{−a²/2} ≤ e⁴ e^{−a²/4}`
    have h1 : Real.sqrt (2 * Real.pi) * |a| + 2 ≤ (Real.sqrt (2 * Real.pi) + 2) * Real.exp |a| := by
      have := Real.add_one_le_exp |a|
      nlinarith [abs_nonneg a]
    have h2 : Real.exp |a| * Real.exp |a| * Real.exp (-a ^ 2 / 2) ≤
        Real.exp 4 * Real.exp (-(1 / 4) * a ^ 2) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have : |a| ^ 2 = a ^ 2 := sq_abs a
      nlinarith [sq_nonneg (|a| - 4)]
    have he : 0 < Real.exp |a| := Real.exp_pos _
    have hg : 0 < Real.exp (-a ^ 2 / 2) := Real.exp_pos _
    rw [div_mul_div_comm, div_le_iff₀ (by positivity)]
    calc (Real.sqrt (2 * Real.pi) * |a| + 2) * Real.exp |a| * Real.exp (-a ^ 2 / 2)
        ≤ (Real.sqrt (2 * Real.pi) + 2) * Real.exp |a| * Real.exp |a| * Real.exp (-a ^ 2 / 2) := by
          gcongr
      _ = (Real.sqrt (2 * Real.pi) + 2) *
          (Real.exp |a| * Real.exp |a| * Real.exp (-a ^ 2 / 2)) := by ring
      _ ≤ (Real.sqrt (2 * Real.pi) + 2) * (Real.exp 4 * Real.exp (-(1 / 4) * a ^ 2)) := by
          gcongr
      _ = (Real.sqrt (2 * Real.pi) + 2) * Real.exp 4 / (Real.sqrt (2 * Real.pi) * coneC₀) *
          Real.exp (-(1 / 4) * a ^ 2) * (coneC₀ * Real.sqrt (2 * Real.pi)) := by
          field_simp

/-! ### The limit `δ → 0` -/

theorem tendsto_one_div_sqrt : Tendsto (fun N : ℝ => 1 / Real.sqrt N) atTop (𝓝 0) := by
  simp_rw [one_div]
  exact tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop

theorem continuous_coneTilt_delta (a t : ℝ) : Continuous fun δ => coneTilt δ a t := by
  unfold coneTilt; fun_prop

/-- `E_{δ,a}[t₊] → E_{0,a}[t₊]` as `δ = N^{−1/2} → 0`, by dominated convergence in `t`. -/
theorem tendsto_coneScaledCorrection (a : ℝ) :
    Tendsto (fun N : ℝ => coneScaledCorrection (1 / Real.sqrt N) a) atTop
      (𝓝 (coneScaledCorrection 0 a)) := by
  have hδ : ∀ N : ℝ, 0 ≤ 1 / Real.sqrt N := fun N => by positivity
  have hpt : ∀ t, Tendsto (fun N : ℝ => coneTilt (1 / Real.sqrt N) a t) atTop
      (𝓝 (coneTilt 0 a t)) :=
    fun t => ((continuous_coneTilt_delta a t).tendsto 0).comp tendsto_one_div_sqrt
  have hnum : Tendsto (fun N : ℝ => ∫ t, max t 0 * coneTilt (1 / Real.sqrt N) a t) atTop
      (𝓝 (∫ t, max t 0 * coneTilt 0 a t)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun t => |t| * Real.exp (-t ^ 2 / 2 + a * t)) (Eventually.of_forall fun N =>
        ((continuous_id.max continuous_const).mul
          (continuous_coneTilt (1 / Real.sqrt N) a)).aestronglyMeasurable)
      (Eventually.of_forall fun N => Eventually.of_forall fun t => ?_)
      (integrable_abs_gaussTilt a) (Eventually.of_forall fun t => (hpt t).const_mul _)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (le_max_right _ _) (coneTilt_pos _ a t).le)]
    exact mul_le_mul (max_le (le_abs_self t) (abs_nonneg t)) (coneTilt_le (hδ N) a t)
      (coneTilt_pos _ a t).le (abs_nonneg t)
  have hden : Tendsto (fun N : ℝ => ∫ t, coneTilt (1 / Real.sqrt N) a t) atTop
      (𝓝 (∫ t, coneTilt 0 a t)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun t => Real.exp (-t ^ 2 / 2 + a * t)) (Eventually.of_forall fun N =>
        (continuous_coneTilt (1 / Real.sqrt N) a).aestronglyMeasurable)
      (Eventually.of_forall fun N => Eventually.of_forall fun t => ?_)
      (integrable_gaussTilt a) (Eventually.of_forall hpt)
    rw [Real.norm_eq_abs, abs_of_pos (coneTilt_pos _ a t)]
    exact coneTilt_le (hδ N) a t
  exact hnum.div hden (integral_coneTilt_pos le_rfl a).ne'

/-! ### The averaged limit -/

/-- The average over the sample field converges,
`∫ E_{δ_N,a}[t₊] γ(a) da → ∫ E_{0,a}[t₊] γ(a) da`, by dominated convergence under the envelope. -/
theorem tendsto_integral_coneScaledCorrection :
    Tendsto (fun N : ℝ => ∫ a, coneScaledCorrection (1 / Real.sqrt N) a * gaussDensity a) atTop
      (𝓝 (∫ a, coneScaledCorrection 0 a * gaussDensity a)) := by
  refine tendsto_integral_filter_of_dominated_convergence
    (fun a => (Real.sqrt (2 * Real.pi) * |a| + 2) * Real.exp |a| / coneC₀ * gaussDensity a)
    (Eventually.of_forall fun N => ((measurable_coneScaledCorrection _).mul
      continuous_gaussDensity.measurable).aestronglyMeasurable)
    ?_ integrable_coneEnvelope
    (Eventually.of_forall fun a => (tendsto_coneScaledCorrection a).mul_const _)
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with N hN
  refine Eventually.of_forall fun a => ?_
  have hδ0 : 0 ≤ 1 / Real.sqrt N := by positivity
  have hδ1 : 1 / Real.sqrt N ≤ 1 := by
    rw [div_le_one (Real.sqrt_pos.2 (by linarith))]
    exact Real.one_le_sqrt.2 hN
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (coneScaledCorrection_nonneg hδ0 a)
    (gaussDensity_nonneg a))]
  exact mul_le_mul_of_nonneg_right (coneScaledCorrection_le hδ0 hδ1 a) (gaussDensity_nonneg a)

/-! ### The value of the limit: `E[(a + G)₊] = 1/√π` -/

/-- At `δ = 0`: `E_{0,a}[t₊] = ∫ t₊ e^{−t²/2 + at} / (√(2π) e^{a²/2})`. -/
theorem coneScaledCorrection_zero (a : ℝ) :
    coneScaledCorrection 0 a = (∫ t, max t 0 * Real.exp (-t ^ 2 / 2 + a * t)) /
      (Real.sqrt (2 * Real.pi) * Real.exp (a ^ 2 / 2)) := by
  unfold coneScaledCorrection coneTilt
  simp only [zero_mul, sub_zero]
  rw [integral_gaussTilt]

/-- The kernel `K(a,t) = t₊ e^{−(t−a)²/2 − a²/2}/(2π)`. -/
noncomputable def coneKernel (a t : ℝ) : ℝ :=
  max t 0 * Real.exp (-(t - a) ^ 2 / 2 - a ^ 2 / 2) / (2 * Real.pi)

theorem continuous_coneKernel : Continuous fun p : ℝ × ℝ => coneKernel p.1 p.2 := by
  unfold coneKernel; fun_prop

theorem coneKernel_nonneg (a t : ℝ) : 0 ≤ coneKernel a t := by
  unfold coneKernel
  have := le_max_right t 0
  positivity

/-- `E_{0,a}[t₊] γ(a) = ∫ K(a,t) dt`. -/
theorem coneScaledCorrection_zero_mul_gaussDensity (a : ℝ) :
    coneScaledCorrection 0 a * gaussDensity a = ∫ t, coneKernel a t := by
  rw [coneScaledCorrection_zero]
  unfold gaussDensity
  have e : ∀ t : ℝ, coneKernel a t =
      max t 0 * Real.exp (-t ^ 2 / 2 + a * t) * (Real.exp (-a ^ 2) / (2 * Real.pi)) := by
    intro t
    unfold coneKernel
    rw [show -(t - a) ^ 2 / 2 - a ^ 2 / 2 = (-t ^ 2 / 2 + a * t) + -a ^ 2 by ring, Real.exp_add]
    ring
  simp_rw [e]
  rw [integral_mul_const]
  set I := ∫ t, max t 0 * Real.exp (-t ^ 2 / 2 + a * t) with hI
  clear_value I
  set s := Real.sqrt (2 * Real.pi) with hsdef
  have hs : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hss : s * s = 2 * Real.pi := Real.mul_self_sqrt (by positivity)
  have h1 : Real.exp (-a ^ 2) = Real.exp (-a ^ 2 / 2) * Real.exp (-a ^ 2 / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have hE : Real.exp (a ^ 2 / 2) = (Real.exp (-a ^ 2 / 2))⁻¹ := by
    rw [← Real.exp_neg]; congr 1; ring
  have he : 0 < Real.exp (-a ^ 2 / 2) := Real.exp_pos _
  rw [hE, ← hss, h1]
  field_simp

/-- `K(a,t) = [t₊ e^{−t²/4}/(2π)] e^{−(a − t/2)²}`. -/
theorem coneKernel_eq (a t : ℝ) :
    coneKernel a t = max t 0 * Real.exp (-t ^ 2 / 4) / (2 * Real.pi) *
      Real.exp (-(1 : ℝ) * (a - t / 2) ^ 2) := by
  unfold coneKernel
  rw [show -(t - a) ^ 2 / 2 - a ^ 2 / 2 = -t ^ 2 / 4 + -(1 : ℝ) * (a - t / 2) ^ 2 by ring,
    Real.exp_add]
  ring

/-- The `a`-integral of the kernel: `∫ K(a,t) da = t₊ √π e^{−t²/4}/(2π)`. -/
theorem integral_coneKernel_left (t : ℝ) :
    ∫ a, coneKernel a t = max t 0 * Real.exp (-t ^ 2 / 4) / (2 * Real.pi) * Real.sqrt Real.pi := by
  simp_rw [coneKernel_eq]
  rw [integral_const_mul, integral_sub_right_eq_self (fun a : ℝ => Real.exp (-(1 : ℝ) * a ^ 2))
    (t / 2), integral_gaussian, div_one]

theorem integrable_coneKernel_slice (t : ℝ) : Integrable (fun a => coneKernel a t) := by
  simp_rw [coneKernel_eq]
  exact ((integrable_exp_neg_mul_sq one_pos).comp_sub_right (t / 2)).const_mul _

/-- `∫₀^∞ t e^{−t²/4} dt = 2`. -/
theorem integral_mul_exp_neg_quarter_sq_Ioi :
    ∫ t in Ioi (0 : ℝ), t * Real.exp (-t ^ 2 / 4) = 2 := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 1) (b := 1 / 4)
    (by norm_num) (by norm_num) (by norm_num)
  have e : ∀ x ∈ Ioi (0 : ℝ), x ^ (1 : ℝ) * Real.exp (-(1 / 4) * x ^ (2 : ℝ)) =
      x * Real.exp (-x ^ 2 / 4) := by
    intro x _
    rw [Real.rpow_one, Real.rpow_two]
    congr 2
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi e] at h
  rw [h, show (-(1 + 1) / 2 : ℝ) = -1 by norm_num, Real.rpow_neg (by norm_num), Real.rpow_one,
    show ((1 : ℝ) + 1) / 2 = 1 by norm_num, Real.Gamma_one]
  norm_num

theorem integrable_coneKernel_uncurry :
    Integrable (Function.uncurry fun a t => coneKernel a t) (volume.prod volume) := by
  refine (integrable_prod_iff' continuous_coneKernel.aestronglyMeasurable).2 ⟨?_, ?_⟩
  · exact Eventually.of_forall fun t => integrable_coneKernel_slice t
  · have e : ∀ t : ℝ, ∫ a, ‖coneKernel a t‖ =
        Real.sqrt Real.pi / (2 * Real.pi) * (max t 0 * Real.exp (-t ^ 2 / 4)) := by
      intro t
      simp_rw [Real.norm_eq_abs, abs_of_nonneg (coneKernel_nonneg _ _)]
      rw [integral_coneKernel_left]
      ring
    simp_rw [e]
    refine ((integrable_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 4)).abs.const_mul
      (Real.sqrt Real.pi / (2 * Real.pi))).mono' ?_ (Eventually.of_forall fun t => ?_)
    · exact (by fun_prop : Continuous fun t : ℝ => Real.sqrt Real.pi / (2 * Real.pi) *
        (max t 0 * Real.exp (-t ^ 2 / 4))).aestronglyMeasurable
    · have h0 : 0 ≤ max t 0 * Real.exp (-t ^ 2 / 4) := by
        have := le_max_right t 0; positivity
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), abs_mul, abs_of_pos (Real.exp_pos _),
        show Real.exp (-(1 / 4) * t ^ 2) = Real.exp (-t ^ 2 / 4) by congr 1; ring]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact mul_le_mul_of_nonneg_right (max_le (le_abs_self t) (abs_nonneg t)) (Real.exp_pos _).le

/-- ★★ `∫ E_{0,a}[t₊] γ(a) da = E[(a + G)₊] = 1/√π`: Fubini on the kernel, the `a`-integral is a
Gaussian, and `∫₀^∞ t e^{−t²/4} dt = 2`. -/
theorem integral_coneScaledCorrection_zero :
    ∫ a, coneScaledCorrection 0 a * gaussDensity a = 1 / Real.sqrt Real.pi := by
  simp_rw [coneScaledCorrection_zero_mul_gaussDensity]
  rw [integral_integral_swap integrable_coneKernel_uncurry]
  simp_rw [integral_coneKernel_left]
  have e : (fun t : ℝ => max t 0 * Real.exp (-t ^ 2 / 4) / (2 * Real.pi) * Real.sqrt Real.pi) =
      fun t => Real.sqrt Real.pi / (2 * Real.pi) * (max t 0 * Real.exp (-t ^ 2 / 4)) := by
    funext t; ring
  rw [e, integral_const_mul,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi (0 : ℝ)) (fun t ht => by
      simp only [mem_Ioi, not_lt] at ht
      rw [max_eq_right ht, zero_mul]),
    setIntegral_congr_fun measurableSet_Ioi (fun t (ht : 0 < t) => by
      rw [max_eq_left ht.le]),
    integral_mul_exp_neg_quarter_sq_Ioi]
  have hpi : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi := Real.mul_self_sqrt Real.pi_pos.le
  have hs : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  rw [div_mul_eq_mul_div, div_eq_div_iff (by positivity) hs.ne']
  linear_combination 2 * hpi

/-! ### The headline -/

/-- ★★★ **The averaged first correction of the cone posterior**: with the sample field
`a ∼ N(0,1)`, `√N (E_a[Z_N[u₁²; a]/Z_N[1; a]] − ½) → 1/√π` (the average of the RATIOS; the
average of the evidences is the prior mass). -/
theorem cone_averaged_correction :
    Tendsto (fun N : ℝ => Real.sqrt N *
      ((∫ a, coneNumSq N a / coneDen N a * gaussDensity a) - 1 / 2)) atTop
      (𝓝 (1 / Real.sqrt Real.pi)) := by
  rw [← integral_coneScaledCorrection_zero]
  refine tendsto_integral_coneScaledCorrection.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with N hN
  have hN0 : 0 < N := by linarith
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have hδ0 : 0 ≤ 1 / Real.sqrt N := by positivity
  have hδ1 : 1 / Real.sqrt N ≤ 1 := by
    rw [div_le_one hs]
    exact Real.one_le_sqrt.2 hN
  have hint : Integrable (fun a => coneScaledCorrection (1 / Real.sqrt N) a * gaussDensity a) :=
    integrable_coneEnvelope.mono' ((measurable_coneScaledCorrection _).mul
      continuous_gaussDensity.measurable).aestronglyMeasurable
      (Eventually.of_forall fun a => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (coneScaledCorrection_nonneg hδ0 a)
          (gaussDensity_nonneg a))]
        exact mul_le_mul_of_nonneg_right (coneScaledCorrection_le hδ0 hδ1 a)
          (gaussDensity_nonneg a))
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
  rw [integral_add (integrable_gaussDensity.const_mul _) (hint.const_mul _), integral_const_mul,
    integral_const_mul, hγ]
  field_simp
  ring

end Grammar
