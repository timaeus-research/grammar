/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.ConeAveragedRemainder

/-!
# The cone: the second coefficient of the averaged posterior

`E_N = E_a[Z_N[u₁²; a]/Z_N[1; a]] = ½ + 1/(√π√N) + c₂/N + O(N^{−3/2})` with

  `c₂ = ∫ G(a) γ(a) da`,  `G(a) = −Cov_{T ∼ N(a,1)}(T₊, |T|)` (`coneCorrectionDeriv`).

DCXXIX wrote the frozen ratio as `½ + N^{−1/2} F_δ(a)`, `δ = N^{−1/2}`, `F_δ(a) = E_{δ,a}[t₊]` with
the tilt `w_{δ,a}(t) = e^{−t²/2 + at − δ|t|}`, and DCXXXIII proved the Lipschitz bound
`|F_δ − F_0| ≤ δ B(a)`.  Here the expansion is pushed one order further: with
`|1 − e^{−x} − x| ≤ x²` (`abs_one_sub_exp_neg_sub_le`) the numerator and denominator of `F_δ` are
`P_δ = P_0 − δQ₁ + O(δ²M₃)`, `D_δ = D_0 − δM₁ + O(δ²M₂)` (`Q₁ = ∫ t₊|t| w`, `M_k = ∫ |t|^k w`), so

  `|F_δ(a) − F_0(a) − δ G(a)| ≤ δ² K(a)`   (★★ `coneScaledCorrection_second_order`)

with the explicit Gaussian-integrable envelope `K = coneQuadEnvelope`, and integrating against
`γ` gives the rate (★★★ `cone_second_coeff_bound`)

  `|N(E_N − ½ − 1/(√π√N)) − c₂| ≤ C₂/√N`,   `C₂ = ∫ K γ`,

hence the limit (★★★ `tendsto_cone_second_coeff`).  The symmetric form
`c₂ = −½∫(a² + 1 − m(a)²)γ` and the value `−5/6 + √3/π` are the next unit (examples_slop §3;
Astra round-12 target 3).  Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

/-! ### The second-order elementary inequality and the cubic moment -/

/-- `|1 − e^{−x} − x| ≤ x²` for `x ≥ 0` (via `e^{−x} ≤ 1/(1+x) ≤ 1 − x + x²`). -/
theorem abs_one_sub_exp_neg_sub_le {x : ℝ} (hx : 0 ≤ x) :
    |1 - Real.exp (-x) - x| ≤ x ^ 2 := by
  have h1 : Real.exp (-x) ≤ 1 - x + x ^ 2 := by
    have hpos : 0 < 1 + x := by linarith
    have hup : 1 + x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
    have hinv : Real.exp (-x) ≤ 1 / (1 + x) := by
      rw [Real.exp_neg, inv_eq_one_div]
      exact one_div_le_one_div_of_le hpos hup
    refine hinv.trans ?_
    rw [div_le_iff₀ hpos]
    nlinarith [pow_nonneg hx 3]
  have h2 : 1 - x ≤ Real.exp (-x) := by linarith [Real.add_one_le_exp (-x)]
  rw [abs_le]
  constructor <;> nlinarith

/-- `∫ |t|³ e^{−t²/2} dt = 4`. -/
theorem integral_cube_abs_mul_exp_neg_half_sq :
    ∫ t : ℝ, |t| ^ 3 * Real.exp (-t ^ 2 / 2) = 4 := by
  have h := integral_comp_abs (f := fun t : ℝ => t ^ 3 * Real.exp (-t ^ 2 / 2))
  simp only [sq_abs] at h
  rw [h]
  have h3 := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 3) (b := 1 / 2)
    (by norm_num) (by norm_num) (by norm_num)
  have e : ∀ x ∈ Ioi (0 : ℝ), x ^ (3 : ℝ) * Real.exp (-(1 / 2) * x ^ (2 : ℝ)) =
      x ^ 3 * Real.exp (-x ^ 2 / 2) := by
    intro x _
    rw [Real.rpow_two, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    congr 2
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi e] at h3
  rw [h3, show (-(3 + 1) / 2 : ℝ) = -2 by norm_num, show ((3 : ℝ) + 1) / 2 = 2 by norm_num,
    Real.Gamma_two, Real.rpow_neg (by norm_num), show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast]
  norm_num

theorem integrable_cube_abs_mul_exp_neg_half_sq :
    Integrable (fun t : ℝ => |t| ^ 3 * Real.exp (-t ^ 2 / 2)) := by
  have := integrable_rpow_mul_exp_neg_mul_sq (b := 1 / 2) (by norm_num) (s := 3) (by norm_num)
  have h4 : Integrable (fun x : ℝ => x ^ 4 * Real.exp (-x ^ 2 / 2)) := by
    have := integrable_rpow_mul_exp_neg_mul_sq (b := 1 / 2) (by norm_num) (s := 4) (by norm_num)
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    congr 2
    ring
  have h0 : Integrable (fun x : ℝ => Real.exp (-x ^ 2 / 2)) := by
    have := integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only
    congr 1
    ring
  refine (h4.add h0).mono' (by fun_prop :
    Continuous fun t : ℝ => |t| ^ 3 * Real.exp (-t ^ 2 / 2)).aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  simp only [Pi.add_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hE : 0 < Real.exp (-t ^ 2 / 2) := Real.exp_pos _
  have ha : |t| ^ 3 ≤ t ^ 4 + 1 := by
    have h2 : |t| ^ 2 = t ^ 2 := sq_abs t
    have h4 : |t| ^ 4 = t ^ 4 := by rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, h2, ← pow_mul]
    nlinarith [abs_nonneg t, sq_nonneg (|t| ^ 2 - |t|), sq_nonneg (|t| - 1)]
  nlinarith

/-- `|t|³ w_{0,a}` is integrable. -/
theorem integrable_cube_abs_gaussTilt (a : ℝ) :
    Integrable (fun t : ℝ => |t| ^ 3 * Real.exp (-t ^ 2 / 2 + a * t)) := by
  have h1 : Integrable (fun t : ℝ => |t - a| ^ 3 * Real.exp (-(t - a) ^ 2 / 2)) :=
    integrable_cube_abs_mul_exp_neg_half_sq.comp_sub_right a
  have h2 : Integrable (fun t : ℝ => |a| ^ 3 * Real.exp (-(t - a) ^ 2 / 2)) := by
    have := ((integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)).comp_sub_right a).const_mul
      (|a| ^ 3)
    refine this.congr (Eventually.of_forall fun t => ?_)
    simp only
    congr 2
    ring
  have h12 : Integrable (fun t : ℝ => |t - a| ^ 3 * Real.exp (-(t - a) ^ 2 / 2) +
      |a| ^ 3 * Real.exp (-(t - a) ^ 2 / 2)) := h1.add h2
  refine (h12.const_mul (4 * Real.exp (a ^ 2 / 2))).mono'
    (by fun_prop :
      Continuous fun t : ℝ => |t| ^ 3 * Real.exp (-t ^ 2 / 2 + a * t)).aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), gaussTilt_eq]
  have hE : 0 ≤ Real.exp (a ^ 2 / 2) * Real.exp (-(t - a) ^ 2 / 2) := by positivity
  have hcube : |t| ^ 3 ≤ 4 * |t - a| ^ 3 + 4 * |a| ^ 3 := by
    have h1 : |t| ≤ |t - a| + |a| := by
      calc |t| = |(t - a) + a| := by ring_nf
        _ ≤ |t - a| + |a| := abs_add_le _ _
    have hx := abs_nonneg (t - a)
    have hy := abs_nonneg a
    calc |t| ^ 3 ≤ (|t - a| + |a|) ^ 3 := pow_le_pow_left₀ (abs_nonneg t) h1 3
      _ ≤ 4 * |t - a| ^ 3 + 4 * |a| ^ 3 := by
          nlinarith [mul_nonneg (mul_nonneg hx hy) (sq_nonneg (|t - a| - |a|))]
  nlinarith [mul_le_mul_of_nonneg_right hcube hE]

/-- `∫ |t|³ w_{0,a} ≤ 4 e^{a²/2}(4 + √(2π)|a|³)`. -/
theorem integral_cube_abs_gaussTilt_le (a : ℝ) :
    ∫ t : ℝ, |t| ^ 3 * Real.exp (-t ^ 2 / 2 + a * t) ≤
      4 * Real.exp (a ^ 2 / 2) * (4 + Real.sqrt (2 * Real.pi) * |a| ^ 3) := by
  have hgauss : ∫ u : ℝ, Real.exp (-u ^ 2 / 2) = Real.sqrt (2 * Real.pi) := by
    have e : ∀ u : ℝ, Real.exp (-u ^ 2 / 2) = Real.exp (-(1 / 2) * u ^ 2) := fun u => by
      congr 1; ring
    simp_rw [e]
    rw [integral_gaussian, show Real.pi / (1 / 2) = 2 * Real.pi by ring]
  have h0 : Integrable (fun u : ℝ => Real.exp (-u ^ 2 / 2)) := by
    have := integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)
    refine this.congr (Eventually.of_forall fun u => ?_)
    simp only
    congr 1
    ring
  have hI2 : Integrable (fun u : ℝ => (4 * |u| ^ 3 + 4 * |a| ^ 3) * Real.exp (-u ^ 2 / 2)) := by
    refine ((integrable_cube_abs_mul_exp_neg_half_sq.const_mul 4).add
      (h0.const_mul (4 * |a| ^ 3))).congr (Eventually.of_forall fun u => ?_)
    simp only [Pi.add_apply]
    ring
  have hshift : ∫ t : ℝ, |t| ^ 3 * Real.exp (-t ^ 2 / 2 + a * t) =
      Real.exp (a ^ 2 / 2) * ∫ u : ℝ, |u + a| ^ 3 * Real.exp (-u ^ 2 / 2) := by
    rw [← integral_const_mul,
      ← integral_add_right_eq_self (fun u : ℝ => Real.exp (a ^ 2 / 2) *
        (|u + a| ^ 3 * Real.exp (-u ^ 2 / 2))) (-a)]
    congr 1
    funext t
    rw [gaussTilt_eq]
    simp only [neg_add_cancel_right]
    ring_nf
  rw [hshift]
  have hb : ∫ u : ℝ, |u + a| ^ 3 * Real.exp (-u ^ 2 / 2) ≤
      ∫ u : ℝ, (4 * |u| ^ 3 + 4 * |a| ^ 3) * Real.exp (-u ^ 2 / 2) := by
    refine integral_mono ?_ hI2 fun u => ?_
    · refine hI2.mono' (by fun_prop :
        Continuous fun u : ℝ => |u + a| ^ 3 * Real.exp (-u ^ 2 / 2)).aestronglyMeasurable
        (Eventually.of_forall fun u => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hE : 0 < Real.exp (-u ^ 2 / 2) := Real.exp_pos _
      have hx := abs_nonneg u
      have hy := abs_nonneg a
      have h1 : |u + a| ≤ |u| + |a| := abs_add_le _ _
      have hc : |u + a| ^ 3 ≤ 4 * |u| ^ 3 + 4 * |a| ^ 3 := by
        calc |u + a| ^ 3 ≤ (|u| + |a|) ^ 3 := pow_le_pow_left₀ (abs_nonneg _) h1 3
          _ ≤ 4 * |u| ^ 3 + 4 * |a| ^ 3 := by
              nlinarith [mul_nonneg (mul_nonneg hx hy) (sq_nonneg (|u| - |a|))]
      exact mul_le_mul_of_nonneg_right hc hE.le
    · have hE : 0 < Real.exp (-u ^ 2 / 2) := Real.exp_pos _
      have hx := abs_nonneg u
      have hy := abs_nonneg a
      have h1 : |u + a| ≤ |u| + |a| := abs_add_le _ _
      have hc : |u + a| ^ 3 ≤ 4 * |u| ^ 3 + 4 * |a| ^ 3 := by
        calc |u + a| ^ 3 ≤ (|u| + |a|) ^ 3 := pow_le_pow_left₀ (abs_nonneg _) h1 3
          _ ≤ 4 * |u| ^ 3 + 4 * |a| ^ 3 := by
              nlinarith [mul_nonneg (mul_nonneg hx hy) (sq_nonneg (|u| - |a|))]
      exact mul_le_mul_of_nonneg_right hc hE.le
  have hval : ∫ u : ℝ, (4 * |u| ^ 3 + 4 * |a| ^ 3) * Real.exp (-u ^ 2 / 2) =
      4 * 4 + 4 * |a| ^ 3 * Real.sqrt (2 * Real.pi) := by
    have e : (fun u : ℝ => (4 * |u| ^ 3 + 4 * |a| ^ 3) * Real.exp (-u ^ 2 / 2)) =
        fun u => 4 * (|u| ^ 3 * Real.exp (-u ^ 2 / 2)) + 4 * |a| ^ 3 * Real.exp (-u ^ 2 / 2) := by
      funext u; ring
    rw [e, integral_add (integrable_cube_abs_mul_exp_neg_half_sq.const_mul 4)
      (h0.const_mul (4 * |a| ^ 3)), integral_const_mul, integral_const_mul,
      integral_cube_abs_mul_exp_neg_half_sq, hgauss]
  have hE : 0 < Real.exp (a ^ 2 / 2) := Real.exp_pos _
  calc Real.exp (a ^ 2 / 2) * ∫ u : ℝ, |u + a| ^ 3 * Real.exp (-u ^ 2 / 2)
      ≤ Real.exp (a ^ 2 / 2) * (4 * 4 + 4 * |a| ^ 3 * Real.sqrt (2 * Real.pi)) := by
        rw [← hval]; exact mul_le_mul_of_nonneg_left hb hE.le
    _ = 4 * Real.exp (a ^ 2 / 2) * (4 + Real.sqrt (2 * Real.pi) * |a| ^ 3) := by ring

/-! ### The second-order expansions of `P_δ` and `D_δ` -/

/-- `|P_δ − P_0 + δ Q₁| ≤ δ² M₃`, `Q₁ = ∫ t₊|t| w_{0,a}`, `M₃ = ∫ |t|³ w_{0,a}`. -/
theorem posPart_coneTilt_second_order {δ : ℝ} (hδ : 0 ≤ δ) (a : ℝ) :
    |(∫ t, max t 0 * coneTilt δ a t) - (∫ t, max t 0 * coneTilt 0 a t) +
      δ * ∫ t, max t 0 * |t| * coneTilt 0 a t| ≤
      δ ^ 2 * ∫ t, |t| ^ 3 * Real.exp (-t ^ 2 / 2 + a * t) := by
  have hpt : ∀ t : ℝ, max t 0 * coneTilt δ a t - max t 0 * coneTilt 0 a t +
      δ * (max t 0 * |t| * coneTilt 0 a t) =
      -(max t 0 * ((1 - Real.exp (-(δ * |t|)) - δ * |t|) * Real.exp (-t ^ 2 / 2 + a * t))) := by
    intro t
    unfold coneTilt
    rw [show -t ^ 2 / 2 + a * t - δ * |t| = (-t ^ 2 / 2 + a * t) + -(δ * |t|) by ring, Real.exp_add]
    simp only [zero_mul, sub_zero]
    ring
  have hQ : Integrable (fun t : ℝ => max t 0 * |t| * coneTilt 0 a t) := by
    refine (integrable_sq_gaussTilt a).mono' (by
      have := continuous_coneTilt 0 a
      fun_prop : Continuous fun t : ℝ => max t 0 * |t| * coneTilt 0 a t).aestronglyMeasurable
      (Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by
      have := le_max_right t 0; have := coneTilt_pos 0 a t; positivity)]
    unfold coneTilt
    simp only [zero_mul, sub_zero]
    have hm : max t 0 ≤ |t| := max_le (le_abs_self t) (abs_nonneg t)
    have hab : |t| * |t| = t ^ 2 := by rw [← sq, sq_abs]
    have hE : 0 < Real.exp (-t ^ 2 / 2 + a * t) := Real.exp_pos _
    calc max t 0 * |t| * Real.exp (-t ^ 2 / 2 + a * t)
        ≤ |t| * |t| * Real.exp (-t ^ 2 / 2 + a * t) := by
          gcongr
        _ = t ^ 2 * Real.exp (-t ^ 2 / 2 + a * t) := by rw [hab]
  have hsub : Integrable (fun t : ℝ => max t 0 * coneTilt δ a t - max t 0 * coneTilt 0 a t) :=
    (integrable_posPart_coneTilt hδ a).sub (integrable_posPart_coneTilt le_rfl a)
  rw [← integral_sub (integrable_posPart_coneTilt hδ a) (integrable_posPart_coneTilt le_rfl a),
    ← integral_const_mul, ← integral_add hsub (hQ.const_mul δ)]
  simp_rw [hpt]
  rw [integral_neg, abs_neg, ← integral_const_mul]
  have hint : Integrable (fun t : ℝ => max t 0 *
      ((1 - Real.exp (-(δ * |t|)) - δ * |t|) * Real.exp (-t ^ 2 / 2 + a * t))) := by
    have := hsub.add (hQ.const_mul δ)
    refine this.neg.congr (Eventually.of_forall fun t => ?_)
    simp only [Pi.neg_apply, Pi.add_apply]
    rw [hpt t, neg_neg]
  refine (abs_integral_le_integral_abs).trans (integral_mono hint.abs
    ((integrable_cube_abs_gaussTilt a).const_mul _) fun t => ?_)
  have hm : max t 0 ≤ |t| := max_le (le_abs_self t) (abs_nonneg t)
  have hm0 : 0 ≤ max t 0 := le_max_right t 0
  have hE : 0 < Real.exp (-t ^ 2 / 2 + a * t) := Real.exp_pos _
  have hb := abs_one_sub_exp_neg_sub_le (mul_nonneg hδ (abs_nonneg t))
  have hab : |t| ^ 3 = |t| * |t| ^ 2 := by ring
  rw [abs_mul, abs_mul, abs_of_nonneg hm0, abs_of_pos hE]
  calc max t 0 * (|(1 - Real.exp (-(δ * |t|)) - δ * |t|)| * Real.exp (-t ^ 2 / 2 + a * t))
      ≤ |t| * ((δ * |t|) ^ 2 * Real.exp (-t ^ 2 / 2 + a * t)) := by gcongr
    _ = δ ^ 2 * (|t| ^ 3 * Real.exp (-t ^ 2 / 2 + a * t)) := by rw [hab]; ring

/-- `|D_δ − D_0 + δ M₁| ≤ δ² M₂`, `M₁ = ∫ |t| w_{0,a}`, `M₂ = ∫ t² w_{0,a}`. -/
theorem coneTilt_second_order {δ : ℝ} (hδ : 0 ≤ δ) (a : ℝ) :
    |(∫ t, coneTilt δ a t) - (∫ t, coneTilt 0 a t) +
      δ * ∫ t, |t| * Real.exp (-t ^ 2 / 2 + a * t)| ≤
      δ ^ 2 * ∫ t, t ^ 2 * Real.exp (-t ^ 2 / 2 + a * t) := by
  have hpt : ∀ t : ℝ, coneTilt δ a t - coneTilt 0 a t +
      δ * (|t| * Real.exp (-t ^ 2 / 2 + a * t)) =
      -((1 - Real.exp (-(δ * |t|)) - δ * |t|) * Real.exp (-t ^ 2 / 2 + a * t)) := by
    intro t
    unfold coneTilt
    rw [show -t ^ 2 / 2 + a * t - δ * |t| = (-t ^ 2 / 2 + a * t) + -(δ * |t|) by ring, Real.exp_add]
    simp only [zero_mul, sub_zero]
    ring
  have hsub : Integrable (fun t : ℝ => coneTilt δ a t - coneTilt 0 a t) :=
    (integrable_coneTilt hδ a).sub (integrable_coneTilt le_rfl a)
  rw [← integral_sub (integrable_coneTilt hδ a) (integrable_coneTilt le_rfl a),
    ← integral_const_mul, ← integral_add hsub ((integrable_abs_gaussTilt a).const_mul δ)]
  simp_rw [hpt]
  rw [integral_neg, abs_neg, ← integral_const_mul]
  have hint : Integrable (fun t : ℝ =>
      (1 - Real.exp (-(δ * |t|)) - δ * |t|) * Real.exp (-t ^ 2 / 2 + a * t)) := by
    have := hsub.add ((integrable_abs_gaussTilt a).const_mul δ)
    refine this.neg.congr (Eventually.of_forall fun t => ?_)
    simp only [Pi.neg_apply, Pi.add_apply]
    rw [hpt t, neg_neg]
  refine (abs_integral_le_integral_abs).trans (integral_mono hint.abs
    ((integrable_sq_gaussTilt a).const_mul _) fun t => ?_)
  have hE : 0 < Real.exp (-t ^ 2 / 2 + a * t) := Real.exp_pos _
  have hb := abs_one_sub_exp_neg_sub_le (mul_nonneg hδ (abs_nonneg t))
  have hab : |t| ^ 2 = t ^ 2 := sq_abs t
  rw [abs_mul, abs_of_pos hE]
  calc |(1 - Real.exp (-(δ * |t|)) - δ * |t|)| * Real.exp (-t ^ 2 / 2 + a * t)
      ≤ (δ * |t|) ^ 2 * Real.exp (-t ^ 2 / 2 + a * t) := by gcongr
    _ = δ ^ 2 * (t ^ 2 * Real.exp (-t ^ 2 / 2 + a * t)) := by rw [← hab]; ring

/-! ### The derivative `G(a) = −Cov_a(T₊, |T|)` and its envelope -/

/-- `G(a) = −(Q₁D₀ − P₀M₁)/D₀² = −Cov_{T ∼ N(a,1)}(T₊, |T|)`: the `δ`-derivative of `F_δ(a)`
at `0`. -/
noncomputable def coneCorrectionDeriv (a : ℝ) : ℝ :=
  -((∫ t, max t 0 * |t| * coneTilt 0 a t) * (∫ t, coneTilt 0 a t) -
      (∫ t, max t 0 * coneTilt 0 a t) * ∫ t, |t| * Real.exp (-t ^ 2 / 2 + a * t)) /
    (∫ t, coneTilt 0 a t) ^ 2

/-- `2 ≤ √(2π) ≤ 3`. -/
theorem sqrt_two_pi_bounds : 2 ≤ Real.sqrt (2 * Real.pi) ∧ Real.sqrt (2 * Real.pi) ≤ 3 := by
  constructor
  · calc (2 : ℝ) = Real.sqrt (2 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt (2 * Real.pi) := Real.sqrt_le_sqrt (by nlinarith [Real.pi_gt_three])
  · calc Real.sqrt (2 * Real.pi) ≤ Real.sqrt (3 ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith [Real.pi_lt_four])
      _ = 3 := Real.sqrt_sq (by norm_num)

theorem conePosSqMoment_nonneg (a : ℝ) : 0 ≤ ∫ t, max t 0 * |t| * coneTilt 0 a t :=
  integral_nonneg fun t => by
    have := le_max_right t 0; have := coneTilt_pos 0 a t; positivity

/-- `Q₁ ≤ M₂`. -/
theorem conePosSqMoment_le (a : ℝ) :
    ∫ t, max t 0 * |t| * coneTilt 0 a t ≤ ∫ t, t ^ 2 * Real.exp (-t ^ 2 / 2 + a * t) := by
  have hQ : Integrable (fun t : ℝ => max t 0 * |t| * coneTilt 0 a t) := by
    refine (integrable_sq_gaussTilt a).mono' (by
      have := continuous_coneTilt 0 a
      fun_prop : Continuous fun t : ℝ => max t 0 * |t| * coneTilt 0 a t).aestronglyMeasurable
      (Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by
      have := le_max_right t 0; have := coneTilt_pos 0 a t; positivity)]
    unfold coneTilt
    simp only [zero_mul, sub_zero]
    have hm : max t 0 ≤ |t| := max_le (le_abs_self t) (abs_nonneg t)
    have hab : |t| * |t| = t ^ 2 := by rw [← sq, sq_abs]
    calc max t 0 * |t| * Real.exp (-t ^ 2 / 2 + a * t)
        ≤ |t| * |t| * Real.exp (-t ^ 2 / 2 + a * t) := by gcongr
      _ = t ^ 2 * Real.exp (-t ^ 2 / 2 + a * t) := by rw [hab]
  refine integral_mono hQ (integrable_sq_gaussTilt a) fun t => ?_
  unfold coneTilt
  simp only [zero_mul, sub_zero]
  have hm : max t 0 ≤ |t| := max_le (le_abs_self t) (abs_nonneg t)
  have hab : |t| * |t| = t ^ 2 := by rw [← sq, sq_abs]
  calc max t 0 * |t| * Real.exp (-t ^ 2 / 2 + a * t)
      ≤ |t| * |t| * Real.exp (-t ^ 2 / 2 + a * t) := by gcongr
    _ = t ^ 2 * Real.exp (-t ^ 2 / 2 + a * t) := by rw [hab]

/-- `|G(a)| ≤ 4(a² + 1)`. -/
theorem abs_coneCorrectionDeriv_le (a : ℝ) : |coneCorrectionDeriv a| ≤ 4 * (a ^ 2 + 1) := by
  unfold coneCorrectionDeriv
  set P₀ := ∫ t, max t 0 * coneTilt 0 a t with hP₀
  set D₀ := ∫ t, coneTilt 0 a t with hD₀
  set Q₁ := ∫ t, max t 0 * |t| * coneTilt 0 a t with hQ₁
  set M₁ := ∫ t, |t| * Real.exp (-t ^ 2 / 2 + a * t) with hM₁
  set M₂ := ∫ t, t ^ 2 * Real.exp (-t ^ 2 / 2 + a * t) with hM₂
  set s := Real.sqrt (2 * Real.pi) with hs
  set E := Real.exp (a ^ 2 / 2) with hE
  have hs2 : 2 ≤ s := sqrt_two_pi_bounds.1
  have hE0 : 0 < E := Real.exp_pos _
  have hD₀0 : 0 < D₀ := integral_coneTilt_pos le_rfl a
  have hD₀eq : D₀ = s * E := by
    rw [hD₀]
    unfold coneTilt
    simp only [zero_mul, sub_zero]
    exact integral_gaussTilt a
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
  have hQ₁0 : 0 ≤ Q₁ := conePosSqMoment_nonneg a
  have hQ₁le : Q₁ ≤ M₂ := conePosSqMoment_le a
  clear_value P₀ D₀ Q₁ M₁ M₂ s E
  rw [hD₀eq, abs_div, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < (s * E) ^ 2),
    div_le_iff₀ (by positivity)]
  have hM₁sq : M₁ * M₁ ≤ E * E * (s * (|a| + 1)) ^ 2 := by
    have h1 : M₁ ≤ E * (s * (|a| + 1)) := hM₁le.trans (by nlinarith [abs_nonneg a])
    calc M₁ * M₁ ≤ (E * (s * (|a| + 1))) * (E * (s * (|a| + 1))) :=
          mul_le_mul h1 h1 hM₁0 (by positivity)
      _ = E * E * (s * (|a| + 1)) ^ 2 := by ring
  have hsqa : (|a| + 1) ^ 2 ≤ 2 * (a ^ 2 + 1) := by
    have : |a| ^ 2 = a ^ 2 := sq_abs a
    nlinarith [sq_nonneg (|a| - 1)]
  rw [abs_le]
  constructor
  · nlinarith [mul_nonneg hQ₁0 (by positivity : (0 : ℝ) ≤ s * E), mul_nonneg hP₀0 hM₁0,
      mul_le_mul_of_nonneg_right hM₂le (by positivity : (0 : ℝ) ≤ s * E),
      mul_le_mul hP₀le hM₁le hM₁0 hM₁0, mul_le_mul_of_nonneg_left hsqa
        (by positivity : (0 : ℝ) ≤ E * E * s ^ 2)]
  · nlinarith [mul_nonneg hQ₁0 (by positivity : (0 : ℝ) ≤ s * E), mul_nonneg hP₀0 hM₁0,
      mul_le_mul_of_nonneg_right hM₂le (by positivity : (0 : ℝ) ≤ s * E),
      mul_le_mul hP₀le hM₁le hM₁0 hM₁0, mul_le_mul_of_nonneg_left hsqa
        (by positivity : (0 : ℝ) ≤ E * E * s ^ 2)]

/-- The second-order envelope `K(a) = (e^{|a|}/c₀)[6s(a² + 1)(|a| + 1) + 4s|a|³ + 16]`. -/
noncomputable def coneQuadEnvelope (a : ℝ) : ℝ :=
  Real.exp |a| / coneC₀ * (6 * Real.sqrt (2 * Real.pi) * (a ^ 2 + 1) * (|a| + 1) +
    4 * Real.sqrt (2 * Real.pi) * |a| ^ 3 + 16)

set_option maxHeartbeats 1600000 in
-- the twelve folded integrals and the long `calc` chains exceed the default heartbeat budget
/-- ★★ **The second-order bound**: `|F_δ(a) − F_0(a) − δ G(a)| ≤ δ² K(a)` for `0 ≤ δ ≤ 1`. -/
theorem coneScaledCorrection_second_order {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (a : ℝ) :
    |coneScaledCorrection δ a - coneScaledCorrection 0 a - δ * coneCorrectionDeriv a| ≤
      δ ^ 2 * coneQuadEnvelope a := by
  have hG := abs_coneCorrectionDeriv_le a
  have hP := posPart_coneTilt_second_order hδ0 a
  have hD := coneTilt_second_order hδ0 a
  have hDlip := abs_integral_coneTilt_sub_le hδ0 a
  unfold coneCorrectionDeriv at hG
  unfold coneScaledCorrection coneCorrectionDeriv coneQuadEnvelope
  set Pδ := ∫ t, max t 0 * coneTilt δ a t with hPδ
  set P₀ := ∫ t, max t 0 * coneTilt 0 a t with hP₀
  set Dδ := ∫ t, coneTilt δ a t with hDδ
  set D₀ := ∫ t, coneTilt 0 a t with hD₀
  set Q₁ := ∫ t, max t 0 * |t| * coneTilt 0 a t with hQ₁
  set M₁ := ∫ t, |t| * Real.exp (-t ^ 2 / 2 + a * t) with hM₁
  set M₂ := ∫ t, t ^ 2 * Real.exp (-t ^ 2 / 2 + a * t) with hM₂
  set M₃ := ∫ t, |t| ^ 3 * Real.exp (-t ^ 2 / 2 + a * t) with hM₃
  set s := Real.sqrt (2 * Real.pi) with hs
  set E := Real.exp (a ^ 2 / 2) with hE
  have hs2 : 2 ≤ s := sqrt_two_pi_bounds.1
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
  have hM₃le : M₃ ≤ 4 * E * (4 + s * |a| ^ 3) := integral_cube_abs_gaussTilt_le a
  have hM₁0 : 0 ≤ M₁ := integral_nonneg fun t => by positivity
  have hM₂0 : 0 ≤ M₂ := integral_nonneg fun t => by positivity
  have hM₃0 : 0 ≤ M₃ := integral_nonneg fun t => by positivity
  clear_value Pδ P₀ Dδ D₀ Q₁ M₁ M₂ M₃ s E
  set G := -(Q₁ * D₀ - P₀ * M₁) / D₀ ^ 2 with hGdef
  clear_value G
  -- the key identity
  have key : Pδ / Dδ - P₀ / D₀ - δ * G =
      G * δ * (D₀ - Dδ) / Dδ +
        ((Pδ - P₀ + δ * Q₁) * D₀ - P₀ * (Dδ - D₀ + δ * M₁)) / (Dδ * D₀) := by
    rw [hGdef]
    field_simp
    ring
  rw [key]
  have hneg : Real.exp (-|a|) = (Real.exp |a|)⁻¹ := Real.exp_neg _
  -- the two ratio bounds
  have hM₁s : M₁ ≤ E * (s * (|a| + 1)) := hM₁le.trans (by nlinarith [abs_nonneg a])
  have hR1 : M₁ / Dδ ≤ s * (|a| + 1) * Real.exp |a| / coneC₀ := by
    rw [div_le_iff₀ hDδ0]
    calc M₁ ≤ E * (s * (|a| + 1)) := hM₁s
      _ = s * (|a| + 1) * Real.exp |a| / coneC₀ * (Real.exp (-|a|) * E * coneC₀) := by
          rw [hneg]; field_simp
      _ ≤ s * (|a| + 1) * Real.exp |a| / coneC₀ * Dδ :=
          mul_le_mul_of_nonneg_left hDδge (by positivity)
  have hR2 : (M₃ * D₀ + M₁ * M₂) / (Dδ * D₀) ≤
      Real.exp |a| * (16 + 4 * s * |a| ^ 3 + 2 * s * (|a| + 1) * (a ^ 2 + 1)) / coneC₀ := by
    rw [div_le_iff₀ (mul_pos hDδ0 hD₀0)]
    have hnum : M₃ * D₀ + M₁ * M₂ ≤
        s * E * E * (16 + 4 * s * |a| ^ 3 + 2 * s * (|a| + 1) * (a ^ 2 + 1)) := by
      rw [hD₀eq]
      have h1 : M₃ * (s * E) ≤ 4 * E * (4 + s * |a| ^ 3) * (s * E) :=
        mul_le_mul_of_nonneg_right hM₃le (by positivity)
      have h2 : M₁ * M₂ ≤ (E * (s * (|a| + 1))) * (2 * s * E * (a ^ 2 + 1)) :=
        mul_le_mul hM₁s hM₂le hM₂0 (by positivity)
      nlinarith
    have hden : Real.exp (-|a|) * E * coneC₀ * (s * E) ≤ Dδ * D₀ := by
      rw [hD₀eq]
      exact mul_le_mul_of_nonneg_right hDδge (by positivity)
    calc M₃ * D₀ + M₁ * M₂
        ≤ s * E * E * (16 + 4 * s * |a| ^ 3 + 2 * s * (|a| + 1) * (a ^ 2 + 1)) := hnum
      _ = Real.exp |a| * (16 + 4 * s * |a| ^ 3 + 2 * s * (|a| + 1) * (a ^ 2 + 1)) / coneC₀ *
          (Real.exp (-|a|) * E * coneC₀ * (s * E)) := by
          rw [hneg]; field_simp
      _ ≤ Real.exp |a| * (16 + 4 * s * |a| ^ 3 + 2 * s * (|a| + 1) * (a ^ 2 + 1)) / coneC₀ *
          (Dδ * D₀) := mul_le_mul_of_nonneg_left hden (by positivity)
  -- the first term
  have hfirst : |G * δ * (D₀ - Dδ) / Dδ| ≤
      δ ^ 2 * (4 * (a ^ 2 + 1) * (s * (|a| + 1) * Real.exp |a| / coneC₀)) := by
    rw [abs_div, abs_of_pos hDδ0, abs_mul, abs_mul, abs_of_nonneg hδ0, div_le_iff₀ hDδ0]
    have hR1' : M₁ ≤ s * (|a| + 1) * Real.exp |a| / coneC₀ * Dδ := by
      rwa [div_le_iff₀ hDδ0] at hR1
    calc |G| * δ * |D₀ - Dδ| ≤ 4 * (a ^ 2 + 1) * δ * (δ * M₁) := by gcongr
      _ ≤ 4 * (a ^ 2 + 1) * δ * (δ * (s * (|a| + 1) * Real.exp |a| / coneC₀ * Dδ)) := by gcongr
      _ = δ ^ 2 * (4 * (a ^ 2 + 1) * (s * (|a| + 1) * Real.exp |a| / coneC₀)) * Dδ := by ring
  -- the second term
  have hsecond : |((Pδ - P₀ + δ * Q₁) * D₀ - P₀ * (Dδ - D₀ + δ * M₁)) / (Dδ * D₀)| ≤
      δ ^ 2 * (Real.exp |a| * (16 + 4 * s * |a| ^ 3 + 2 * s * (|a| + 1) * (a ^ 2 + 1)) /
        coneC₀) := by
    rw [abs_div, abs_of_pos (mul_pos hDδ0 hD₀0), div_le_iff₀ (mul_pos hDδ0 hD₀0)]
    have hR2' : M₃ * D₀ + M₁ * M₂ ≤ Real.exp |a| *
        (16 + 4 * s * |a| ^ 3 + 2 * s * (|a| + 1) * (a ^ 2 + 1)) / coneC₀ * (Dδ * D₀) := by
      rwa [div_le_iff₀ (mul_pos hDδ0 hD₀0)] at hR2
    calc |(Pδ - P₀ + δ * Q₁) * D₀ - P₀ * (Dδ - D₀ + δ * M₁)|
        ≤ |(Pδ - P₀ + δ * Q₁) * D₀| + |P₀ * (Dδ - D₀ + δ * M₁)| := abs_sub _ _
      _ = |Pδ - P₀ + δ * Q₁| * D₀ + P₀ * |Dδ - D₀ + δ * M₁| := by
          rw [abs_mul, abs_mul, abs_of_pos hD₀0, abs_of_nonneg hP₀0]
      _ ≤ δ ^ 2 * M₃ * D₀ + M₁ * (δ ^ 2 * M₂) := by gcongr
      _ = δ ^ 2 * (M₃ * D₀ + M₁ * M₂) := by ring
      _ ≤ δ ^ 2 * (Real.exp |a| * (16 + 4 * s * |a| ^ 3 + 2 * s * (|a| + 1) * (a ^ 2 + 1)) /
          coneC₀ * (Dδ * D₀)) := mul_le_mul_of_nonneg_left hR2' (by positivity)
      _ = δ ^ 2 * (Real.exp |a| * (16 + 4 * s * |a| ^ 3 + 2 * s * (|a| + 1) * (a ^ 2 + 1)) /
          coneC₀) * (Dδ * D₀) := by ring
  calc |G * δ * (D₀ - Dδ) / Dδ +
        ((Pδ - P₀ + δ * Q₁) * D₀ - P₀ * (Dδ - D₀ + δ * M₁)) / (Dδ * D₀)|
      ≤ |G * δ * (D₀ - Dδ) / Dδ| +
        |((Pδ - P₀ + δ * Q₁) * D₀ - P₀ * (Dδ - D₀ + δ * M₁)) / (Dδ * D₀)| := abs_add_le _ _
    _ ≤ δ ^ 2 * (4 * (a ^ 2 + 1) * (s * (|a| + 1) * Real.exp |a| / coneC₀)) +
        δ ^ 2 * (Real.exp |a| * (16 + 4 * s * |a| ^ 3 + 2 * s * (|a| + 1) * (a ^ 2 + 1)) /
          coneC₀) := add_le_add hfirst hsecond
    _ = δ ^ 2 * (Real.exp |a| / coneC₀ *
        (6 * s * (a ^ 2 + 1) * (|a| + 1) + 4 * s * |a| ^ 3 + 16)) := by
        field_simp
        ring

/-! ### Measurability and integrability -/

theorem measurable_coneCorrectionDeriv : Measurable coneCorrectionDeriv := by
  unfold coneCorrectionDeriv
  have hc := continuous_coneTilt_pair 0
  have h1 : StronglyMeasurable (fun a : ℝ => ∫ t, max t 0 * |t| * coneTilt 0 a t) :=
    (((continuous_snd.max continuous_const).mul continuous_snd.abs).mul
      hc).stronglyMeasurable.integral_prod_right'
  have h2 : StronglyMeasurable (fun a : ℝ => ∫ t, coneTilt 0 a t) :=
    hc.stronglyMeasurable.integral_prod_right'
  have h3 : StronglyMeasurable (fun a : ℝ => ∫ t, max t 0 * coneTilt 0 a t) :=
    ((continuous_snd.max continuous_const).mul hc).stronglyMeasurable.integral_prod_right'
  have h4 : StronglyMeasurable (fun a : ℝ => ∫ t, |t| * Real.exp (-t ^ 2 / 2 + a * t)) :=
    (by fun_prop : Continuous fun p : ℝ × ℝ =>
      |p.2| * Real.exp (-p.2 ^ 2 / 2 + p.1 * p.2)).stronglyMeasurable.integral_prod_right'
  exact (((h1.measurable.mul h2.measurable).sub (h3.measurable.mul h4.measurable)).neg).div
    (h2.measurable.pow_const 2)

/-- `(a² + 1) γ(a)` is integrable. -/
theorem integrable_sq_add_one_mul_gaussDensity :
    Integrable (fun a : ℝ => (a ^ 2 + 1) * gaussDensity a) := by
  have h1 : Integrable (fun a : ℝ => a ^ 2 * gaussDensity a) := by
    have := integrable_sq_mul_exp_neg_half_sq.div_const (Real.sqrt (2 * Real.pi))
    refine this.congr (Eventually.of_forall fun a => ?_)
    unfold gaussDensity
    simp only
    ring
  refine (h1.add integrable_gaussDensity).congr (Eventually.of_forall fun a => ?_)
  simp only [Pi.add_apply]
  ring

theorem integrable_coneCorrectionDeriv :
    Integrable (fun a : ℝ => coneCorrectionDeriv a * gaussDensity a) := by
  refine (integrable_sq_add_one_mul_gaussDensity.const_mul 4).mono'
    (measurable_coneCorrectionDeriv.mul continuous_gaussDensity.measurable).aestronglyMeasurable
    (Eventually.of_forall fun a => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gaussDensity_nonneg a), ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (abs_coneCorrectionDeriv_le a) (gaussDensity_nonneg a)

/-- `K(a) γ(a) ≤ 268 e⁴/(√(2π) c₀) e^{−a²/4}`, so it is integrable. -/
theorem integrable_coneQuadEnvelope :
    Integrable (fun a : ℝ => coneQuadEnvelope a * gaussDensity a) := by
  have hK : Integrable (fun a : ℝ => 268 * Real.exp 4 / (Real.sqrt (2 * Real.pi) * coneC₀) *
      Real.exp (-(1 / 4) * a ^ 2)) :=
    (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 4)).const_mul _
  refine hK.mono' ?_ (Eventually.of_forall fun a => ?_)
  · exact ((by unfold coneQuadEnvelope; fun_prop : Continuous coneQuadEnvelope).mul
      continuous_gaussDensity).aestronglyMeasurable
  · have hc := coneC₀_pos
    have hs := sqrt_two_pi_bounds
    have hs0 : 0 < Real.sqrt (2 * Real.pi) := by linarith
    have h0 : 0 ≤ coneQuadEnvelope a * gaussDensity a := by
      have := gaussDensity_nonneg a
      unfold coneQuadEnvelope
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    unfold coneQuadEnvelope gaussDensity
    -- the polynomial is at most `268 e^{|a|}`
    have hpoly : 6 * Real.sqrt (2 * Real.pi) * (a ^ 2 + 1) * (|a| + 1) +
        4 * Real.sqrt (2 * Real.pi) * |a| ^ 3 + 16 ≤ 268 * Real.exp |a| := by
      have h3 : |a| ^ 3 ≤ 6 * Real.exp |a| := by
        have := Real.pow_div_factorial_le_exp |a| (abs_nonneg a) 3
        norm_num [Nat.factorial] at this
        linarith
      have h2 : |a| ^ 2 ≤ 2 * Real.exp |a| := by
        have := Real.pow_div_factorial_le_exp |a| (abs_nonneg a) 2
        norm_num [Nat.factorial] at this
        rw [sq_abs]
        linarith
      have h1 : |a| ≤ Real.exp |a| := by linarith [Real.add_one_le_exp |a|]
      have h0' : 1 ≤ Real.exp |a| := Real.one_le_exp (abs_nonneg a)
      have hsq : a ^ 2 = |a| ^ 2 := (sq_abs a).symm
      rw [hsq]
      have ha0 := abs_nonneg a
      nlinarith [mul_le_mul_of_nonneg_left h3
          (by positivity : (0 : ℝ) ≤ 6 * Real.sqrt (2 * Real.pi)),
        mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 6 * Real.sqrt (2 * Real.pi)),
        mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 6 * Real.sqrt (2 * Real.pi)),
        mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 4 * Real.sqrt (2 * Real.pi))]
    have hexp : Real.exp |a| * Real.exp |a| * Real.exp (-a ^ 2 / 2) ≤
        Real.exp 4 * Real.exp (-(1 / 4) * a ^ 2) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have : |a| ^ 2 = a ^ 2 := sq_abs a
      nlinarith [sq_nonneg (|a| - 4)]
    have hea : 0 < Real.exp |a| := Real.exp_pos _
    have hg : 0 < Real.exp (-a ^ 2 / 2) := Real.exp_pos _
    calc Real.exp |a| / coneC₀ * (6 * Real.sqrt (2 * Real.pi) * (a ^ 2 + 1) * (|a| + 1) +
          4 * Real.sqrt (2 * Real.pi) * |a| ^ 3 + 16) *
          (Real.exp (-a ^ 2 / 2) / Real.sqrt (2 * Real.pi))
        ≤ Real.exp |a| / coneC₀ * (268 * Real.exp |a|) *
          (Real.exp (-a ^ 2 / 2) / Real.sqrt (2 * Real.pi)) := by gcongr
      _ = 268 / (Real.sqrt (2 * Real.pi) * coneC₀) *
          (Real.exp |a| * Real.exp |a| * Real.exp (-a ^ 2 / 2)) := by
          field_simp
      _ ≤ 268 / (Real.sqrt (2 * Real.pi) * coneC₀) *
          (Real.exp 4 * Real.exp (-(1 / 4) * a ^ 2)) := by gcongr
      _ = 268 * Real.exp 4 / (Real.sqrt (2 * Real.pi) * coneC₀) * Real.exp (-(1 / 4) * a ^ 2) := by
          ring

/-! ### The averaged second coefficient -/

/-- `c₂ = ∫ G(a) γ(a) da`. -/
noncomputable def coneSecondCoeff : ℝ := ∫ a, coneCorrectionDeriv a * gaussDensity a

/-- `C₂ = ∫ K(a) γ(a) da`. -/
noncomputable def coneQuadConst : ℝ := ∫ a, coneQuadEnvelope a * gaussDensity a

/-- The averaged posterior minus its two leading terms is `N^{−1/2} ∫ (F_δ − F_0) γ`,
`δ = N^{−1/2}`. -/
theorem cone_averaged_sub_eq {N : ℝ} (hN : 1 ≤ N) :
    (∫ a, coneNumSq N a / coneDen N a * gaussDensity a) - 1 / 2 -
      1 / (Real.sqrt Real.pi * Real.sqrt N) =
      1 / Real.sqrt N * ∫ a, (coneScaledCorrection (1 / Real.sqrt N) a -
        coneScaledCorrection 0 a) * gaussDensity a := by
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
  rw [← hdiff, mul_sub, hzero]
  field_simp
  ring

/-- ★★★ **The second coefficient with a rate**: for `N ≥ 1`,
`|N(E_N − ½ − 1/(√π√N)) − c₂| ≤ C₂/√N`. -/
theorem cone_second_coeff_bound {N : ℝ} (hN : 1 ≤ N) :
    |N * ((∫ a, coneNumSq N a / coneDen N a * gaussDensity a) - 1 / 2 -
      1 / (Real.sqrt Real.pi * Real.sqrt N)) - coneSecondCoeff| ≤ coneQuadConst / Real.sqrt N := by
  have hN0 : 0 < N := by linarith
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have hδ0 : 0 ≤ 1 / Real.sqrt N := by positivity
  have hδ1 : 1 / Real.sqrt N ≤ 1 := by
    rw [div_le_one hs]; exact Real.one_le_sqrt.2 hN
  have hNN : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN0.le
  have hint : ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 →
      Integrable (fun a => coneScaledCorrection δ a * gaussDensity a) := fun δ h0 h1 =>
    integrable_coneEnvelope.mono' ((measurable_coneScaledCorrection _).mul
      continuous_gaussDensity.measurable).aestronglyMeasurable
      (Eventually.of_forall fun a => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (coneScaledCorrection_nonneg h0 a)
          (gaussDensity_nonneg a))]
        exact mul_le_mul_of_nonneg_right (coneScaledCorrection_le h0 h1 a) (gaussDensity_nonneg a))
  have hFint : Integrable (fun a => (coneScaledCorrection (1 / Real.sqrt N) a -
      coneScaledCorrection 0 a) * gaussDensity a) := by
    refine ((hint _ hδ0 hδ1).sub (hint 0 le_rfl zero_le_one)).congr
      (Eventually.of_forall fun a => ?_)
    simp only [Pi.sub_apply]
    ring
  rw [cone_averaged_sub_eq hN]
  unfold coneSecondCoeff
  set I := ∫ a, (coneScaledCorrection (1 / Real.sqrt N) a - coneScaledCorrection 0 a) *
    gaussDensity a with hI
  set J := ∫ a, coneCorrectionDeriv a * gaussDensity a with hJ
  -- `N · N^{−1/2} I − J = √N ∫ (F_δ − F_0 − δ G) γ`
  have hmain : N * (1 / Real.sqrt N * I) - J =
      ∫ a, Real.sqrt N * ((coneScaledCorrection (1 / Real.sqrt N) a - coneScaledCorrection 0 a -
        1 / Real.sqrt N * coneCorrectionDeriv a) * gaussDensity a) := by
    have h1 : N * (1 / Real.sqrt N * I) - J = Real.sqrt N * (I - 1 / Real.sqrt N * J) := by
      have h2 : N * (1 / Real.sqrt N) = Real.sqrt N := by
        rw [mul_one_div, div_eq_iff hs.ne', hNN]
      calc N * (1 / Real.sqrt N * I) - J = (N * (1 / Real.sqrt N)) * I - J := by ring
        _ = Real.sqrt N * I - J := by rw [h2]
        _ = Real.sqrt N * (I - 1 / Real.sqrt N * J) := by field_simp
    rw [h1, hI, hJ, ← integral_const_mul, ← integral_sub hFint
      (integrable_coneCorrectionDeriv.const_mul _), ← integral_const_mul]
    congr 1
    funext a
    ring
  rw [hmain]
  have hdom : Integrable (fun a : ℝ => 1 / Real.sqrt N * (coneQuadEnvelope a * gaussDensity a)) :=
    integrable_coneQuadEnvelope.const_mul _
  have hpt : ∀ a : ℝ, |Real.sqrt N * ((coneScaledCorrection (1 / Real.sqrt N) a -
      coneScaledCorrection 0 a - 1 / Real.sqrt N * coneCorrectionDeriv a) * gaussDensity a)| ≤
      1 / Real.sqrt N * (coneQuadEnvelope a * gaussDensity a) := by
    intro a
    rw [abs_mul, abs_mul, abs_of_pos hs, abs_of_nonneg (gaussDensity_nonneg a)]
    have hb := coneScaledCorrection_second_order hδ0 hδ1 a
    calc Real.sqrt N * (|coneScaledCorrection (1 / Real.sqrt N) a - coneScaledCorrection 0 a -
          1 / Real.sqrt N * coneCorrectionDeriv a| * gaussDensity a)
        ≤ Real.sqrt N * ((1 / Real.sqrt N) ^ 2 * coneQuadEnvelope a * gaussDensity a) := by
          have := gaussDensity_nonneg a
          gcongr
      _ = 1 / Real.sqrt N * (coneQuadEnvelope a * gaussDensity a) := by
          field_simp
  have hleft : Integrable (fun a : ℝ => |Real.sqrt N * ((coneScaledCorrection (1 / Real.sqrt N) a -
      coneScaledCorrection 0 a - 1 / Real.sqrt N * coneCorrectionDeriv a) * gaussDensity a)|) := by
    refine hdom.mono' ?_ (Eventually.of_forall fun a => ?_)
    · exact ((((measurable_coneScaledCorrection _).sub (measurable_coneScaledCorrection 0)).sub
        (measurable_coneCorrectionDeriv.const_mul _)).mul continuous_gaussDensity.measurable
        |>.const_mul _).abs.aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_abs]
      exact hpt a
  calc |∫ a, Real.sqrt N * ((coneScaledCorrection (1 / Real.sqrt N) a - coneScaledCorrection 0 a -
        1 / Real.sqrt N * coneCorrectionDeriv a) * gaussDensity a)|
      ≤ ∫ a, |Real.sqrt N * ((coneScaledCorrection (1 / Real.sqrt N) a -
          coneScaledCorrection 0 a - 1 / Real.sqrt N * coneCorrectionDeriv a) * gaussDensity a)| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ a, 1 / Real.sqrt N * (coneQuadEnvelope a * gaussDensity a) :=
        integral_mono hleft hdom hpt
    _ = coneQuadConst / Real.sqrt N := by
        rw [integral_const_mul]
        unfold coneQuadConst
        ring

/-- ★★★ **The second coefficient**: `N(E_N − ½ − 1/(√π√N)) → c₂ = ∫ G γ`. -/
theorem tendsto_cone_second_coeff :
    Tendsto (fun N : ℝ => N * ((∫ a, coneNumSq N a / coneDen N a * gaussDensity a) - 1 / 2 -
      1 / (Real.sqrt Real.pi * Real.sqrt N))) atTop (𝓝 coneSecondCoeff) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun N : ℝ => coneQuadConst * (1 / Real.sqrt N)) atTop (𝓝 0) := by
    have := tendsto_one_div_sqrt.const_mul coneQuadConst
    simpa using this
  refine squeeze_zero' (Eventually.of_forall fun N => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with N hN
  rw [Real.norm_eq_abs]
  refine (cone_second_coeff_bound hN).trans (le_of_eq ?_)
  ring

end Grammar
