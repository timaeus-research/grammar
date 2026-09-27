/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.GaussianAbsMean

/-!
# The cone: the exact second coefficient `c₂ = −5/6 + √3/π`

With `m(a) = a b(a) + 2γ(a)` (`coneAbsMean_eq`), `b = 2∫₀^a γ`, the moment `∫ m² γ` reduces to
three Gaussian integrations by parts on the whole line (Mathlib's
`integral_mul_deriv_eq_deriv_mul_of_integrable` and `integral_of_hasDerivAt_of_tendsto`):

* `B = ∫ b² γ = ⅓`  (`(b³/6)' = b² γ`, `b(±∞) = ±1`);
* `I = ∫ a b γ² = ∫ γ³ = H`  (`(−γ²/2)' = a γ²`, `b' = 2γ`);
* `∫ a² b² γ = B + 4I`  (`(−γ)' = a γ`, `(a b²)' = b² + 4 a b γ`);
* `H = ∫ γ³ = 1/(2π√3)`  (a Gaussian integral).

Hence `∫ m² γ = B + 8I + 4H = ⅓ + 12H = ⅓ + 2√3/π` (★★ `integral_coneAbsMean_sq`) and, by the
symmetric form `c₂ = −½∫(a² + 1 − m²)γ` (DCXL) with `∫ a² γ = ∫ γ = 1`,

  `c₂ = −5/6 + √3/π = −0.28200`   (★★★ `coneSecondCoeff_eq`),

so the averaged cone posterior is `½ + 1/(√π√N) + (−5/6 + √3/π)/N + O(N^{−3/2})`
(examples_slop §3; Astra round-13 target 1).  Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

/-! ### Integrability of the pieces -/

theorem integrable_sq_mul_gaussDensity : Integrable (fun a : ℝ => a ^ 2 * gaussDensity a) := by
  have := integrable_sq_mul_exp_neg_half_sq.div_const (Real.sqrt (2 * Real.pi))
  refine this.congr (Eventually.of_forall fun a => ?_)
  unfold gaussDensity
  simp only
  ring

theorem integrable_mul_gaussDensity : Integrable (fun a : ℝ => a * gaussDensity a) := by
  have := integrable_mul_exp_neg_half_sq.div_const (Real.sqrt (2 * Real.pi))
  refine this.congr (Eventually.of_forall fun a => ?_)
  unfold gaussDensity
  simp only
  ring

/-- Multiplying an integrable function by a bounded continuous one keeps it integrable. -/
theorem integrable_mul_of_bounded {g f : ℝ → ℝ} (hg : Integrable g) (hf : Continuous f) {C : ℝ}
    (hC : ∀ x, |f x| ≤ C) : Integrable (fun x => f x * g x) :=
  hg.bdd_mul hf.aestronglyMeasurable (Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs]; exact hC x)

theorem abs_coneB_sq_le (a : ℝ) : |coneB a ^ 2| ≤ 1 := by
  rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) (abs_coneB_le a)

theorem integrable_coneB_sq_mul_gaussDensity :
    Integrable (fun a : ℝ => coneB a ^ 2 * gaussDensity a) :=
  integrable_mul_of_bounded (f := fun a => coneB a ^ 2) integrable_gaussDensity
    (continuous_coneB.pow 2) abs_coneB_sq_le

theorem integrable_gaussDensity_sq : Integrable (fun a : ℝ => gaussDensity a ^ 2) := by
  have := integrable_mul_of_bounded (f := gaussDensity) integrable_gaussDensity
    continuous_gaussDensity (C := 1) fun a => by
      rw [abs_of_nonneg (gaussDensity_nonneg a)]; exact gaussDensity_le_one a
  refine this.congr (Eventually.of_forall fun a => ?_)
  simp only
  ring

theorem integrable_mul_coneB_mul_gaussDensity_sq :
    Integrable (fun a : ℝ => a * coneB a * gaussDensity a ^ 2) := by
  have := integrable_mul_of_bounded (f := fun a => coneB a * gaussDensity a)
    integrable_mul_gaussDensity (continuous_coneB.mul continuous_gaussDensity) (C := 1) fun a => by
      rw [abs_mul, abs_of_nonneg (gaussDensity_nonneg a)]
      exact mul_le_one₀ (abs_coneB_le a) (gaussDensity_nonneg a) (gaussDensity_le_one a)
  refine this.congr (Eventually.of_forall fun a => ?_)
  simp only
  ring

theorem integrable_gaussDensity_cube : Integrable (fun a : ℝ => gaussDensity a ^ 3) := by
  have := integrable_mul_of_bounded (f := fun a => gaussDensity a ^ 2) integrable_gaussDensity
    (continuous_gaussDensity.pow 2) (C := 1) fun a => by
      rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) (by
        rw [abs_of_nonneg (gaussDensity_nonneg a)]; exact gaussDensity_le_one a)
  refine this.congr (Eventually.of_forall fun a => ?_)
  simp only
  ring

theorem integrable_sq_mul_coneB_sq_mul_gaussDensity :
    Integrable (fun a : ℝ => a ^ 2 * coneB a ^ 2 * gaussDensity a) := by
  have := integrable_mul_of_bounded (f := fun a => coneB a ^ 2) integrable_sq_mul_gaussDensity
    (continuous_coneB.pow 2) abs_coneB_sq_le
  refine this.congr (Eventually.of_forall fun a => ?_)
  simp only
  ring

/-! ### The three integrations by parts and the Gaussian cube -/

/-- `B = ∫ b² γ = ⅓`. -/
theorem integral_coneB_sq_mul_gaussDensity : ∫ a, coneB a ^ 2 * gaussDensity a = 1 / 3 := by
  have h := integral_of_hasDerivAt_of_tendsto (f := fun a => coneB a ^ 3 / 6)
    (f' := fun a => coneB a ^ 2 * gaussDensity a) (fun a => ?_)
    integrable_coneB_sq_mul_gaussDensity ((tendsto_coneB_atBot.pow 3).div_const 6)
    ((tendsto_coneB_atTop.pow 3).div_const 6)
  · rw [h]; norm_num
  · refine (((hasDerivAt_coneB a).pow 3).div_const 6).congr_deriv ?_
    simp only [Nat.cast_ofNat]
    ring

/-- `I = ∫ a b γ² = ∫ γ³`. -/
theorem integral_mul_coneB_mul_gaussDensity_sq :
    ∫ a, a * coneB a * gaussDensity a ^ 2 = ∫ a, gaussDensity a ^ 3 := by
  have hv : ∀ a : ℝ, HasDerivAt (fun a => -gaussDensity a ^ 2 / 2) (a * gaussDensity a ^ 2) a := by
    intro a
    refine (((hasDerivAt_gaussDensity a).pow 2).neg.div_const 2).congr_deriv ?_
    simp only [Nat.cast_ofNat]
    ring
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable (u := coneB)
    (u' := fun a => 2 * gaussDensity a) (v := fun a => -gaussDensity a ^ 2 / 2)
    (v' := fun a => a * gaussDensity a ^ 2) (fun a _ => hasDerivAt_coneB a) (fun a _ => hv a)
    ?_ ?_ ?_
  · have e1 : (fun a : ℝ => coneB a * (a * gaussDensity a ^ 2)) =
        fun a => a * coneB a * gaussDensity a ^ 2 := by funext a; ring
    have e2 : (fun a : ℝ => 2 * gaussDensity a * (-gaussDensity a ^ 2 / 2)) =
        fun a => -(gaussDensity a ^ 3) := by funext a; ring
    rw [e1, e2, integral_neg, neg_neg] at h
    exact h
  · refine integrable_mul_coneB_mul_gaussDensity_sq.congr (Eventually.of_forall fun a => ?_)
    simp only [Pi.mul_apply]
    ring
  · refine integrable_gaussDensity_cube.neg.congr (Eventually.of_forall fun a => ?_)
    simp only [Pi.mul_apply, Pi.neg_apply]
    ring
  · have := integrable_mul_of_bounded (f := coneB) integrable_gaussDensity_sq continuous_coneB
      abs_coneB_le
    refine (this.const_mul (-(1 / 2))).congr (Eventually.of_forall fun a => ?_)
    simp only [Pi.mul_apply]
    ring

/-- `∫ a² b² γ = ∫ b² γ + 4 ∫ a b γ²`. -/
theorem integral_sq_mul_coneB_sq_mul_gaussDensity :
    ∫ a, a ^ 2 * coneB a ^ 2 * gaussDensity a =
      (∫ a, coneB a ^ 2 * gaussDensity a) + 4 * ∫ a, a * coneB a * gaussDensity a ^ 2 := by
  have hu : ∀ a : ℝ, HasDerivAt (fun a => a * coneB a ^ 2)
      (coneB a ^ 2 + 4 * a * coneB a * gaussDensity a) a := by
    intro a
    refine ((hasDerivAt_id a).mul ((hasDerivAt_coneB a).pow 2)).congr_deriv ?_
    simp only [Nat.cast_ofNat, id, Pi.pow_apply]
    ring
  have hv : ∀ a : ℝ, HasDerivAt (fun a => -gaussDensity a) (a * gaussDensity a) a := by
    intro a
    refine (hasDerivAt_gaussDensity a).neg.congr_deriv ?_
    ring
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable (u := fun a => a * coneB a ^ 2)
    (u' := fun a => coneB a ^ 2 + 4 * a * coneB a * gaussDensity a) (v := fun a => -gaussDensity a)
    (v' := fun a => a * gaussDensity a) (fun a _ => hu a) (fun a _ => hv a) ?_ ?_ ?_
  · have e1 : (fun a : ℝ => a * coneB a ^ 2 * (a * gaussDensity a)) =
        fun a => a ^ 2 * coneB a ^ 2 * gaussDensity a := by funext a; ring
    have e2 : (fun a : ℝ => (coneB a ^ 2 + 4 * a * coneB a * gaussDensity a) * -gaussDensity a) =
        fun a => -(coneB a ^ 2 * gaussDensity a + 4 * (a * coneB a * gaussDensity a ^ 2)) := by
      funext a; ring
    rw [e1, e2, integral_neg, neg_neg, integral_add integrable_coneB_sq_mul_gaussDensity
      (integrable_mul_coneB_mul_gaussDensity_sq.const_mul 4), integral_const_mul] at h
    exact h
  · refine integrable_sq_mul_coneB_sq_mul_gaussDensity.congr (Eventually.of_forall fun a => ?_)
    simp only [Pi.mul_apply]
    ring
  · refine (integrable_coneB_sq_mul_gaussDensity.add
      (integrable_mul_coneB_mul_gaussDensity_sq.const_mul 4)).neg.congr
      (Eventually.of_forall fun a => ?_)
    simp only [Pi.mul_apply, Pi.neg_apply, Pi.add_apply]
    ring
  · have := integrable_mul_of_bounded (f := fun a => coneB a ^ 2) integrable_mul_gaussDensity
      (continuous_coneB.pow 2) abs_coneB_sq_le
    refine this.neg.congr (Eventually.of_forall fun a => ?_)
    simp only [Pi.mul_apply, Pi.neg_apply]
    ring

/-- `H = ∫ γ³ = 1/(2π√3)`. -/
theorem integral_gaussDensity_cube : ∫ a, gaussDensity a ^ 3 = 1 / (2 * Real.pi * Real.sqrt 3) := by
  unfold gaussDensity
  have e : (fun a : ℝ => (Real.exp (-a ^ 2 / 2) / Real.sqrt (2 * Real.pi)) ^ 3) =
      fun a => (1 / Real.sqrt (2 * Real.pi) ^ 3) * Real.exp (-(3 / 2) * a ^ 2) := by
    funext a
    rw [div_pow, ← Real.exp_nat_mul]
    push_cast
    rw [show (3 : ℝ) * (-a ^ 2 / 2) = -(3 / 2) * a ^ 2 by ring]
    ring
  rw [e, integral_const_mul, integral_gaussian]
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have h3 : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hsq : Real.sqrt (2 * Real.pi) ^ 2 = 2 * Real.pi := Real.sq_sqrt (by positivity)
  have h3sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hdiv : Real.sqrt (Real.pi / (3 / 2)) = Real.sqrt (2 * Real.pi) / Real.sqrt 3 := by
    rw [← Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    ring
  rw [hdiv]
  field_simp
  nlinarith [hsq, h3sq]

/-! ### The moment `∫ m² γ` and the value -/

theorem integrable_coneAbsMean_sq_mul_gaussDensity :
    Integrable (fun a : ℝ => coneAbsMean a ^ 2 * gaussDensity a) := by
  simp_rw [coneAbsMean_eq]
  have e : (fun a : ℝ => (a * coneB a + 2 * gaussDensity a) ^ 2 * gaussDensity a) =
      fun a => a ^ 2 * coneB a ^ 2 * gaussDensity a + 4 * (a * coneB a * gaussDensity a ^ 2) +
        4 * gaussDensity a ^ 3 := by
    funext a; ring
  rw [e]
  exact (integrable_sq_mul_coneB_sq_mul_gaussDensity.add
    (integrable_mul_coneB_mul_gaussDensity_sq.const_mul 4)).add
    (integrable_gaussDensity_cube.const_mul 4)

/-- ★★ `∫ m(a)² γ(a) da = ⅓ + 2√3/π`. -/
theorem integral_coneAbsMean_sq :
    ∫ a, coneAbsMean a ^ 2 * gaussDensity a = 1 / 3 + 2 * Real.sqrt 3 / Real.pi := by
  simp_rw [coneAbsMean_eq]
  have e : (fun a : ℝ => (a * coneB a + 2 * gaussDensity a) ^ 2 * gaussDensity a) =
      fun a => a ^ 2 * coneB a ^ 2 * gaussDensity a + 4 * (a * coneB a * gaussDensity a ^ 2) +
        4 * gaussDensity a ^ 3 := by
    funext a; ring
  have h12 : Integrable (fun a : ℝ => a ^ 2 * coneB a ^ 2 * gaussDensity a +
      4 * (a * coneB a * gaussDensity a ^ 2)) :=
    integrable_sq_mul_coneB_sq_mul_gaussDensity.add
      (integrable_mul_coneB_mul_gaussDensity_sq.const_mul 4)
  rw [e, integral_add h12 (integrable_gaussDensity_cube.const_mul 4),
    integral_add integrable_sq_mul_coneB_sq_mul_gaussDensity
    (integrable_mul_coneB_mul_gaussDensity_sq.const_mul 4), integral_const_mul, integral_const_mul,
    integral_sq_mul_coneB_sq_mul_gaussDensity, integral_coneB_sq_mul_gaussDensity,
    integral_mul_coneB_mul_gaussDensity_sq, integral_gaussDensity_cube]
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have h3' : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  field_simp
  nlinarith [h3]

theorem integral_sq_mul_gaussDensity : ∫ a, a ^ 2 * gaussDensity a = 1 := by
  unfold gaussDensity
  have e : (fun a : ℝ => a ^ 2 * (Real.exp (-a ^ 2 / 2) / Real.sqrt (2 * Real.pi))) =
      fun a => (a ^ 2 * Real.exp (-(1 : ℝ) * a ^ 2 / 2)) / Real.sqrt (2 * Real.pi) := by
    funext a; ring_nf
  rw [e, integral_div, integral_sq_exp_cond one_pos, Real.sqrt_one]
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  field_simp

/-- ★★★ **The exact second coefficient of the averaged cone posterior**: `c₂ = −5/6 + √3/π`. -/
theorem coneSecondCoeff_eq : coneSecondCoeff = -(5 / 6 : ℝ) + Real.sqrt 3 / Real.pi := by
  rw [coneSecondCoeff_eq_symmetric]
  have e : (fun a : ℝ => (a ^ 2 + 1 - coneAbsMean a ^ 2) * gaussDensity a) =
      fun a => (a ^ 2 * gaussDensity a + gaussDensity a) - coneAbsMean a ^ 2 * gaussDensity a := by
    funext a; ring
  have hAB : Integrable (fun a : ℝ => a ^ 2 * gaussDensity a + gaussDensity a) :=
    integrable_sq_mul_gaussDensity.add integrable_gaussDensity
  rw [e, integral_sub hAB integrable_coneAbsMean_sq_mul_gaussDensity,
    integral_add integrable_sq_mul_gaussDensity
    integrable_gaussDensity, integral_sq_mul_gaussDensity, integral_gaussDensity,
    integral_coneAbsMean_sq]
  ring

end Grammar
