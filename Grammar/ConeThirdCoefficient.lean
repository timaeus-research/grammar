/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.ConeClosedForm
import Grammar.ConeAveragedPosterior

/-!
# The cone's third coefficient:
`Z_N = 4π²√(π/2) N^{−1/2} − 4π² N^{−1} + 2π²√(π/2) N^{−3/2} + o(N^{−3/2})`

At zero field the closed form of `ConeClosedForm` reads `Z_N = 4π² N^{−1/2} F(1/√N)` with
`F(x) = e^{x²/2} T(x)`, `T(c) = ∫_c^∞ e^{−s²/2} ds` (`cone_evidence_zero_field`).  The tail has
`T' = −e^{−x²/2}` (`hasDerivAt_gaussTailStd`, from the interval-integral fundamental theorem
after `T(x) = T(0) − ∫₀^x e^{−s²/2}`), so `F' = xF − 1` (`hasDerivAt_coneTailFactor`),
`F(0) = √(π/2)`, `F'(0) = −1`, `F''(0) = √(π/2)`, and one l'Hôpital step gives
`(F(x) − √(π/2) + x)/x² → √(π/2)/2` (★★ `tendsto_coneTailFactor_second`).  Hence

  ★★★ `cone_third_coefficient : N√N·(Z_N − 4π²√(π/2)/√N + 4π²/N) → 2π²√(π/2)`,

the coefficient `c₃ = 2π²√(π/2)` of `N^{−3/2}` in the cone's population expansion (examples_slop
§3; Astra round 27 target (v)).  Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

/-! ### The Gaussian tail -/

theorem integrable_exp_neg_sq_half : Integrable (fun s : ℝ => Real.exp (-s ^ 2 / 2)) := by
  have := integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)
  refine this.congr (Eventually.of_forall fun s => ?_)
  simp only
  ring_nf

/-- `T(0) = √(π/2)`. -/
theorem gaussTailStd_zero : gaussTailStd 0 = Real.sqrt (Real.pi / 2) := by
  unfold gaussTailStd
  have h := integral_gaussian_Ioi (1 / 2 : ℝ)
  rw [setIntegral_congr_fun measurableSet_Ioi (fun s _ => by
    rw [show -s ^ 2 / 2 = -(1 / 2) * s ^ 2 by ring]), h,
    show Real.pi / (1 / 2) = 2 ^ 2 * (Real.pi / 2) by ring, Real.sqrt_mul (by norm_num),
    Real.sqrt_sq (by norm_num)]
  ring

theorem gaussTailStd_eq (x : ℝ) :
    gaussTailStd x = gaussTailStd 0 - ∫ s in (0 : ℝ)..x, Real.exp (-s ^ 2 / 2) := by
  have hint := integrable_exp_neg_sq_half
  have h1 : ∀ c : ℝ, gaussTailStd c = (∫ s, Real.exp (-s ^ 2 / 2)) -
      ∫ s in Iic c, Real.exp (-s ^ 2 / 2) := by
    intro c
    unfold gaussTailStd
    rw [← integral_add_compl measurableSet_Iic hint, compl_Iic]
    ring
  rw [h1 x, h1 0, ← intervalIntegral.integral_Iic_sub_Iic hint.integrableOn hint.integrableOn]
  ring

theorem hasDerivAt_gaussTailStd (x : ℝ) :
    HasDerivAt gaussTailStd (-Real.exp (-x ^ 2 / 2)) x := by
  have hcont : Continuous (fun s : ℝ => Real.exp (-s ^ 2 / 2)) := by fun_prop
  have h := intervalIntegral.integral_hasDerivAt_right (hcont.intervalIntegrable 0 x)
    (hcont.stronglyMeasurableAtFilter volume (𝓝 x)) hcont.continuousAt
  have h2 := h.const_sub (gaussTailStd 0)
  exact h2.congr_of_eventuallyEq (Eventually.of_forall gaussTailStd_eq)

/-! ### `F(x) = e^{x²/2} T(x)` -/

/-- `F(x) = e^{x²/2} T(x)`, the closed form's shape function. -/
noncomputable def coneTailFactor (x : ℝ) : ℝ := Real.exp (x ^ 2 / 2) * gaussTailStd x

theorem coneTailFactor_zero : coneTailFactor 0 = Real.sqrt (Real.pi / 2) := by
  unfold coneTailFactor
  rw [gaussTailStd_zero]
  simp

/-- `F' = xF − 1`. -/
theorem hasDerivAt_coneTailFactor (x : ℝ) :
    HasDerivAt coneTailFactor (x * coneTailFactor x - 1) x := by
  have hE : HasDerivAt (fun x : ℝ => Real.exp (x ^ 2 / 2)) (Real.exp (x ^ 2 / 2) * x) x := by
    have := (((hasDerivAt_id' (x := x)).pow 2).div_const 2).exp
    refine this.congr_deriv ?_
    norm_num
  have := hE.mul (hasDerivAt_gaussTailStd x)
  unfold coneTailFactor
  refine this.congr_deriv ?_
  rw [mul_neg, ← Real.exp_add, show x ^ 2 / 2 + -x ^ 2 / 2 = 0 by ring, Real.exp_zero]
  ring

/-- ★★ `(F(x) − √(π/2) + x)/x² → √(π/2)/2` as `x → 0⁺`. -/
theorem tendsto_coneTailFactor_second :
    Tendsto (fun x : ℝ => (coneTailFactor x - Real.sqrt (Real.pi / 2) + x) / x ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.sqrt (Real.pi / 2) / 2)) := by
  refine HasDerivAt.lhopital_zero_nhdsGT (f' := fun x => x * coneTailFactor x)
    (g' := fun x => 2 * x) ?_ ?_ ?_ ?_ ?_ ?_
  · refine Eventually.of_forall fun x => ?_
    have := ((hasDerivAt_coneTailFactor x).sub_const (Real.sqrt (Real.pi / 2))).add
      (hasDerivAt_id' (x := x))
    refine this.congr_deriv ?_
    ring
  · refine Eventually.of_forall fun x => ?_
    have h : HasDerivAt (fun x : ℝ => x ^ 2) (((2 : ℕ) : ℝ) * x ^ (2 - 1) * 1) x :=
      (hasDerivAt_id' (x := x)).pow 2
    refine h.congr_deriv ?_
    norm_num
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact mul_ne_zero two_ne_zero (ne_of_gt hx)
  · have hc := (hasDerivAt_coneTailFactor 0).continuousAt
    have := ((hc.tendsto.sub_const (Real.sqrt (Real.pi / 2))).add tendsto_id).mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simpa [coneTailFactor_zero] using this
  · have : Tendsto (fun x : ℝ => x ^ 2) (𝓝 0) (𝓝 ((0 : ℝ) ^ 2)) := (continuous_pow 2).tendsto 0
    simpa using this.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  · have hc := (hasDerivAt_coneTailFactor 0).continuousAt
    have := (hc.tendsto.div_const 2).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    rw [coneTailFactor_zero] at this
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := ne_of_gt hx
    field_simp

/-! ### The cone at zero field -/

/-- `Z_N(0) = 4π² N^{−1/2} F(1/√N)`. -/
theorem cone_evidence_zero_field {N : ℝ} (hN : 0 < N) :
    ∫ u : (ℝ × ℝ) × (ℝ × ℝ),
        Real.exp (-N * coneQ u ^ 2 / 2 + Real.sqrt N * coneQ u * 0) * gaussW u =
      4 * Real.pi ^ 2 * (Real.sqrt N)⁻¹ * coneTailFactor (1 / Real.sqrt N) := by
  rw [cone_evidence_closed hN 0]
  unfold coneTailFactor
  simp only [zero_sub, zero_add, sub_zero, add_zero, neg_sq]
  ring

theorem tendsto_one_div_sqrt_nhdsGT :
    Tendsto (fun N : ℝ => 1 / Real.sqrt N) atTop (𝓝[>] (0 : ℝ)) := by
  refine tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_sqrt, ?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with N hN
  exact one_div_pos.2 (Real.sqrt_pos.2 hN)

/-- ★★★ **The cone's third coefficient**: `c₃ = 2π²√(π/2)`, i.e.
`N√N·(Z_N − 4π²√(π/2)/√N + 4π²/N) → 2π²√(π/2)`. -/
theorem cone_third_coefficient :
    Tendsto (fun N : ℝ => N * Real.sqrt N *
      ((∫ u : (ℝ × ℝ) × (ℝ × ℝ),
        Real.exp (-N * coneQ u ^ 2 / 2 + Real.sqrt N * coneQ u * 0) * gaussW u) -
        4 * Real.pi ^ 2 * Real.sqrt (Real.pi / 2) / Real.sqrt N + 4 * Real.pi ^ 2 / N))
      atTop (𝓝 (2 * Real.pi ^ 2 * Real.sqrt (Real.pi / 2))) := by
  have h := (tendsto_coneTailFactor_second.comp tendsto_one_div_sqrt_nhdsGT).const_mul
    (4 * Real.pi ^ 2)
  rw [show 4 * Real.pi ^ 2 * (Real.sqrt (Real.pi / 2) / 2) =
    2 * Real.pi ^ 2 * Real.sqrt (Real.pi / 2) by ring] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with N hN
  simp only [Function.comp_apply]
  rw [cone_evidence_zero_field hN]
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 hN
  have hN2 : N = Real.sqrt N ^ 2 := (Real.sq_sqrt hN.le).symm
  set s := Real.sqrt N with hsdef
  clear_value s
  rw [hN2]
  field_simp

end Grammar
