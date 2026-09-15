/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.EmpiricalPieceIntegral

/-!
# Lipschitz dependence of the empirical box integral on the field

For `σ ≥ 0` and `|a|, |b| ≤ M` the mean value theorem gives
`|e^{−σ² + σa} − e^{−σ² + σb}| ≤ σ e^{−σ² + σM} |a − b|`, and `σM ≤ σ²/4 + M²`,
`σ e^{−σ²/4} ≤ 1` turn this into `e^{M²} |a − b| e^{−σ²/2}` (`abs_exp_field_sub_le`). With
`σ = √N u^k` the empirical box integrals of two fields within `δ` on the box therefore differ by
at most `e^{M²} δ A · empBoxIntegral h k (N/2) b 0 1`, the half-temperature zero-field integral
(`abs_empBoxIntegral_sub_le`). Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

/-- `σ e^{−σ²/4} ≤ 1` for `σ ≥ 0`. -/
theorem mul_exp_neg_sq_div_four_le_one {σ : ℝ} (hσ : 0 ≤ σ) :
    σ * Real.exp (-(σ ^ 2 / 4)) ≤ 1 := by
  have hq := Real.quadratic_le_exp_of_nonneg (x := σ ^ 2 / 2) (by positivity)
  have h1 : σ ^ 2 ≤ Real.exp (σ ^ 2 / 2) := by nlinarith [sq_nonneg (σ ^ 2 / 2 - 1)]
  have h2 : (σ * Real.exp (-(σ ^ 2 / 4))) ^ 2 ≤ 1 := by
    rw [mul_pow, ← Real.exp_nat_mul]
    have : ((2 : ℕ) : ℝ) * -(σ ^ 2 / 4) = -(σ ^ 2 / 2) := by push_cast; ring
    rw [this, Real.exp_neg]
    rw [← div_eq_mul_inv, div_le_one (Real.exp_pos _)]
    exact h1
  have h0 : 0 ≤ σ * Real.exp (-(σ ^ 2 / 4)) := mul_nonneg hσ (Real.exp_pos _).le
  nlinarith

/-- **Field Lipschitz bound**: for `σ ≥ 0` and `|a|, |b| ≤ M`,
`|e^{−σ² + σa} − e^{−σ² + σb}| ≤ e^{M²} |a − b| e^{−σ²/2}`. -/
theorem abs_exp_field_sub_le {σ M a b : ℝ} (hσ : 0 ≤ σ) (ha : |a| ≤ M) (hb : |b| ≤ M) :
    |Real.exp (-σ ^ 2 + σ * a) - Real.exp (-σ ^ 2 + σ * b)| ≤
      Real.exp (M ^ 2) * |a - b| * Real.exp (-(σ ^ 2 / 2)) := by
  have hM0 : 0 ≤ M := (abs_nonneg a).trans ha
  set f : ℝ → ℝ := fun c => Real.exp (-σ ^ 2 + σ * c) with hf
  have hderiv : ∀ c, HasDerivAt f (Real.exp (-σ ^ 2 + σ * c) * σ) c := fun c => by
    have := (((hasDerivAt_id c).const_mul σ).const_add (-σ ^ 2)).exp
    simpa [hf] using this
  have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le (f := f) (s := Icc (-M) M)
    (C := Real.exp (M ^ 2) * Real.exp (-(σ ^ 2 / 2)))
    (fun c _ => (hderiv c).differentiableAt) ?_ (convex_Icc _ _) (abs_le.1 hb) (abs_le.1 ha)
  · rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmvt
    calc |Real.exp (-σ ^ 2 + σ * a) - Real.exp (-σ ^ 2 + σ * b)| = |f a - f b| := rfl
      _ ≤ Real.exp (M ^ 2) * Real.exp (-(σ ^ 2 / 2)) * |a - b| := hmvt
      _ = Real.exp (M ^ 2) * |a - b| * Real.exp (-(σ ^ 2 / 2)) := by ring
  · intro c hc
    rw [(hderiv c).deriv, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_nonneg hσ]
    have hc' : σ * c ≤ σ * M := mul_le_mul_of_nonneg_left hc.2 hσ
    have hamgm : σ * M ≤ σ ^ 2 / 4 + M ^ 2 := by nlinarith [sq_nonneg (σ / 2 - M)]
    have hσe := mul_exp_neg_sq_div_four_le_one hσ
    calc Real.exp (-σ ^ 2 + σ * c) * σ
        ≤ Real.exp (M ^ 2) * Real.exp (-(σ ^ 2 / 2)) * (Real.exp (-(σ ^ 2 / 4)) * σ) := by
          rw [← mul_assoc, ← Real.exp_add, ← Real.exp_add]
          exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (by linarith)) hσ
      _ ≤ Real.exp (M ^ 2) * Real.exp (-(σ ^ 2 / 2)) * 1 := by
          gcongr
          rw [mul_comm]; exact hσe
      _ = Real.exp (M ^ 2) * Real.exp (-(σ ^ 2 / 2)) := mul_one _

/-- **Lipschitz dependence of the empirical box integral on the field**: for continuous fields
`ξ, ζ` bounded by `M` and within `δ` on the box, and `|η| ≤ A`,
`|empBoxIntegral h k N b ξ η − empBoxIntegral h k N b ζ η| ≤
  e^{M²} δ A · empBoxIntegral h k (N/2) b 0 1`. -/
theorem abs_empBoxIntegral_sub_le {d : ℕ} (h k : Fin d → ℕ) {N b : ℝ} (hN : 0 ≤ N)
    {ξ ζ η : (Fin d → ℝ) → ℝ} (hξc : Continuous ξ) (hζc : Continuous ζ) (hηc : Continuous η)
    {M δ A : ℝ} (hM : ∀ u ∈ SmoothEngine.box (Fin d) b, |ξ u| ≤ M)
    (hM' : ∀ u ∈ SmoothEngine.box (Fin d) b, |ζ u| ≤ M)
    (hδ : ∀ u ∈ SmoothEngine.box (Fin d) b, |ξ u - ζ u| ≤ δ)
    (hA : ∀ u ∈ SmoothEngine.box (Fin d) b, |η u| ≤ A) :
    |empBoxIntegral h k N b ξ η - empBoxIntegral h k N b ζ η| ≤
      Real.exp (M ^ 2) * δ * A * empBoxIntegral h k (N / 2) b (fun _ => 0) fun _ => 1 := by
  have hmh := SmoothEngine.continuous_mono (ι := Fin d) h
  have hm2 := SmoothEngine.continuous_mono (ι := Fin d) (fun i => 2 * k i)
  have hmk := SmoothEngine.continuous_mono (ι := Fin d) k
  have hbox : SmoothEngine.box (Fin d) b ⊆ SmoothEngine.closedBox d b :=
    SmoothEngine.box_subset_closedBox b
  have hintOf : ∀ φ : (Fin d → ℝ) → ℝ, Continuous φ →
      IntegrableOn (fun u : Fin d → ℝ => η u * SmoothEngine.mono h u *
        Real.exp (-N * SmoothEngine.mono (fun i => 2 * k i) u +
          Real.sqrt N * SmoothEngine.mono k u * φ u)) (SmoothEngine.box (Fin d) b) := by
    intro φ hφ
    have hc : Continuous fun u : Fin d → ℝ => η u * SmoothEngine.mono h u *
        Real.exp (-N * SmoothEngine.mono (fun i => 2 * k i) u +
          Real.sqrt N * SmoothEngine.mono k u * φ u) := by fun_prop
    exact (hc.continuousOn.integrableOn_compact (SmoothEngine.isCompact_closedBox b)).mono_set hbox
  have hcontG : Continuous fun u : Fin d → ℝ => Real.exp (M ^ 2) * δ * A *
      (1 * SmoothEngine.mono h u * Real.exp (-(N / 2) * SmoothEngine.mono (fun i => 2 * k i) u +
        Real.sqrt (N / 2) * SmoothEngine.mono k u * 0)) := by fun_prop
  have hintG : IntegrableOn (fun u : Fin d → ℝ => Real.exp (M ^ 2) * δ * A *
      (1 * SmoothEngine.mono h u * Real.exp (-(N / 2) * SmoothEngine.mono (fun i => 2 * k i) u +
        Real.sqrt (N / 2) * SmoothEngine.mono k u * 0))) (SmoothEngine.box (Fin d) b) :=
    (hcontG.continuousOn.integrableOn_compact (SmoothEngine.isCompact_closedBox b)).mono_set hbox
  unfold empBoxIntegral
  rw [← integral_sub (hintOf ξ hξc) (hintOf ζ hζc), ← integral_const_mul]
  have hle := norm_integral_le_of_norm_le (μ := volume.restrict (SmoothEngine.box (Fin d) b))
    (f := fun u : Fin d → ℝ => η u * SmoothEngine.mono h u *
      Real.exp (-N * SmoothEngine.mono (fun i => 2 * k i) u +
        Real.sqrt N * SmoothEngine.mono k u * ξ u) -
      η u * SmoothEngine.mono h u *
      Real.exp (-N * SmoothEngine.mono (fun i => 2 * k i) u +
        Real.sqrt N * SmoothEngine.mono k u * ζ u)) hintG ?_
  · rwa [Real.norm_eq_abs] at hle
  rw [ae_restrict_iff' (SmoothEngine.measurableSet_box b)]
  refine Eventually.of_forall fun u hu => ?_
  have hm1 : 0 ≤ SmoothEngine.mono k u :=
    Finset.prod_nonneg fun i _ => pow_nonneg (SmoothEngine.pos_of_mem_box hu i).le _
  have hmh0 : 0 ≤ SmoothEngine.mono h u :=
    Finset.prod_nonneg fun i _ => pow_nonneg (SmoothEngine.pos_of_mem_box hu i).le _
  set σ := Real.sqrt N * SmoothEngine.mono k u with hσdef
  have hσ : 0 ≤ σ := mul_nonneg (Real.sqrt_nonneg _) hm1
  have hσsq : σ ^ 2 = N * SmoothEngine.mono (fun i => 2 * k i) u := by
    rw [hσdef, mul_pow, Real.sq_sqrt hN, SmoothEngine.mono_two_mul_eq_sq]
  have hfield := abs_exp_field_sub_le hσ (hM u hu) (hM' u hu)
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA u hu)
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans (hδ u hu)
  have hδu : |ξ u - ζ u| ≤ δ := hδ u hu
  have hexp1 : -N * SmoothEngine.mono (fun i => 2 * k i) u + σ * ξ u = -σ ^ 2 + σ * ξ u := by
    rw [hσsq]; ring
  have hexp2 : -N * SmoothEngine.mono (fun i => 2 * k i) u + σ * ζ u = -σ ^ 2 + σ * ζ u := by
    rw [hσsq]; ring
  have hexp3 : -(N / 2) * SmoothEngine.mono (fun i => 2 * k i) u +
      Real.sqrt (N / 2) * SmoothEngine.mono k u * 0 = -(σ ^ 2 / 2) := by
    rw [hσsq]; ring
  rw [← mul_sub, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hmh0, hexp1, hexp2, hexp3]
  calc |η u| * SmoothEngine.mono h u * |Real.exp (-σ ^ 2 + σ * ξ u) - Real.exp (-σ ^ 2 + σ * ζ u)|
      ≤ A * SmoothEngine.mono h u * (Real.exp (M ^ 2) * δ * Real.exp (-(σ ^ 2 / 2))) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_right (hA u hu) hmh0)
          (hfield.trans ?_) (abs_nonneg _) (mul_nonneg hA0 hmh0)
        gcongr
    _ = Real.exp (M ^ 2) * δ * A * (1 * SmoothEngine.mono h u * Real.exp (-(σ ^ 2 / 2))) := by ring

end Grammar
