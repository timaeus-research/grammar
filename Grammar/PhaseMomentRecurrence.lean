/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.MomentRecurrence

/-!
# Phase-dressed moment recurrence (unit 331; Astra #39 unit 9)

The zero-order phase moments `J_{ν,i}(a) = ∫_0^∞ t^{ν−1}(−log t)^i e^{−βt + β√t a} dt`
(`fluctMoment β a 0 ν i`) satisfy the exponent recurrence
```
J_{ν+1,i}(a) = (ν J_{ν,i}(a) − i J_{ν,i−1}(a))/β + (a/2) J_{ν+1/2,i}(a)
```
(`fluctMoment_succ_exponent_phase`): integration by parts against `−e^{−βt+β√t a}/β`, whose
derivative carries the extra `−a/(2√t)` factor that produces the half-shifted moment. Valid for
`β > 0`, `ν > 0`, every real phase `a` and every `i` (the `i = 0` term reads as zero); at `a = 0`
it is `fluctMoment_succ_exponent`. The phase derivative is `∂_a J_{ν,i}(a) = β J_{ν+1/2,i}(a)`
(`hasDerivAt_fluctMoment_phase`; differentiation under the integral, dominated on `|a − a₀| < 1` by
the moment with phase `|a₀| + 1`). Boundary terms vanish by `t^ν(−log t)^i → 0` at `0⁺` and by the
Gaussian-type domination `e^{−βt+β√t a} ≤ e^{βa²/2} e^{−βt/2}` at `∞`. This is the kernel identity
for a constant-phase coefficient transport; the transport itself is not attempted here. Zero
`sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

/-- `phaseKernel` at phase order zero. -/
theorem phaseKernel_zero (β a t : ℝ) :
    phaseKernel β a 0 t = Real.exp (-(β * t) + β * Real.sqrt t * a) := by
  simp [phaseKernel]

/-- The kernel exponent `−βt + β√t a` and its derivative on `t > 0`. -/
theorem hasDerivAt_phaseExponent (β a : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t => -(β * t) + β * Real.sqrt t * a)
      (-β + β * (1 / (2 * Real.sqrt t)) * a) t := by
  have h1 : HasDerivAt (fun t : ℝ => -(β * t)) (-β) t := by
    have h0 := ((hasDerivAt_id t).const_mul β).neg
    refine (h0.congr_deriv (by simp)).congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
    simp
  have h2 : HasDerivAt (fun t : ℝ => β * Real.sqrt t * a) (β * (1 / (2 * Real.sqrt t)) * a) t :=
    ((Real.hasDerivAt_sqrt ht.ne').const_mul β).mul_const a
  exact h1.add h2

/-- `t^μ (−log t)^i e^{−βt+β√t a} → 0` as `t → 0⁺` for `μ > 0`. -/
theorem tendsto_powNegLog_phase_nhdsGT_zero {μ : ℝ} (hμ : 0 < μ) (i : ℕ) (β a : ℝ) :
    Tendsto (fun t : ℝ => t ^ μ * (-Real.log t) ^ i * Real.exp (-(β * t) + β * Real.sqrt t * a))
      (𝓝[>] 0) (𝓝 0) := by
  have h1 := tendsto_powNegLog_exp_nhdsGT_zero hμ i β
  have h2 : Tendsto (fun t : ℝ => Real.exp (β * Real.sqrt t * a)) (𝓝[>] 0) (𝓝 1) := by
    have : Tendsto (fun t : ℝ => Real.exp (β * Real.sqrt t * a)) (𝓝 0)
        (𝓝 (Real.exp (β * Real.sqrt 0 * a))) :=
      (Real.continuous_exp.comp ((continuous_const.mul Real.continuous_sqrt).mul
        continuous_const)).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  have := h1.mul h2
  rw [zero_mul] at this
  refine this.congr' (Eventually.of_forall fun t => ?_)
  rw [mul_assoc, ← Real.exp_add]

/-- `t^μ (−log t)^i e^{−βt+β√t a} → 0` as `t → ∞` for `β > 0`. -/
theorem tendsto_powNegLog_phase_atTop (μ : ℝ) (i : ℕ) {β : ℝ} (hβ : 0 < β) (a : ℝ) :
    Tendsto (fun t : ℝ => t ^ μ * (-Real.log t) ^ i * Real.exp (-(β * t) + β * Real.sqrt t * a))
      atTop (𝓝 0) := by
  have hmaj := ((tendsto_powNegLog_exp_atTop μ i (half_pos hβ)).const_mul
    (Real.exp (β * a ^ 2 / 2))).norm
  rw [mul_zero, norm_zero] at hmaj
  refine squeeze_zero_norm' ?_ hmaj
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  have ht0 : 0 ≤ t := by linarith
  have hK := phaseKernel_le β a hβ 0 ht0
  rw [phaseKernel_zero, pow_zero, one_mul] at hK
  simp only [Real.norm_eq_abs, abs_mul, Real.abs_exp]
  have hnn : 0 ≤ |t ^ μ| * |(-Real.log t) ^ i| := by positivity
  calc |t ^ μ| * |(-Real.log t) ^ i| * Real.exp (-(β * t) + β * Real.sqrt t * a)
      ≤ |t ^ μ| * |(-Real.log t) ^ i| * (Real.exp (β * a ^ 2 / 2) * Real.exp (-(β * t / 2))) :=
        mul_le_mul_of_nonneg_left hK hnn
    _ = Real.exp (β * a ^ 2 / 2) * (|t ^ μ| * |(-Real.log t) ^ i| * Real.exp (-(β / 2 * t))) := by
        rw [show -(β * t / 2) = -(β / 2 * t) by ring]
        ring

/-- **The phase-dressed exponent recurrence**
`J_{μ+1,i}(a) = (μ J_{μ,i}(a) − i J_{μ,i−1}(a))/β + (a/2) J_{μ+1/2,i}(a)` for `μ > 0`, `β > 0`. -/
theorem fluctMoment_succ_exponent_phase {β : ℝ} (hβ : 0 < β) {μ : ℝ} (hμ : 0 < μ) (a : ℝ)
    (i : ℕ) :
    fluctMoment β a 0 (μ + 1) i =
      (μ * fluctMoment β a 0 μ i - (i : ℝ) * fluctMoment β a 0 μ (i - 1)) / β +
        a / 2 * fluctMoment β a 0 (μ + 1 / 2) i := by
  set u : ℝ → ℝ := fun t => t ^ μ * (-Real.log t) ^ i with hu
  set u' : ℝ → ℝ := fun t => μ * t ^ (μ - 1) * (-Real.log t) ^ i -
    (i : ℝ) * t ^ (μ - 1) * (-Real.log t) ^ (i - 1) with hu'
  set v : ℝ → ℝ := fun t => -(Real.exp (-(β * t) + β * Real.sqrt t * a) / β) with hv
  set v' : ℝ → ℝ := fun t => Real.exp (-(β * t) + β * Real.sqrt t * a) *
    (1 - a / (2 * Real.sqrt t)) with hv'
  have hud : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt u (u' t) t := fun t ht => hasDerivAt_powNegLog μ i ht
  have hvd : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt v (v' t) t := by
    intro t ht
    have ht0 : 0 < t := ht
    have hst : Real.sqrt t ≠ 0 := (Real.sqrt_pos.2 ht0).ne'
    have hd := (((hasDerivAt_phaseExponent β a ht0).exp).div_const β).neg
    refine hd.congr_deriv ?_
    simp only [hv']
    field_simp
    ring
  have hA := integrableOn_fluct β a hβ 0 hμ i
  have hB := integrableOn_fluct β a hβ 0 hμ (i - 1)
  have hC := integrableOn_fluct β a hβ 0 (ν := μ + 1) (by linarith) i
  have hD := integrableOn_fluct β a hβ 0 (ν := μ + 1 / 2) (by linarith) i
  simp only [phaseKernel_zero] at hA hB hC hD
  -- the pointwise identity behind `u v'`
  have hpt : ∀ t ∈ Ioi (0 : ℝ),
      t ^ (μ + 1 - 1) * (-Real.log t) ^ i * Real.exp (-(β * t) + β * Real.sqrt t * a) -
        a / 2 * (t ^ (μ + 1 / 2 - 1) * (-Real.log t) ^ i *
          Real.exp (-(β * t) + β * Real.sqrt t * a)) = u t * v' t := by
    intro t ht
    have ht0 : 0 < t := ht
    have hst : 0 < Real.sqrt t := Real.sqrt_pos.2 ht0
    have hsq : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht0.le
    have hhalf : t ^ (μ + 1 / 2 - 1) = t ^ μ / Real.sqrt t := by
      rw [show μ + 1 / 2 - 1 = μ - 1 / 2 by ring, Real.rpow_sub ht0, Real.sqrt_eq_rpow]
    simp only [hu, hv', add_sub_cancel_right, hhalf]
    field_simp
  have hI1 : IntegrableOn (fun t => u t * v' t) (Ioi 0) :=
    (hC.sub (hD.const_mul (a / 2))).congr_fun (fun t ht => hpt t ht) measurableSet_Ioi
  have hI2 : IntegrableOn (fun t => u' t * v t) (Ioi 0) := by
    have hh := ((hA.const_mul μ).sub (hB.const_mul (i : ℝ))).const_mul (-(1 / β))
    refine IntegrableOn.congr_fun hh (fun t _ => ?_) measurableSet_Ioi
    simp only [hu', hv, Pi.sub_apply]
    field_simp
  have h0 : Tendsto (fun t => u t * v t) (𝓝[>] 0) (𝓝 0) := by
    have := ((tendsto_powNegLog_phase_nhdsGT_zero hμ i β a).div_const β).neg
    rw [zero_div, neg_zero] at this
    refine this.congr' (Eventually.of_forall fun t => ?_)
    simp only [hu, hv]
    ring
  have hinf : Tendsto (fun t => u t * v t) atTop (𝓝 0) := by
    have := ((tendsto_powNegLog_phase_atTop μ i hβ a).div_const β).neg
    rw [zero_div, neg_zero] at this
    refine this.congr' (Eventually.of_forall fun t => ?_)
    simp only [hu, hv]
    ring
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul hud hvd hI1 hI2 h0 hinf
  unfold fluctMoment
  simp only [phaseKernel_zero]
  have hL : ∫ t in Ioi (0 : ℝ), u t * v' t =
      (∫ t in Ioi (0 : ℝ), t ^ (μ + 1 - 1) * (-Real.log t) ^ i *
        Real.exp (-(β * t) + β * Real.sqrt t * a)) -
      a / 2 * ∫ t in Ioi (0 : ℝ), t ^ (μ + 1 / 2 - 1) * (-Real.log t) ^ i *
        Real.exp (-(β * t) + β * Real.sqrt t * a) := by
    rw [← integral_const_mul, ← integral_sub hC (hD.const_mul _)]
    exact (setIntegral_congr_fun measurableSet_Ioi fun t ht => hpt t ht).symm
  have hR : ∫ t in Ioi (0 : ℝ), u' t * v t =
      -((μ * ∫ t in Ioi (0 : ℝ), t ^ (μ - 1) * (-Real.log t) ^ i *
          Real.exp (-(β * t) + β * Real.sqrt t * a)) -
        (i : ℝ) * ∫ t in Ioi (0 : ℝ), t ^ (μ - 1) * (-Real.log t) ^ (i - 1) *
          Real.exp (-(β * t) + β * Real.sqrt t * a)) / β := by
    calc ∫ t in Ioi (0 : ℝ), u' t * v t = ∫ t in Ioi (0 : ℝ), -(1 / β) *
          (μ * (t ^ (μ - 1) * (-Real.log t) ^ i * Real.exp (-(β * t) + β * Real.sqrt t * a)) -
            (i : ℝ) * (t ^ (μ - 1) * (-Real.log t) ^ (i - 1) *
              Real.exp (-(β * t) + β * Real.sqrt t * a))) := by
          refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
          simp only [hu', hv]
          field_simp
      _ = _ := by
          rw [integral_const_mul, integral_sub (hA.const_mul μ) (hB.const_mul (i : ℝ)),
            integral_const_mul, integral_const_mul]
          ring
  rw [hL, hR] at hibp
  linear_combination hibp

/-- **Phase derivative** `∂_a J_{μ,i}(a) = β J_{μ+1/2,i}(a)` for `μ > 0`, `β > 0`. -/
theorem hasDerivAt_fluctMoment_phase {β : ℝ} (hβ : 0 < β) {μ : ℝ} (hμ : 0 < μ) (i : ℕ) (a₀ : ℝ) :
    HasDerivAt (fun a => fluctMoment β a 0 μ i) (β * fluctMoment β a₀ 0 (μ + 1 / 2) i) a₀ := by
  set F : ℝ → ℝ → ℝ := fun a t => t ^ (μ - 1) * (-Real.log t) ^ i *
    Real.exp (-(β * t) + β * Real.sqrt t * a) with hF
  set F' : ℝ → ℝ → ℝ := fun a t => t ^ (μ - 1) * (-Real.log t) ^ i *
    Real.exp (-(β * t) + β * Real.sqrt t * a) * (β * Real.sqrt t) with hF'
  set bound : ℝ → ℝ := fun t => β * ‖t ^ (μ + 1 / 2 - 1) * (-Real.log t) ^ i *
    Real.exp (-(β * t) + β * Real.sqrt t * (|a₀| + 1))‖ with hbound
  have hF'eq : ∀ a t, 0 < t → F' a t = β * (t ^ (μ + 1 / 2 - 1) * (-Real.log t) ^ i *
      Real.exp (-(β * t) + β * Real.sqrt t * a)) := by
    intro a t ht0
    simp only [hF']
    rw [show μ + 1 / 2 - 1 = (μ - 1) + 1 / 2 by ring, Real.rpow_add ht0, Real.sqrt_eq_rpow]
    ring
  have hFmeas : ∀ a, AEStronglyMeasurable (F a) (volume.restrict (Ioi 0)) := by
    intro a
    have := integrableOn_fluct β a hβ 0 hμ i
    simp only [phaseKernel_zero] at this
    exact this.aestronglyMeasurable
  have hFint : Integrable (F a₀) (volume.restrict (Ioi 0)) := by
    have := integrableOn_fluct β a₀ hβ 0 hμ i
    simp only [phaseKernel_zero] at this
    exact this
  have hF'meas : AEStronglyMeasurable (F' a₀) (volume.restrict (Ioi 0)) := by
    have hint := integrableOn_fluct β a₀ hβ 0 (ν := μ + 1 / 2) (by linarith) i
    simp only [phaseKernel_zero] at hint
    exact (IntegrableOn.congr_fun (hint.const_mul β) (fun t ht => (hF'eq a₀ t ht).symm)
      measurableSet_Ioi).aestronglyMeasurable
  have hbound_int : Integrable bound (volume.restrict (Ioi 0)) := by
    have hint := integrableOn_fluct β (|a₀| + 1) hβ 0 (ν := μ + 1 / 2) (by linarith) i
    simp only [phaseKernel_zero] at hint
    exact hint.norm.const_mul β
  have hbound_le : ∀ᵐ t ∂(volume.restrict (Ioi 0)), ∀ a ∈ Metric.ball a₀ 1,
      ‖F' a t‖ ≤ bound t := by
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht a ha => ?_
    have ht0 : 0 < t := ht
    have ha' : a ≤ |a₀| + 1 := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt] at ha
      linarith [le_abs_self a₀]
    have hexp : Real.exp (-(β * t) + β * Real.sqrt t * a) ≤
        Real.exp (-(β * t) + β * Real.sqrt t * (|a₀| + 1)) := by
      rw [Real.exp_le_exp]
      have : β * Real.sqrt t * a ≤ β * Real.sqrt t * (|a₀| + 1) :=
        mul_le_mul_of_nonneg_left ha' (by positivity)
      linarith
    rw [hF'eq a t ht0]
    simp only [hbound, Real.norm_eq_abs, abs_mul, abs_of_pos hβ, Real.abs_exp]
    gcongr
  have hderiv : ∀ᵐ t ∂(volume.restrict (Ioi 0)), ∀ a ∈ Metric.ball a₀ 1,
      HasDerivAt (fun a => F a t) (F' a t) a := by
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun t _ a _ => ?_
    have hd := ((((hasDerivAt_id a).const_mul (β * Real.sqrt t)).const_add
      (-(β * t))).exp).const_mul (t ^ (μ - 1) * (-Real.log t) ^ i)
    refine (hd.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
    · simp only [hF', id]
      ring
    · simp only [hF, id]
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
    (F := F) (F' := F') (x₀ := a₀) (s := Metric.ball a₀ 1) (bound := bound)
    (Metric.ball_mem_nhds _ one_pos) (Eventually.of_forall hFmeas) hFint hF'meas hbound_le
    hbound_int hderiv
  have hfun : (fun a => fluctMoment β a 0 μ i) =
      fun a => ∫ t, F a t ∂(volume.restrict (Ioi 0)) := by
    funext a
    unfold fluctMoment
    simp only [phaseKernel_zero, hF]
  rw [hfun]
  refine key.2.congr_deriv ?_
  unfold fluctMoment
  simp only [phaseKernel_zero]
  rw [← integral_const_mul]
  exact setIntegral_congr_fun measurableSet_Ioi fun t ht => hF'eq a₀ t ht

end Grammar
