/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.PopulationGammaMoment
import Grammar.MonomialPhaseTail

/-!
# The exponent recurrence of the zero-phase moments (Programme Q, N2, unit 314)

The zero-phase kernel moments `M(μ,i) = fluctMoment β 0 0 μ i = ∫₀^∞ t^{μ−1}(−log t)^i e^{−βt} dt`
satisfy, for `μ > 0`, `β > 0`, the integration-by-parts recurrence
```
M(μ+1, i) = (μ M(μ, i) − i M(μ, i−1)) / β                     (fluctMoment_succ_exponent)
```
(`u = t^μ(−log t)^i`, `v' = e^{−βt}`; the boundary terms vanish at `0⁺` because `μ > 0` and at `∞`
by exponential decay). For `i = 0` the second term is `0 · M(μ, 0)`. This is the analytic input to
the coefficient transport `C_K(μ+1, j) = (μ C(μ,j) − (j+1) C(μ,j+1))/β` (unit 315): inserting the
energy `u^{2k}` shifts the state-density exponents by one and the kernel moments by one in `μ`. The
recurrence is stated only for `μ > 0` (Astra #38 / review v38: no totalised-integral shortcuts).
Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

/-- Derivative of `t^μ (−log t)^i` for `t > 0`. -/
theorem hasDerivAt_powNegLog (μ : ℝ) (i : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t => t ^ μ * (-Real.log t) ^ i)
      (μ * t ^ (μ - 1) * (-Real.log t) ^ i - (i : ℝ) * t ^ (μ - 1) * (-Real.log t) ^ (i - 1)) t :=
by
  have h1 : HasDerivAt (fun t : ℝ => t ^ μ) (μ * t ^ (μ - 1)) t :=
    Real.hasDerivAt_rpow_const (Or.inl ht.ne')
  have h2 : HasDerivAt (fun t : ℝ => (-Real.log t) ^ i)
      ((i : ℝ) * (-Real.log t) ^ (i - 1) * (-t⁻¹)) t :=
    ((Real.hasDerivAt_log ht.ne').neg).pow i
  refine (h1.mul h2).congr_deriv ?_
  rw [Real.rpow_sub_one ht.ne']
  field_simp
  ring

/-- `t^μ (−log t)^i e^{−βt} → 0` as `t → 0⁺` for `μ > 0`. -/
theorem tendsto_powNegLog_exp_nhdsGT_zero {μ : ℝ} (hμ : 0 < μ) (i : ℕ) (β : ℝ) :
    Tendsto (fun t : ℝ => t ^ μ * (-Real.log t) ^ i * Real.exp (-(β * t))) (𝓝[>] 0) (𝓝 0) := by
  have hexp : Tendsto (fun t : ℝ => Real.exp (-(β * t))) (𝓝[>] 0) (𝓝 1) := by
    have : Tendsto (fun t : ℝ => Real.exp (-(β * t))) (𝓝 0) (𝓝 (Real.exp (-(β * 0)))) :=
      (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  have hmain : Tendsto (fun t : ℝ => t ^ μ * (-Real.log t) ^ i) (𝓝[>] 0) (𝓝 0) := by
    rcases Nat.eq_zero_or_pos i with hi | hi
    · subst hi
      simp only [pow_zero, mul_one]
      have := (Real.continuousAt_rpow_const 0 μ (Or.inr hμ.le)).tendsto
      rw [Real.zero_rpow hμ.ne'] at this
      exact this.mono_left nhdsWithin_le_nhds
    · have hpos : (0 : ℝ) < μ / i := by positivity
      have h := ((tendsto_log_mul_rpow_nhdsGT_zero hpos).neg).pow i
      rw [neg_zero, zero_pow hi.ne'] at h
      refine h.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht0 : 0 < t := ht
      have hi' : (i : ℝ) ≠ 0 := by exact_mod_cast hi.ne'
      rw [neg_mul_eq_neg_mul, mul_pow, ← Real.rpow_natCast (t ^ (μ / i)) i, ← Real.rpow_mul ht0.le,
        div_mul_cancel₀ _ hi', mul_comm]
  simpa using hmain.mul hexp

/-- `t^μ (−log t)^i e^{−βt} → 0` as `t → ∞` for `β > 0`. -/
theorem tendsto_powNegLog_exp_atTop (μ : ℝ) (i : ℕ) {β : ℝ} (hβ : 0 < β) :
    Tendsto (fun t : ℝ => t ^ μ * (-Real.log t) ^ i * Real.exp (-(β * t))) atTop (𝓝 0) := by
  have hmaj := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (μ + i) β hβ
  refine squeeze_zero_norm' ?_ hmaj
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  have ht0 : 0 < t := by linarith
  have hlog0 : 0 ≤ Real.log t := Real.log_nonneg ht
  have hlogle : Real.log t ≤ t := (Real.log_le_sub_one_of_pos ht0).trans (by linarith)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht0 _),
    abs_of_pos (Real.exp_pos _), abs_pow, abs_neg, abs_of_nonneg hlog0, Real.rpow_add ht0,
    Real.rpow_natCast, show -β * t = -(β * t) by ring]
  gcongr

/-- **The exponent recurrence** `M(μ+1, i) = (μ M(μ,i) − i M(μ,i−1))/β` for `μ > 0`, `β > 0`. -/
theorem fluctMoment_succ_exponent {β : ℝ} (hβ : 0 < β) {μ : ℝ} (hμ : 0 < μ) (i : ℕ) :
    fluctMoment β 0 0 (μ + 1) i =
      (μ * fluctMoment β 0 0 μ i - (i : ℝ) * fluctMoment β 0 0 μ (i - 1)) / β := by
  set u : ℝ → ℝ := fun t => t ^ μ * (-Real.log t) ^ i with hu
  set u' : ℝ → ℝ := fun t => μ * t ^ (μ - 1) * (-Real.log t) ^ i -
    (i : ℝ) * t ^ (μ - 1) * (-Real.log t) ^ (i - 1) with hu'
  set v : ℝ → ℝ := fun t => -(Real.exp (-(β * t)) / β) with hv
  set v' : ℝ → ℝ := fun t => Real.exp (-(β * t)) with hv'
  have hud : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt u (u' t) t := fun t ht => hasDerivAt_powNegLog μ i ht
  have hvd : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt v (v' t) t := by
    intro t _
    have h1 : HasDerivAt (fun t : ℝ => -(β * t)) (-β) t := by
      have h0 := (hasDerivAt_id t).const_mul (-β)
      refine (h0.congr_deriv (by simp)).congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
      simp only [id]
      ring
    have h2 := (h1.exp.div_const β).neg
    refine h2.congr_deriv ?_
    simp only [hv']
    field_simp
  have hA := integrableOn_fluct β 0 hβ 0 hμ i
  have hB := integrableOn_fluct β 0 hβ 0 hμ (i - 1)
  simp only [phaseKernel_zero_zero] at hA hB
  have hI1 : IntegrableOn (fun t => u t * v' t) (Ioi 0) := by
    have := integrableOn_fluct β 0 hβ 0 (ν := μ + 1) (by linarith) i
    simp only [phaseKernel_zero_zero] at this
    refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only [hu, hv', add_sub_cancel_right]
  have hI2 : IntegrableOn (fun t => u' t * v t) (Ioi 0) := by
    have h := ((hA.const_mul μ).sub (hB.const_mul (i : ℝ))).const_mul (-(1 / β))
    refine IntegrableOn.congr_fun h (fun t _ => ?_) measurableSet_Ioi
    simp only [hu', hv, Pi.sub_apply]
    field_simp
  have h0 : Tendsto (fun t => u t * v t) (𝓝[>] 0) (𝓝 0) := by
    have := ((tendsto_powNegLog_exp_nhdsGT_zero hμ i β).div_const β).neg
    rw [zero_div, neg_zero] at this
    refine this.congr' (Eventually.of_forall fun t => ?_)
    simp only [hu, hv]
    ring
  have hinf : Tendsto (fun t => u t * v t) atTop (𝓝 0) := by
    have := ((tendsto_powNegLog_exp_atTop μ i hβ).div_const β).neg
    rw [zero_div, neg_zero] at this
    refine this.congr' (Eventually.of_forall fun t => ?_)
    simp only [hu, hv]
    ring
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul hud hvd hI1 hI2 h0 hinf
  unfold fluctMoment
  simp only [phaseKernel_zero_zero]
  have hL : ∫ t in Ioi (0 : ℝ), t ^ (μ + 1 - 1) * (-Real.log t) ^ i * Real.exp (-(β * t)) =
      ∫ t in Ioi (0 : ℝ), u t * v' t := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [hu, hv', add_sub_cancel_right]
  have hR : ∫ t in Ioi (0 : ℝ), u' t * v t = -(1 / β) *
      ((μ * ∫ t in Ioi (0 : ℝ), t ^ (μ - 1) * (-Real.log t) ^ i * Real.exp (-(β * t))) -
        (i : ℝ) * ∫ t in Ioi (0 : ℝ), t ^ (μ - 1) * (-Real.log t) ^ (i - 1) *
          Real.exp (-(β * t))) := by
    calc ∫ t in Ioi (0 : ℝ), u' t * v t = ∫ t in Ioi (0 : ℝ), -(1 / β) *
          (μ * (t ^ (μ - 1) * (-Real.log t) ^ i * Real.exp (-(β * t))) -
            (i : ℝ) * (t ^ (μ - 1) * (-Real.log t) ^ (i - 1) * Real.exp (-(β * t)))) := by
          refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
          simp only [hu', hv]
          field_simp
      _ = _ := by
          rw [integral_const_mul, integral_sub (hA.const_mul μ) (hB.const_mul (i : ℝ)),
            integral_const_mul, integral_const_mul]
  rw [hL, hibp, hR]
  field_simp
  ring

end Grammar
