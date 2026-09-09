/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.EnergyHierarchy

/-!
# The Laplace transform of `NK` under the population posterior: the Gamma limit (unit 327)

Inserting `e^{-tNK}` into the population integral is exactly a change of inverse temperature,
`𝒵_{β+t}(N) = 𝒵_β(N (β+t)/β)` (`origPhaseIntegral_beta_rescale`: the phase `(β+t) N u^{2k}` is
`β N' u^{2k}` with `N' = N(β+t)/β`). Hence, at chart level for a continuous amplitude with nonzero
face functional,
```
E_{N,β}[e^{-tNK}] = 𝒵_{β+t}(N)/𝒵_β(N) → (β/(β+t))^λ        (t ≥ 0),
```
the Laplace transform of the `Gamma(λ, β)` law (`energy_laplace_chart`): the population posterior
law of `NK` has the Gamma Laplace transform in the limit. The proof uses only the leading asymptotic
`𝒵_β(N) ~ A N^{-λ}(log N)^{m−1}` at the two arguments `N` and `N(β+t)/β` (the logarithmic ratio
tends to one), not parameter-uniform asymptotics. Not claimed: weak convergence of the law of `NK`
(a Laplace-transform continuity theorem is not invoked); the assembled version needs the residual to
respect the exact rescaling and is not stated. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

/-- **Exact temperature rescaling**: `𝒵_{β+t}(N) = 𝒵_β(N (β+t)/β)` for zero-noise data. -/
theorem origPhaseIntegral_beta_rescale (n : ℕ) (h k : Fin (n + 1) → ℕ) {β : ℝ} (hβ : β ≠ 0)
    (t N b : ℝ) (η : (Fin (n + 1) → ℝ) → ℝ) :
    origPhaseIntegral n h k (β + t) N b (fun _ => 0) η =
      origPhaseIntegral n h k β (N * ((β + t) / β)) b (fun _ => 0) η := by
  unfold origPhaseIntegral
  congr 1
  funext u
  simp only [mul_zero, add_zero]
  rw [show β * (N * ((β + t) / β)) = (β + t) * N by
    rw [mul_comm β, mul_assoc, div_mul_cancel₀ _ hβ, mul_comm]]

/-- **Gamma Laplace transform limit**: `𝒵_{β+t}(N)/𝒵_β(N) → (β/(β+t))^λ` for `t ≥ 0`, i.e.
`E_{N,β}[e^{-tNK}] → (β/(β+t))^λ`, at chart level with nonzero face functional. -/
theorem energy_laplace_chart (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {β : ℝ}
    (hβ : 0 < β) {t : ℝ} (ht : 0 ≤ t) (η : (Fin (n + 1) → ℝ) → ℝ) (hηc : Continuous η) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (hA : amplitudeCoeff h k l β η ≠ 0) :
    Tendsto (fun N => origPhaseIntegral n h k (β + t) N 1 (fun _ => 0) η /
      origPhaseIntegral n h k β N 1 (fun _ => 0) η) atTop (𝓝 ((β / (β + t)) ^ l)) := by
  have hβt : 0 < β + t := by linarith
  set c : ℝ := (β + t) / β with hc
  have hc0 : 0 < c := div_pos hβt hβ
  have hl0 : 0 < l := by
    obtain ⟨i, hi⟩ := hatt
    rw [← hi]
    exact ratioExp_pos h k hk i
  have hT := amplitude_tendsto n h k hk l β hl0 hβ hmin hatt η hηc
  have hT' : Tendsto (fun N => origPhaseIntegral n h k β N 1 (fun _ => 0) η /
      (N ^ (-l) * Real.log N ^ (multCount (ratioExp h k) l - 1))) atTop
      (𝓝 (amplitudeCoeff h k l β η)) := by
    refine hT.congr' (Eventually.of_forall fun N => ?_)
    dsimp only
    rw [origPhaseIntegral_population_one]
  have hM : Tendsto (fun N : ℝ => N * c) atTop atTop := tendsto_id.atTop_mul_const hc0
  have hTc := hT'.comp hM
  have hlog : Tendsto (fun N : ℝ => (1 + Real.log c * (Real.log N)⁻¹) ^
      (multCount (ratioExp h k) l - 1)) atTop (𝓝 1) := by
    have := (((tendsto_const_nhds (x := Real.log c)).mul tendsto_inv_log).const_add (1 : ℝ)).pow
      (multCount (ratioExp h k) l - 1)
    simpa using this
  have hmain := ((hTc.mul hlog).const_mul (c ^ (-l))).div hT' hA
  rw [mul_one] at hmain
  have hval : c ^ (-l) * amplitudeCoeff h k l β η / amplitudeCoeff h k l β η =
      (β / (β + t)) ^ l := by
    rw [mul_div_assoc, div_self hA, mul_one, Real.rpow_neg hc0.le, ← Real.inv_rpow hc0.le, hc,
      inv_div]
  rw [hval] at hmain
  refine hmain.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ), eventually_gt_atTop (1 / c),
    hT'.eventually (isOpen_ne.mem_nhds hA)] with N hN hNc hne
  have hN0 : 0 < N := by linarith
  have hNc1 : 1 < N * c := by rwa [div_lt_iff₀ hc0] at hNc
  have hlogN : Real.log N ≠ 0 := (Real.log_pos hN).ne'
  have hpowN : N ^ (-l) ≠ 0 := (Real.rpow_pos_of_pos hN0 _).ne'
  have hpowc : c ^ (-l) ≠ 0 := (Real.rpow_pos_of_pos hc0 _).ne'
  have hlogNpow : Real.log N ^ (multCount (ratioExp h k) l - 1) ≠ 0 := pow_ne_zero _ hlogN
  have hZ : origPhaseIntegral n h k β N 1 (fun _ => 0) η ≠ 0 := by
    intro h0
    apply hne
    simp only [Set.mem_setOf_eq, h0, zero_div]
  simp only [Pi.div_apply, Function.comp_def]
  rw [origPhaseIntegral_beta_rescale n h k hβ.ne' t N 1 η, ← hc, Real.mul_rpow hN0.le hc0.le,
    Real.log_mul hN0.ne' hc0.ne']
  have hone : 1 + Real.log c * (Real.log N)⁻¹ = (Real.log N + Real.log c) / Real.log N := by
    field_simp
  rw [hone, div_pow]
  have hlogM : Real.log N + Real.log c ≠ 0 := by
    have := Real.log_pos hNc1
    rw [Real.log_mul hN0.ne' hc0.ne'] at this
    exact this.ne'
  have hlogMpow : (Real.log N + Real.log c) ^ (multCount (ratioExp h k) l - 1) ≠ 0 :=
    pow_ne_zero _ hlogM
  field_simp

end Grammar
