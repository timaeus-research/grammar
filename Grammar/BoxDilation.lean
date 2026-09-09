/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.PopulationEquivalent
import Grammar.BoxScaling

/-!
# Positive normal boxes: dilation and the leading term (Programme Q, N4, unit 317)

The population results of Programmes P–Q are stated on the unit normal box. For a box `(0,b]^d`,
`b > 0`, the exact dilation (with `H = |h| + d`, `K = |k|`)
```
𝒵_b(N; η) = b^H · 𝒵_1(N b^{2K}; η(b·))                              (origPhaseIntegral_dilation)
```
(change of variables `u = b v`) transports every unit-box statement. In particular the leading
term on the box is
```
𝒵_b(N; η)/(N^{-λ}(log N)^{m−1}) → b^H (b^{2K})^{-λ} · amplitudeCoeff h k λ β (η(b·))
                                                                    (population_box_tendsto)
```
(the top-log coefficient picks up the prefactor `b^{H−2Kλ}` and the face functional of the
rescaled amplitude; the shift of `log N` by `2K log b` affects only lower log powers). The
admissibility of the rescaled amplitude is inherited: `η(b·)` is continuous, and a holomorphic
extension on the polydisc of radius `R` rescales to radius `R/b`, which is why the Taylor tree on
the box needs `b < R`. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology Asymptotics

namespace Grammar

/-- **Exact dilation** of the population integral to the unit box. -/
theorem origPhaseIntegral_dilation (n : ℕ) (h k : Fin (n + 1) → ℕ) (β : ℝ) {N b : ℝ} (hb : 0 < b)
    (η : (Fin (n + 1) → ℝ) → ℝ) :
    origPhaseIntegral n h k β N b (fun _ => 0) η =
      b ^ (∑ i, h i + (n + 1)) *
        origPhaseIntegral n h k β (N * b ^ (2 * ∑ i, k i)) 1 (fun _ => 0) fun v => η (b • v) := by
  set F : (Fin (n + 1) → ℝ) → ℝ := fun u => η u * (∏ i, u i ^ h i) *
    Real.exp (-(β * N * ∏ i, u i ^ (2 * k i)) + β * (Real.sqrt N * ∏ i, u i ^ k i) * 0) with hF
  set G : (Fin (n + 1) → ℝ) → ℝ := fun v => η (b • v) * (∏ i, v i ^ h i) *
    Real.exp (-(β * (N * b ^ (2 * ∑ i, k i)) * ∏ i, v i ^ (2 * k i)) +
      β * (Real.sqrt (N * b ^ (2 * ∑ i, k i)) * ∏ i, v i ^ k i) * 0) with hG
  have hFG : ∀ v, F (b • v) = b ^ (∑ i, h i) * G v := by
    intro v
    simp only [hF, hG, Pi.smul_apply, smul_eq_mul, mul_zero, add_zero]
    have h1 : ∏ i, (b * v i) ^ h i = b ^ (∑ i, h i) * ∏ i, v i ^ h i := by
      rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun i _ => mul_pow _ _ _
    have h2 : ∏ i, (b * v i) ^ (2 * k i) = b ^ (2 * ∑ i, k i) * ∏ i, v i ^ (2 * k i) := by
      rw [Finset.mul_sum, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun i _ => mul_pow _ _ _
    rw [h1, h2, show -(β * N * (b ^ (2 * ∑ i, k i) * ∏ i, v i ^ (2 * k i))) =
      -(β * (N * b ^ (2 * ∑ i, k i)) * ∏ i, v i ^ (2 * k i)) by ring]
    ring
  have hind : ∀ v, (piBox (n + 1) (Ioc 0 b)).indicator F (b • v) =
      (unitBox (n + 1)).indicator (fun v => b ^ (∑ i, h i) * G v) v := by
    intro v
    by_cases hv : v ∈ unitBox (n + 1)
    · rw [Set.indicator_of_mem hv, Set.indicator_of_mem ((smul_mem_piBox_Ioc_iff hb v).2 hv), hFG]
    · rw [Set.indicator_of_notMem hv,
        Set.indicator_of_notMem (fun h' => hv ((smul_mem_piBox_Ioc_iff hb v).1 h'))]
  have hscale := Measure.integral_comp_smul (volume : Measure (Fin (n + 1) → ℝ))
    ((piBox (n + 1) (Ioc 0 b)).indicator F) b
  rw [Module.finrank_fin_fun, smul_eq_mul, abs_of_nonneg (inv_nonneg.2 (pow_nonneg hb.le _)),
    integral_indicator (measurableSet_piBox _ _ measurableSet_Ioc)] at hscale
  simp_rw [hind] at hscale
  rw [integral_indicator (measurableSet_unitBox _), integral_const_mul] at hscale
  -- `hscale : b^{|h|} ∫_{unitBox} G = (b^d)⁻¹ * 𝒵_b`
  have hpos : (0 : ℝ) < b ^ (n + 1) := pow_pos hb _
  have hset : piBox (n + 1) (Ioc (0 : ℝ) 1) = unitBox (n + 1) := rfl
  unfold origPhaseIntegral
  rw [hset]
  have hZ : ∫ u in piBox (n + 1) (Ioc 0 b), F u =
      b ^ (n + 1) * (b ^ (∑ i, h i) * ∫ v in unitBox (n + 1), G v) := by
    rw [hscale]
    field_simp
  simp only [hF, hG] at hZ
  rw [hZ, pow_add]
  ring

/-- The rescaled amplitude is continuous. -/
theorem continuous_rescale {d : ℕ} (b : ℝ) {η : (Fin d → ℝ) → ℝ} (hηc : Continuous η) :
    Continuous fun v : Fin d → ℝ => η (b • v) :=
  hηc.comp (continuous_const_smul b)

/-- **The leading term on a positive box** `(0,b]^d`. -/
theorem population_box_tendsto (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {b : ℝ} (hb : 0 < b) {l : ℝ} (hmin : ∀ i, l ≤ ratioExp h k i)
    (hatt : ∃ i, ratioExp h k i = l) (η : (Fin (n + 1) → ℝ) → ℝ) (hηc : Continuous η) :
    Tendsto (fun N => origPhaseIntegral n h k β N b (fun _ => 0) η /
        (N ^ (-l) * Real.log N ^ (multCount (ratioExp h k) l - 1))) atTop
      (𝓝 (b ^ (∑ i, h i + (n + 1)) * (b ^ (2 * ∑ i, k i)) ^ (-l) *
        amplitudeCoeff h k l β fun v => η (b • v))) := by
  set c : ℝ := b ^ (2 * ∑ i, k i) with hc
  have hc0 : 0 < c := pow_pos hb _
  set m := multCount (ratioExp h k) l with hm
  have hl0 : 0 < l := by
    obtain ⟨i, hi⟩ := hatt
    rw [← hi]
    exact ratioExp_pos h k hk i
  -- Headline VIII for the rescaled amplitude, composed with `M = N c`
  have hT := amplitude_tendsto n h k hk l β hl0 hβ hmin hatt (fun v => η (b • v))
    (continuous_rescale b hηc)
  have hM : Tendsto (fun N : ℝ => N * c) atTop atTop := tendsto_id.atTop_mul_const hc0
  have hTc := hT.comp hM
  -- the logarithmic ratio tends to one
  have hlog : Tendsto (fun N : ℝ => (1 + Real.log c * (Real.log N)⁻¹) ^ (m - 1)) atTop (𝓝 1) := by
    have := (((tendsto_const_nhds (x := Real.log c)).mul tendsto_inv_log).const_add (1 : ℝ)).pow
      (m - 1)
    simpa using this
  have hmain := (hTc.mul hlog).const_mul (b ^ (∑ i, h i + (n + 1)) * c ^ (-l))
  rw [mul_one] at hmain
  refine hmain.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ), eventually_gt_atTop (1 / c)] with N hN hNc
  have hN0 : 0 < N := by linarith
  have hNc1 : 1 < N * c := by rwa [div_lt_iff₀ hc0] at hNc
  have hlogN : Real.log N ≠ 0 := (Real.log_pos hN).ne'
  simp only [Function.comp]
  rw [origPhaseIntegral_dilation n h k β hb η, ← hc, origPhaseIntegral_population_one,
    Real.mul_rpow hN0.le hc0.le, Real.log_mul hN0.ne' hc0.ne']
  simp only [← hm]
  have hone : 1 + Real.log c * (Real.log N)⁻¹ = (Real.log N + Real.log c) / Real.log N := by
    field_simp
  rw [hone, div_pow]
  have hpowN : N ^ (-l) ≠ 0 := (Real.rpow_pos_of_pos hN0 _).ne'
  have hpowc : c ^ (-l) ≠ 0 := (Real.rpow_pos_of_pos hc0 _).ne'
  have hlogM : Real.log N + Real.log c ≠ 0 := by
    have := Real.log_pos hNc1
    rw [Real.log_mul hN0.ne' hc0.ne'] at this
    exact this.ne'
  have hlogMpow : (Real.log N + Real.log c) ^ (m - 1) ≠ 0 := pow_ne_zero _ hlogM
  have hlogNpow : Real.log N ^ (m - 1) ≠ 0 := pow_ne_zero _ hlogN
  field_simp

end Grammar
