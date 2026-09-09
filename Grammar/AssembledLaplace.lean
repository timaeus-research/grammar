/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.GammaLaplace
import Grammar.PopulationAssembly

/-!
# The assembled Gamma Laplace-transform limit (unit 339; Astra #40 unit 6)

For zero-noise joint data the chart integrals rescale exactly under a change of inverse
temperature, `𝒵_I(β+t; N) = 𝒵_I(β; N(β+t)/β)` (`dataBoxIntegral_beta_rescale`,
`gInt_beta_rescale`), so for external decompositions at both temperatures whose residuals are
negligible at the leading scale `N^{-μ_*}(log N)^{m_*−1}`,
```
𝒵_{β+t}(N)/𝒵_β(N) → (β/(β+t))^{μ_*}        (t ≥ 0, A_* ≠ 0)
```
(`energy_laplace_assembled`): `E_{N,β}[e^{-tNK}] → (β/(β+t))^{μ_*}` after finite chart assembly,
the Laplace transform of `Gamma(μ_*, β)`. Exact rescaling of the residual is not needed, only its
negligibility at both temperatures. Not claimed: weak convergence of the law of `NK`. Zero
`sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

/-- Zero-noise data integrals rescale exactly under a temperature change. -/
theorem dataBoxIntegral_beta_rescale (n : ℕ) (h k : Fin (n + 1) → ℕ) {β : ℝ} (hβ : β ≠ 0)
    (t N : ℝ) (x : DataSpace (n + 1)) (hx : xiCoord x = 0) :
    dataBoxIntegral n h k (β + t) N 1 x = dataBoxIntegral n h k β (N * ((β + t) / β)) 1 x := by
  rw [dataBoxIntegral_population n h k (β + t) N x hx, dataBoxIntegral_population n h k β _ x hx,
    origPhaseIntegral_beta_rescale n h k hβ t N 1 (dataAmplitude x)]

variable {M : ℕ} {K : Fin M → Type*} [∀ I, TopologicalSpace (K I)] [∀ I, CompactSpace (K I)]
  [∀ I, T2Space (K I)] [∀ I, MeasurableSpace (K I)] [∀ I, OpensMeasurableSpace (K I)]
  {n : Fin M → ℕ} (ν : (I : Fin M) → Measure (K I)) [∀ I, IsFiniteMeasure (ν I)]
  (h k : (I : Fin M) → Fin (n I + 1) → ℕ) (β : ℝ)

omit [∀ I, CompactSpace (K I)] [∀ I, T2Space (K I)] [∀ I, OpensMeasurableSpace (K I)]
  [∀ I, IsFiniteMeasure (ν I)] in
/-- The assembled zero-noise integral rescales exactly under a temperature change. -/
theorem gInt_beta_rescale (hβ : β ≠ 0) (t N : ℝ) (x : JointData K n)
    (hx : ∀ I v, xiCoord (x.chart I v) = 0) :
    gInt ν h k (β + t) (fun _ => 1) x N = gInt ν h k β (fun _ => 1) x (N * ((β + t) / β)) := by
  unfold gInt tanIntegral
  refine Finset.sum_congr rfl fun I _ => ?_
  congr 1
  funext v
  exact dataBoxIntegral_beta_rescale (n I) (h I) (k I) hβ t N (x.chart I v) (hx I v)

/-- **Assembled Gamma Laplace-transform limit**: `𝒵_{β+t}(N)/𝒵_β(N) → (β/(β+t))^{μ_*}`. -/
theorem energy_laplace_assembled (hk : ∀ I i, 0 < k I i) (hβ : 0 < β) (x : JointData K n)
    (hx : ∀ I v, xiCoord (x.chart I v) = 0) (lam : Fin M → ℝ)
    (hmin : ∀ I i, lam I ≤ ratioExp (h I) (k I) i) (hatt : ∀ I, ∃ i, ratioExp (h I) (k I) i = lam I)
    {μs : ℝ} (hμ : ∀ I, μs ≤ lam I) (hμatt : ∃ I, lam I = μs) {ms : ℕ}
    (hm : ∀ I, lam I = μs → multCount (ratioExp (h I) (k I)) (lam I) ≤ ms)
    (hmatt : ∃ I, lam I = μs ∧ multCount (ratioExp (h I) (k I)) (lam I) = ms) {t : ℝ} (ht : 0 ≤ t)
    (Zβ Eβ Zt Et : ℝ → ℝ) (hdβ : ∀ N, Zβ N = gInt ν h k β (fun _ => 1) x N + Eβ N)
    (hEβ : Tendsto (fun N => Eβ N / (N ^ (-μs) * Real.log N ^ (ms - 1))) atTop (𝓝 0))
    (hdt : ∀ N, Zt N = gInt ν h k (β + t) (fun _ => 1) x N + Et N)
    (hEt : Tendsto (fun N => Et N / (N ^ (-μs) * Real.log N ^ (ms - 1))) atTop (𝓝 0))
    (hA : assembledFace ν h k β x lam μs ms ≠ 0) :
    Tendsto (fun N => Zt N / Zβ N) atTop (𝓝 ((β / (β + t)) ^ μs)) := by
  have hβt : 0 < β + t := by linarith
  set c : ℝ := (β + t) / β with hc
  have hc0 : 0 < c := div_pos hβt hβ
  have hden := population_assembled_tendsto ν h k β hk hβ x hx lam hmin hatt hμ hμatt hm hmatt Zβ Eβ
    hdβ hEβ
  have hg := population_assembled_tendsto ν h k β hk hβ x hx lam hmin hatt hμ hμatt hm hmatt
    (gInt ν h k β (fun _ => 1) x) (fun _ => 0) (fun N => by simp)
    (by simpa using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (𝓝 0)))
  have hM : Tendsto (fun N : ℝ => N * c) atTop atTop := tendsto_id.atTop_mul_const hc0
  have hgc := hg.comp hM
  have hlog : Tendsto (fun N : ℝ => (1 + Real.log c * (Real.log N)⁻¹) ^ (ms - 1)) atTop (𝓝 1) := by
    have := (((tendsto_const_nhds (x := Real.log c)).mul tendsto_inv_log).const_add (1 : ℝ)).pow
      (ms - 1)
    simpa using this
  -- the rescaled assembled integral at the leading scale
  have hnum0 : Tendsto (fun N => gInt ν h k β (fun _ => 1) x (N * c) /
      (N ^ (-μs) * Real.log N ^ (ms - 1))) atTop
      (𝓝 (c ^ (-μs) * assembledFace ν h k β x lam μs ms)) := by
    have := (hgc.mul hlog).const_mul (c ^ (-μs))
    rw [mul_one] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ), eventually_gt_atTop (1 / c)] with N hN hNc
    have hN0 : 0 < N := by linarith
    have hNc1 : 1 < N * c := by rwa [div_lt_iff₀ hc0] at hNc
    have hlogN : Real.log N ≠ 0 := (Real.log_pos hN).ne'
    simp only [Function.comp_def]
    rw [Real.mul_rpow hN0.le hc0.le, Real.log_mul hN0.ne' hc0.ne']
    have hone : 1 + Real.log c * (Real.log N)⁻¹ = (Real.log N + Real.log c) / Real.log N := by
      field_simp
    rw [hone, div_pow]
    have hpowN : N ^ (-μs) ≠ 0 := (Real.rpow_pos_of_pos hN0 _).ne'
    have hpowc : c ^ (-μs) ≠ 0 := (Real.rpow_pos_of_pos hc0 _).ne'
    have hlogM : Real.log N + Real.log c ≠ 0 := by
      have := Real.log_pos hNc1
      rw [Real.log_mul hN0.ne' hc0.ne'] at this
      exact this.ne'
    have hlogMpow : (Real.log N + Real.log c) ^ (ms - 1) ≠ 0 := pow_ne_zero _ hlogM
    have hlogNpow : Real.log N ^ (ms - 1) ≠ 0 := pow_ne_zero _ hlogN
    field_simp
  have hnum : Tendsto (fun N => Zt N / (N ^ (-μs) * Real.log N ^ (ms - 1))) atTop
      (𝓝 (c ^ (-μs) * assembledFace ν h k β x lam μs ms)) := by
    have := hnum0.add hEt
    rw [add_zero] at this
    refine this.congr' (Eventually.of_forall fun N => ?_)
    dsimp only
    rw [hdt N, gInt_beta_rescale ν h k β hβ.ne' t N x hx, ← hc, add_div]
  have hq := hnum.div hden hA
  have hval : c ^ (-μs) * assembledFace ν h k β x lam μs ms / assembledFace ν h k β x lam μs ms =
      (β / (β + t)) ^ μs := by
    rw [mul_div_assoc, div_self hA, mul_one, Real.rpow_neg hc0.le, ← Real.inv_rpow hc0.le, hc,
      inv_div]
  rw [hval] at hq
  refine hq.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ), hden.eventually (isOpen_ne.mem_nhds hA)]
    with N hN hne
  have hN0 : 0 < N := by linarith
  have hpow : N ^ (-μs) * Real.log N ^ (ms - 1) ≠ 0 :=
    mul_ne_zero (Real.rpow_pos_of_pos hN0 _).ne' (pow_ne_zero _ (Real.log_pos hN).ne')
  have hZ : Zβ N ≠ 0 := by
    intro h0
    apply hne
    simp only [h0, zero_div]
  have hlogN : Real.log N ^ (ms - 1) ≠ 0 := pow_ne_zero _ (Real.log_pos hN).ne'
  simp only [Pi.div_apply]
  field_simp

end Grammar
