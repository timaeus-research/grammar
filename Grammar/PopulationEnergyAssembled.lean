/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.PopulationAssembly
import Grammar.PopulationEnergy

/-!
# The energy observable after finite chart assembly (Astra #37 P5, unit 305)

With the same charts, tangential measures and zero-noise data as the denominator, inserting
`K∘π = u^{2k_I}` on chart `I` is the weight change `h_I ↦ h_I + 2k_I`; the global first candidate
moves from `(μ_*, m_*−1)` to `(μ_*+1, m_*−1)` with the same tied charts, and the assembled face
functional becomes `(μ_*/β) A_*` (`assembledFace_add_two_k`: every tied chart has `λ_I = μ_*`, so
each contribution is multiplied by `μ_*/β`). Hence, for
```
𝒵_pop[1] = ∑_I 𝒵^I(h_I) + E,        𝒵_pop[K] = ∑_I 𝒵^I(h_I + 2k_I) + E_K
```
with residuals negligible at the respective scales and `A_* ≠ 0`,
```
N · 𝒵_pop[K](N) / 𝒵_pop[1](N) → μ_*/β                     (energy_ratio_assembled_tendsto)
```
(`β = 1`: `n E_n[K] → λ`, the global RLCT). Conditional on the two external decompositions; if
`A_* = 0` the first-candidate theorems do not justify the conclusion. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology Asymptotics

namespace Grammar

variable {M : ℕ} {K : Fin M → Type*} [∀ I, TopologicalSpace (K I)] [∀ I, CompactSpace (K I)]
  [∀ I, T2Space (K I)] [∀ I, MeasurableSpace (K I)] [∀ I, OpensMeasurableSpace (K I)]
  {n : Fin M → ℕ} (ν : (I : Fin M) → Measure (K I)) [∀ I, IsFiniteMeasure (ν I)]
  (h k : (I : Fin M) → Fin (n I + 1) → ℕ) (β : ℝ)

omit [∀ I, CompactSpace (K I)] [∀ I, T2Space (K I)] [∀ I, OpensMeasurableSpace (K I)]
  [∀ I, IsFiniteMeasure (ν I)] in
/-- The chart face functional of the shifted weight is `λ_I/β` times the original. -/
theorem chartFace_add_two_k (hk : ∀ I i, 0 < k I i) (hβ : 0 < β) (x : JointData K n)
    (lam : Fin M → ℝ) (hlam : ∀ I, 0 < lam I) (I : Fin M) :
    chartFace ν (fun I i => h I i + 2 * k I i) k β x (fun I => lam I + 1) I =
      lam I / β * chartFace ν h k β x lam I := by
  unfold chartFace
  rw [← integral_const_mul]
  congr 1
  funext v
  exact amplitudeCoeff_add_two_k (h I) (k I) (hk I) (hlam I) hβ _

omit [∀ I, CompactSpace (K I)] [∀ I, T2Space (K I)] [∀ I, OpensMeasurableSpace (K I)]
  [∀ I, IsFiniteMeasure (ν I)] in
/-- **The assembled face functional of the energy observable is `(μ_*/β) A_*`.** -/
theorem assembledFace_add_two_k (hk : ∀ I i, 0 < k I i) (hβ : 0 < β) (x : JointData K n)
    (lam : Fin M → ℝ) (hlam : ∀ I, 0 < lam I) (μs : ℝ) (ms : ℕ) :
    assembledFace ν (fun I i => h I i + 2 * k I i) k β x (fun I => lam I + 1) (μs + 1) ms =
      μs / β * assembledFace ν h k β x lam μs ms := by
  unfold assembledFace
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  simp only [add_left_inj, multCount_add_two_k (h I) (k I) (hk I) (lam I)]
  split_ifs with hI
  · rw [chartFace_add_two_k ν h k β hk hβ x lam hlam I, hI.1]
  · rw [mul_zero]

/-- **`N · E_N[K∘π] → μ_*/β` after finite chart assembly**: for zero-noise joint data, external
decompositions of the population integrals with and without the energy inserted (with residuals
negligible at the respective first-candidate scales), and `A_* ≠ 0`. -/
theorem energy_ratio_assembled_tendsto (hk : ∀ I i, 0 < k I i) (hβ : 0 < β) (x : JointData K n)
    (hx : ∀ I v, xiCoord (x.chart I v) = 0) (lam : Fin M → ℝ)
    (hmin : ∀ I i, lam I ≤ ratioExp (h I) (k I) i) (hatt : ∀ I, ∃ i, ratioExp (h I) (k I) i = lam I)
    {μs : ℝ} (hμ : ∀ I, μs ≤ lam I) (hμatt : ∃ I, lam I = μs) {ms : ℕ}
    (hm : ∀ I, lam I = μs → multCount (ratioExp (h I) (k I)) (lam I) ≤ ms)
    (hmatt : ∃ I, lam I = μs ∧ multCount (ratioExp (h I) (k I)) (lam I) = ms)
    (Zpop E ZK EK : ℝ → ℝ) (hdecomp : ∀ N, Zpop N = gInt ν h k β (fun _ => 1) x N + E N)
    (hE : Tendsto (fun N => E N / (N ^ (-μs) * Real.log N ^ (ms - 1))) atTop (𝓝 0))
    (hdecompK : ∀ N, ZK N = gInt ν (fun I i => h I i + 2 * k I i) k β (fun _ => 1) x N + EK N)
    (hEK : Tendsto (fun N => EK N / (N ^ (-(μs + 1)) * Real.log N ^ (ms - 1))) atTop (𝓝 0))
    (hA : assembledFace ν h k β x lam μs ms ≠ 0) :
    Tendsto (fun N => N * (ZK N / Zpop N)) atTop (𝓝 (μs / β)) := by
  have hlam : ∀ I, 0 < lam I := fun I => by
    obtain ⟨i, hi⟩ := hatt I
    rw [← hi]
    exact ratioExp_pos (h I) (k I) (hk I) i
  have hμs : 0 < μs := by
    obtain ⟨I, hI⟩ := hμatt
    rw [← hI]
    exact hlam I
  -- the denominator
  have hd := population_assembled_isEquivalent ν h k β hk hβ x hx lam hmin hatt hμ hμatt hm hmatt
    Zpop E hdecomp hE hA
  -- the numerator: shifted weights
  have hminK : ∀ I i, lam I + 1 ≤ ratioExp (fun i => h I i + 2 * k I i) (k I) i := fun I =>
    hmin_add_two_k (h I) (k I) (hk I) (hmin I)
  have hattK : ∀ I, ∃ i, ratioExp (fun i => h I i + 2 * k I i) (k I) i = lam I + 1 := fun I =>
    hatt_add_two_k (h I) (k I) (hk I) (hatt I)
  have hμK : ∀ I, μs + 1 ≤ lam I + 1 := fun I => by linarith [hμ I]
  have hμattK : ∃ I, lam I + 1 = μs + 1 := by
    obtain ⟨I, hI⟩ := hμatt
    exact ⟨I, by rw [hI]⟩
  have hmK : ∀ I, lam I + 1 = μs + 1 →
      multCount (ratioExp (fun i => h I i + 2 * k I i) (k I)) (lam I + 1) ≤ ms := fun I hI => by
    rw [multCount_add_two_k (h I) (k I) (hk I)]
    exact hm I (add_left_inj 1 |>.1 hI)
  have hmattK : ∃ I, lam I + 1 = μs + 1 ∧
      multCount (ratioExp (fun i => h I i + 2 * k I i) (k I)) (lam I + 1) = ms := by
    obtain ⟨I, hI1, hI2⟩ := hmatt
    exact ⟨I, by rw [hI1], by rw [multCount_add_two_k (h I) (k I) (hk I)]; exact hI2⟩
  have hAK : assembledFace ν (fun I i => h I i + 2 * k I i) k β x (fun I => lam I + 1) (μs + 1)
      ms ≠ 0 := by
    rw [assembledFace_add_two_k ν h k β hk hβ x lam hlam μs ms]
    exact mul_ne_zero (div_ne_zero hμs.ne' hβ.ne') hA
  have hn := population_assembled_isEquivalent ν (fun I i => h I i + 2 * k I i) k β hk hβ x hx
    (fun I => lam I + 1) hminK hattK hμK hμattK hmK hmattK ZK EK hdecompK hEK hAK
  rw [assembledFace_add_two_k ν h k β hk hβ x lam hlam μs ms] at hn
  have hq := isEquivalent_quotient_powLog hn hd hA
  have hmul := (IsEquivalent.refl (u := fun N : ℝ => N) (l := atTop)).mul hq
  refine hmul.symm.tendsto_nhds (tendsto_const_nhds.congr' ?_)
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
  have hN0 : 0 < N := by linarith
  have hlog : Real.log N ^ (ms - 1) ≠ 0 := pow_ne_zero _ (Real.log_pos hN).ne'
  simp only [Pi.mul_apply]
  rw [show -(μs + 1 - μs) = (-1 : ℝ) by ring, Real.rpow_neg_one, div_self hlog,
    mul_div_assoc, div_self hA]
  field_simp

end Grammar
