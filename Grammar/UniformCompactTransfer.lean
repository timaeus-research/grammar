/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Measure.Tight

/-!
# Transfer of convergence in distribution through uniformly convergent maps

Two abstract probabilistic lemmas for the empirical programme.

* `tendstoInMeasure_of_tendstoUniformlyOn_compacts`: if the laws of `L n : Ω → E` are tight and
  `T n → T` uniformly on compact sets, then `T n (L n) − T (L n) → 0` in probability.
* `tendstoInDistribution_comp_of_tendstoUniformlyOn_compacts` ★★: if moreover `L n ⇒ G` in
  distribution and `T` is continuous, then `T n (L n) ⇒ T (G)` (continuous mapping theorem for
  `T ∘ L n`, then Mathlib's `tendstoInDistribution_of_tendstoInMeasure_sub`).
* `tendstoInMeasure_zero_of_tight_bound`: a random remainder `Y n` with `|Y n| ≤ c(M n) r n`,
  `r n → 0` deterministic, `c` monotone on `[0, ∞)` and `M n = O_p(1)` tends to `0` in
  probability.

Zero `sorry`/`axiom`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Grammar

variable {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
  {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']

omit [IsProbabilityMeasure P] in
/-- Tight laws and uniform convergence on compacts give convergence in probability of the
difference `T n (L n) − T (L n)` to `0`. -/
theorem tendstoInMeasure_of_tendstoUniformlyOn_compacts {L : ℕ → Ω → E}
    (hLm : ∀ n, Measurable (L n))
    (htight : IsTightMeasureSet (Set.range fun n => P.map (L n)))
    {T : ℕ → E → ℝ} {Tlim : E → ℝ}
    (hunif : ∀ C : Set E, IsCompact C → TendstoUniformlyOn T Tlim atTop C) :
    TendstoInMeasure P ((fun n ω => T n (L n ω)) - fun n => Tlim ∘ L n) atTop 0 := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  obtain ⟨K, hKc, hK⟩ := (isTightMeasureSet_iff_exists_isCompact_measure_compl_le.1 htight) η hη
  have hu := Metric.tendstoUniformlyOn_iff.1 (hunif K hKc) ε hε
  filter_upwards [hu] with n hn
  calc P {ω | ε ≤ ‖((fun n ω => T n (L n ω)) - fun n => Tlim ∘ L n) n ω - (0 : ℕ → Ω → ℝ) n ω‖}
      ≤ P (L n ⁻¹' Kᶜ) := by
        refine measure_mono fun ω hω => ?_
        simp only [Set.mem_ofPred_eq, Pi.sub_apply, Pi.zero_apply, Function.comp_apply,
          sub_zero, Real.norm_eq_abs] at hω
        intro hK'
        have := hn (L n ω) hK'
        rw [Real.dist_eq, abs_sub_comm] at this
        exact absurd hω (not_le.2 this)
    _ = P.map (L n) Kᶜ := (Measure.map_apply (hLm n) hKc.isClosed.measurableSet.compl).symm
    _ ≤ η := hK _ ⟨n, rfl⟩

/-- ★★ **Transfer of convergence in distribution through uniformly convergent maps**: if
`L n ⇒ G`, the laws of `L n` are tight, `T n → T` uniformly on compacts with `T` and the `T n`
continuous, then `T n (L n) ⇒ T (G)`. -/
theorem tendstoInDistribution_comp_of_tendstoUniformlyOn_compacts {L : ℕ → Ω → E}
    (hLm : ∀ n, Measurable (L n)) {G : Ω' → E}
    (hLG : TendstoInDistribution L atTop G (fun _ => P) P')
    (htight : IsTightMeasureSet (Set.range fun n => P.map (L n)))
    {T : ℕ → E → ℝ} {Tlim : E → ℝ} (hTc : ∀ n, Continuous (T n)) (hlimc : Continuous Tlim)
    (hunif : ∀ C : Set E, IsCompact C → TendstoUniformlyOn T Tlim atTop C) :
    TendstoInDistribution (fun n ω => T n (L n ω)) atTop (fun ω => Tlim (G ω)) (fun _ => P) P' := by
  have hX : TendstoInDistribution (fun n => Tlim ∘ L n) atTop (Tlim ∘ G) (fun _ => P) P' :=
    hLG.continuous_comp hlimc
  exact tendstoInDistribution_of_tendstoInMeasure_sub (X := fun n => Tlim ∘ L n) _ _ hX
    (tendstoInMeasure_of_tendstoUniformlyOn_compacts hLm htight hunif)
    fun n => ((hTc n).measurable.comp (hLm n)).aemeasurable

omit [IsProbabilityMeasure P] in
/-- A random remainder dominated by `c(M n) · r n`, with `r n → 0`, `c` monotone on `[0, ∞)`,
`M n ≥ 0` and `M n = O_p(1)`, tends to `0` in probability. -/
theorem tendstoInMeasure_zero_of_tight_bound {Y : ℕ → Ω → ℝ} {M : ℕ → Ω → ℝ} {r : ℕ → ℝ}
    {c : ℝ → ℝ} (hc : MonotoneOn c (Set.Ici 0)) (hM0 : ∀ n ω, 0 ≤ M n ω)
    (hbound : ∀ n ω, |Y n ω| ≤ c (M n ω) * r n) (hr : Tendsto r atTop (𝓝 0))
    (hr0 : ∀ n, 0 ≤ r n)
    (hM : ∀ η : ℝ≥0∞, 0 < η → ∃ R : ℝ, ∀ᶠ n in atTop, P {ω | R < M n ω} ≤ η) :
    TendstoInMeasure P Y atTop 0 := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  obtain ⟨R, hR⟩ := hM η hη
  set R' := max R 0 with hR'
  have hR'0 : 0 ≤ R' := le_max_right _ _
  have hsmall : ∀ᶠ n in atTop, |c R' * r n| < ε := by
    have := (hr.const_mul (c R')).norm
    rw [mul_zero, norm_zero] at this
    exact (this.eventually (gt_mem_nhds hε)).mono fun n hn => by simpa using hn
  filter_upwards [hR, hsmall] with n hn hsn
  calc P {ω | ε ≤ ‖Y n ω - (0 : Ω → ℝ) ω‖} ≤ P {ω | R < M n ω} := by
        refine measure_mono fun ω hω => ?_
        simp only [Set.mem_ofPred_eq, Pi.zero_apply, sub_zero, Real.norm_eq_abs] at hω ⊢
        by_contra hle
        push Not at hle
        have hMR' : M n ω ≤ R' := hle.trans (le_max_left _ _)
        have hcm : c (M n ω) ≤ c R' := hc (hM0 n ω) hR'0 hMR'
        have h1 : |Y n ω| ≤ c R' * r n :=
          (hbound n ω).trans (mul_le_mul_of_nonneg_right hcm (hr0 n))
        have h2 : c R' * r n ≤ |c R' * r n| := le_abs_self _
        linarith
    _ ≤ η := hn

end Grammar
