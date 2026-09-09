/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

/-!
# Laplace-transform continuity theorem for laws on `[0,∞)` (unit 346; Astra #41 unit 5)

Probability measures on `ℝ` carried by `[0,∞)` whose Laplace transforms `∫ e^{-ty}` converge at
every `t ≥ 0` to those of a probability measure carried by `[0,∞)` converge weakly.  Proof: the
functions `y ↦ e^{-(s y⁺ + t y⁻)}` (`s, t ≥ 0`) form a multiplicative monoid of bounded continuous
functions on `ℝ` whose span is a star subalgebra separating points; against measures carried by
`[0,∞)` their integrals are Laplace transforms; tightness follows from the elementary bound
`ν(y > M) ≤ (1 − ∫e^{-ty} dν)/(1 − e^{-tM})` and `∫ e^{-ty} dν₀ → 1` as `t ↓ 0`.  The conclusion
is Mathlib's tight-plus-separating-algebra criterion.  No general transform library is built.
-/

namespace Grammar

open MeasureTheory Filter Topology Set BoundedContinuousFunction

/-! ### The generating monoid -/

/-- `y ↦ e^{-(s y⁺ + t y⁻)}`. -/
noncomputable def expSplitFun (s t y : ℝ) : ℝ := Real.exp (-(s * max y 0 + t * max (-y) 0))

theorem continuous_expSplitFun (s t : ℝ) : Continuous (expSplitFun s t) := by
  unfold expSplitFun
  fun_prop

theorem norm_expSplitFun_le_one {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (y : ℝ) :
    ‖expSplitFun s t y‖ ≤ 1 := by
  unfold expSplitFun
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
  have h1 : 0 ≤ s * max y 0 := mul_nonneg hs (le_max_right _ _)
  have h2 : 0 ≤ t * max (-y) 0 := mul_nonneg ht (le_max_right _ _)
  linarith

/-- The bounded continuous function `y ↦ e^{-(s y⁺ + t y⁻)}`. -/
noncomputable def expSplit (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (expSplitFun s t) (continuous_expSplitFun s t) 1
    (norm_expSplitFun_le_one hs ht)

/-- The generating set `{e^{-(s y⁺ + t y⁻)} : s, t ≥ 0}`. -/
def expSplitSet : Set (ℝ →ᵇ ℝ) :=
  {f | ∃ s t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧ ∀ y, f y = expSplitFun s t y}

theorem expSplit_mem (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) : expSplit s t hs ht ∈ expSplitSet :=
  ⟨s, t, hs, ht, fun _ => rfl⟩

theorem one_mem_expSplitSet : (1 : ℝ →ᵇ ℝ) ∈ expSplitSet :=
  ⟨0, 0, le_rfl, le_rfl, fun y => by simp [expSplitFun]⟩

theorem mul_mem_expSplitSet {f g : ℝ →ᵇ ℝ} (hf : f ∈ expSplitSet) (hg : g ∈ expSplitSet) :
    f * g ∈ expSplitSet := by
  obtain ⟨s₁, t₁, hs₁, ht₁, hf⟩ := hf
  obtain ⟨s₂, t₂, hs₂, ht₂, hg⟩ := hg
  refine ⟨s₁ + s₂, t₁ + t₂, by positivity, by positivity, fun y => ?_⟩
  rw [BoundedContinuousFunction.mul_apply, hf, hg]
  unfold expSplitFun
  rw [← Real.exp_add]
  congr 1
  ring

/-- The span of the generating monoid, as a star subalgebra of `ℝ →ᵇ ℝ`. -/
noncomputable def laplaceAlgebra : StarSubalgebra ℝ (ℝ →ᵇ ℝ) where
  toSubalgebra := (Submodule.span ℝ expSplitSet).toSubalgebra
    (Submodule.subset_span one_mem_expSplitSet) fun x y hx hy => by
      have : x * y ∈ Submodule.span ℝ expSplitSet * Submodule.span ℝ expSplitSet :=
        Submodule.mul_mem_mul hx hy
      rw [Submodule.span_mul_span] at this
      exact Submodule.span_mono
        (Set.mul_subset_iff.2 fun f hf g hg => mul_mem_expSplitSet hf hg) this
  star_mem' := fun {f} hf => by
    rwa [show star f = f from BoundedContinuousFunction.ext fun y => by simp]

theorem mem_laplaceAlgebra {f : ℝ →ᵇ ℝ} :
    f ∈ laplaceAlgebra ↔ f ∈ Submodule.span ℝ expSplitSet := Iff.rfl

theorem laplaceAlgebra_separatesPoints :
    (laplaceAlgebra.map (BoundedContinuousFunction.toContinuousMapStarₐ ℝ)).SeparatesPoints := by
  intro x y hxy
  obtain ⟨f, hf, hne⟩ : ∃ f : ℝ →ᵇ ℝ, f ∈ laplaceAlgebra ∧ f x ≠ f y := by
    rcases ne_or_eq (max x 0) (max y 0) with h | h
    · refine ⟨expSplit 1 0 zero_le_one le_rfl, Submodule.subset_span (expSplit_mem _ _ _ _), ?_⟩
      change expSplitFun 1 0 x ≠ expSplitFun 1 0 y
      unfold expSplitFun
      simp only [one_mul, zero_mul, add_zero]
      exact fun h' => h (neg_injective (Real.exp_injective h'))
    · have h' : max (-x) 0 ≠ max (-y) 0 := by
        intro h'
        apply hxy
        rw [← max_zero_sub_max_neg_zero_eq_self x, ← max_zero_sub_max_neg_zero_eq_self y, h, h']
      refine ⟨expSplit 0 1 le_rfl zero_le_one, Submodule.subset_span (expSplit_mem _ _ _ _), ?_⟩
      change expSplitFun 0 1 x ≠ expSplitFun 0 1 y
      unfold expSplitFun
      simp only [one_mul, zero_mul, zero_add]
      exact fun h'' => h' (neg_injective (Real.exp_injective h''))
  refine ⟨BoundedContinuousFunction.toContinuousMapStarₐ ℝ f, ?_, hne⟩
  simp only [StarSubalgebra.coe_toSubalgebra, StarSubalgebra.coe_map, Set.mem_image,
    SetLike.mem_coe, exists_exists_and_eq_and]
  exact ⟨f, hf, rfl⟩

/-! ### Measures carried by `[0,∞)` -/

theorem ae_nonneg_of_measure_Iio {ν : Measure ℝ} (h0 : ν (Iio 0) = 0) : ∀ᵐ y ∂ν, 0 ≤ y := by
  rw [ae_iff]
  convert h0 using 2
  ext y
  simp [not_le]

/-- Against a law carried by `[0,∞)`, the generating functions integrate to Laplace transforms. -/
theorem integral_expSplit_eq {ν : Measure ℝ} (h0 : ν (Iio 0) = 0) {f : ℝ →ᵇ ℝ} {s t : ℝ}
    (hf : ∀ y, f y = expSplitFun s t y) :
    ∫ y, f y ∂ν = ∫ y, Real.exp (-(s * y)) ∂ν := by
  refine integral_congr_ae ?_
  filter_upwards [ae_nonneg_of_measure_Iio h0] with y hy
  rw [hf, expSplitFun, max_eq_left hy, max_eq_right (neg_nonpos.2 hy), mul_zero, add_zero]

theorem laplaceAlgebra_integral_tendsto {ι : Type*} {𝓕 : Filter ι} (ν : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (ν i)] (ν₀ : Measure ℝ) [IsProbabilityMeasure ν₀]
    (h0 : ∀ i, ν i (Iio 0) = 0) (h0' : ν₀ (Iio 0) = 0)
    (hL : ∀ s : ℝ, 0 ≤ s → Tendsto (fun i => ∫ y, Real.exp (-(s * y)) ∂(ν i)) 𝓕
      (𝓝 (∫ y, Real.exp (-(s * y)) ∂ν₀)))
    {g : ℝ →ᵇ ℝ} (hg : g ∈ laplaceAlgebra) :
    Tendsto (fun i => ∫ y, g y ∂(ν i)) 𝓕 (𝓝 (∫ y, g y ∂ν₀)) := by
  rw [mem_laplaceAlgebra] at hg
  induction hg using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨s, t, hs, -, hf⟩ := hf
    simp only [integral_expSplit_eq (h0 _) hf, integral_expSplit_eq h0' hf]
    exact hL s hs
  | zero =>
    simp only [BoundedContinuousFunction.coe_zero, Pi.zero_apply, integral_zero]
    exact tendsto_const_nhds
  | add f g _ _ hf hg =>
    simp only [BoundedContinuousFunction.coe_add, Pi.add_apply]
    rw [integral_add (BoundedContinuousFunction.integrable _ _)
      (BoundedContinuousFunction.integrable _ _)]
    refine (hf.add hg).congr' (Eventually.of_forall fun i => ?_)
    dsimp only
    rw [integral_add (BoundedContinuousFunction.integrable _ _)
      (BoundedContinuousFunction.integrable _ _)]
  | smul c f _ hf =>
    simp only [BoundedContinuousFunction.coe_smul, smul_eq_mul, integral_const_mul]
    exact hf.const_mul c

/-- The Laplace transform of a probability law carried by `[0,∞)` tends to `1` as `t ↓ 0`. -/
theorem laplace_tendsto_one (ν : Measure ℝ) [IsProbabilityMeasure ν] (h0 : ν (Iio 0) = 0) :
    Tendsto (fun t : ℝ => ∫ y, Real.exp (-(t * y)) ∂ν) (𝓝[>] 0) (𝓝 1) := by
  have hae := ae_nonneg_of_measure_Iio h0
  have := tendsto_integral_filter_of_dominated_convergence (μ := ν) (l := 𝓝[>] (0 : ℝ))
    (F := fun t y => Real.exp (-(t * y))) (f := fun _ => (1 : ℝ)) (fun _ => (1 : ℝ))
    (Eventually.of_forall fun t =>
      (by fun_prop : Continuous fun y => Real.exp (-(t * y))).aestronglyMeasurable)
    (eventually_nhdsWithin_of_forall fun t (ht : t ∈ Ioi (0 : ℝ)) => hae.mono fun y hy => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
      have : 0 ≤ t * y := mul_nonneg (le_of_lt ht) hy
      linarith)
    (integrable_const 1)
    (Eventually.of_forall fun y => by
      have : Tendsto (fun t : ℝ => Real.exp (-(t * y))) (𝓝 0) (𝓝 (Real.exp (-(0 * y)))) :=
        (Real.continuous_exp.comp
          (continuous_neg.comp (continuous_id.mul continuous_const))).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds)
  simpa using this

/-- The tail bound `ν(y > M) ≤ (1 − ∫ e^{-ty} dν)/(1 − e^{-tM})`. -/
theorem measure_Ioi_le_laplace (ν : Measure ℝ) [IsProbabilityMeasure ν] (h0 : ν (Iio 0) = 0)
    {t M : ℝ} (ht : 0 < t) (hM : 0 < M) :
    ν (Ioi M) ≤ ENNReal.ofReal
      ((1 - ∫ y, Real.exp (-(t * y)) ∂ν) / (1 - Real.exp (-(t * M)))) := by
  have hc : 0 < 1 - Real.exp (-(t * M)) := by
    have : Real.exp (-(t * M)) < Real.exp 0 := Real.exp_lt_exp.2 (by nlinarith)
    rw [Real.exp_zero] at this
    linarith
  have hae := ae_nonneg_of_measure_Iio h0
  have hpt : ∀ᵐ y ∂ν, (1 - Real.exp (-(t * M))) * (Ioi M).indicator (1 : ℝ → ℝ) y ≤
      1 - Real.exp (-(t * y)) := by
    filter_upwards [hae] with y hy
    by_cases hyM : y ∈ Ioi M
    · rw [indicator_of_mem hyM, Pi.one_apply, mul_one]
      have : Real.exp (-(t * y)) ≤ Real.exp (-(t * M)) :=
        Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left (le_of_lt hyM) ht.le))
      linarith
    · rw [indicator_of_notMem hyM, mul_zero]
      have : Real.exp (-(t * y)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
      linarith
  have hexp : Integrable (fun y => Real.exp (-(t * y))) ν :=
    (integrable_const (1 : ℝ)).mono'
      (by fun_prop : Continuous fun y => Real.exp (-(t * y))).aestronglyMeasurable
      (hae.mono fun y hy => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
        have : 0 ≤ t * y := mul_nonneg ht.le hy
        linarith)
  have hI1 : Integrable
      (fun y : ℝ => (1 - Real.exp (-(t * M))) * (Ioi M).indicator (1 : ℝ → ℝ) y) ν :=
    ((integrable_const (1 : ℝ)).indicator measurableSet_Ioi).const_mul _
  have hI2 : Integrable (fun y : ℝ => 1 - Real.exp (-(t * y))) ν := (integrable_const _).sub hexp
  have hint := integral_mono_ae hI1 hI2 hpt
  rw [integral_const_mul, integral_indicator_one measurableSet_Ioi,
    integral_sub (integrable_const _) hexp, integral_const, probReal_univ, smul_eq_mul,
    mul_one, measureReal_def] at hint
  have hnn : 0 ≤ 1 - ∫ y, Real.exp (-(t * y)) ∂ν :=
    le_trans (mul_nonneg hc.le ENNReal.toReal_nonneg) hint
  rw [ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (div_nonneg hnn hc.le), le_div_iff₀ hc]
  linarith

/-- **Tightness from Laplace transforms** for a sequence of laws carried by `[0,∞)`. -/
theorem isTightMeasureSet_of_laplace (ν : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (ν n)]
    (ν₀ : Measure ℝ) [IsProbabilityMeasure ν₀] (h0 : ∀ n, ν n (Iio 0) = 0) (h0' : ν₀ (Iio 0) = 0)
    (hL : ∀ t : ℝ, 0 ≤ t → Tendsto (fun n => ∫ y, Real.exp (-(t * y)) ∂(ν n)) atTop
      (𝓝 (∫ y, Real.exp (-(t * y)) ∂ν₀))) :
    IsTightMeasureSet {ν n | n} := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  rcases eq_or_ne ε ⊤ with hεtop | hεtop
  · exact ⟨∅, isCompact_empty, fun _ _ => hεtop ▸ le_top⟩
  have hε'0 : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεtop
  have hc0 : 0 < 1 - Real.exp (-1) := by
    have := Real.exp_lt_exp.2 (show (-1 : ℝ) < 0 by norm_num)
    rw [Real.exp_zero] at this
    linarith
  -- a small `t₀` at which the limit transform is close to `1`, and the tail index `N₀`
  obtain ⟨t₀, ht₀L, ht₀⟩ := (((laplace_tendsto_one ν₀ h0').eventually
    (lt_mem_nhds (by nlinarith : 1 - (1 - Real.exp (-1)) * ε.toReal / 2 < 1))).and
    self_mem_nhdsWithin).exists
  have ht₀0 : 0 < t₀ := ht₀
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 ((hL t₀ ht₀0.le).eventually
    (lt_mem_nhds (show 1 - (1 - Real.exp (-1)) * ε.toReal <
      ∫ y, Real.exp (-(t₀ * y)) ∂ν₀ by nlinarith)))
  -- the initial segment: each law has small tails
  have h3 : ∀ n, ∃ M : ℝ, ν n (Ici M) ≤ ε := fun n => by
    have hmeas := tendsto_measure_iInter_atTop (ι := ℕ) (μ := ν n)
      (s := fun m : ℕ => Ici (m : ℝ)) (fun m => measurableSet_Ici.nullMeasurableSet)
      (fun i j hij => Ici_subset_Ici.2 (by exact_mod_cast hij)) ⟨0, measure_ne_top _ _⟩
    have hempty : ⋂ m : ℕ, Ici (m : ℝ) = ∅ := by
      ext y
      simp only [mem_iInter, mem_Ici, mem_empty_iff_false, iff_false, not_forall, not_le]
      exact exists_nat_gt y
    rw [hempty, measure_empty] at hmeas
    obtain ⟨m, hm⟩ := (hmeas.eventually (Iic_mem_nhds hε)).exists
    exact ⟨m, hm⟩
  choose Ms hMs using h3
  set M : ℝ := 1 / t₀ + ∑ n ∈ Finset.range N₀, |Ms n| with hMdef
  have hM1 : 1 / t₀ ≤ M := le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  have hM0 : 0 < M := lt_of_lt_of_le (by positivity) hM1
  have hMs_le : ∀ n < N₀, Ms n ≤ M := fun n hn =>
    (le_abs_self _).trans ((Finset.single_le_sum (fun _ _ => abs_nonneg _)
      (Finset.mem_range.2 hn)).trans (le_add_of_nonneg_left (by positivity : (0 : ℝ) ≤ 1 / t₀)))
  refine ⟨Icc (-M) M, isCompact_Icc, ?_⟩
  rintro _ ⟨n, rfl⟩
  have hsub : (Icc (-M) M)ᶜ ⊆ Iio 0 ∪ Ioi M := fun y hy => by
    simp only [mem_compl_iff, mem_Icc, not_and_or, not_le] at hy
    rcases hy with hy | hy
    · exact Or.inl (show y < 0 by linarith)
    · exact Or.inr hy
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  rw [h0 n, zero_add]
  rcases lt_or_ge n N₀ with hn | hn
  · exact (measure_mono (Ioi_subset_Ici_self.trans (Ici_subset_Ici.2 (hMs_le n hn)))).trans
      (hMs n)
  · calc ν n (Ioi M) ≤ ν n (Ioi (1 / t₀)) := measure_mono (Ioi_subset_Ioi hM1)
      _ ≤ ENNReal.ofReal ((1 - ∫ y, Real.exp (-(t₀ * y)) ∂(ν n)) /
          (1 - Real.exp (-(t₀ * (1 / t₀))))) :=
          measure_Ioi_le_laplace (ν n) (h0 n) ht₀0 (by positivity)
      _ ≤ ε := by
          rw [mul_one_div_cancel ht₀0.ne', ← ENNReal.ofReal_toReal hεtop]
          have := hN₀ n hn
          exact ENNReal.ofReal_le_ofReal (by rw [div_le_iff₀ hc0]; linarith)

/-- **Laplace continuity theorem on `[0,∞)`**: probability laws on `ℝ` carried by `[0,∞)` whose
Laplace transforms converge at every `t ≥ 0` to those of a law carried by `[0,∞)` converge
weakly. -/
theorem tendsto_of_laplace (ν : ℕ → ProbabilityMeasure ℝ) (ν₀ : ProbabilityMeasure ℝ)
    (h0 : ∀ n, (ν n : Measure ℝ) (Iio 0) = 0) (h0' : (ν₀ : Measure ℝ) (Iio 0) = 0)
    (hL : ∀ t : ℝ, 0 ≤ t → Tendsto (fun n => ∫ y, Real.exp (-(t * y)) ∂(ν n : Measure ℝ)) atTop
      (𝓝 (∫ y, Real.exp (-(t * y)) ∂(ν₀ : Measure ℝ)))) :
    Tendsto ν atTop (𝓝 ν₀) :=
  ProbabilityMeasure.tendsto_of_tight_of_separatesPoints ℝ
    (isTightMeasureSet_of_laplace (fun n => (ν n : Measure ℝ)) ν₀ h0 h0' hL)
    laplaceAlgebra_separatesPoints fun _ hg =>
      laplaceAlgebra_integral_tendsto (fun n => (ν n : Measure ℝ)) ν₀ h0 h0' hL hg

end Grammar
