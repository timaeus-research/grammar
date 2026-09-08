/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.StochasticAssembly

/-!
# Paper-facing bridges for the assembled stochastic Taylor tree (Stage S16)

Unit 285 (review v30 nonblocking improvements). (i) **Exponential residual bridge**
(`tendstoInMeasure_target_of_exp`): if the residual satisfies `E_ℓ e^{εN_ℓ} → 0` in probability
for some `ε > 0` (the paper's `R_n = o_p(e^{-ε' n})`), then `E_ℓ/(N_ℓ^{-μ}(log N_ℓ)^j) → 0` in
probability at every target scale. (ii) **Almost-everywhere decomposition**
(`tendstoInDistribution_assembled_ae`): Headline XXXVII with the chart decomposition
`Z^0_ℓ = ∑_I 𝒵^I(N_ℓ; X_{ℓ,I}) + E_ℓ` required only `μ`-almost everywhere. (iii) The paper-facing
combination (`tendstoInDistribution_assembled_exp`): a.e. decomposition with an exponentially
small residual.

**Index translation.** The paper writes `n^{-μ}(log n)^{m-1}`, `m = 1, …, d`; the formal log degree
is `j = m − 1 ∈ {0, …, D}`, the sample size `N_ℓ` is the paper's `n`, and the ordering `≺` puts
larger log powers first at equal exponent (paper: `(μ,m) < (μ',m')`). **Borel setup.** The
measurable structure on the joint data `JointData K n` is the Borel σ-algebra of the sup-norm
topology, fixed by the declared `MeasurableSpace`/`BorelSpace` instances (not the product
σ-algebra); continuity of the coefficient functionals therefore gives their measurability.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

open scoped Classical

variable {ι Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {l : Filter ι}

/-- **Exponentially small residuals are negligible at every target scale**: if
`E_ℓ · e^{ε N_ℓ} → 0` in probability for some `ε > 0` and `N_ℓ → ∞`, then
`E_ℓ / (N_ℓ^{-μ₀} (log N_ℓ)^j) → 0` in probability for every `μ₀` and `j`. -/
theorem tendstoInMeasure_target_of_exp (E : ι → Ω → ℝ) (Nseq : ι → ℝ) (hN : Tendsto Nseq l atTop)
    {ε : ℝ} (hε : 0 < ε)
    (hE : TendstoInMeasure μ (fun i ω => E i ω * Real.exp (ε * Nseq i)) l (fun _ => 0))
    (μ₀ : ℝ) (j : ℕ) :
    TendstoInMeasure μ (fun i ω => E i ω / (Nseq i ^ (-μ₀) * Real.log (Nseq i) ^ j)) l
      (fun _ => 0) := by
  rw [tendstoInMeasure_iff_norm] at hE ⊢
  intro δ hδ
  have hE' := hE δ hδ
  -- eventually `1 ≤ N^{-μ₀} (log N)^j e^{εN}`, so `|E/D| ≤ |E e^{εN}|`
  have hdet : ∀ᶠ N : ℝ in atTop, 1 ≤ N ^ (-μ₀) * Real.log N ^ j * Real.exp (ε * N) := by
    have h1 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero μ₀ ε hε
    have h2 : ∀ᶠ N : ℝ in atTop, N ^ μ₀ * Real.exp (-ε * N) < 1 :=
      h1.eventually (gt_mem_nhds one_pos)
    filter_upwards [h2, eventually_ge_atTop (Real.exp 1)] with N hN1 hNe
    have hN0 : 0 < N := lt_of_lt_of_le (Real.exp_pos 1) hNe
    have hlog1 : 1 ≤ Real.log N := by
      rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hNe
    have hlj : 1 ≤ Real.log N ^ j := one_le_pow₀ hlog1
    have hpos : 0 < N ^ μ₀ * Real.exp (-ε * N) := by positivity
    have hinv : 1 ≤ N ^ (-μ₀) * Real.exp (ε * N) := by
      have : N ^ (-μ₀) * Real.exp (ε * N) = (N ^ μ₀ * Real.exp (-ε * N))⁻¹ := by
        rw [Real.rpow_neg hN0.le, mul_inv, ← Real.exp_neg]
        congr 1; congr 1; ring
      rw [this]
      exact one_le_inv_iff₀.2 ⟨hpos, hN1.le⟩
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (N ^ (-μ₀) * Real.exp (ε * N)) * Real.log N ^ j :=
          mul_le_mul hinv hlj zero_le_one (by positivity)
      _ = _ := by ring
  have hev := hN.eventually hdet
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hE'
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [hev] with i hi
  refine measure_mono fun ω hω => ?_
  simp only [mem_setOf_eq, sub_zero, Real.norm_eq_abs] at hω ⊢
  have hD : 0 < Nseq i ^ (-μ₀) * Real.log (Nseq i) ^ j * Real.exp (ε * Nseq i) := by
    linarith
  have hDpos : 0 < Nseq i ^ (-μ₀) * Real.log (Nseq i) ^ j := by
    have := Real.exp_pos (ε * Nseq i)
    by_contra hcon
    rw [not_lt] at hcon
    nlinarith
  calc δ ≤ |E i ω / (Nseq i ^ (-μ₀) * Real.log (Nseq i) ^ j)| := hω
    _ = |E i ω| / (Nseq i ^ (-μ₀) * Real.log (Nseq i) ^ j) := by
        rw [abs_div, abs_of_pos hDpos]
    _ ≤ |E i ω| * Real.exp (ε * Nseq i) := by
        rw [div_le_iff₀ hDpos]
        calc |E i ω| = |E i ω| * 1 := by ring
          _ ≤ |E i ω| * (Nseq i ^ (-μ₀) * Real.log (Nseq i) ^ j * Real.exp (ε * Nseq i)) :=
              mul_le_mul_of_nonneg_left hi (abs_nonneg _)
          _ = _ := by ring
    _ = |E i ω * Real.exp (ε * Nseq i)| := by
        rw [abs_mul, abs_of_pos (Real.exp_pos _)]

variable {M : ℕ} {K : Fin M → Type*} [∀ I, TopologicalSpace (K I)] [∀ I, CompactSpace (K I)]
  [∀ I, T2Space (K I)] [∀ I, MeasurableSpace (K I)] [∀ I, OpensMeasurableSpace (K I)]
  {n : Fin M → ℕ} (ν : (I : Fin M) → Measure (K I)) [∀ I, IsFiniteMeasure (ν I)]
  (h k : (I : Fin M) → Fin (n I + 1) → ℕ) (β : ℝ) (b : Fin M → ℝ)

variable {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'} [IsProbabilityMeasure μ']
  [l.IsCountablyGenerated]

/-- **Headline XXXVII with an almost-everywhere chart decomposition.** -/
theorem tendstoInDistribution_assembled_ae (hk : ∀ I i, 0 < k I i) (hβ : 0 < β)
    (hb : ∀ I, 0 < b I) {μ₀ : ℝ} (hμ : ∃ m : ℕ, μ₀ = (m : ℝ) / commonQ k) {j : ℕ}
    (hj : j ≤ commonD n) (X : ι → Ω → JointData K n) (hXm : ∀ i, Measurable (X i))
    (Z : Ω' → JointData K n) (hX : TendstoInDistribution X l Z (fun _ => μ) μ') (Nseq : ι → ℝ)
    (hN0 : ∀ i, 0 ≤ Nseq i) (hN : Tendsto Nseq l atTop) (Zg E : ι → Ω → ℝ)
    (hZm : ∀ i, Measurable (Zg i))
    (hdecomp : ∀ i, ∀ᵐ ω ∂μ, Zg i ω = gInt ν h k β b (X i ω) (Nseq i) + E i ω)
    (hE : TendstoInMeasure μ (fun i ω => E i ω / (Nseq i ^ (-μ₀) * Real.log (Nseq i) ^ j)) l
      (fun _ => 0)) :
    TendstoInDistribution (fun i ω =>
        (Zg i ω - absPredSum (commonQ k) (commonD n) (gCoeff ν h k β b (X i ω)) μ₀ j (Nseq i)) /
          (Nseq i ^ (-μ₀) * Real.log (Nseq i) ^ j)) l
      (fun ω => gCoeff ν h k β b (Z ω) μ₀ j) (fun _ => μ) μ' := by
  have hR := tendstoInDistribution_gRemainder ν h k β b hk hβ hb hμ hj X hXm Z hX Nseq hN0 hN
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ hR ?_ fun i => ?_
  · refine TendstoInMeasure.congr (fun i => ?_) (Eventually.of_forall fun _ => rfl) hE
    filter_upwards [hdecomp i] with ω hω
    simp only [Pi.sub_apply]
    unfold gRemainder abstractRemainder
    rw [hω]
    ring
  · refine Measurable.aemeasurable (Measurable.div_const (Measurable.sub (hZm i) ?_) _)
    unfold absPredSum absTerm
    exact Finset.measurable_sum _ fun p _ =>
      (((continuous_gCoeff ν h k β b hk hβ hb p.1 p.2).measurable).comp (hXm i)).mul_const _

/-- **Headline XXXVII, paper-facing form**: a.e. chart decomposition with an exponentially small
residual `E_ℓ e^{εN_ℓ} → 0` in probability (the paper's `R_n = o_p(e^{-ε' n})`). -/
theorem tendstoInDistribution_assembled_exp (hk : ∀ I i, 0 < k I i) (hβ : 0 < β)
    (hb : ∀ I, 0 < b I) {μ₀ : ℝ} (hμ : ∃ m : ℕ, μ₀ = (m : ℝ) / commonQ k) {j : ℕ}
    (hj : j ≤ commonD n) (X : ι → Ω → JointData K n) (hXm : ∀ i, Measurable (X i))
    (Z : Ω' → JointData K n) (hX : TendstoInDistribution X l Z (fun _ => μ) μ') (Nseq : ι → ℝ)
    (hN0 : ∀ i, 0 ≤ Nseq i) (hN : Tendsto Nseq l atTop) (Zg E : ι → Ω → ℝ)
    (hZm : ∀ i, Measurable (Zg i))
    (hdecomp : ∀ i, ∀ᵐ ω ∂μ, Zg i ω = gInt ν h k β b (X i ω) (Nseq i) + E i ω) {ε : ℝ}
    (hε : 0 < ε)
    (hE : TendstoInMeasure μ (fun i ω => E i ω * Real.exp (ε * Nseq i)) l (fun _ => 0)) :
    TendstoInDistribution (fun i ω =>
        (Zg i ω - absPredSum (commonQ k) (commonD n) (gCoeff ν h k β b (X i ω)) μ₀ j (Nseq i)) /
          (Nseq i ^ (-μ₀) * Real.log (Nseq i) ^ j)) l
      (fun ω => gCoeff ν h k β b (Z ω) μ₀ j) (fun _ => μ) μ' :=
  tendstoInDistribution_assembled_ae ν h k β b hk hβ hb hμ hj X hXm Z hX Nseq hN0 hN Zg E hZm
    hdecomp (tendstoInMeasure_target_of_exp E Nseq hN hε hE μ₀ j)

end Grammar
