/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.AssemblyBridges

/-!
# Quotients converge in distribution when the limiting denominator is a.s. nonzero (Stage S17)

Unit 286 (Astra #35, tranche A4-L: the generic quotient theorem). If the pairs
`(Y_ℓ, W_ℓ) ⇒ (A, B)` jointly in distribution (measurable real random variables) and
`P(B = 0) = 0`, then `Y_ℓ / W_ℓ ⇒ A / B` (`tendstoInDistribution_div`). No continuous mapping
theorem for a.s.-continuous maps is needed: the truncated division
`T_δ(a, b) = a b / max(b², δ²)` is globally continuous and agrees with `a / b` on `|b| ≥ δ`; for a
test function `f` of oscillation `≤ C`, `|∫ f(Y/W) − ∫ f(T_δ(Y,W))| ≤ C·P(|W| ≤ δ)`, portmanteau
bounds `limsup P(|W_ℓ| ≤ δ)` by `P(|B| ≤ δ)`, which tends to `0` as `δ ↓ 0` because `P(B = 0) = 0`,
and continuous mapping handles `T_δ` at fixed `δ`. Division is Lean's totalised division: the value
of `A/B` on the null set `{B = 0}` is irrelevant to its law; nothing is claimed about `W_ℓ ≠ 0`
almost surely at finite `ℓ`. A scaled form (`tendstoInDistribution_div_of_scaled`) removes a common
deterministic normalisation `a_ℓ` from numerator and denominator.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

variable {ι Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {μ' : Measure Ω'} [IsProbabilityMeasure μ'] {l : Filter ι}
  [l.IsCountablyGenerated]

/-- The truncated division `T_δ(a, b) = a b / max(b², δ²)`. -/
noncomputable def truncDiv (δ : ℝ) (p : ℝ × ℝ) : ℝ := p.1 * p.2 / max (p.2 ^ 2) (δ ^ 2)

theorem continuous_truncDiv {δ : ℝ} (hδ : 0 < δ) : Continuous (truncDiv δ) := by
  unfold truncDiv
  refine (continuous_fst.mul continuous_snd).div
    ((continuous_snd.pow 2).max continuous_const) fun p => ?_
  exact ne_of_gt (lt_of_lt_of_le (pow_pos hδ 2) (le_max_right _ _))

/-- On `|b| ≥ δ > 0` the truncated division is the division. -/
theorem truncDiv_eq_div {δ : ℝ} (hδ : 0 < δ) {a b : ℝ} (hb : δ ≤ |b|) :
    truncDiv δ (a, b) = a / b := by
  unfold truncDiv
  have hb0 : b ≠ 0 := by
    intro h; rw [h, abs_zero] at hb; linarith
  have hsq : δ ^ 2 ≤ b ^ 2 := by
    rw [← sq_abs b]; exact pow_le_pow_left₀ hδ.le hb 2
  simp only
  rw [max_eq_left hsq, pow_two]
  field_simp

/-- Comparison of a test function with bounded oscillation along the division and the truncated
division: the difference is supported on `{|V| ≤ δ}` and bounded by the oscillation `C`. -/
theorem abs_integral_div_sub_truncDiv_le {Ω'' : Type*} [MeasurableSpace Ω''] (ν : Measure Ω'')
    [IsProbabilityMeasure ν] {f : ℝ → ℝ} (hfc : Continuous f) {C : ℝ}
    (hfC : ∀ x y, dist (f x) (f y) ≤ C) {δ : ℝ} (hδ : 0 < δ) {U V : Ω'' → ℝ}
    (hU : Measurable U) (hV : Measurable V) :
    |∫ ω, f (U ω / V ω) ∂ν - ∫ ω, f (truncDiv δ (U ω, V ω)) ∂ν| ≤
      C * (ν {ω | |V ω| ≤ δ}).toReal := by
  have hfm : Measurable f := hfc.measurable
  have hfb : ∀ x, ‖f x‖ ≤ ‖f 0‖ + C := fun x => by
    have := hfC x 0
    rw [Real.dist_eq] at this
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    linarith [abs_sub_abs_le_abs_sub (f x) (f 0)]
  have hS : MeasurableSet {ω | |V ω| ≤ δ} := measurableSet_le hV.abs measurable_const
  have hUV : Measurable fun ω => (U ω, V ω) := hU.prodMk hV
  have h1 : Integrable (fun ω => f (U ω / V ω)) ν :=
    (integrable_const (‖f 0‖ + C)).mono' (hfm.comp (hU.div hV)).aestronglyMeasurable
      (Eventually.of_forall fun ω => hfb _)
  have h2 : Integrable (fun ω => f (truncDiv δ (U ω, V ω))) ν :=
    (integrable_const (‖f 0‖ + C)).mono'
      (hfm.comp ((continuous_truncDiv hδ).measurable.comp hUV)).aestronglyMeasurable
      (Eventually.of_forall fun ω => hfb _)
  rw [← integral_sub h1 h2]
  have hind : ∀ ω, ‖f (U ω / V ω) - f (truncDiv δ (U ω, V ω))‖ ≤
      {ω | |V ω| ≤ δ}.indicator (fun _ => C) ω := by
    intro ω
    by_cases hω : |V ω| ≤ δ
    · rw [indicator_of_mem (show ω ∈ {ω | |V ω| ≤ δ} from hω)]
      have := hfC (U ω / V ω) (truncDiv δ (U ω, V ω))
      rwa [Real.dist_eq, ← Real.norm_eq_abs] at this
    · rw [indicator_of_notMem (show ω ∉ {ω | |V ω| ≤ δ} from hω),
        truncDiv_eq_div hδ (not_le.1 hω).le, sub_self, norm_zero]
  have hint : Integrable ({ω | |V ω| ≤ δ}.indicator fun _ => (C : ℝ)) ν :=
    (integrable_const _).indicator hS
  have := norm_integral_le_of_norm_le hint (Eventually.of_forall hind)
  rw [Real.norm_eq_abs, integral_indicator_const _ hS, smul_eq_mul, measureReal_def] at this
  linarith

/-- The tail probabilities `P(|B| ≤ 1/(m+1))` tend to `P(B = 0)`, which is zero. -/
theorem tendsto_measure_abs_le_of_ae_ne_zero (B : Ω' → ℝ) (hBm : Measurable B)
    (hB : μ' {ω | B ω = 0} = 0) :
    Tendsto (fun m : ℕ => μ' {ω | |B ω| ≤ 1 / ((m : ℝ) + 1)}) atTop (𝓝 0) := by
  have hnull : ∀ m : ℕ, NullMeasurableSet {ω | |B ω| ≤ 1 / ((m : ℝ) + 1)} μ' := fun m =>
    (measurableSet_le hBm.abs measurable_const).nullMeasurableSet
  have hanti : Antitone fun m : ℕ => {ω | |B ω| ≤ 1 / ((m : ℝ) + 1)} := by
    intro m m' hmm' ω hω
    simp only [mem_setOf_eq] at hω ⊢
    refine hω.trans (one_div_le_one_div_of_le (by positivity) ?_)
    exact_mod_cast Nat.succ_le_succ hmm'
  have h := tendsto_measure_iInter_atTop (μ := μ') hnull hanti ⟨0, measure_ne_top _ _⟩
  have hinter : (⋂ m : ℕ, {ω | |B ω| ≤ 1 / ((m : ℝ) + 1)}) = {ω | B ω = 0} := by
    ext ω
    simp only [mem_iInter, mem_setOf_eq]
    constructor
    · intro hall
      by_contra hne
      have hpos : 0 < |B ω| := abs_pos.2 hne
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt hpos
      exact absurd (hall m) (not_le.2 hm)
    · intro h0 m
      rw [h0, abs_zero]; positivity
  rw [hinter, hB] at h
  exact h

/-- **Quotients converge in distribution.** If `(Y_ℓ, W_ℓ) ⇒ (A, B)` jointly and `P(B = 0) = 0`,
then `Y_ℓ / W_ℓ ⇒ A / B`. -/
theorem tendstoInDistribution_div (Y W : ι → Ω → ℝ) (hYm : ∀ i, Measurable (Y i))
    (hWm : ∀ i, Measurable (W i)) (A B : Ω' → ℝ) (hAm : Measurable A) (hBm : Measurable B)
    (hYW : TendstoInDistribution (fun i ω => (Y i ω, W i ω)) l (fun ω => (A ω, B ω))
      (fun _ => μ) μ')
    (hB : μ' {ω | B ω = 0} = 0) :
    TendstoInDistribution (fun i ω => Y i ω / W i ω) l (fun ω => A ω / B ω) (fun _ => μ) μ' := by
  have hmY : ∀ i, AEMeasurable (fun ω => Y i ω / W i ω) μ := fun i =>
    ((hYm i).div (hWm i)).aemeasurable
  have hmAB : AEMeasurable (fun ω => A ω / B ω) μ' := (hAm.div hBm).aemeasurable
  have hW : TendstoInDistribution W l B (fun _ => μ) μ' :=
    hYW.continuous_comp (g := Prod.snd) continuous_snd
  refine ⟨hmY, hmAB, ?_⟩
  refine (tendsto_iff_forall_lipschitz_integral_tendsto (Ω := ℝ)).2 ?_
  rintro f ⟨C, hfC⟩ ⟨L, hfL⟩
  have hfc : Continuous f := hfL.continuous
  simp only [ProbabilityMeasure.coe_mk]
  have hfm : Measurable f := hfc.measurable
  have hrwL : ∫ y, f y ∂(μ'.map fun ω => A ω / B ω) = ∫ ω, f (A ω / B ω) ∂μ' :=
    integral_map hmAB hfm.aestronglyMeasurable
  have hrw : ∀ i, ∫ y, f y ∂(μ.map fun ω => Y i ω / W i ω) = ∫ ω, f (Y i ω / W i ω) ∂μ :=
    fun i => integral_map (hmY i) hfm.aestronglyMeasurable
  simp_rw [hrw, hrwL]
  have hC0 : 0 ≤ C := le_trans dist_nonneg (hfC 0 0)
  rw [Metric.tendsto_nhds]
  intro ε hε
  set η : ℝ := ε / (6 * (C + 1)) with hη
  have hη0 : 0 < η := by positivity
  -- choose `δ = 1/(m+1)` with `P(|B| ≤ δ) < η`
  obtain ⟨m, hm⟩ := ((tendsto_measure_abs_le_of_ae_ne_zero B hBm hB).eventually
    (gt_mem_nhds (ENNReal.ofReal_pos.2 hη0))).exists
  set δ : ℝ := 1 / ((m : ℝ) + 1) with hδ
  have hδ0 : 0 < δ := by positivity
  -- portmanteau: eventually `P(|W_i| ≤ δ) < η`
  have hF : IsClosed {b : ℝ | |b| ≤ δ} := isClosed_le continuous_abs continuous_const
  have hport := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hW.tendsto hF
  simp only [ProbabilityMeasure.coe_mk] at hport
  have hmap : ∀ i, (μ.map (W i)) {b | |b| ≤ δ} = μ {ω | |W i ω| ≤ δ} := fun i =>
    Measure.map_apply (hWm i) hF.measurableSet
  have hmap' : (μ'.map B) {b | |b| ≤ δ} = μ' {ω | |B ω| ≤ δ} :=
    Measure.map_apply hBm hF.measurableSet
  simp only [hmap, hmap'] at hport
  have hev1 : ∀ᶠ i in l, μ {ω | |W i ω| ≤ δ} < ENNReal.ofReal η :=
    eventually_lt_of_limsup_lt (lt_of_le_of_lt hport hm)
  -- continuous mapping at the fixed truncation `δ`
  have hT := hYW.continuous_comp (g := truncDiv δ) (continuous_truncDiv hδ0)
  have hTt := (tendsto_iff_forall_lipschitz_integral_tendsto.1 hT.tendsto) f ⟨C, hfC⟩ ⟨L, hfL⟩
  simp only [ProbabilityMeasure.coe_mk] at hTt
  have hrwT : ∀ i, ∫ y, f y ∂(μ.map fun ω => truncDiv δ (Y i ω, W i ω)) =
      ∫ ω, f (truncDiv δ (Y i ω, W i ω)) ∂μ := fun i =>
    integral_map (hT.forall_aemeasurable i) hfm.aestronglyMeasurable
  have hrwTL : ∫ y, f y ∂(μ'.map fun ω => truncDiv δ (A ω, B ω)) =
      ∫ ω, f (truncDiv δ (A ω, B ω)) ∂μ' :=
    integral_map hT.aemeasurable_limit hfm.aestronglyMeasurable
  simp_rw [Function.comp_def, hrwT, hrwTL] at hTt
  rw [Metric.tendsto_nhds] at hTt
  have hev2 := hTt (ε / 3) (by positivity)
  filter_upwards [hev1, hev2] with i hi1 hi2
  have hA1 := abs_integral_div_sub_truncDiv_le μ hfc hfC hδ0 (hYm i) (hWm i)
  have hA2 := abs_integral_div_sub_truncDiv_le μ' hfc hfC hδ0 hAm hBm
  have hr1 : (μ {ω | |W i ω| ≤ δ}).toReal < η := ENNReal.toReal_lt_of_lt_ofReal hi1
  have hr2 : (μ' {ω | |B ω| ≤ δ}).toReal < η := ENNReal.toReal_lt_of_lt_ofReal hm
  rw [Real.dist_eq] at hi2 ⊢
  have h2Cη : C * η ≤ ε / 3 := by
    rw [hη]
    rw [show C * (ε / (6 * (C + 1))) = ε / 6 * (C / (C + 1)) by field_simp]
    have : C / (C + 1) ≤ 1 := div_le_one_of_le₀ (by linarith) (by positivity)
    nlinarith
  have hb1 : C * (μ {ω | |W i ω| ≤ δ}).toReal ≤ C * η :=
    mul_le_mul_of_nonneg_left hr1.le hC0
  have hb2 : C * (μ' {ω | |B ω| ≤ δ}).toReal ≤ C * η :=
    mul_le_mul_of_nonneg_left hr2.le hC0
  have htri1 := abs_sub_le (∫ ω, f (Y i ω / W i ω) ∂μ) (∫ ω, f (truncDiv δ (Y i ω, W i ω)) ∂μ)
    (∫ ω, f (A ω / B ω) ∂μ')
  have htri2 := abs_sub_le (∫ ω, f (truncDiv δ (Y i ω, W i ω)) ∂μ)
    (∫ ω, f (truncDiv δ (A ω, B ω)) ∂μ') (∫ ω, f (A ω / B ω) ∂μ')
  rw [abs_sub_comm (∫ ω, f (truncDiv δ (A ω, B ω)) ∂μ')] at htri2
  linarith

/-- **Scaled quotients**: if `(U_ℓ/a_ℓ, V_ℓ/a_ℓ) ⇒ (A, B)` for a deterministic normalisation `a_ℓ`
and `P(B = 0) = 0`, then `U_ℓ/V_ℓ ⇒ A/B` (the normalisation cancels, at every index where
`a_ℓ ≠ 0`; where `a_ℓ = 0` both quotients are compared through the totalised division). -/
theorem tendstoInDistribution_div_of_scaled (U V : ι → Ω → ℝ) (a : ι → ℝ) (ha : ∀ i, a i ≠ 0)
    (hUm : ∀ i, Measurable (U i)) (hVm : ∀ i, Measurable (V i)) (A B : Ω' → ℝ)
    (hAm : Measurable A) (hBm : Measurable B)
    (hUV : TendstoInDistribution (fun i ω => (U i ω / a i, V i ω / a i)) l (fun ω => (A ω, B ω))
      (fun _ => μ) μ')
    (hB : μ' {ω | B ω = 0} = 0) :
    TendstoInDistribution (fun i ω => U i ω / V i ω) l (fun ω => A ω / B ω) (fun _ => μ) μ' := by
  have h := tendstoInDistribution_div (fun i ω => U i ω / a i) (fun i ω => V i ω / a i)
    (fun i => (hUm i).div_const _) (fun i => (hVm i).div_const _) A B hAm hBm hUV hB
  have heq : (fun i ω => U i ω / a i / (V i ω / a i)) = fun i ω => U i ω / V i ω := by
    funext i ω
    exact div_div_div_cancel_right₀ (ha i) _ _
  rw [heq] at h
  exact h

end Grammar
