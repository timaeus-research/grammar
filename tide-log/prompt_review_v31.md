# Fidelity review v31 — Programme S tranche A4-L, units 286–287: quotients in distribution and the leading-order posterior quotient (Headline XXXVIII)

You are an independent statement-level reviewer of a Lean 4 / Mathlib formalisation (repository `timaeus-research/grammar`, branch `tide/stochastic-taylor-tree`, pin `e0ab5ba`) of the grammar paper's §4.3. Reviews v27–v30 passed units 270–285 (Programme S: Headlines XXXIV–XXXVII′ — the stochastic Taylor tree at chart level, after tangential integration, and after finite chart assembly with an external decomposition; all conditional on joint convergence in distribution of the weighted-ℓ¹ tangential data). Astra consult #35 authorised tranche A4-L: the leading-order posterior quotient only (`cor:empirical_expectation`'s leading term), with the statement gate: generic theorem "`(Y_ℓ,W_ℓ) ⇒ (A,B)` jointly and `P(B = 0) = 0` ⇒ `Y_ℓ/W_ℓ ⇒ A/B`" via the truncated division `T_δ(a,b) = ab/max(b²,δ²)`; assembled corollary with numerator/denominator as one jointly convergent datum, predecessor sums vanishing at the SOURCE (not merely at the limit), the leading scale `a_ℓ = N_ℓ^{-μ₀}(log N_ℓ)^{j₀}`, and `P(C¹_{μ₀,j₀}(X) = 0) = 0`; NO all-orders expansion, no random leading index, no derivation of positivity. Units 286–287 implement this. Please review the STATEMENTS (mechanical excerpts, docstring + statement up to `:=`; the extractor may truncate/duplicate — the source has exactly one of each; everything compiles with zero `sorry` and no additional axioms) and the two proofs reproduced in full.

Background (frozen): `gInt ν h k β b x N = ∑_I ∫_{K_I} Z(N; x_I v) dν_I` (assembled integral), `gCoeff ν h k β b x μ j = ∑_I ∫ C_{μ,j}(x_I v) dν_I` (assembled canonical coefficient), `absPredSum Q D c μ j N = ∑_{(ν,q) ≺ (μ,j)} c ν q · N^{-ν}(log N)^q` over the finite predecessor set on the common lattice `Q = commonQ k`, degree `D = commonD n`; `gRemainder ν h k β b x μ j N = (gInt x N − absPredSum Q D (gCoeff x) μ j N)/(N^{-μ}(log N)^j)`; Headline XXXVII: `gRemainder(X_ℓ)(N_ℓ) ⇒ gCoeff(X) μ j`; `tendstoUniformlyOn_gRemainder` (uniform on joint balls); `tendstoInMeasure_zero_of_uniform_on_balls''` (vector-valued errors, uniform smallness on balls + norm-boundedness in probability ⇒ convergence in probability), `normBounded_of_tendstoInDistribution'`; Mathlib `tendstoInDistribution_of_tendstoInMeasure_sub` (Slutsky), `TendstoInDistribution.continuous_comp`, `tendsto_iff_forall_lipschitz_integral_tendsto` (weak convergence ↔ integrals of bounded Lipschitz test functions; needs `l.IsCountablyGenerated`), `ProbabilityMeasure.limsup_measure_closed_le_of_tendsto` (portmanteau).

## Statements

### Grammar/QuotientInDistribution.lean

Ambient `variable` lines (as written in the file):
```lean
variable {ι Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {μ' : Measure Ω'} [IsProbabilityMeasure μ'] {l : Filter ι}
  [l.IsCountablyGenerated]
```

```lean
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

```
### Grammar/PosteriorLeading.lean

Ambient `variable` lines (as written in the file):
```lean
variable {ι Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {μ' : Measure Ω'} [IsProbabilityMeasure μ'] {l : Filter ι}
variable {M : ℕ} {K : Fin M → Type*} [∀ I, TopologicalSpace (K I)] [∀ I, CompactSpace (K I)]
  [∀ I, T2Space (K I)] [∀ I, MeasurableSpace (K I)] [∀ I, OpensMeasurableSpace (K I)]
  {n : Fin M → ℕ}
variable (ν : (I : Fin M) → Measure (K I)) [∀ I, IsFiniteMeasure (ν I)]
  (h k : (I : Fin M) → Fin (n I + 1) → ℕ) (β : ℝ) (b : Fin M → ℝ)
variable {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'} [IsProbabilityMeasure μ']
  [l.IsCountablyGenerated]
```

```lean
/-!
# The leading-order posterior quotient after chart assembly (Stage S18 — Headline XXXVIII)

Unit 287 (Astra #35, tranche A4-L). Numerator and denominator of the posterior expectation
`E[φ] = Z^0[φ]/Z^0[1]` are the assembled integrals of two amplitude families on the same charts
(`η_φ = φ·η_1` and `η_1`, common phase); their joint tangential data form `PairData K n =
JointData K n × JointData K n` (sup norm, Borel σ-algebra by declared instances; `.den`, `.num`).
Let `(X_ℓ, Y_ℓ) ⇒ (X, Y)` jointly, `N_ℓ → ∞`, `N_ℓ > 1`, and let the external a.e. decompositions
`Z^0_ℓ[1] = 𝒵^{glob}(N_ℓ; X_ℓ) + E¹_ℓ`, `Z^0_ℓ[φ] = 𝒵^{glob}(N_ℓ; Y_ℓ) + E^φ_ℓ` hold with residuals
negligible in probability at the leading scale `a_ℓ = N_ℓ^{-μ₀}(log N_ℓ)^{j₀}`. Suppose the target
`(μ₀, j₀)` is **leading at the source**: all predecessor sums vanish a.s. for both families, and
the limiting denominator coefficient is a.s. nonzero, `P(C¹_{μ₀,j₀}(X) = 0) = 0`. Then

`Z^0_ℓ[φ] / Z^0_ℓ[1] ⇒ C^φ_{μ₀,j₀}(Y) / C¹_{μ₀,j₀}(X)`

(`tendstoInDistribution_posterior_leading`, **Headline XXXVIII**): the leading-order clause of
`cor:empirical_expectation` after finite chart assembly in arbitrary normal dimensions. Route:
joint convergence of the normalised pair `(Z^0[φ]/a, Z^0[1]/a)` by vector Slutsky (the pair of
assembled remainders converges in probability to the pair of coefficients; residuals and vanishing
predecessors enter through a.e. congruence), then the generic quotient theorem of unit 286.
Non-claims: no all-orders quotient expansion; the leading target is deterministic and given;
predecessor vanishing at the LIMIT alone would not suffice; finite-sample positivity of `Z^0[1]` is
a separate application fact; no randomness of the leading index; joint convergence is a hypothesis.
-/

theorem of unit 286.
Non-claims: no all-orders quotient expansion; the leading target is deterministic and given;
predecessor vanishing at the LIMIT alone would not suffice; finite-sample positivity of `Z^0[1]` is
a separate application fact; no randomness of the leading index; joint convergence is a hypothesis.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

open scoped Classical

variable {ι Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {μ' : Measure Ω'} [IsProbabilityMeasure μ'] {l : Filter ι}

/-! ### Two small in-measure lemmas -/

theorem tendstoInMeasure_add_zero {E : Type*} [NormedAddCommGroup E] {f g : ι → Ω → E}
    (hf : TendstoInMeasure μ f l (fun _ => 0)) (hg : TendstoInMeasure μ g l (fun _ => 0)) :
    TendstoInMeasure μ (fun i ω => f i ω + g i ω) l (fun _ => 0) := by
  rw [tendstoInMeasure_iff_norm] at hf hg ⊢
  intro ε hε
  have h1 := hf (ε / 2) (half_pos hε)
  have h2 := hg (ε / 2) (half_pos hε)
  have := h1.add h2
  rw [add_zero] at this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds this
    (Eventually.of_forall fun _ => bot_le) (Eventually.of_forall fun i => ?_)
  refine (measure_mono fun ω hω => ?_).trans (measure_union_le _ _)
  simp only [mem_setOf_eq, sub_zero, mem_union] at hω ⊢
  by_contra hcon
  push Not at hcon
  have := norm_add_le (f i ω) (g i ω)
  linarith [hcon.1, hcon.2]

theorem tendstoInMeasure_prodMk_zero' {f g : ι → Ω → ℝ}
    (hf : TendstoInMeasure μ f l (fun _ => 0)) (hg : TendstoInMeasure μ g l (fun _ => 0)) :
    TendstoInMeasure μ (fun i ω => (f i ω, g i ω)) l (fun _ => (0 : ℝ × ℝ)) := by
  rw [tendstoInMeasure_iff_norm] at hf hg ⊢
  intro ε hε
  have := (hf ε hε).add (hg ε hε)
  rw [add_zero] at this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds this
    (Eventually.of_forall fun _ => bot_le) (Eventually.of_forall fun i => ?_)
  refine (measure_mono fun ω hω => ?_).trans (measure_union_le _ _)
  simp only [mem_setOf_eq, sub_zero, mem_union, Prod.norm_def, Prod.fst_zero, Prod.snd_zero] at hω ⊢
  rcases le_max_iff.1 hω with h | h
  · exact Or.inl h
  · exact Or.inr h

/-! ### Pair data -/

variable {M : ℕ} {K : Fin M → Type*} [∀ I, TopologicalSpace (K I)] [∀ I, CompactSpace (K I)]
  [∀ I, T2Space (K I)] [∀ I, MeasurableSpace (K I)] [∀ I, OpensMeasurableSpace (K I)]
  {n : Fin M → ℕ}

/-- Joint tangential data of the denominator (first) and numerator (second) families. -/
def PairData (K : Fin M → Type*) [∀ I, TopologicalSpace (K I)] (n : Fin M → ℕ) :=
  JointData K n × JointData K n

noncomputable instance : NormedAddCommGroup (PairData K n) :=
  inferInstanceAs (NormedAddCommGroup (JointData K n × JointData K n))
noncomputable instance : MeasurableSpace (PairData K n) := borel (PairData K n)
instance : BorelSpace (PairData K n) := ⟨rfl⟩

/-- The denominator datum. -/
def PairData.den (p : PairData K n) : JointData K n := p.1
/-- The numerator datum. -/
def PairData.num (p : PairData K n) : JointData K n := p.2

theorem continuous_den : Continuous fun p : PairData K n => p.den :=
  (continuous_fst : Continuous fun p : JointData K n × JointData K n => p.1)

theorem continuous_num : Continuous fun p : PairData K n => p.num :=
  (continuous_snd : Continuous fun p : JointData K n × JointData K n => p.2)

theorem norm_den_le (p : PairData K n) : ‖p.den‖ ≤ ‖p‖ :=
  norm_fst_le (p : JointData K n × JointData K n)

theorem norm_num_le (p : PairData K n) : ‖p.num‖ ≤ ‖p‖ :=
  norm_snd_le (p : JointData K n × JointData K n)

variable (ν : (I : Fin M) → Measure (K I)) [∀ I, IsFiniteMeasure (ν I)]
  (h k : (I : Fin M) → Fin (n I + 1) → ℕ) (β : ℝ) (b : Fin M → ℝ)

/-- The pair of leading coefficients `(C^φ_{μ,j}(num), C¹_{μ,j}(den))`. -/
noncomputable def pairCoeff (p : PairData K n) (μ₀ : ℝ) (j : ℕ) : ℝ × ℝ :=
  (gCoeff ν h k β b p.num μ₀ j, gCoeff ν h k β b p.den μ₀ j)

theorem continuous_pairCoeff (hk : ∀ I i, 0 < k I i) (hβ : 0 < β) (hb : ∀ I, 0 < b I) (μ₀ : ℝ)
    (j : ℕ) : Continuous fun p : PairData K n => pairCoeff ν h k β b p μ₀ j :=
  ((continuous_gCoeff ν h k β b hk hβ hb μ₀ j).comp continuous_num).prodMk
    ((continuous_gCoeff ν h k β b hk hβ hb μ₀ j).comp continuous_den)

/-- The pair of assembled remainders minus the pair of coefficients tends to zero in probability. -/
theorem tendstoInMeasure_pairRemainder_sub (hk : ∀ I i, 0 < k I i) (hβ : 0 < β) (hb : ∀ I, 0 < b I)
    {μ₀ : ℝ} (hμ : ∃ m : ℕ, μ₀ = (m : ℝ) / commonQ k) {j : ℕ} (hj : j ≤ commonD n)
    (XY : ι → Ω → PairData K n) (Z : Ω' → PairData K n)
    (hXY : TendstoInDistribution XY l Z (fun _ => μ) μ') (Nseq : ι → ℝ)
    (hN : Tendsto Nseq l atTop) :
    TendstoInMeasure μ (fun i ω =>
      (gRemainder ν h k β b (XY i ω).num μ₀ j (Nseq i) - gCoeff ν h k β b (XY i ω).num μ₀ j,
       gRemainder ν h k β b (XY i ω).den μ₀ j (Nseq i) - gCoeff ν h k β b (XY i ω).den μ₀ j))
      l (fun _ => (0 : ℝ × ℝ)) := by
  refine tendstoInMeasure_zero_of_uniform_on_balls'' _ XY (fun R hR ε hε => ?_)
    (normBounded_of_tendstoInDistribution' XY Z hXY)
  have hu := Metric.tendstoUniformlyOn_iff.1
    (tendstoUniformlyOn_gRemainder ν h k β b hk hβ hb hμ hj R) ε hε
  filter_upwards [hN.eventually hu] with i hi ω hω
  have h1 := hi (XY i ω).num (by simpa using (norm_num_le (XY i ω)).trans hω)
  have h2 := hi (XY i ω).den (by simpa using (norm_den_le (XY i ω)).trans hω)
  rw [Real.dist_eq, abs_sub_comm] at h1 h2
  rw [Prod.norm_def]
  exact max_le (by simpa [Real.norm_eq_abs] using h1.le) (by simpa [Real.norm_eq_abs] using h2.le)

variable {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'} [IsProbabilityMeasure μ']
  [l.IsCountablyGenerated]

/-- **Joint convergence of the normalised numerator and denominator** at a source-leading target. -/
theorem tendstoInDistribution_pair_normalised (hk : ∀ I i, 0 < k I i) (hβ : 0 < β)
    (hb : ∀ I, 0 < b I) {μ₀ : ℝ} (hμ : ∃ m : ℕ, μ₀ = (m : ℝ) / commonQ k) {j₀ : ℕ}
    (hj : j₀ ≤ commonD n) (XY : ι → Ω → PairData K n) (hXYm : ∀ i, Measurable (XY i))
    (Z : Ω' → PairData K n) (hXY : TendstoInDistribution XY l Z (fun _ => μ) μ') (Nseq : ι → ℝ)
    (hN1 : ∀ i, 1 < Nseq i) (hN : Tendsto Nseq l atTop) (Zφ Z1 Eφ E1 : ι → Ω → ℝ)
    (hZφm : ∀ i, Measurable (Zφ i)) (hZ1m : ∀ i, Measurable (Z1 i))
    (hdφ : ∀ i, ∀ᵐ ω ∂μ, Zφ i ω = gInt ν h k β b (XY i ω).num (Nseq i) + Eφ i ω)
    (hd1 : ∀ i, ∀ᵐ ω ∂μ, Z1 i ω = gInt ν h k β b (XY i ω).den (Nseq i) + E1 i ω)
    (hEφ : TendstoInMeasure μ (fun i ω => Eφ i ω / (Nseq i ^ (-μ₀) * Real.log (Nseq i) ^ j₀)) l
      (fun _ => 0))
    (hE1 : TendstoInMeasure μ (fun i ω => E1 i ω / (Nseq i ^ (-μ₀) * Real.log (Nseq i) ^ j₀)) l
      (fun _ => 0))
    (hpφ : ∀ i, ∀ᵐ ω ∂μ,
      absPredSum (commonQ k) (commonD n) (gCoeff ν h k β b (XY i ω).num) μ₀ j₀ (Nseq i) = 0)
    (hp1 : ∀ i, ∀ᵐ ω ∂μ,
      absPredSum (commonQ k) (commonD n) (gCoeff ν h k β b (XY i ω).den) μ₀ j₀ (Nseq i) = 0) :
    TendstoInDistribution (fun i ω => (Zφ i ω / (Nseq i ^ (-μ₀) * Real.log (Nseq i) ^ j₀),
        Z1 i ω / (Nseq i ^ (-μ₀) * Real.log (Nseq i) ^ j₀))) l
      (fun ω => pairCoeff ν h k β b (Z ω) μ₀ j₀) (fun _ => μ) μ' := by
  have hC : TendstoInDistribution (fun i ω => pairCoeff ν h k β b (XY i ω) μ₀ j₀) l
      (fun ω => pairCoeff ν h k β b (Z ω) μ₀ j₀) (fun _ => μ) μ' :=
    hXY.continuous_comp (g := fun p => pairCoeff ν h k β b p μ₀ j₀)
      (continuous_pairCoeff ν h k β b hk hβ hb μ₀ j₀)
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ hC ?_ fun i => ?_
  · -- the difference is a.e. the pair of (remainder − coefficient) plus the normalised residuals
    have hsum := tendstoInMeasure_add_zero
      (tendstoInMeasure_pairRemainder_sub ν h k β b hk hβ hb hμ hj XY Z hXY Nseq hN)
      (tendstoInMeasure_prodMk_zero' hEφ hE1)
    refine TendstoInMeasure.congr (fun i => ?_) (Eventually.of_forall fun _ => rfl) hsum
    filter_upwards [hdφ i, hd1 i, hpφ i, hp1 i] with ω hφ h1 hpφ' hp1'
    simp only [Pi.sub_apply, pairCoeff, Prod.mk_add_mk, Prod.mk_sub_mk]
    unfold gRemainder abstractRemainder
    rw [hφ, h1, hpφ', hp1']
    ext <;> simp only <;> ring
  · exact ((hZφm i).div_const _).prodMk ((hZ1m i).div_const _) |>.aemeasurable

/-- **Headline XXXVIII — the leading-order posterior quotient after chart assembly.** Under the
hypotheses of `tendstoInDistribution_pair_normalised` and `P(C¹_{μ₀,j₀}(X) = 0) = 0`,
`Z^0_ℓ[φ] / Z^0_ℓ[1] ⇒ C^φ_{μ₀,j₀}(Y) / C¹_{μ₀,j₀}(X)`. -/
theorem tendstoInDistribution_posterior_leading (hk : ∀ I i, 0 < k I i) (hβ : 0 < β)
    (hb : ∀ I, 0 < b I) {μ₀ : ℝ} (hμ : ∃ m : ℕ, μ₀ = (m : ℝ) / commonQ k) {j₀ : ℕ}
    (hj : j₀ ≤ commonD n) (XY : ι → Ω → PairData K n) (hXYm : ∀ i, Measurable (XY i))
    (Z : Ω' → PairData K n) (hZm : Measurable Z)
    (hXY : TendstoInDistribution XY l Z (fun _ => μ) μ') (Nseq : ι → ℝ)
    (hN1 : ∀ i, 1 < Nseq i) (hN : Tendsto Nseq l atTop) (Zφ Z1 Eφ E1 : ι → Ω → ℝ)
    (hZφm : ∀ i, Measurable (Zφ i)) (hZ1m : ∀ i, Measurable (Z1 i))
    (hdφ : ∀ i, ∀ᵐ ω ∂μ, Zφ i ω = gInt ν h k β b (XY i ω).num (Nseq i) + Eφ i ω)
    (hd1 : ∀ i, ∀ᵐ ω ∂μ, Z1 i ω = gInt ν h k β b (XY i ω).den (Nseq i) + E1 i ω)
    (hEφ : TendstoInMeasure μ (fun i ω => Eφ i ω / (Nseq i ^ (-μ₀) * Real.log (Nseq i) ^ j₀)) l
      (fun _ => 0))
    (hE1 : TendstoInMeasure μ (fun i ω => E1 i ω / (Nseq i ^ (-μ₀) * Real.log (Nseq i) ^ j₀)) l
      (fun _ => 0))
    (hpφ : ∀ i, ∀ᵐ ω ∂μ,
      absPredSum (commonQ k) (commonD n) (gCoeff ν h k β b (XY i ω).num) μ₀ j₀ (Nseq i) = 0)
    (hp1 : ∀ i, ∀ᵐ ω ∂μ,
      absPredSum (commonQ k) (commonD n) (gCoeff ν h k β b (XY i ω).den) μ₀ j₀ (Nseq i) = 0)
    (hB : μ' {ω | gCoeff ν h k β b (Z ω).den μ₀ j₀ = 0} = 0) :
    TendstoInDistribution (fun i ω => Zφ i ω / Z1 i ω) l
      (fun ω => gCoeff ν h k β b (Z ω).num μ₀ j₀ / gCoeff ν h k β b (Z ω).den μ₀ j₀)
      (fun _ => μ) μ' := by
  have hpair := tendstoInDistribution_pair_normalised ν h k β b hk hβ hb hμ hj XY hXYm Z hXY Nseq
    hN1 hN Zφ Z1 Eφ E1 hZφm hZ1m hdφ hd1 hEφ hE1 hpφ hp1
  have ha : ∀ i, Nseq i ^ (-μ₀) * Real.log (Nseq i) ^ j₀ ≠ 0 := fun i => by
    have h0 : 0 < Nseq i := lt_trans one_pos (hN1 i)
    have hl : 0 < Real.log (Nseq i) := Real.log_pos (hN1 i)
    positivity
  have hAm : Measurable fun ω => gCoeff ν h k β b (Z ω).num μ₀ j₀ :=
    ((continuous_gCoeff ν h k β b hk hβ hb μ₀ j₀).comp continuous_num).measurable.comp hZm
  have hBm : Measurable fun ω => gCoeff ν h k β b (Z ω).den μ₀ j₀ :=
    ((continuous_gCoeff ν h k β b hk hβ hb μ₀ j₀).comp continuous_den).measurable.comp hZm
  exact tendstoInDistribution_div_of_scaled Zφ Z1 _ ha hZφm hZ1m _ _ hAm hBm hpair hB

end Grammar

```


## Full proof of the generic quotient theorem (unit 286)

```lean
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


```

## Full proof of the joint normalised convergence (unit 287)

```lean
/-- **Joint convergence of the normalised numerator and denominator** at a source-leading target. -/
theorem tendstoInDistribution_pair_normalised (hk : ∀ I i, 0 < k I i) (hβ : 0 < β)
    (hb : ∀ I, 0 < b I) {μ₀ : ℝ} (hμ : ∃ m : ℕ, μ₀ = (m : ℝ) / commonQ k) {j₀ : ℕ}
    (hj : j₀ ≤ commonD n) (XY : ι → Ω → PairData K n) (hXYm : ∀ i, Measurable (XY i))
    (Z : Ω' → PairData K n) (hXY : TendstoInDistribution XY l Z (fun _ => μ) μ') (Nseq : ι → ℝ)
    (hN1 : ∀ i, 1 < Nseq i) (hN : Tendsto Nseq l atTop) (Zφ Z1 Eφ E1 : ι → Ω → ℝ)
    (hZφm : ∀ i, Measurable (Zφ i)) (hZ1m : ∀ i, Measurable (Z1 i))
    (hdφ : ∀ i, ∀ᵐ ω ∂μ, Zφ i ω = gInt ν h k β b (XY i ω).num (Nseq i) + Eφ i ω)
    (hd1 : ∀ i, ∀ᵐ ω ∂μ, Z1 i ω = gInt ν h k β b (XY i ω).den (Nseq i) + E1 i ω)
    (hEφ : TendstoInMeasure μ (fun i ω => Eφ i ω / (Nseq i ^ (-μ₀) * Real.log (Nseq i) ^ j₀)) l
      (fun _ => 0))
    (hE1 : TendstoInMeasure μ (fun i ω => E1 i ω / (Nseq i ^ (-μ₀) * Real.log (Nseq i) ^ j₀)) l
      (fun _ => 0))
    (hpφ : ∀ i, ∀ᵐ ω ∂μ,
      absPredSum (commonQ k) (commonD n) (gCoeff ν h k β b (XY i ω).num) μ₀ j₀ (Nseq i) = 0)
    (hp1 : ∀ i, ∀ᵐ ω ∂μ,
      absPredSum (commonQ k) (commonD n) (gCoeff ν h k β b (XY i ω).den) μ₀ j₀ (Nseq i) = 0) :
    TendstoInDistribution (fun i ω => (Zφ i ω / (Nseq i ^ (-μ₀) * Real.log (Nseq i) ^ j₀),
        Z1 i ω / (Nseq i ^ (-μ₀) * Real.log (Nseq i) ^ j₀))) l
      (fun ω => pairCoeff ν h k β b (Z ω) μ₀ j₀) (fun _ => μ) μ' := by
  have hC : TendstoInDistribution (fun i ω => pairCoeff ν h k β b (XY i ω) μ₀ j₀) l
      (fun ω => pairCoeff ν h k β b (Z ω) μ₀ j₀) (fun _ => μ) μ' :=
    hXY.continuous_comp (g := fun p => pairCoeff ν h k β b p μ₀ j₀)
      (continuous_pairCoeff ν h k β b hk hβ hb μ₀ j₀)
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ hC ?_ fun i => ?_
  · -- the difference is a.e. the pair of (remainder − coefficient) plus the normalised residuals
    have hsum := tendstoInMeasure_add_zero
      (tendstoInMeasure_pairRemainder_sub ν h k β b hk hβ hb hμ hj XY Z hXY Nseq hN)
      (tendstoInMeasure_prodMk_zero' hEφ hE1)
    refine TendstoInMeasure.congr (fun i => ?_) (Eventually.of_forall fun _ => rfl) hsum
    filter_upwards [hdφ i, hd1 i, hpφ i, hp1 i] with ω hφ h1 hpφ' hp1'
    simp only [Pi.sub_apply, pairCoeff, Prod.mk_add_mk, Prod.mk_sub_mk]
    unfold gRemainder abstractRemainder
    rw [hφ, h1, hpφ', hp1']
    ext <;> simp only <;> ring
  · exact ((hZφm i).div_const _).prodMk ((hZ1m i).div_const _) |>.aemeasurable


```

## Questions
1. **u286.** Is `tendstoInDistribution_div` correctly stated and proved (joint convergence hypothesis on the pair; measurability of `Y_ℓ, W_ℓ, A, B`; `P(B = 0) = 0`; totalised division)? Check the truncated-division comparison `abs_integral_div_sub_truncDiv_le` (oscillation bound `C·P(|V| ≤ δ)`), the tails lemma, the portmanteau step (closed set `{|b| ≤ δ}`, marginal `W ⇒ B` by continuous mapping with `Prod.snd`), the `ε/3` bookkeeping with `η = ε/(6(C+1))`, and the scaled form (`a_ℓ ≠ 0` for all `ℓ`). Is anything claimed about `W_ℓ ≠ 0`?
2. **u287.** Is `PairData` (a `def` synonym of `JointData × JointData` with sup norm and declared Borel instances) an honest joint model of numerator and denominator data with a common phase? (The common phase is NOT enforced by the type — the pair may have different phases; the paper's case `η_φ = φ·η_1` with shared `ξ_n` is a special case. Should the docstring say so?) Check `tendstoInDistribution_pair_normalised`: the a.e. identity `Z^0/a = (gRemainder − gCoeff) + E/a + gCoeff` using vanishing predecessor sums; the vector Slutsky step (`tendstoInMeasure_add_zero`, `tendstoInMeasure_prodMk_zero'`); the hypotheses `N_ℓ > 1` (so `a_ℓ ≠ 0`), a.e. decompositions, residual negligibility at the target scale, source-vanishing predecessor sums (`∀ i, ∀ᵐ ω, absPredSum … = 0`), and `P(gCoeff (Z ω).den μ₀ j₀ = 0) = 0`. Is `tendstoInDistribution_posterior_leading` a faithful rendering of the leading term of `cor:empirical_expectation` (`d_{s₀,q₀} = A_{i₀,j₀}/B_{k₀,p₀}` with common leading indices) at the assembled level?
3. **Non-claims** for XXXVIII (deterministic leading target; source vanishing needed, limit vanishing insufficient; finite-sample positivity of `Z^0[1]` separate; joint convergence hypothesis; no all-orders quotient; no expectation convergence).
4. Verdict per unit, overall, should-fix list (blocking / nonblocking) before freezing A4-L.
