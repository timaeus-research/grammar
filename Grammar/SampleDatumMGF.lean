import Grammar.PopulationBoundDischarge
import Grammar.SampleExpansion
import Grammar.PopulationDataBridge

/-!
# The full-box exponential-moment bound for the sample datum

The certified-core expectation assembly (`tendsto_integral_scaled_assembly_of_dominated_cores`)
takes as its remaining analytic hypothesis the *full-box exponential-moment bound* of the finite-`n`
phase field: `E e^{tξ_n(u)} ≤ e^{ct²/2}` for every `u` in the box. For the sample datum
`ξ_n = n^{−1/2}∑_{i<n}(Y_i − EY_0) + A` of i.i.d. phase observations `Y_i = phaseObs(X_i)` with
`‖Y_i‖_{ℓ¹} ≤ M₀` and an amplitude datum `A` (zero phase), the phase field at `u` is the
normalised centred sum of the bounded i.i.d. real variables `ξ_{Y_i}(u)` (the evaluation
`x ↦ ξ_x(u)` is a continuous linear functional of norm `≤ 1` on the data space,
`phaseEvalCLM`), so Hoeffding's lemma gives the bound with `c = M₀²`, uniformly in `n` and in
`u ∈ [0,1]^d` (`lintegral_exp_phase_sampleDatum_le`). Consequently the expectation assembly for
the sample datum holds with only the field limit `A_n Z^core_n ⇒ L`, the domination of the box
exponent pairs and `E|A_n Rem_n| → 0` as hypotheses
(`tendsto_integral_scaled_assembly_sampleDatum`).

Non-claims: the field limit is not derived here (it is the content of the stochastic expansion
CXVIII in the coefficient form); the amplitude datum is fixed; boundedness of the phase
observations is a hypothesis on the sampling law (bounded Taylor data at the box radius).
-/

open MeasureTheory ProbabilityTheory Set Filter Topology

namespace Grammar

open CoeffFamily

section PhaseFunctional

variable {d : ℕ}

theorem evalF_add {c c' : CoeffFamily d} (hc : AbsSummable c) (hc' : AbsSummable c')
    {u : Fin d → ℝ} (hu : u ∈ closedCube d) :
    evalF (fun γ => c γ + c' γ) u = evalF c u + evalF c' u := by
  unfold evalF
  rw [← (summable_term hc hu).tsum_add (summable_term hc' hu)]
  exact tsum_congr fun γ => add_mul _ _ _

theorem evalF_const_mul (a : ℝ) (c : CoeffFamily d) (u : Fin d → ℝ) :
    evalF (fun γ => a * c γ) u = a * evalF c u := by
  unfold evalF
  rw [← tsum_mul_left]
  exact tsum_congr fun γ => mul_assoc _ _ _

/-- The phase evaluation `x ↦ ξ_x(u)` as a continuous linear functional on the data space. -/
noncomputable def phaseEvalCLM (u : Fin d → ℝ) (hu : u ∈ closedCube d) : DataSpace d →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun x => evalF (xiCoord x) u
      map_add' := fun x y => by
        have e : xiCoord (x + y) = fun γ => xiCoord x γ + xiCoord y γ := by
          funext γ
          simp [xiCoord]
        rw [e]
        exact evalF_add (absSummable_xiCoord x) (absSummable_xiCoord y) hu
      map_smul' := fun a x => by
        have e : xiCoord (a • x) = fun γ => a * xiCoord x γ := by
          funext γ
          simp [xiCoord, lp.coeFn_smul]
        rw [e, evalF_const_mul]
        rfl }
    1 fun x => by
      rw [one_mul, Real.norm_eq_abs]
      exact (abs_evalF_le (absSummable_xiCoord x) hu).trans (mass_xiCoord_le x)

theorem phaseEvalCLM_apply (u : Fin d → ℝ) (hu : u ∈ closedCube d) (x : DataSpace d) :
    phaseEvalCLM u hu x = evalF (xiCoord x) u := rfl

theorem abs_phaseEvalCLM_le (u : Fin d → ℝ) (hu : u ∈ closedCube d) (x : DataSpace d) :
    |phaseEvalCLM u hu x| ≤ ‖x‖ :=
  (abs_evalF_le (absSummable_xiCoord x) hu).trans (mass_xiCoord_le x)

end PhaseFunctional

section Sample

variable {d : ℕ} {𝓧 : Type*} [MeasurableSpace 𝓧] (b : ℝ) (hb : 0 < b) (c : 𝓧 → CoeffFamily d)
  (hc : ∀ x, AbsSummableAt (c x) b)
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → 𝓧)

/-- Bounded phase observations are integrable. -/
theorem integrable_sampleObs_of_bounded (hcm : ∀ γ, Measurable fun x => c x γ)
    (hXm : ∀ i, Measurable (X i)) {M : ℝ} (hM : ∀ x, ‖phaseObs b hb c hc x‖ ≤ M) (i : ℕ) :
    Integrable (sampleObs b hb c hc X i) P :=
  Integrable.of_bound (measurable_sampleObs b hb c hc X hcm hXm i).aestronglyMeasurable M
    (Filter.Eventually.of_forall fun ω => hM (X i ω))

omit [MeasurableSpace 𝓧] [IsProbabilityMeasure P] in
theorem measurable_empiricalSum_of_integrable {ι : Type*} [Countable ι] {Y : ℕ → Ω → L1Seq ι}
    (hint : Integrable (Y 0) P) (hYm : ∀ i, Measurable (Y i)) (n : ℕ) :
    Measurable (empiricalSum Y P n) := by
  refine measurable_of_coords fun j => ?_
  simp_rw [empiricalSum_apply hint]
  exact (Finset.measurable_sum _ fun i _ =>
    ((measurable_coord j).comp (hYm i)).sub_const _).const_mul _

theorem measurable_sampleDatum_of_bounded (hcm : ∀ γ, Measurable fun x => c x γ)
    (hXm : ∀ i, Measurable (X i)) {M : ℝ} (hM : ∀ x, ‖phaseObs b hb c hc x‖ ≤ M)
    (A : DataSpace d) (n : ℕ) : Measurable (sampleDatum b hb c hc P X A n) :=
  (continuous_add_const A).measurable.comp (measurable_empiricalSum_of_integrable P
    (integrable_sampleObs_of_bounded b hb c hc P X hcm hXm hM 0)
    (measurable_sampleObs b hb c hc X hcm hXm) n)

/-- The amplitude of the sample datum is the fixed amplitude datum. -/
theorem etaCoord_sampleDatum_of_bounded (hcm : ∀ γ, Measurable fun x => c x γ)
    (hXm : ∀ i, Measurable (X i)) {M : ℝ} (hM : ∀ x, ‖phaseObs b hb c hc x‖ ≤ M)
    (A : DataSpace d) (n : ℕ) (ω : Ω) :
    etaCoord (sampleDatum b hb c hc P X A n ω) = etaCoord A := by
  have hint := integrable_sampleObs_of_bounded b hb c hc P X hcm hXm hM 0
  funext γ
  unfold etaCoord sampleDatum
  rw [lp.coeFn_add, Pi.add_apply, empiricalSum_apply hint]
  simp [sampleObs, phaseObs_inr]

/-- **The phase field of the sample datum is a normalised centred sum of i.i.d. bounded
variables**: `ξ_n(u) = n^{−1/2}∑_{i<n}(ξ_{Y_i}(u) − Eξ_{Y_i}(u))` for a zero-phase amplitude
datum `A`. -/
theorem phaseEval_sampleDatum (hcm : ∀ γ, Measurable fun x => c x γ)
    (hXm : ∀ i, Measurable (X i)) (hXid : ∀ i, IdentDistrib (X i) (X 0) P P) {M : ℝ}
    (hM : ∀ x, ‖phaseObs b hb c hc x‖ ≤ M) (A : DataSpace d) (hA : xiCoord A = 0) (n : ℕ)
    (ω : Ω) {u : Fin d → ℝ} (hu : u ∈ closedCube d) :
    evalF (xiCoord (sampleDatum b hb c hc P X A n ω)) u =
      (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, (phaseEvalCLM u hu (sampleObs b hb c hc X i ω) -
        ∫ ω', phaseEvalCLM u hu (sampleObs b hb c hc X i ω') ∂P) := by
  have hint := integrable_sampleObs_of_bounded b hb c hc P X hcm hXm hM 0
  rw [← phaseEvalCLM_apply u hu]
  unfold sampleDatum empiricalSum
  rw [map_add, map_smul, map_sum, phaseEvalCLM_apply u hu A, hA, evalF_zero, add_zero,
    smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sub, ← ContinuousLinearMap.integral_comp_comm _ hint]
  congr 1
  exact ((identDistrib_sampleObs b hb c hc P X hcm hXid i).comp
    (phaseEvalCLM u hu).continuous.measurable).integral_eq.symm

/-- **The full-box exponential-moment bound for the sample datum (Hoeffding)**: for i.i.d.
phase observations of `ℓ¹`-norm `≤ M` and a zero-phase amplitude datum,
`E e^{tξ_n(u)} ≤ e^{M²t²/2}` for every `n`, every `u ∈ [0,1]^d` and every `t ≥ 0`. -/
theorem lintegral_exp_phase_sampleDatum_le (hcm : ∀ γ, Measurable fun x => c x γ)
    (hXm : ∀ i, Measurable (X i)) (hXind : iIndepFun X P)
    (hXid : ∀ i, IdentDistrib (X i) (X 0) P P) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ x, ‖phaseObs b hb c hc x‖ ≤ M) (A : DataSpace d) (hA : xiCoord A = 0) (n : ℕ)
    {u : Fin d → ℝ} (hu : u ∈ closedCube d) (t : ℝ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (t * evalF (xiCoord (sampleDatum b hb c hc P X A n ω)) u)) ∂P ≤
      ENNReal.ofReal (Real.exp (M ^ 2 * t ^ 2 / 2)) := by
  simp_rw [phaseEval_sampleDatum b hb c hc P X hcm hXm hXid hM A hA _ _ hu]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Finset.range_zero, Finset.sum_empty, mul_zero, Real.exp_zero, ENNReal.ofReal_one,
      lintegral_const, measure_univ, one_mul]
    exact ENNReal.one_le_ofReal.2 (Real.one_le_exp (by positivity))
  · have hZm : ∀ i, Measurable fun ω => phaseEvalCLM u hu (sampleObs b hb c hc X i ω) := fun i =>
      (phaseEvalCLM u hu).continuous.measurable.comp (measurable_sampleObs b hb c hc X hcm hXm i)
    have hind : iIndepFun (fun i ω => phaseEvalCLM u hu (sampleObs b hb c hc X i ω)) P :=
      (iIndepFun_sampleObs b hb c hc P X hcm hXind).comp (fun _ => phaseEvalCLM u hu)
        fun _ => (phaseEvalCLM u hu).continuous.measurable
    have hZ : ∀ i, ∀ᵐ ω ∂P, phaseEvalCLM u hu (sampleObs b hb c hc X i ω) ∈ Icc (-M) M :=
      fun i => Filter.Eventually.of_forall fun ω =>
        abs_le.1 ((abs_phaseEvalCLM_le u hu _).trans (hM (X i ω)))
    refine (lintegral_ofReal_exp_normalisedSum_le hZm hind hZ hn t).trans (le_of_eq ?_)
    congr 3
    rw [sub_neg_eq_add, ← two_mul, Real.norm_eq_abs, abs_of_nonneg (by linarith),
      mul_div_cancel_left₀ _ two_ne_zero]

end Sample

section Assembly

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
variable (n : ℕ) {J : ℕ} (h k : Fin J → Fin (n + 1) → ℕ) (bJ : Fin J → ℝ)
variable {𝓧 : Type*} [MeasurableSpace 𝓧] (X : ℕ → Ω → 𝓧)
variable {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'} [IsProbabilityMeasure μ']

/-- **The expectation assembly for the sample datum**: for i.i.d. samples with bounded chart
phase observations (`‖phaseObs(X_i)‖_{ℓ¹} ≤ M₀`, `pβM₀² < 2`), zero-phase amplitude data of
amplitude mass `≤ M`, and box exponent pairs dominating the scale `A_n = n^λ/(log n)^{m−1}`:
if `A_n Z^core_n ⇒ L` and `E|A_n Rem_n| → 0` then `E[A_n(Z^core_n + Rem_n)] → E L`. The
full-box exponential moments (Hoeffding) and the reduced-temperature population bounds (monomial
asymptotics) are supplied. -/
theorem tendsto_integral_scaled_assembly_sampleDatum (hk : ∀ j i, 0 < k j i)
    {β p M M₀ : ℝ} (hβ : 0 < β) (hp : 1 < p) (hc2 : p * β * M₀ ^ 2 < 2) (hM : 0 ≤ M)
    (hM0 : 0 ≤ M₀) (hb : ∀ j, 0 < bJ j) {lam : ℝ} {mult : ℕ}
    (hdom : ∀ j, lam < minRatio (h j) (k j) ∨
      (lam = minRatio (h j) (k j) ∧
        multCount (ratioExp (h j) (k j)) (minRatio (h j) (k j)) - 1 ≤ mult - 1))
    (c : Fin J → 𝓧 → CoeffFamily (n + 1)) (hc : ∀ j x, AbsSummableAt (c j x) (bJ j))
    (hcm : ∀ j γ, Measurable fun x => c j x γ) (hXm : ∀ i, Measurable (X i))
    (hXind : iIndepFun X P) (hXid : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hobs : ∀ j x, ‖phaseObs (bJ j) (hb j) (c j) (hc j) x‖ ≤ M₀)
    (A : Fin J → DataSpace (n + 1)) (hA : ∀ j, xiCoord (A j) = 0)
    (hAM : ∀ j, mass (etaCoord (A j)) ≤ M) {L : Ω' → ℝ}
    (hcore : TendstoInDistribution (fun m ω => scaleA lam mult m *
      coreSum n h k bJ β (fun m => (m : ℝ))
        (fun j m => sampleDatum (bJ j) (hb j) (c j) (hc j) P X (A j) m) m ω) atTop L
      (fun _ => P) μ')
    {R : ℕ → Ω → ℝ} (hRint : ∀ m, Integrable (fun ω => scaleA lam mult m * R m ω) P)
    (hrem : Tendsto (fun m => ∫ ω, |scaleA lam mult m * R m ω| ∂P) atTop (𝓝 0)) :
    Integrable L μ' ∧ Tendsto (fun m => ∫ ω, scaleA lam mult m *
      (coreSum n h k bJ β (fun m => (m : ℝ))
        (fun j m => sampleDatum (bJ j) (hb j) (c j) (hc j) P X (A j) m) m ω + R m ω) ∂P)
      atTop (𝓝 (∫ ω, L ω ∂μ')) :=
  tendsto_integral_scaled_assembly_of_dominated_cores P n h k bJ hk hβ hp hc2 hM hb hdom
    (fun j m => sampleDatum (bJ j) (hb j) (c j) (hc j) P X (A j) m)
    (fun j m => measurable_sampleDatum_of_bounded (bJ j) (hb j) (c j) (hc j) P X (hcm j) hXm
      (hobs j) (A j) m)
    (fun j m ω => by
      rw [etaCoord_sampleDatum_of_bounded (bJ j) (hb j) (c j) (hc j) P X (hcm j) hXm (hobs j)]
      exact hAM j)
    (fun j m u hu t _ => lintegral_exp_phase_sampleDatum_le (bJ j) (hb j) (c j) (hc j) P X
      (hcm j) hXm hXind hXid hM0 (hobs j) (A j) (hA j) m (unitBox_subset_closedCube _ hu) t)
    hcore hRint hrem

end Assembly

end Grammar
