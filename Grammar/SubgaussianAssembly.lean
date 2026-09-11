import Grammar.SubgaussianPhase
import Grammar.L1GaussianFunctionalL2
import Grammar.JointSampleLimit

/-!
# The annealed sample-datum theorems for sub-Gaussian observations (Astra #62 unit 4)

The single- and several-chart annealed sample-datum theorems (CLXII–CLXIII) and the Gaussian first
moment of the leading coefficient (CLXV) were stated for **bounded** chart phase observations
`‖phaseObs(X_i)‖_{ℓ¹} ≤ M₀` with `pβM₀² < 2`. Here boundedness is replaced by

* the `ℓ¹` CLT certificate (unchanged; it gives integrability of the observations),
* the uniform full-box sub-Gaussian proxy `κ` (`UniformSubgaussianPhase`),
* `p > 1`, `pβκ < 2` for the `L^p`/uniform-integrability argument, and `βκ < 2` for the
  Gaussian first-moment identification,
* the same zero-phase amplitude datum and the same scaled `L¹`-negligible remainder.

Results: the expectation assembly for the sample datum
(`tendsto_integral_scaled_assembly_sampleDatum_subgaussian`), the single-chart theorem
(`tendsto_integral_scaled_sampleDatum_single_subgaussian`), the several-chart theorem
(`tendsto_integral_scaled_coreSum_sampleDatum_subgaussian`), and — with the phase observations in
`L²(P; ℓ¹)` — the identification `E_ν[C^b_{λ,m−1}(Z + A)] = b^{|h|+d} c^{−λ} K_face (Γ(λ)/2)
∫ η_A(π u)(β(1 − βσ²(π u)/2))^{−λ} w(u) du / 2^{m−1}` with `σ²(v) ≤ κ`
(`integral_dataBoxCoeff_leading_eq_subgaussian`). The bounded theorems are the case
`κ = M₀²` (`uniformSubgaussianPhase_of_bounded`, `memLp_two_sampleObs_of_bounded`).

Non-claims: the field limit and the external remainder are as before; for several charts a common
proxy `κ` is used (chart-specific proxies `κ_I` with a common `p` would be the refinement); no
identification with the population coefficient at the original temperature `β`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal

namespace Grammar

open CoeffFamily

section Assembly

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
variable {𝓧 : Type*} [MeasurableSpace 𝓧] (X : ℕ → Ω → 𝓧)

omit [IsProbabilityMeasure P] in
theorem measurable_sampleDatum_of_integrable {d : ℕ} (b : ℝ) (hb : 0 < b) (c : 𝓧 → CoeffFamily d)
    (hc : ∀ x, AbsSummableAt (c x) b) (hcm : ∀ γ, Measurable fun x => c x γ)
    (hXm : ∀ i, Measurable (X i)) (hint : Integrable (sampleObs b hb c hc X 0) P)
    (A : DataSpace d) (m : ℕ) : Measurable (sampleDatum b hb c hc P X A m) :=
  (continuous_add_const A).measurable.comp (measurable_empiricalSum_of_integrable P hint
    (measurable_sampleObs b hb c hc X hcm hXm) m)

variable (n : ℕ) {J : ℕ} (h k : Fin J → Fin (n + 1) → ℕ) (bJ : Fin J → ℝ)
variable {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'} [IsProbabilityMeasure μ']

/-- **The expectation assembly for the sample datum under the sub-Gaussian hypothesis**: for
i.i.d. samples with integrable chart phase observations of uniform full-box sub-Gaussian proxy `κ`
(`pβκ < 2`, `p > 1`), zero-phase amplitude data of amplitude mass `≤ M`, and box exponent pairs
dominating the scale: if `A_n Z^core_n ⇒ L` and `E|A_n Rem_n| → 0` then
`E[A_n(Z^core_n + Rem_n)] → E L`. -/
theorem tendsto_integral_scaled_assembly_sampleDatum_subgaussian (hk : ∀ j i, 0 < k j i)
    {β p M : ℝ} {κ : ℝ≥0} (hβ : 0 < β) (hp : 1 < p) (hc2 : p * β * κ < 2) (hM : 0 ≤ M)
    (hb : ∀ j, 0 < bJ j) {lam : ℝ} {mult : ℕ}
    (hdom : ∀ j, lam < minRatio (h j) (k j) ∨
      (lam = minRatio (h j) (k j) ∧
        multCount (ratioExp (h j) (k j)) (minRatio (h j) (k j)) - 1 ≤ mult - 1))
    (c : Fin J → 𝓧 → CoeffFamily (n + 1)) (hc : ∀ j x, AbsSummableAt (c j x) (bJ j))
    (hcm : ∀ j γ, Measurable fun x => c j x γ) (hXm : ∀ i, Measurable (X i))
    (hXind : iIndepFun X P) (hXid : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hint : ∀ j, Integrable (sampleObs (bJ j) (hb j) (c j) (hc j) X 0) P)
    (hκ : ∀ j, UniformSubgaussianPhase (bJ j) (hb j) (c j) (hc j) P X κ)
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
    (fun j m => measurable_sampleDatum_of_integrable P X (bJ j) (hb j) (c j) (hc j) (hcm j) hXm
      (hint j) (A j) m)
    (fun j m ω => by
      rw [etaCoord_sampleDatum_of_integrable (bJ j) (hb j) (c j) (hc j) P X (hint j)]
      exact hAM j)
    (fun j m u hu t _ => lintegral_exp_phase_sampleDatum_le_of_subgaussian (bJ j) (hb j) (c j)
      (hc j) P X (hcm j) hXind hXid (hκ j) (hint j) (A j) (hA j) m
      (unitBox_subset_closedCube _ hu) t)
    hcore hRint hrem

/-- **The several-chart annealed sample-datum theorem for sub-Gaussian observations**. -/
theorem tendsto_integral_scaled_coreSum_sampleDatum_subgaussian (hb : ∀ I, 0 < bJ I)
    (c : Fin J → 𝓧 → CoeffFamily (n + 1)) (hc : ∀ I x, AbsSummableAt (c I x) (bJ I))
    (hk : ∀ I i, 0 < k I i) {β p M : ℝ} {κ : ℝ≥0}
    (hβ : 0 < β) (hp : 1 < p) (hpc : p * β * κ < 2) (hM : 0 ≤ M)
    {lam : ℝ} {mult : ℕ}
    (hdom : ∀ I, lam < minRatio (h I) (k I) ∨
      (lam = minRatio (h I) (k I) ∧
        multCount (ratioExp (h I) (k I)) (minRatio (h I) (k I)) - 1 ≤ mult - 1))
    (hcm : ∀ I γ, Measurable fun x => c I x γ) (hXm : ∀ i, Measurable (X i))
    (hXind : iIndepFun X P) (hXid : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hc2 : ∀ I γ, MemLp (fun ω => c I (X 0 ω) γ) 2 P)
    (hsum : ∀ I, Summable fun γ : Fin (n + 1) → ℕ =>
      bJ I ^ (∑ i, γ i) * Real.sqrt (∫ ω, (c I (X 0 ω) γ) ^ 2 ∂P))
    (hκ : ∀ I, UniformSubgaussianPhase (bJ I) (hb I) (c I) (hc I) P X κ)
    (A : Fin J → DataSpace (n + 1)) (hA : ∀ I, xiCoord (A I) = 0)
    (hAM : ∀ I, mass (etaCoord (A I)) ≤ M) {R : ℕ → Ω → ℝ}
    (hRint : ∀ m, Integrable (fun ω => scaleA lam mult m * R m ω) P)
    (hrem : Tendsto (fun m => ∫ ω, |scaleA lam mult m * R m ω| ∂P) atTop (𝓝 0)) :
    ∃ ν : ProbabilityMeasure (L1Seq (StackIdx fun _ : Fin J => n)),
      (∀ F : Finset (StackIdx fun _ : Fin J => n),
        (ν : Measure (L1Seq (StackIdx fun _ : Fin J => n))).map (finiteCoords F) =
          gaussianTarget (fun ω => finiteCoords F (stackObs (chartObs bJ hb c hc) (X 0 ω))) P) ∧
      Integrable (fun z => jointLeadingCoeff bJ h k β lam mult (unpackAll z + A))
        (ν : Measure (L1Seq (StackIdx fun _ : Fin J => n))) ∧
      Tendsto (fun m => ∫ ω, scaleA lam mult m *
          (coreSum n h k bJ β (fun m => (m : ℝ))
            (fun I m => sampleDatum (bJ I) (hb I) (c I) (hc I) P X (A I) m) m ω + R m ω) ∂P)
        atTop (𝓝 (∫ z, jointLeadingCoeff bJ h k β lam mult (unpackAll z + A)
          ∂(ν : Measure (L1Seq (StackIdx fun _ : Fin J => n))))) := by
  obtain ⟨ν, hmarg, hcore⟩ := tendstoInDistribution_scaled_coreSum_sampleDatum bJ hb c hc P X h k
    hk hβ hdom hcm hXm hXind hXid hc2 hsum A
  have hint : ∀ I, Integrable (sampleObs (bJ I) (hb I) (c I) (hc I) X 0) P := fun I =>
    integrable_of_summableCoordL2 P
      (summableCoordL2_sampleObs (bJ I) (hb I) (c I) (hc I) P X (hcm I) (hXm 0) (hc2 I) (hsum I))
  obtain ⟨hint', htend⟩ := tendsto_integral_scaled_assembly_sampleDatum_subgaussian P X n h k bJ
    hk hβ hp hpc hM hb hdom c hc hcm hXm hXind hXid hint hκ A hA hAM hcore hRint hrem
  exact ⟨ν, hmarg, hint', htend⟩

end Assembly

section Single

variable {n : ℕ} {𝓧 : Type*} [MeasurableSpace 𝓧] (b : ℝ) (hb : 0 < b)
  (c : 𝓧 → CoeffFamily (n + 1)) (hc : ∀ x, AbsSummableAt (c x) b)
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → 𝓧)
variable (h k : Fin (n + 1) → ℕ)

/-- **The single-chart annealed sample-datum theorem for sub-Gaussian observations**: for i.i.d.
samples with chart phase observations of uniform full-box sub-Gaussian proxy `κ` (`pβκ < 2`,
`p > 1`), the `ℓ¹` CLT certificate, a zero-phase amplitude datum of amplitude mass `≤ M`, and
`E|A_n Rem_n| → 0`: `E[A_n(Z_n(sampleDatum_n) + Rem_n)] → E_ν[C_{λ₀,m₀−1}(Z + A)]`. -/
theorem tendsto_integral_scaled_sampleDatum_single_subgaussian (hk : ∀ i, 0 < k i)
    {β p M : ℝ} {κ : ℝ≥0} (hβ : 0 < β) (hp : 1 < p) (hpc : p * β * κ < 2) (hM : 0 ≤ M)
    (hcm : ∀ γ, Measurable fun x => c x γ) (hXm : ∀ i, Measurable (X i))
    (hXind : iIndepFun X P) (hXid : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hc2 : ∀ γ, MemLp (fun ω => c (X 0 ω) γ) 2 P)
    (hsum : Summable fun γ : Fin (n + 1) → ℕ =>
      b ^ (∑ i, γ i) * Real.sqrt (∫ ω, (c (X 0 ω) γ) ^ 2 ∂P))
    (hκ : UniformSubgaussianPhase b hb c hc P X κ) (A : DataSpace (n + 1)) (hA : xiCoord A = 0)
    (hAM : mass (etaCoord A) ≤ M) {R : ℕ → Ω → ℝ}
    (hRint : ∀ m, Integrable (fun ω =>
      scaleA (minRatio h k) (multCount (ratioExp h k) (minRatio h k)) m * R m ω) P)
    (hrem : Tendsto (fun m => ∫ ω, |scaleA (minRatio h k)
      (multCount (ratioExp h k) (minRatio h k)) m * R m ω| ∂P) atTop (𝓝 0)) :
    ∃ ν : ProbabilityMeasure (L1Seq (DataIdx (n + 1))),
      (∀ F : Finset (DataIdx (n + 1)),
        (ν : Measure (L1Seq (DataIdx (n + 1)))).map (finiteCoords F) =
          gaussianTarget (fun ω => finiteCoords F (sampleObs b hb c hc X 0 ω)) P) ∧
      Integrable (fun x => dataBoxCoeff n h k β b (x + A) (minRatio h k)
        (multCount (ratioExp h k) (minRatio h k) - 1))
        (ν : Measure (L1Seq (DataIdx (n + 1)))) ∧
      Tendsto (fun m => ∫ ω, scaleA (minRatio h k) (multCount (ratioExp h k) (minRatio h k)) m *
          (dataBoxIntegral n h k β m b (sampleDatum b hb c hc P X A m ω) + R m ω) ∂P) atTop
        (𝓝 (∫ x, dataBoxCoeff n h k β b (x + A) (minRatio h k)
          (multCount (ratioExp h k) (minRatio h k) - 1)
            ∂(ν : Measure (L1Seq (DataIdx (n + 1)))))) := by
  obtain ⟨ν, hmarg, hcore⟩ := tendstoInDistribution_scaled_dataBoxIntegral_sampleDatum b hb c hc P
    X h k hk hβ hcm hXm hXind hXid hc2 hsum A
  have hint : Integrable (sampleObs b hb c hc X 0) P :=
    integrable_of_summableCoordL2 P (summableCoordL2_sampleObs b hb c hc P X hcm (hXm 0) hc2 hsum)
  have e : ∀ m ω, coreSum n (fun _ : Fin 1 => h) (fun _ => k) (fun _ => b) β (fun m => (m : ℝ))
      (fun _ m => sampleDatum b hb c hc P X A m) m ω =
      dataBoxIntegral n h k β m b (sampleDatum b hb c hc P X A m ω) := fun m ω => by
    simp [coreSum]
  have hcore' : TendstoInDistribution (fun m ω =>
      scaleA (minRatio h k) (multCount (ratioExp h k) (minRatio h k)) m *
        coreSum n (fun _ : Fin 1 => h) (fun _ => k) (fun _ => b) β (fun m => (m : ℝ))
          (fun _ m => sampleDatum b hb c hc P X A m) m ω) atTop
      (fun x => dataBoxCoeff n h k β b (x + A) (minRatio h k)
        (multCount (ratioExp h k) (minRatio h k) - 1)) (fun _ => P)
      (ν : Measure (L1Seq (DataIdx (n + 1)))) := by
    simpa only [e] using hcore
  obtain ⟨hint', htend⟩ := tendsto_integral_scaled_assembly_sampleDatum_subgaussian P X n
    (fun _ : Fin 1 => h) (fun _ => k) (fun _ => b) (fun _ => hk) hβ hp hpc hM (fun _ => hb)
    (fun _ => Or.inr ⟨rfl, le_rfl⟩) (fun _ => c) (fun _ => hc) (fun _ => hcm) hXm hXind hXid
    (fun _ => hint) (fun _ => hκ) (fun _ => A) (fun _ => hA) (fun _ => hAM) hcore' hRint hrem
  refine ⟨ν, hmarg, hint', ?_⟩
  simpa only [e] using htend

end Single

/-! ### The Gaussian first moment of the leading coefficient for sub-Gaussian observations -/

section Moment

variable (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {β : ℝ} (hβ : 0 < β) {b : ℝ}
  (hb : 0 < b) {l : ℝ} (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
variable {𝓧 : Type*} [MeasurableSpace 𝓧] (c : 𝓧 → CoeffFamily (n + 1))
  (hc : ∀ x, AbsSummableAt (c x) b)
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → 𝓧)

include hβ in
/-- The Gaussian first moment of the phase-dressed moment of the `ℓ¹` limit at a face point, for
phase observations in `L²` with uniform sub-Gaussian proxy `κ`, `βκ < 2`. -/
theorem integral_phaseMoment_evalF_subgaussian (hcm : ∀ γ, Measurable fun x => c x γ)
    (hXm : ∀ i, Measurable (X i)) (hc2 : ∀ γ, MemLp (fun ω => c (X 0 ω) γ) 2 P)
    (hsum : Summable fun γ : Fin (n + 1) → ℕ =>
      b ^ (∑ i, γ i) * Real.sqrt (∫ ω, (c (X 0 ω) γ) ^ 2 ∂P))
    (hM2 : MemLp (sampleObs b hb c hc X 0) 2 P) {κ : ℝ≥0}
    (hκ : UniformSubgaussianPhase b hb c hc P X κ) (hβκ : β * κ < 2) (hl : 0 < l)
    {ν : ProbabilityMeasure (L1Seq (DataIdx (n + 1)))}
    (hmarg : ∀ F : Finset (DataIdx (n + 1)),
      (ν : Measure (L1Seq (DataIdx (n + 1)))).map (finiteCoords F) =
        gaussianTarget (fun ω => finiteCoords F (sampleObs b hb c hc X 0 ω)) P)
    (htail : ∀ F : Finset (DataIdx (n + 1)),
      ∫⁻ x, ‖x - truncate F x‖ₑ ∂(ν : Measure (L1Seq (DataIdx (n + 1)))) ≤
        ENNReal.ofReal (sigmaTail P (sampleObs b hb c hc X 0) F))
    {v : Fin (n + 1) → ℝ} (hv : v ∈ closedCube (n + 1)) :
    Integrable (fun Z : DataSpace (n + 1) => phaseMoment β (2 * l) (evalF (xiCoord Z) v))
        (ν : Measure (L1Seq (DataIdx (n + 1)))) ∧
      ∫ Z, phaseMoment β (2 * l) (evalF (xiCoord Z) v) ∂(ν : Measure (L1Seq (DataIdx (n + 1)))) =
        Real.Gamma l * (β * (1 - β * phaseVar b hb c hc P X v / 2)) ^ (-l) / 2 := by
  have hσ : β * phaseVar b hb c hc P X v < 2 := by
    have h1 := phaseVar_le_of_uniformSubgaussian b hb c hc P X hcm hXm hκ hv
    have : β * phaseVar b hb c hc P X v ≤ β * κ := mul_le_mul_of_nonneg_left h1 hβ.le
    linarith
  have hL := map_phaseEvalCLM_eq_gaussianReal_of_memLp b hb c hc P X hcm hXm hc2 hsum hM2 hmarg
    htail hv
  obtain ⟨hint, hval⟩ := integral_fluctuation_gaussianReal β l _ hβ hl
    (phaseVar_nonneg b hb c hc P X v) hσ
  have hfm : Measurable (fluctuation β l) := (continuous_fluctuation β l hβ hl).measurable
  have hLm : Measurable (phaseEvalCLM v hv) := (phaseEvalCLM v hv).continuous.measurable
  have e : (fun Z : DataSpace (n + 1) => phaseMoment β (2 * l) (evalF (xiCoord Z) v)) =
      fun Z => fluctuation β l (phaseEvalCLM v hv Z) / 2 := by
    funext Z
    rw [phaseMoment_eq_half_fluctuation, phaseEvalCLM_apply]
  rw [e]
  have hint' : Integrable (fun Z : DataSpace (n + 1) => fluctuation β l (phaseEvalCLM v hv Z))
      (ν : Measure (L1Seq (DataIdx (n + 1)))) := by
    have := (integrable_map_measure hfm.aestronglyMeasurable hLm.aemeasurable).1 (hL ▸ hint)
    exact this
  refine ⟨hint'.div_const 2, ?_⟩
  unfold phaseVar at hval ⊢
  rw [integral_div, ← integral_map hLm.aemeasurable hfm.aestronglyMeasurable, hL, hval]

include hk hβ hb hmin hatt in
/-- **The Gaussian first moment of the leading coefficient for sub-Gaussian observations**: for
phase observations in `L²` with uniform full-box sub-Gaussian proxy `κ` (`βκ < 2`) and a
zero-phase amplitude datum `A`,
`E_ν[C^b_{λ,m−1}(Z + A)] = b^{|h|+d} c^{−λ} K_face (Γ(λ)/2) ∫_{(0,1]^d} η_A(π u)
(β(1 − βσ²(π u)/2))^{−λ} w(u) du / 2^{m−1}`, `σ²(v) = Var[ξ_{Y₀}(v)] ≤ κ`. -/
theorem integral_dataBoxCoeff_leading_eq_subgaussian (hcm : ∀ γ, Measurable fun x => c x γ)
    (hXm : ∀ i, Measurable (X i)) (hc2 : ∀ γ, MemLp (fun ω => c (X 0 ω) γ) 2 P)
    (hsum : Summable fun γ : Fin (n + 1) → ℕ =>
      b ^ (∑ i, γ i) * Real.sqrt (∫ ω, (c (X 0 ω) γ) ^ 2 ∂P))
    (hM2 : MemLp (sampleObs b hb c hc X 0) 2 P) {κ : ℝ≥0}
    (hκ : UniformSubgaussianPhase b hb c hc P X κ) (hβκ : β * κ < 2)
    {ν : ProbabilityMeasure (L1Seq (DataIdx (n + 1)))}
    (hmarg : ∀ F : Finset (DataIdx (n + 1)),
      (ν : Measure (L1Seq (DataIdx (n + 1)))).map (finiteCoords F) =
        gaussianTarget (fun ω => finiteCoords F (sampleObs b hb c hc X 0 ω)) P)
    (htail : ∀ F : Finset (DataIdx (n + 1)),
      ∫⁻ x, ‖x - truncate F x‖ₑ ∂(ν : Measure (L1Seq (DataIdx (n + 1)))) ≤
        ENNReal.ofReal (sigmaTail P (sampleObs b hb c hc X 0) F))
    (A : DataSpace (n + 1)) (hA : xiCoord A = 0) :
    Integrable (fun Z : DataSpace (n + 1) =>
        dataBoxCoeff n h k β b (Z + A) l (multCount (ratioExp h k) l - 1))
        (ν : Measure (L1Seq (DataIdx (n + 1)))) ∧
      ∫ Z, dataBoxCoeff n h k β b (Z + A) l (multCount (ratioExp h k) l - 1)
          ∂(ν : Measure (L1Seq (DataIdx (n + 1)))) =
        b ^ (∑ i, h i + (n + 1)) * (b ^ (2 * ∑ i, k i)) ^ (-l) *
          (1 / (((multCount (ratioExp h k) l - 1).factorial : ℝ) *
              ∏ i, if ratioExp h k i = l then (k i : ℝ) else 1) *
            (∫ u in unitBox (n + 1), faceWeight h k l (dataAmplitude A) u *
              (Real.Gamma l * (β * (1 - β * phaseVar b hb c hc P X
                (cubeClamp (faceProj h k l u)) / 2)) ^ (-l) / 2)) /
            2 ^ (multCount (ratioExp h k) l - 1)) := by
  have hl : 0 < l := by
    obtain ⟨i, hi⟩ := hatt
    rw [← hi]
    exact ratioExp_pos h k hk i
  set K₁ : ℝ := b ^ (∑ i, h i + (n + 1)) * (b ^ (2 * ∑ i, k i)) ^ (-l) with hK₁
  set K₂ : ℝ := 1 / (((multCount (ratioExp h k) l - 1).factorial : ℝ) *
    ∏ i, if ratioExp h k i = l then (k i : ℝ) else 1) with hK₂
  set F : (Fin (n + 1) → ℝ) → DataSpace (n + 1) → ℝ := fun u Z =>
    faceWeight h k l (dataAmplitude A) u *
      phaseMoment β (2 * l) (evalF (xiCoord Z) (cubeClamp (faceProj h k l u))) with hF
  -- the pointwise identity for data with vanishing amplitude
  have hae := ae_etaCoord_eq_zero_of_memLp b hb c hc P X hcm hXm hc2 hsum hM2 hmarg htail
  have hpt : ∀ Z : DataSpace (n + 1), etaCoord Z = 0 →
      dataBoxCoeff n h k β b (Z + A) l (multCount (ratioExp h k) l - 1) =
        K₁ * (K₂ * (∫ u in unitBox (n + 1), F u Z) / 2 ^ (multCount (ratioExp h k) l - 1)) := by
    intro Z hZ
    rw [dataBoxCoeff_leading_eq_spatialFace n h k hk hβ hb hmin hatt,
      dataPhase_add_of_xiCoord_eq_zero Z A hA, dataAmplitude_add_of_etaCoord_eq_zero Z A hZ,
      spatialFace_eq_faceWeight]
    rfl
  -- joint measurability
  have hξ : Measurable (fun p : (Fin (n + 1) → ℝ) × DataSpace (n + 1) =>
      evalF (xiCoord p.2) (cubeClamp (faceProj h k l p.1))) :=
    (measurable_uncurry_xiField measurable_id).comp
      (measurable_snd.prodMk ((measurable_faceProj h k l).comp measurable_fst))
  have hFm : Measurable (Function.uncurry F) :=
    ((measurable_faceWeight h k l (continuous_dataAmplitude A)).comp measurable_fst).mul
      ((continuous_phaseMoment β (2 * l) hβ (by linarith)).measurable.comp hξ)
  -- the inner Gaussian moment
  have hinner : ∀ u : Fin (n + 1) → ℝ,
      Integrable (fun Z => F u Z) (ν : Measure (L1Seq (DataIdx (n + 1)))) ∧
      ∫ Z, F u Z ∂(ν : Measure (L1Seq (DataIdx (n + 1)))) =
        faceWeight h k l (dataAmplitude A) u *
          (Real.Gamma l * (β * (1 - β * phaseVar b hb c hc P X
            (cubeClamp (faceProj h k l u)) / 2)) ^ (-l) / 2) := by
    intro u
    obtain ⟨hint, hval⟩ := integral_phaseMoment_evalF_subgaussian n hβ hb c hc P X hcm hXm hc2
      hsum hM2 hκ hβκ hl hmarg htail (cubeClamp_mem_closedCube (faceProj h k l u))
    refine ⟨hint.const_mul _, ?_⟩
    change ∫ Z, faceWeight h k l (dataAmplitude A) u *
      phaseMoment β (2 * l) (evalF (xiCoord Z) (cubeClamp (faceProj h k l u)))
        ∂(ν : Measure (L1Seq (DataIdx (n + 1)))) = _
    rw [integral_const_mul, hval]
  -- the uniform bound on the Gaussian moment
  have hC₀ : ∀ u : Fin (n + 1) → ℝ,
      |Real.Gamma l * (β * (1 - β * phaseVar b hb c hc P X (cubeClamp (faceProj h k l u)) / 2))
        ^ (-l) / 2| ≤ Real.Gamma l * (β * (1 - β * κ / 2)) ^ (-l) / 2 := by
    intro u
    have hσle := phaseVar_le_of_uniformSubgaussian b hb c hc P X hcm hXm hκ
      (cubeClamp_mem_closedCube (faceProj h k l u))
    have hσ0 := phaseVar_nonneg b hb c hc P X (cubeClamp (faceProj h k l u))
    have hpos : 0 < β * (1 - β * κ / 2) := mul_pos hβ (by linarith)
    have hσβ : β * phaseVar b hb c hc P X (cubeClamp (faceProj h k l u)) ≤ β * κ :=
      mul_le_mul_of_nonneg_left hσle hβ.le
    have hG := Real.Gamma_pos_of_pos hl
    rw [abs_of_nonneg (div_nonneg (mul_nonneg hG.le (Real.rpow_nonneg
      (mul_nonneg hβ.le (by linarith)) _)) two_pos.le)]
    refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hG.le) two_pos.le
    exact Real.rpow_le_rpow_of_nonpos hpos (by nlinarith) (by linarith)
  -- product integrability in the order (u, Z)
  have hprod : Integrable (Function.uncurry F)
      ((volume.restrict (unitBox (n + 1))).prod (ν : Measure (L1Seq (DataIdx (n + 1))))) := by
    refine (integrable_prod_iff hFm.aestronglyMeasurable).2
      ⟨Eventually.of_forall fun u => (hinner u).1, ?_⟩
    have hbound : ∀ u, ‖∫ Z, ‖F u Z‖ ∂(ν : Measure (L1Seq (DataIdx (n + 1))))‖ ≤
        ‖faceWeight h k l (dataAmplitude A) u‖ *
          (Real.Gamma l * (β * (1 - β * κ / 2)) ^ (-l) / 2) := by
      intro u
      have h1 : ∀ Z, ‖F u Z‖ = ‖faceWeight h k l (dataAmplitude A) u‖ *
          phaseMoment β (2 * l) (evalF (xiCoord Z) (cubeClamp (faceProj h k l u))) := by
        intro Z
        change ‖faceWeight h k l (dataAmplitude A) u *
          phaseMoment β (2 * l) (evalF (xiCoord Z) (cubeClamp (faceProj h k l u)))‖ = _
        rw [norm_mul, Real.norm_eq_abs (phaseMoment _ _ _),
          abs_of_pos (phaseMoment_pos β (2 * l) _ hβ (by linarith))]
      simp_rw [h1]
      rw [integral_const_mul, norm_mul, norm_norm]
      obtain ⟨-, hval⟩ := integral_phaseMoment_evalF_subgaussian n hβ hb c hc P X hcm hXm hc2
        hsum hM2 hκ hβκ hl hmarg htail (cubeClamp_mem_closedCube (faceProj h k l u))
      rw [hval, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hC₀ u) (abs_nonneg _)
    exact Integrable.mono'
      ((integrableOn_faceWeight h k hk hmin (continuous_dataAmplitude A)).norm.mul_const _)
      hFm.aestronglyMeasurable.norm.integral_prod_right' (Eventually.of_forall hbound)
  -- Fubini and assembly
  have hswap := integral_integral_swap hprod
  have hintZ : Integrable (fun Z => ∫ u in unitBox (n + 1), F u Z)
      (ν : Measure (L1Seq (DataIdx (n + 1)))) := hprod.integral_prod_right
  have hae' : (fun Z : DataSpace (n + 1) =>
      dataBoxCoeff n h k β b (Z + A) l (multCount (ratioExp h k) l - 1)) =ᵐ[
        (ν : Measure (L1Seq (DataIdx (n + 1))))]
      fun Z => K₁ * (K₂ * (∫ u in unitBox (n + 1), F u Z) / 2 ^ (multCount (ratioExp h k) l - 1)) :=
    hae.mono fun Z hZ => hpt Z hZ
  refine ⟨(((hintZ.const_mul K₂).div_const _).const_mul K₁).congr hae'.symm, ?_⟩
  rw [integral_congr_ae hae', integral_const_mul, integral_div, integral_const_mul, ← hswap]
  congr 3
  refine setIntegral_congr_fun (measurableSet_unitBox _) fun u _ => ?_
  exact (hinner u).2

end Moment

end Grammar
