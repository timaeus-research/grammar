import Grammar.LeadingCoeffGaussianMoment

/-!
# Functionals of the `ℓ¹` Gaussian limit under `L²` observations (Astra #62 unit 2)

CLXIV (`map_eq_gaussianReal_of_marginals`) identified the law of every continuous linear
functional of the `ℓ¹` Gaussian limit for **bounded** observations `‖Y₀‖_{ℓ¹} ≤ M₀`. The
boundedness entered only through the dominated-convergence step `Var[L(T_F Y₀)] → Var[L(Y₀)]`; it
is replaced here by the Banach-valued moment hypothesis `Y₀ ∈ L²(P; ℓ¹)` (`MemLp (Y 0) 2 P`), with
the dominating functions `‖L‖‖Y₀‖` and `‖L‖²‖Y₀‖²` (`tendsto_variance_truncate_of_memLp`):

`ν.map L = N(0, Var[L(Y₀)])` for `Y₀ ∈ L²` (`map_eq_gaussianReal_of_marginals_of_memLp`),

hence the phase evaluation of the `ℓ¹` Gaussian limit of the sample phase observations is
`N(0, Var[ξ_{Y₀}(u)])` (`map_phaseEvalCLM_eq_gaussianReal_of_memLp`) and its amplitude coordinates
vanish almost surely (`ae_etaCoord_eq_zero_of_memLp`), for phase observations in `L²`. Bounded
observations are in `L²` (`memLp_two_sampleObs_of_bounded`), so CLXIV is the special case.

Non-claims: the summable coordinate-`L²` certificate of the `ℓ¹` CLT is **not** replaced by
`MemLp Y₀ 2` (both are hypotheses; the Banach `L²` norm is not derived from the coordinate
certificate here); no `IsGaussian` instance for `ν`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace

namespace Grammar

open CoeffFamily

section Functional

variable {ι : Type*} [Countable ι] [DecidableEq ι]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {Y : ℕ → Ω → L1Seq ι} (hY : SummableCoordL2 P (Y 0))
  {ν : ProbabilityMeasure (L1Seq ι)}
  (hmarg : ∀ F : Finset ι, (ν : Measure (L1Seq ι)).map (finiteCoords F) =
    gaussianTarget (fun ω => finiteCoords F (Y 0 ω)) P)
  (htail : ∀ F : Finset ι, ∫⁻ x, ‖x - truncate F x‖ₑ ∂(ν : Measure (L1Seq ι)) ≤
    ENNReal.ofReal (sigmaTail P (Y 0) F))
  (L : L1Seq ι →L[ℝ] ℝ)

omit [Countable ι] in
include hY in
/-- Along an exhaustion, `Var[L(T_F Y₀)] → Var[L(Y₀)]` for observations in `L²(P; ℓ¹)`. -/
theorem tendsto_variance_truncate_of_memLp (hM : MemLp (Y 0) 2 P) {F : ℕ → Finset ι}
    (hF : Monotone F) (hcov : ∀ j, ∃ k, j ∈ F k) :
    Tendsto (fun k => Var[fun ω => L (truncate (F k) (Y 0 ω)); P]) atTop
      (𝓝 (Var[fun ω => L (Y 0 ω); P])) := by
  have hmeas : ∀ k, AEStronglyMeasurable (fun ω => L (truncate (F k) (Y 0 ω))) P := fun k =>
    ((L.continuous.comp (truncate (F k)).continuous).measurable.comp
      hY.measurable).aestronglyMeasurable
  have hmeas' : AEStronglyMeasurable (fun ω => L (Y 0 ω)) P :=
    (L.continuous.measurable.comp hY.measurable).aestronglyMeasurable
  have hbd : ∀ k ω, ‖L (truncate (F k) (Y 0 ω))‖ ≤ ‖L‖ * ‖Y 0 ω‖ := fun k ω =>
    (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left (norm_truncate_le _ _) (norm_nonneg _))
  have hbd' : ∀ ω, ‖L (Y 0 ω)‖ ≤ ‖L‖ * ‖Y 0 ω‖ := fun ω => L.le_opNorm _
  have hpt : ∀ ω, Tendsto (fun k => L (truncate (F k) (Y 0 ω))) atTop (𝓝 (L (Y 0 ω))) :=
    fun ω => (L.continuous.tendsto _).comp (tendsto_truncate hF hcov _)
  have hg2 : MemLp (fun ω => ‖L‖ * ‖Y 0 ω‖) 2 P := hM.norm.const_mul _
  have hg2' : Integrable (fun ω => (‖L‖ * ‖Y 0 ω‖) ^ 2) P :=
    (memLp_two_iff_integrable_sq hg2.1).1 hg2
  have hg1 : Integrable (fun ω => ‖L‖ * ‖Y 0 ω‖) P :=
    memLp_one_iff_integrable.1 (hg2.mono_exponent (by norm_num))
  have hnn : ∀ ω, ‖L‖ * ‖Y 0 ω‖ ≤ ‖‖L‖ * ‖Y 0 ω‖‖ := fun ω => le_abs_self _
  have hL2 : ∀ k, MemLp (fun ω => L (truncate (F k) (Y 0 ω))) 2 P := fun k =>
    hg2.of_le (hmeas k) (Eventually.of_forall fun ω => (hbd k ω).trans (hnn ω))
  have hL2' : MemLp (fun ω => L (Y 0 ω)) 2 P :=
    hg2.of_le hmeas' (Eventually.of_forall fun ω => (hbd' ω).trans (hnn ω))
  simp_rw [variance_eq_sub (hL2 _), variance_eq_sub hL2', Pi.pow_apply]
  have h1 : Tendsto (fun k => ∫ ω, L (truncate (F k) (Y 0 ω)) ^ 2 ∂P) atTop
      (𝓝 (∫ ω, L (Y 0 ω) ^ 2 ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun ω => (‖L‖ * ‖Y 0 ω‖) ^ 2)
      (fun k => (hmeas k).pow 2) hg2' (fun k => Eventually.of_forall fun ω => ?_)
      (Eventually.of_forall fun ω => (hpt ω).pow 2)
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hbd k ω) 2
  have h2 : Tendsto (fun k => ∫ ω, L (truncate (F k) (Y 0 ω)) ∂P) atTop
      (𝓝 (∫ ω, L (Y 0 ω) ∂P)) :=
    tendsto_integral_of_dominated_convergence (fun ω => ‖L‖ * ‖Y 0 ω‖) hmeas hg1
      (fun k => Eventually.of_forall (hbd k)) (Eventually.of_forall hpt)
  exact h1.sub (h2.pow 2)

include hY hmarg htail in
/-- **Continuous linear functionals of the `ℓ¹` Gaussian limit are centred Gaussian** with the
variance of the functional of the observation, for observations in `L²(P; ℓ¹)`. -/
theorem map_eq_gaussianReal_of_marginals_of_memLp (hM : MemLp (Y 0) 2 P) :
    (ν : Measure (L1Seq ι)).map L = gaussianReal 0 (Var[fun ω => L (Y 0 ω); P]).toNNReal := by
  obtain ⟨F, hF, hcov⟩ := exists_finset_exhaustion (ι := ι)
  refine Measure.ext_of_charFun (funext fun t => ?_)
  rw [charFun_apply_real, integral_map L.continuous.measurable.aemeasurable (by fun_prop),
    charFun_gaussianReal]
  have hlim1 : Tendsto (fun k => ∫ x, Complex.exp (↑(t * L (truncate (F k) x)) * Complex.I)
      ∂(ν : Measure (L1Seq ι))) atTop
      (𝓝 (∫ x, Complex.exp (↑t * ↑(L x) * Complex.I) ∂(ν : Measure (L1Seq ι)))) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hs : Tendsto (fun k => |t| * ‖L‖ * sigmaTail P (Y 0) (F k)) atTop (𝓝 0) := by
      simpa using (tendsto_sigmaTail (P := P) (Y 0) hF hcov).const_mul (|t| * ‖L‖)
    refine squeeze_zero (fun _ => norm_nonneg _) (fun k => ?_) hs
    rw [norm_sub_rev]
    have := norm_charFun_sub_le htail L (F k) t
    simpa [Complex.ofReal_mul] using this
  have hlim2 : Tendsto (fun k => ∫ x, Complex.exp (↑(t * L (truncate (F k) x)) * Complex.I)
      ∂(ν : Measure (L1Seq ι))) atTop
      (𝓝 (Complex.exp (-((t ^ 2 * Var[fun ω => L (Y 0 ω); P] : ℝ) : ℂ) / 2))) := by
    simp_rw [charFun_map_truncate hY hmarg L _ t]
    refine Tendsto.cexp (Tendsto.div_const (Tendsto.neg ?_) 2)
    exact (Complex.continuous_ofReal.tendsto _).comp
      ((tendsto_variance_truncate_of_memLp hY L hM hF hcov).const_mul (t ^ 2))
  rw [tendsto_nhds_unique hlim1 hlim2, Real.coe_toNNReal _ (variance_nonneg _ _)]
  push_cast
  ring_nf

end Functional

section Phase

variable {d : ℕ} {𝓧 : Type*} [MeasurableSpace 𝓧] (b : ℝ) (hb : 0 < b) (c : 𝓧 → CoeffFamily d)
  (hc : ∀ x, AbsSummableAt (c x) b)
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → 𝓧)

/-- Bounded phase observations are in `L²(P; ℓ¹)`. -/
theorem memLp_two_sampleObs_of_bounded (hcm : ∀ γ, Measurable fun x => c x γ)
    (hXm : ∀ i, Measurable (X i)) {M₀ : ℝ} (hM : ∀ x, ‖phaseObs b hb c hc x‖ ≤ M₀) :
    MemLp (sampleObs b hb c hc X 0) 2 P :=
  MemLp.of_bound (measurable_sampleObs b hb c hc X hcm hXm 0).aestronglyMeasurable M₀
    (Filter.Eventually.of_forall fun ω => hM (X 0 ω))

/-- **The phase evaluation of the `ℓ¹` Gaussian limit of the sample phase observations is a
centred Gaussian variable** with variance `Var[ξ_{Y₀}(u)]`, for phase observations in `L²`. -/
theorem map_phaseEvalCLM_eq_gaussianReal_of_memLp (hcm : ∀ γ, Measurable fun x => c x γ)
    (hXm : ∀ i, Measurable (X i)) (hc2 : ∀ γ, MemLp (fun ω => c (X 0 ω) γ) 2 P)
    (hsum : Summable fun γ : Fin d → ℕ => b ^ (∑ i, γ i) * Real.sqrt (∫ ω, (c (X 0 ω) γ) ^ 2 ∂P))
    (hM : MemLp (sampleObs b hb c hc X 0) 2 P) {ν : ProbabilityMeasure (L1Seq (DataIdx d))}
    (hmarg : ∀ F : Finset (DataIdx d), (ν : Measure (L1Seq (DataIdx d))).map (finiteCoords F) =
      gaussianTarget (fun ω => finiteCoords F (sampleObs b hb c hc X 0 ω)) P)
    (htail : ∀ F : Finset (DataIdx d),
      ∫⁻ x, ‖x - truncate F x‖ₑ ∂(ν : Measure (L1Seq (DataIdx d))) ≤
        ENNReal.ofReal (sigmaTail P (sampleObs b hb c hc X 0) F))
    {u : Fin d → ℝ} (hu : u ∈ closedCube d) :
    (ν : Measure (L1Seq (DataIdx d))).map (phaseEvalCLM u hu) =
      gaussianReal 0 (Var[fun ω => CoeffFamily.evalF (xiCoord (phaseObs b hb c hc (X 0 ω))) u;
        P]).toNNReal :=
  map_eq_gaussianReal_of_marginals_of_memLp
    (summableCoordL2_sampleObs b hb c hc P X hcm (hXm 0) hc2 hsum) hmarg htail
    (phaseEvalCLM u hu) hM

/-- **The amplitude coordinates of the `ℓ¹` Gaussian limit of the phase observations vanish
almost surely**, for phase observations in `L²`. -/
theorem ae_etaCoord_eq_zero_of_memLp (hcm : ∀ γ, Measurable fun x => c x γ)
    (hXm : ∀ i, Measurable (X i)) (hc2 : ∀ γ, MemLp (fun ω => c (X 0 ω) γ) 2 P)
    (hsum : Summable fun γ : Fin d → ℕ => b ^ (∑ i, γ i) * Real.sqrt (∫ ω, (c (X 0 ω) γ) ^ 2 ∂P))
    (hM : MemLp (sampleObs b hb c hc X 0) 2 P) {ν : ProbabilityMeasure (L1Seq (DataIdx d))}
    (hmarg : ∀ F : Finset (DataIdx d), (ν : Measure (L1Seq (DataIdx d))).map (finiteCoords F) =
      gaussianTarget (fun ω => finiteCoords F (sampleObs b hb c hc X 0 ω)) P)
    (htail : ∀ F : Finset (DataIdx d),
      ∫⁻ x, ‖x - truncate F x‖ₑ ∂(ν : Measure (L1Seq (DataIdx d))) ≤
        ENNReal.ofReal (sigmaTail P (sampleObs b hb c hc X 0) F)) :
    ∀ᵐ Z ∂(ν : Measure (L1Seq (DataIdx d))), etaCoord Z = 0 := by
  have hY := summableCoordL2_sampleObs b hb c hc P X hcm (hXm 0) hc2 hsum
  have key : ∀ γ : Fin d → ℕ, ∀ᵐ Z ∂(ν : Measure (L1Seq (DataIdx d))), Z (Sum.inr γ) = 0 := by
    intro γ
    have hL := map_eq_gaussianReal_of_marginals_of_memLp hY hmarg htail (coordCLM (Sum.inr γ)) hM
    have hvar : Var[fun ω => coordCLM (Sum.inr γ) (sampleObs b hb c hc X 0 ω); P] = 0 := by
      have e : (fun ω => coordCLM (Sum.inr γ) (sampleObs b hb c hc X 0 ω)) = fun _ => (0 : ℝ) := by
        funext ω
        simp [sampleObs, phaseObs_inr]
      rw [e]
      exact variance_zero P
    rw [hvar, Real.toNNReal_zero, gaussianReal_zero_var] at hL
    have hs : MeasurableSet {x : ℝ | ¬ x = 0} := by
      convert (measurableSet_singleton (0 : ℝ)).compl using 1
      ext x
      simp
    rw [ae_iff]
    change (ν : Measure (L1Seq (DataIdx d))) (coordCLM (Sum.inr γ) ⁻¹' {x : ℝ | ¬ x = 0}) = 0
    rw [← Measure.map_apply (coordCLM (Sum.inr γ)).continuous.measurable hs, hL,
      Measure.dirac_apply' _ hs, Set.indicator_of_notMem]
    simp
  have hall := ae_all_iff.2 key
  filter_upwards [hall] with Z hZ
  funext γ
  exact hZ γ

end Phase

end Grammar
