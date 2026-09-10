import Grammar.SampleDatumLimit
import Grammar.L1SeqCLT

/-!
# Continuous linear functionals of the `ℓ¹` Gaussian limit are Gaussian

The `ℓ¹` central limit theorem (CXVI, `clt_l1`) produces a law `ν` on `ℓ¹(ι)` through two
certificates: its finite coordinate marginals are the centred Gaussians with the covariance of the
observation `Y₀` (`finiteCoords`), and its tails are controlled,
`∫ ‖x − T_F x‖ dν ≤ ∑_{j∉F} σ_j`. For **bounded** observations (`‖Y₀‖_{ℓ¹} ≤ M₀`) these two
certificates determine the law of every continuous linear functional `L` of `ν`:

`ν.map L = N(0, Var[L(Y₀)])` (`map_eq_gaussianReal_of_marginals`).

Proof: `L ∘ T_F` is a finite coordinate combination, so its law under `ν` is the image of the
Gaussian marginal and its characteristic function is `exp(−t² Var[L(T_F Y₀)]/2)`
(`charFun_map_truncate`); the characteristic functions of `L ∘ T_F` and `L` differ by at most
`|t| ‖L‖ ∑_{j∉F} σ_j` (`norm_charFun_sub_le`), which tends to zero along an exhaustion; and
`Var[L(T_F Y₀)] → Var[L(Y₀)]` by dominated convergence (`tendsto_variance_truncate`). Uniqueness of
limits and `Measure.ext_of_charFun` conclude. In particular the phase evaluation `x ↦ ξ_x(u)`
of the `ℓ¹` Gaussian limit of the sample phase observations is a centred Gaussian variable
(`map_phaseEvalCLM_eq_gaussianReal`).

Non-claims: no `IsGaussian` instance for `ν` as a Banach-space measure is constructed (the
statement is per functional, under the two certificates and boundedness); unbounded observations
are not treated.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace

namespace Grammar

open CoeffFamily

section Functional

variable {ι : Type*} [Countable ι] [DecidableEq ι]

/-- `‖e^{ia} − e^{ib}‖ ≤ |a − b|`. -/
theorem norm_cexp_mul_I_sub_le (a b : ℝ) :
    ‖Complex.exp (↑a * Complex.I) - Complex.exp (↑b * Complex.I)‖ ≤ |a - b| := by
  have h1 : Complex.exp (↑a * Complex.I) - Complex.exp (↑b * Complex.I) =
      Complex.exp (↑b * Complex.I) * (Complex.exp (Complex.I * ↑(a - b)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    push_cast
    ring_nf
  rw [h1, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  exact Real.norm_exp_I_mul_ofReal_sub_one_le.trans (le_of_eq (Real.norm_eq_abs _))

/-- The coefficient vector `(L(e_j))_{j ∈ F}` of a functional. -/
noncomputable def functionalCoeffVec (L : L1Seq ι →L[ℝ] ℝ) (F : Finset ι) : EuclideanSpace ℝ F :=
  (EuclideanSpace.equiv F ℝ).symm fun j => L (singleCLM (j : ι) 1)

omit [Countable ι] in
@[simp] theorem functionalCoeffVec_apply (L : L1Seq ι →L[ℝ] ℝ) (F : Finset ι) (j : F) :
    functionalCoeffVec L F j = L (singleCLM (j : ι) 1) := rfl

omit [Countable ι] in
/-- `L(T_F x) = ⟪P_F x, (L(e_j))_j⟫`. -/
theorem apply_truncate_eq_inner (L : L1Seq ι →L[ℝ] ℝ) (F : Finset ι) (x : L1Seq ι) :
    L (truncate F x) = ⟪finiteCoords F x, functionalCoeffVec L F⟫_ℝ := by
  rw [PiLp.inner_apply]
  simp only [finiteCoords_apply, functionalCoeffVec_apply, RCLike.inner_apply, conj_trivial]
  rw [truncate, sum_apply, map_sum, ← Finset.sum_coe_sort F]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ContinuousLinearMap.comp_apply, coordCLM_apply, show singleCLM (j : ι) (x j) =
    (x j) • singleCLM (j : ι) 1 by rw [← map_smul, smul_eq_mul, mul_one], map_smul, smul_eq_mul,
    mul_comm]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {Y : ℕ → Ω → L1Seq ι} (hY : SummableCoordL2 P (Y 0))
  {ν : ProbabilityMeasure (L1Seq ι)}
  (hmarg : ∀ F : Finset ι, (ν : Measure (L1Seq ι)).map (finiteCoords F) =
    gaussianTarget (fun ω => finiteCoords F (Y 0 ω)) P)
  (htail : ∀ F : Finset ι, ∫⁻ x, ‖x - truncate F x‖ₑ ∂(ν : Measure (L1Seq ι)) ≤
    ENNReal.ofReal (sigmaTail P (Y 0) F))
  (L : L1Seq ι →L[ℝ] ℝ)

include hY hmarg in
/-- The characteristic function of `L ∘ T_F` under `ν` is that of `N(0, Var[L(T_F Y₀)])`. -/
theorem charFun_map_truncate (F : Finset ι) (t : ℝ) :
    ∫ x, Complex.exp (↑(t * L (truncate F x)) * Complex.I) ∂(ν : Measure (L1Seq ι)) =
      Complex.exp (-((t ^ 2 * Var[fun ω => L (truncate F (Y 0 ω)); P] : ℝ) : ℂ) / 2) := by
  have h1 : ∫ x, Complex.exp (↑(t * L (truncate F x)) * Complex.I) ∂(ν : Measure (L1Seq ι)) =
      charFun ((ν : Measure (L1Seq ι)).map (finiteCoords F)) (t • functionalCoeffVec L F) := by
    rw [charFun_apply, integral_map (finiteCoords F).continuous.measurable.aemeasurable
      (by fun_prop)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [inner_smul_right, apply_truncate_eq_inner]
  rw [h1, hmarg F, charFun_gaussianTarget (memLp_finiteCoords_comp hY F)]
  congr 2
  have e : (fun ω => ⟪finiteCoords F (Y 0 ω), t • functionalCoeffVec L F⟫_ℝ) =
      fun ω => t * L (truncate F (Y 0 ω)) := by
    funext ω
    rw [inner_smul_right, apply_truncate_eq_inner]
  rw [e, variance_const_mul]

omit [IsProbabilityMeasure P] in
include htail in
/-- The characteristic functions of `L` and `L ∘ T_F` under `ν` differ by at most
`|t| ‖L‖ ∑_{j∉F} σ_j`. -/
theorem norm_charFun_sub_le (F : Finset ι) (t : ℝ) :
    ‖(∫ x, Complex.exp (↑(t * L x) * Complex.I) ∂(ν : Measure (L1Seq ι))) -
        ∫ x, Complex.exp (↑(t * L (truncate F x)) * Complex.I) ∂(ν : Measure (L1Seq ι))‖ ≤
      |t| * ‖L‖ * sigmaTail P (Y 0) F := by
  have hi1 : Integrable (fun x : L1Seq ι => Complex.exp (↑(t * L x) * Complex.I))
      (ν : Measure (L1Seq ι)) :=
    Integrable.of_bound (by fun_prop) 1 (Eventually.of_forall fun x => by
      rw [Complex.norm_exp_ofReal_mul_I])
  have hi2 : Integrable (fun x : L1Seq ι => Complex.exp (↑(t * L (truncate F x)) * Complex.I))
      (ν : Measure (L1Seq ι)) :=
    Integrable.of_bound (by fun_prop) 1 (Eventually.of_forall fun x => by
      rw [Complex.norm_exp_ofReal_mul_I])
  have hint : Integrable (fun x : L1Seq ι => x - truncate F x) (ν : Measure (L1Seq ι)) :=
    ⟨(continuous_id.sub (truncate F).continuous).aestronglyMeasurable,
      hasFiniteIntegral_iff_enorm.2 ((htail F).trans_lt ENNReal.ofReal_lt_top)⟩
  have hnorm : ∫ x, ‖x - truncate F x‖ ∂(ν : Measure (L1Seq ι)) ≤ sigmaTail P (Y 0) F := by
    rw [← ENNReal.ofReal_le_ofReal_iff (sigmaTail_nonneg (Y 0) F),
      ofReal_integral_norm_eq_lintegral_enorm hint]
    exact htail F
  rw [← integral_sub hi1 hi2]
  refine (norm_integral_le_integral_norm _).trans ?_
  calc ∫ x, ‖Complex.exp (↑(t * L x) * Complex.I) -
          Complex.exp (↑(t * L (truncate F x)) * Complex.I)‖ ∂(ν : Measure (L1Seq ι))
      ≤ ∫ x, |t| * ‖L‖ * ‖x - truncate F x‖ ∂(ν : Measure (L1Seq ι)) := by
        refine integral_mono (hi1.sub hi2).norm (hint.norm.const_mul _) fun x => ?_
        refine (norm_cexp_mul_I_sub_le _ _).trans ?_
        rw [← mul_sub, abs_mul, ← map_sub, mul_assoc]
        exact mul_le_mul_of_nonneg_left (L.le_opNorm _) (abs_nonneg _)
    _ = |t| * ‖L‖ * ∫ x, ‖x - truncate F x‖ ∂(ν : Measure (L1Seq ι)) := integral_const_mul _ _
    _ ≤ |t| * ‖L‖ * sigmaTail P (Y 0) F :=
        mul_le_mul_of_nonneg_left hnorm (by positivity)

omit [Countable ι] in
include hY in
/-- Along an exhaustion, `Var[L(T_F Y₀)] → Var[L(Y₀)]` for bounded observations. -/
theorem tendsto_variance_truncate {M₀ : ℝ} (hM : ∀ ω, ‖Y 0 ω‖ ≤ M₀) {F : ℕ → Finset ι}
    (hF : Monotone F) (hcov : ∀ j, ∃ k, j ∈ F k) :
    Tendsto (fun k => Var[fun ω => L (truncate (F k) (Y 0 ω)); P]) atTop
      (𝓝 (Var[fun ω => L (Y 0 ω); P])) := by
  have hmeas : ∀ k, AEStronglyMeasurable (fun ω => L (truncate (F k) (Y 0 ω))) P := fun k =>
    ((L.continuous.comp (truncate (F k)).continuous).measurable.comp
      hY.measurable).aestronglyMeasurable
  have hmeas' : AEStronglyMeasurable (fun ω => L (Y 0 ω)) P :=
    (L.continuous.measurable.comp hY.measurable).aestronglyMeasurable
  have hbd : ∀ k ω, ‖L (truncate (F k) (Y 0 ω))‖ ≤ ‖L‖ * M₀ := fun k ω =>
    (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left
      ((norm_truncate_le _ _).trans (hM ω)) (norm_nonneg _))
  have hbd' : ∀ ω, ‖L (Y 0 ω)‖ ≤ ‖L‖ * M₀ := fun ω =>
    (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hM ω) (norm_nonneg _))
  have hpt : ∀ ω, Tendsto (fun k => L (truncate (F k) (Y 0 ω))) atTop (𝓝 (L (Y 0 ω))) :=
    fun ω => (L.continuous.tendsto _).comp (tendsto_truncate hF hcov _)
  have hL2 : ∀ k, MemLp (fun ω => L (truncate (F k) (Y 0 ω))) 2 P := fun k =>
    MemLp.of_bound (hmeas k) _ (Eventually.of_forall (hbd k))
  have hL2' : MemLp (fun ω => L (Y 0 ω)) 2 P := MemLp.of_bound hmeas' _ (Eventually.of_forall hbd')
  simp_rw [variance_eq_sub (hL2 _), variance_eq_sub hL2', Pi.pow_apply]
  have h1 : Tendsto (fun k => ∫ ω, L (truncate (F k) (Y 0 ω)) ^ 2 ∂P) atTop
      (𝓝 (∫ ω, L (Y 0 ω) ^ 2 ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => (‖L‖ * M₀) ^ 2)
      (fun k => (hmeas k).pow 2) (integrable_const _) (fun k => Eventually.of_forall fun ω => ?_)
      (Eventually.of_forall fun ω => (hpt ω).pow 2)
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hbd k ω) 2
  have h2 : Tendsto (fun k => ∫ ω, L (truncate (F k) (Y 0 ω)) ∂P) atTop
      (𝓝 (∫ ω, L (Y 0 ω) ∂P)) :=
    tendsto_integral_of_dominated_convergence (fun _ => ‖L‖ * M₀) hmeas (integrable_const _)
      (fun k => Eventually.of_forall (hbd k)) (Eventually.of_forall hpt)
  exact h1.sub (h2.pow 2)

include hY hmarg htail in
/-- **Continuous linear functionals of the `ℓ¹` Gaussian limit are centred Gaussian** with the
variance of the functional of the observation, for bounded observations. -/
theorem map_eq_gaussianReal_of_marginals {M₀ : ℝ} (hM : ∀ ω, ‖Y 0 ω‖ ≤ M₀) :
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
      ((tendsto_variance_truncate hY L hM hF hcov).const_mul (t ^ 2))
  rw [tendsto_nhds_unique hlim1 hlim2, Real.coe_toNNReal _ (variance_nonneg _ _)]
  push_cast
  ring_nf

end Functional

section Phase

variable {d : ℕ} {𝓧 : Type*} [MeasurableSpace 𝓧] (b : ℝ) (hb : 0 < b) (c : 𝓧 → CoeffFamily d)
  (hc : ∀ x, AbsSummableAt (c x) b)
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → 𝓧)

/-- **The phase evaluation of the `ℓ¹` Gaussian limit of the sample phase observations is a
centred Gaussian variable** with variance `Var[ξ_{Y₀}(u)]`, for bounded observations. -/
theorem map_phaseEvalCLM_eq_gaussianReal (hcm : ∀ γ, Measurable fun x => c x γ)
    (hXm : ∀ i, Measurable (X i)) (hc2 : ∀ γ, MemLp (fun ω => c (X 0 ω) γ) 2 P)
    (hsum : Summable fun γ : Fin d → ℕ => b ^ (∑ i, γ i) * Real.sqrt (∫ ω, (c (X 0 ω) γ) ^ 2 ∂P))
    {M₀ : ℝ} (hM : ∀ x, ‖phaseObs b hb c hc x‖ ≤ M₀) {ν : ProbabilityMeasure (L1Seq (DataIdx d))}
    (hmarg : ∀ F : Finset (DataIdx d), (ν : Measure (L1Seq (DataIdx d))).map (finiteCoords F) =
      gaussianTarget (fun ω => finiteCoords F (sampleObs b hb c hc X 0 ω)) P)
    (htail : ∀ F : Finset (DataIdx d),
      ∫⁻ x, ‖x - truncate F x‖ₑ ∂(ν : Measure (L1Seq (DataIdx d))) ≤
        ENNReal.ofReal (sigmaTail P (sampleObs b hb c hc X 0) F))
    {u : Fin d → ℝ} (hu : u ∈ closedCube d) :
    (ν : Measure (L1Seq (DataIdx d))).map (phaseEvalCLM u hu) =
      gaussianReal 0 (Var[fun ω => CoeffFamily.evalF (xiCoord (phaseObs b hb c hc (X 0 ω))) u;
        P]).toNNReal :=
  map_eq_gaussianReal_of_marginals (summableCoordL2_sampleObs b hb c hc P X hcm (hXm 0) hc2 hsum)
    hmarg htail (phaseEvalCLM u hu) (fun ω => hM (X 0 ω))

end Phase

end Grammar
