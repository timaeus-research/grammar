/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.L1SeqCLT
import Grammar.ClosureEndpoint

/-!
# The `ℓ¹` limit law is a Gaussian measure (companion note, Rank 5, part 1)

The `ℓ¹` central limit theorem (`clt_l1`) delivers a probability law `ν` on `ℓ¹` whose finite
coordinate marginals are centred Gaussians with the covariance of the coordinate data. Here this
is upgraded to Mathlib's `IsGaussian ν`: every continuous linear functional `L` on `ℓ¹` has a
Gaussian law under `ν`.

* Truncations factor through the finite coordinates (`truncate_eq_embedCoords_comp`), so the laws
  `ν.map (truncate F)` are Gaussian (`isGaussian_map_truncate`).
* Along a covering exhaustion `F_k` the truncated functionals `L ∘ T_{F_k}` converge pointwise to
  `L` with the bound `‖L‖‖a‖`; dominated convergence (with `‖a‖ ∈ L²(ν)`, from the summable
  coordinate `L²` norms) transports the means, the variances and the characteristic functions,
  and Mathlib's `isGaussian_iff_charFunDual_eq` closes (`isGaussian_of_truncations`).
* The bridge from the marginal form produced by the CLT (`isGaussian_of_marginals`), and the CLT
  with the Gaussian-measure conclusion added (`clt_l1_isGaussian`).
-/

open MeasureTheory ProbabilityTheory Filter Topology Complex
open scoped ENNReal NNReal

namespace Grammar

variable {ι : Type*} [Countable ι] [DecidableEq ι]

/-! ### Truncations factor through the finite coordinates -/

/-- The embedding `ℝ^F → ℓ¹`, `v ↦ ∑_{j∈F} v_j e_j`. -/
noncomputable def embedCoords (F : Finset ι) : EuclideanSpace ℝ F →L[ℝ] L1Seq ι :=
  ∑ j : F, (singleCLM (j : ι)).comp (EuclideanSpace.proj j)

omit [Countable ι] in
theorem truncate_eq_embedCoords_comp (F : Finset ι) :
    truncate F = (embedCoords F).comp (finiteCoords F) := by
  refine ContinuousLinearMap.ext fun a => ?_
  rw [ContinuousLinearMap.comp_apply, truncate_eq_sum, embedCoords, sum_apply]
  simp only [ContinuousLinearMap.comp_apply, EuclideanSpace.coe_proj, singleCLM_apply]
  exact (Finset.sum_coe_sort F fun j => lp.single (E := fun _ : ι => ℝ) 1 j (a j)).symm

omit [Countable ι] in
theorem isGaussian_map_truncate {ν : Measure (L1Seq ι)} (F : Finset ι)
    [IsGaussian (ν.map (finiteCoords F))] : IsGaussian (ν.map (truncate F)) := by
  rw [truncate_eq_embedCoords_comp, ContinuousLinearMap.coe_comp,
    ← Measure.map_map (embedCoords F).continuous.measurable (finiteCoords F).continuous.measurable]
  infer_instance

/-! ### From Gaussian truncations to a Gaussian measure -/

section Law

variable {ν : Measure (L1Seq ι)} [IsProbabilityMeasure ν]

omit [DecidableEq ι] in
theorem integrable_norm_of_summableCoordL2 (hν : SummableCoordL2 ν id) :
    Integrable (fun a : L1Seq ι => ‖a‖) ν :=
  (memLp_two_of_summableCoordL2 hν).norm.integrable one_le_two

omit [DecidableEq ι] [IsProbabilityMeasure ν] in
theorem integrable_norm_sq_of_summableCoordL2 (hν : SummableCoordL2 ν id) :
    Integrable (fun a : L1Seq ι => ‖a‖ ^ 2) ν :=
  (memLp_two_iff_integrable_sq (memLp_two_of_summableCoordL2 hν).norm.aestronglyMeasurable).1
    (memLp_two_of_summableCoordL2 hν).norm

omit [DecidableEq ι] [IsProbabilityMeasure ν] in
theorem memLp_two_dual (hν : SummableCoordL2 ν id) (L : StrongDual ℝ (L1Seq ι)) :
    MemLp L 2 ν := by
  refine ((memLp_two_of_summableCoordL2 hν).norm.const_mul ‖L‖).of_le
    L.continuous.aestronglyMeasurable (Eventually.of_forall fun a => ?_)
  rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg L) (norm_nonneg (id a)))]
  exact L.le_opNorm a

omit [Countable ι] in
/-- Centred coordinates give centred truncated functionals. -/
theorem integral_comp_truncate_eq_zero (hν : SummableCoordL2 ν id)
    (hmean : ∀ j, ∫ a, a j ∂ν = 0) (L : StrongDual ℝ (L1Seq ι)) (F : Finset ι) :
    ∫ a, L (truncate F a) ∂ν = 0 := by
  have h : ∀ a : L1Seq ι, L (truncate F a) = ∑ j ∈ F, a j * L (singleCLM j 1) := by
    intro a
    rw [truncate_eq_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hs : lp.single (E := fun _ : ι => ℝ) 1 j (a j) = a j • singleCLM j 1 := by
      rw [← map_smul, smul_eq_mul, mul_one]
      rfl
    rw [hs, map_smul, smul_eq_mul]
  simp_rw [h]
  rw [integral_finsetSum (f := fun j (a : L1Seq ι) => a j * L (singleCLM j 1)) F
    fun j _ => ((hν.memLp_coord j).integrable one_le_two).mul_const _]
  simp [integral_mul_const, hmean]

omit [DecidableEq ι] in
/-- Centred coordinates give centred functionals: `∫ L dν = 0` for every `L ∈ (ℓ¹)*`. -/
theorem integral_dual_eq_zero (hν : SummableCoordL2 ν id) (hmean : ∀ j, ∫ a, a j ∂ν = 0)
    (L : StrongDual ℝ (L1Seq ι)) : ∫ a, L a ∂ν = 0 := by
  classical
  obtain ⟨F, hF, hcov⟩ := exists_finset_exhaustion (ι := ι)
  have hpt : ∀ a : L1Seq ι, Tendsto (fun k => L (truncate (F k) a)) atTop (𝓝 (L a)) :=
    fun a => (L.continuous.tendsto _).comp (tendsto_truncate hF hcov a)
  have hbd : ∀ k a, ‖L (truncate (F k) a)‖ ≤ ‖L‖ * ‖a‖ := fun k a =>
    (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left (norm_truncate_le _ _) (norm_nonneg _))
  have hmeas : ∀ k, Continuous fun a => L (truncate (F k) a) := fun k =>
    L.continuous.comp (truncate (F k)).continuous
  have h := tendsto_integral_of_dominated_convergence (fun a => ‖L‖ * ‖a‖)
    (fun k => (hmeas k).aestronglyMeasurable)
    ((integrable_norm_of_summableCoordL2 hν).const_mul _)
    (fun k => Eventually.of_forall fun a => hbd k a) (Eventually.of_forall hpt)
  simp_rw [integral_comp_truncate_eq_zero hν hmean L] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

/-- ★★ **The `ℓ¹` limit law is a Gaussian measure**: a probability law on `ℓ¹` with centred
coordinates, summable coordinate `L²` norms and Gaussian finite truncations is Gaussian. -/
theorem isGaussian_of_truncations (hν : SummableCoordL2 ν id) (hmean : ∀ j, ∫ a, a j ∂ν = 0)
    (hG : ∀ F : Finset ι, IsGaussian (ν.map (truncate F))) : IsGaussian ν := by
  obtain ⟨F, hF, hcov⟩ := exists_finset_exhaustion (ι := ι)
  refine isGaussian_of_charFunDual_eq fun L => ?_
  have hL2 := memLp_two_dual hν L
  have hn2 := integrable_norm_sq_of_summableCoordL2 hν
  have hpt : ∀ a : L1Seq ι, Tendsto (fun k => L (truncate (F k) a)) atTop (𝓝 (L a)) :=
    fun a => (L.continuous.tendsto _).comp (tendsto_truncate hF hcov a)
  have hbd : ∀ k a, ‖L (truncate (F k) a)‖ ≤ ‖L‖ * ‖a‖ := fun k a =>
    (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left (norm_truncate_le _ _) (norm_nonneg _))
  have hmeas : ∀ k, Continuous fun a => L (truncate (F k) a) := fun k =>
    L.continuous.comp (truncate (F k)).continuous
  -- means
  have hmean_k : ∀ k, ∫ a, L (truncate (F k) a) ∂ν = 0 := fun k =>
    integral_comp_truncate_eq_zero hν hmean L (F k)
  have hmean_L : ∫ a, L a ∂ν = 0 := integral_dual_eq_zero hν hmean L
  -- variances
  have hL2k : ∀ k, MemLp (fun a => L (truncate (F k) a)) 2 ν := fun k =>
    memLp_two_dual hν (L.comp (truncate (F k)))
  have hvar_k : ∀ k, Var[fun a => L (truncate (F k) a); ν] = ∫ a, L (truncate (F k) a) ^ 2 ∂ν := by
    intro k
    rw [variance_eq_sub (hL2k k), hmean_k]
    simp [Pi.pow_apply]
  have hvar_L : Var[L; ν] = ∫ a, L a ^ 2 ∂ν := by
    rw [variance_eq_sub hL2, hmean_L]
    simp [Pi.pow_apply]
  have hvar_lim : Tendsto (fun k => Var[fun a => L (truncate (F k) a); ν]) atTop
      (𝓝 (Var[L; ν])) := by
    simp_rw [hvar_k, hvar_L]
    refine tendsto_integral_of_dominated_convergence (fun a => ‖L‖ ^ 2 * ‖a‖ ^ 2)
      (fun k => ((hmeas k).pow 2).aestronglyMeasurable) (hn2.const_mul _)
      (fun k => Eventually.of_forall fun a => ?_) (Eventually.of_forall fun a => (hpt a).pow 2)
    rw [norm_pow, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hbd k a) 2
  -- characteristic functions
  have hchar_k : ∀ k, charFunDual ν (L.comp (truncate (F k))) =
      exp (-(Var[fun a => L (truncate (F k) a); ν] : ℂ) / 2) := by
    intro k
    have := hG (F k)
    rw [← charFunDual_map (truncate (F k)) L, IsGaussian.charFunDual_eq L,
      integral_complex_ofReal, integral_map (truncate (F k)).continuous.measurable.aemeasurable
        L.continuous.aestronglyMeasurable,
      variance_map L.continuous.measurable.aemeasurable
        (truncate (F k)).continuous.measurable.aemeasurable]
    simp only [Function.comp_def]
    rw [hmean_k]
    simp [neg_div]
  have hchar_lim : Tendsto (fun k => charFunDual ν (L.comp (truncate (F k)))) atTop
      (𝓝 (charFunDual ν L)) := by
    simp_rw [charFunDual_apply]
    refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
      (fun k => ?_) (integrable_const _) (fun k => Eventually.of_forall fun a => ?_)
      (Eventually.of_forall fun a => ?_)
    · exact (Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp (hmeas k)).mul
        continuous_const)).aestronglyMeasurable
    · simp only [ContinuousLinearMap.comp_apply]
      exact (Complex.norm_exp_ofReal_mul_I _).le
    · simp only [ContinuousLinearMap.comp_apply]
      exact (Complex.continuous_exp.tendsto _).comp
        (((Complex.continuous_ofReal.tendsto _).comp (hpt a)).mul_const I)
  have hlim2 : Tendsto (fun k => exp (-(Var[fun a => L (truncate (F k) a); ν] : ℂ) / 2)) atTop
      (𝓝 (exp (-(Var[L; ν] : ℂ) / 2))) :=
    (Complex.continuous_exp.tendsto _).comp
      (((Complex.continuous_ofReal.tendsto _).comp hvar_lim).neg.div_const 2)
  have h := tendsto_nhds_unique hchar_lim (hlim2.congr fun k => (hchar_k k).symm)
  rw [h, integral_complex_ofReal, hmean_L]
  congr 1
  push_cast
  ring

end Law

/-! ### The bridge from the CLT's marginal form -/

section Bridge

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {Y : Ω → L1Seq ι} {ν : Measure (L1Seq ι)} [IsProbabilityMeasure ν]

/-- The point `j` of the singleton finite set. -/
def singletonIdx (j : ι) : ({j} : Finset ι) := ⟨j, Finset.mem_singleton_self j⟩

omit [Countable ι] [DecidableEq ι] in
theorem coord_eq_finiteCoords_singleton (a : L1Seq ι) (j : ι) :
    a j = finiteCoords {j} a (singletonIdx j) := rfl

omit [IsProbabilityMeasure P] in
theorem isGaussian_gaussianTarget {κ : Type*} [Fintype κ] [DecidableEq κ]
    (X : Ω → EuclideanSpace ℝ κ) : IsGaussian (gaussianTarget X P) := by
  unfold gaussianTarget
  infer_instance

omit [IsProbabilityMeasure P] in
/-- The coordinate mean of the Gaussian target vanishes. -/
theorem integral_eval_gaussianTarget {κ : Type*} [Fintype κ] [DecidableEq κ]
    (X : Ω → EuclideanSpace ℝ κ) (i : κ) : ∫ v, v i ∂gaussianTarget X P = 0 := by
  have := isGaussian_gaussianTarget (P := P) X
  have h := (EuclideanSpace.proj (𝕜 := ℝ) i : EuclideanSpace ℝ κ →L[ℝ] ℝ).integral_comp_comm
    (μ := gaussianTarget X P) (φ := id) IsGaussian.integrable_id
  simp only [id] at h
  rw [show (fun v : EuclideanSpace ℝ κ => v i) =
    fun v => (EuclideanSpace.proj (𝕜 := ℝ) i : EuclideanSpace ℝ κ →L[ℝ] ℝ) v from rfl, h]
  unfold gaussianTarget
  rw [integral_id_multivariateGaussian, map_zero]

/-- The coordinate second moment of the Gaussian target is the variance of the coordinate. -/
theorem integral_eval_sq_gaussianTarget {κ : Type*} [Fintype κ] [DecidableEq κ]
    {X : Ω → EuclideanSpace ℝ κ} (hX : MemLp X 2 P) (i : κ) :
    ∫ v, v i ^ 2 ∂gaussianTarget X P = Var[fun ω => X ω i; P] := by
  have := isGaussian_gaussianTarget (P := P) X
  have hL : MemLp (fun v : EuclideanSpace ℝ κ => v i) 2 (gaussianTarget X P) :=
    IsGaussian.memLp_dual _ (EuclideanSpace.proj i) 2 (by simp)
  have h := variance_eq_sub hL
  rw [integral_eval_gaussianTarget] at h
  simp only [Pi.pow_apply, zero_pow two_ne_zero, sub_zero] at h
  rw [← h]
  unfold gaussianTarget
  rw [variance_eval_multivariateGaussian (covMat_posSemidef hX)]
  simp only [covMat, Matrix.of_apply]
  have hm : Measurable (EuclideanSpace.proj (𝕜 := ℝ) i : EuclideanSpace ℝ κ →L[ℝ] ℝ) :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.measurable
  exact covariance_self (hm.comp_aemeasurable hX.aestronglyMeasurable.aemeasurable)

variable (hY : SummableCoordL2 P Y)
  (hmarg : ∀ F : Finset ι,
    ν.map (finiteCoords F) = gaussianTarget (fun ω => finiteCoords F (Y ω)) P)
include hY hmarg

omit [DecidableEq ι] [IsProbabilityMeasure P] hmarg in
theorem memLp_two_finiteCoords_comp (F : Finset ι) :
    MemLp (fun ω => finiteCoords F (Y ω)) 2 P :=
  (finiteCoords F).comp_memLp' (memLp_two_of_summableCoordL2 hY)

omit [Countable ι] [IsProbabilityMeasure ν] [IsProbabilityMeasure P] hY in
theorem isGaussian_map_finiteCoords (F : Finset ι) : IsGaussian (ν.map (finiteCoords F)) := by
  rw [hmarg F]
  exact isGaussian_gaussianTarget _

omit [IsProbabilityMeasure ν] [IsProbabilityMeasure P] hY in
/-- The coordinates of the limit law are centred. -/
theorem integral_coord_eq_zero (j : ι) : ∫ a, a j ∂ν = 0 := by
  have h : (fun a : L1Seq ι => a j) = fun a => finiteCoords {j} a (singletonIdx j) := rfl
  rw [h, ← integral_map (f := fun v : EuclideanSpace ℝ ({j} : Finset ι) => v (singletonIdx j))
    (finiteCoords {j}).continuous.measurable.aemeasurable
    ((EuclideanSpace.proj (𝕜 := ℝ) (singletonIdx j) : EuclideanSpace ℝ ({j} : Finset ι) →L[ℝ] ℝ)
      |>.continuous.aestronglyMeasurable), hmarg, integral_eval_gaussianTarget]

omit [IsProbabilityMeasure ν] in
/-- The coordinate second moments of the limit law are the coordinate variances of the data. -/
theorem integral_coord_sq_eq (j : ι) : ∫ a, a j ^ 2 ∂ν = Var[fun ω => Y ω j; P] := by
  have h : (fun a : L1Seq ι => a j ^ 2) = fun a => finiteCoords {j} a (singletonIdx j) ^ 2 := rfl
  rw [h, ← integral_map (f := fun v : EuclideanSpace ℝ ({j} : Finset ι) => v (singletonIdx j) ^ 2)
    (finiteCoords {j}).continuous.measurable.aemeasurable
    (((EuclideanSpace.proj (𝕜 := ℝ) (singletonIdx j) : EuclideanSpace ℝ ({j} : Finset ι) →L[ℝ] ℝ)
      |>.continuous.pow 2).aestronglyMeasurable), hmarg,
    integral_eval_sq_gaussianTarget (memLp_two_finiteCoords_comp hY {j})]
  rfl

omit [IsProbabilityMeasure ν] in
/-- The coordinates of the limit law are in `L²` with norms dominated by those of the data. -/
theorem summableCoordL2_id_of_marginals : SummableCoordL2 ν id := by
  refine ⟨measurable_id, fun j => ?_, ?_⟩
  · have := isGaussian_map_finiteCoords hmarg ({j} : Finset ι)
    have h : MemLp (fun v : EuclideanSpace ℝ ({j} : Finset ι) => v (singletonIdx j)) 2
        (ν.map (finiteCoords {j})) :=
      IsGaussian.memLp_dual _ (EuclideanSpace.proj (singletonIdx j)) 2 (by simp)
    exact (memLp_map_measure_iff (EuclideanSpace.proj (𝕜 := ℝ) (singletonIdx j) :
      EuclideanSpace ℝ ({j} : Finset ι) →L[ℝ] ℝ).continuous.aestronglyMeasurable
      (finiteCoords {j}).continuous.measurable.aemeasurable).1 h
  · refine hY.summable.of_nonneg_of_le (fun j => coordL2_nonneg _ _ _) fun j => ?_
    unfold coordL2
    refine Real.sqrt_le_sqrt ?_
    simp only [id]
    rw [integral_coord_sq_eq hY hmarg j, variance_eq_sub (hY.memLp_coord j)]
    simp only [Pi.pow_apply]
    exact sub_le_self _ (sq_nonneg _)

/-- ★★ **The `ℓ¹` limit law of the CLT is a Gaussian measure.** -/
theorem isGaussian_of_marginals : IsGaussian ν :=
  isGaussian_of_truncations (summableCoordL2_id_of_marginals hY hmarg)
    (integral_coord_eq_zero hmarg) fun F => by
      have := isGaussian_map_finiteCoords hmarg F
      exact isGaussian_map_truncate F

/-- The limit law is centred: `∫ L dν = 0` for every `L ∈ (ℓ¹)*`. -/
theorem integral_dual_eq_zero_of_marginals (L : StrongDual ℝ (L1Seq ι)) : ∫ a, L a ∂ν = 0 :=
  integral_dual_eq_zero (summableCoordL2_id_of_marginals hY hmarg) (integral_coord_eq_zero hmarg) L

end Bridge

/-! ### The `ℓ¹` CLT with a Gaussian-measure limit -/

section CLT

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {Y : ℕ → Ω → L1Seq ι}

/-- ★★ **The `ℓ¹` central limit theorem with a Gaussian-measure limit**: the limit law `ν` of
`clt_l1` is a Gaussian measure on `ℓ¹` (every continuous linear functional has a Gaussian law),
with the centred Gaussian finite coordinate marginals and the tail certificate. -/
theorem clt_l1_isGaussian (hY : SummableCoordL2 P (Y 0)) (hindep : iIndepFun Y P)
    (hident : ∀ i, IdentDistrib (Y i) (Y 0) P P) (hYm : ∀ i, Measurable (Y i)) :
    ∃ ν : ProbabilityMeasure (L1Seq ι), IsGaussian (ν : Measure (L1Seq ι)) ∧
      TendstoInDistribution (empiricalSum Y P) atTop id (fun _ => P) (ν : Measure (L1Seq ι)) ∧
      (∀ F : Finset ι, (ν : Measure (L1Seq ι)).map (finiteCoords F) =
        gaussianTarget (fun ω => finiteCoords F (Y 0 ω)) P) ∧
      ∀ F : Finset ι, ∫⁻ x, ‖x - truncate F x‖ₑ ∂(ν : Measure (L1Seq ι)) ≤
        ENNReal.ofReal (sigmaTail P (Y 0) F) := by
  obtain ⟨ν, hconv, hmarg, htail⟩ := clt_l1 hY hindep hident hYm
  have : IsProbabilityMeasure (ν : Measure (L1Seq ι)) := ν.2
  exact ⟨ν, isGaussian_of_marginals (ν := (ν : Measure (L1Seq ι))) hY hmarg, hconv, hmarg, htail⟩

end CLT

end Grammar
