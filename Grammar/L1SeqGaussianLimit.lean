/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.L1SeqTight
import Grammar.EmpiricalTail
import Grammar.CLTFiniteDim

/-!
# Existence of the Gaussian limit in `ℓ¹` by tightness

For i.i.d. `ℓ¹`-valued observations with the moment hypothesis, the laws of the empirical sums are
tight (`isTightMeasureSet_empiricalLaw`), so by Prokhorov's theorem
(`isCompact_closure_of_isTightMeasureSet`) a subsequence converges weakly to a probability law `ν`
on `ℓ¹` (`exists_subseq_tendsto_empiricalLaw`).  Every finite coordinate projection of `ν` is the
centred Gaussian with the covariance matrix of the corresponding coordinates of `Y_0`
(`exists_gaussianLimit`), identified through the finite-dimensional CLT along the subsequence and
uniqueness of weak limits; `ν` also inherits the uniform tail bounds
`∫ ‖x − T_F x‖ dν ≤ ∑_{j∉F} σ_j` (bounded continuous truncations of the tail functional and
monotone convergence).

No Gaussian process is constructed on a product space, and no covariance factorisation is needed:
the limit is extracted from the empirical laws themselves.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace BoundedContinuousFunction

namespace Grammar

variable {ι : Type*} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-! ### Finite coordinate projections of the empirical sums -/

section Projection

variable {Y : ℕ → Ω → L1Seq ι}

/-- The finite coordinate projection of the empirical sum is the finite-dimensional normalised
sum of the projected observations. -/
theorem finiteCoords_empiricalSum (hint : Integrable (Y 0) P) (F : Finset ι) (n : ℕ) (ω : Ω) :
    finiteCoords F (empiricalSum Y P n ω) =
      normalisedSum (fun i ω => finiteCoords F (Y i ω)) P n ω := by
  unfold empiricalSum normalisedSum
  rw [map_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sub, (finiteCoords F).integral_comp_comm hint]

theorem memLp_finiteCoords_comp (hY : SummableCoordL2 P (Y 0)) (F : Finset ι) :
    MemLp (fun ω => finiteCoords F (Y 0 ω)) 2 P := by
  have hm : AEStronglyMeasurable (fun ω => finiteCoords F (Y 0 ω)) P :=
    ((finiteCoords F).continuous.measurable.comp hY.measurable).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm hm]
  have : ∀ ω, ‖finiteCoords F (Y 0 ω)‖ ^ 2 = ∑ j : F, (Y 0 ω j) ^ 2 := fun ω => by
    rw [EuclideanSpace.norm_sq_eq]
    simp [Real.norm_eq_abs, sq_abs]
  simp_rw [this]
  exact integrable_finsetSum _ fun j _ => (hY.memLp_coord j).integrable_sq

theorem iIndepFun_finiteCoords_comp (hindep : iIndepFun Y P) (F : Finset ι) :
    iIndepFun (fun i ω => finiteCoords F (Y i ω)) P :=
  hindep.comp (fun _ => finiteCoords F) fun _ => (finiteCoords F).continuous.measurable

theorem identDistrib_finiteCoords_comp (hident : ∀ i, IdentDistrib (Y i) (Y 0) P P)
    (F : Finset ι) (i : ℕ) :
    IdentDistrib (fun ω => finiteCoords F (Y i ω)) (fun ω => finiteCoords F (Y 0 ω)) P P :=
  (hident i).comp (finiteCoords F).continuous.measurable

end Projection

variable [Countable ι] [IsProbabilityMeasure P] [DecidableEq ι]

omit [Countable ι] in
theorem truncate_empty (x : L1Seq ι) : truncate (∅ : Finset ι) x = 0 := by
  simp [truncate_eq_sum]

section Limit

variable {Y : ℕ → Ω → L1Seq ι} (hY : SummableCoordL2 P (Y 0)) (hindep : iIndepFun Y P)
  (hident : ∀ i, IdentDistrib (Y i) (Y 0) P P) (hYm : ∀ i, Measurable (Y i))
include hY hYm

/-- The law of the empirical sum as a probability measure on `ℓ¹`. -/
noncomputable def empiricalLaw (n : ℕ) : ProbabilityMeasure (L1Seq ι) :=
  ⟨P.map (empiricalSum Y P n),
    Measure.isProbabilityMeasure_map (measurable_empiricalSum hY hYm n).aemeasurable⟩

omit [DecidableEq ι] in
theorem empiricalLaw_toMeasure (n : ℕ) :
    (empiricalLaw hY hYm n : Measure (L1Seq ι)) = P.map (empiricalSum Y P n) := rfl

omit [DecidableEq ι] in
include hindep hident in
/-- The empirical laws are tight. -/
theorem isTightMeasureSet_empiricalLaw :
    IsTightMeasureSet {((μ : ProbabilityMeasure (L1Seq ι)) : Measure (L1Seq ι)) |
      μ ∈ Set.range (empiricalLaw hY hYm)} := by
  classical
  obtain ⟨F, hF, hcov⟩ := exists_finset_exhaustion (ι := ι)
  have h := isTightMeasureSet_of_tails (P := P) (measurable_empiricalSum hY hYm)
    (C := sigmaTail P (Y 0) ∅) (fun n => by
      have := lintegral_enorm_sub_truncate_empirical_le hY hindep hident hYm ∅ n
      simpa [truncate_empty] using this)
    (F := F) (tendsto_sigmaTail (Y 0) hF hcov)
    (fun k n => lintegral_enorm_sub_truncate_empirical_le hY hindep hident hYm (F k) n)
  convert h using 1
  ext μ
  constructor
  · rintro ⟨ν, ⟨n, rfl⟩, rfl⟩; exact ⟨n, rfl⟩
  · rintro ⟨n, rfl⟩; exact ⟨empiricalLaw hY hYm n, ⟨n, rfl⟩, rfl⟩

omit [DecidableEq ι] in
include hindep hident in
/-- **Prokhorov**: a subsequence of the empirical laws converges weakly to some `ν`. -/
theorem exists_subseq_tendsto_empiricalLaw :
    ∃ ν : ProbabilityMeasure (L1Seq ι), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun i => empiricalLaw hY hYm (φ i)) atTop (𝓝 ν) := by
  have hc := isCompact_closure_of_isTightMeasureSet
    (isTightMeasureSet_empiricalLaw hY hindep hident hYm)
  have hmem : ∀ n, empiricalLaw hY hYm n ∈ closure (Set.range (empiricalLaw hY hYm)) :=
    fun n => subset_closure ⟨n, rfl⟩
  obtain ⟨ν, -, φ, hφ, hlim⟩ := hc.tendsto_subseq hmem
  exact ⟨ν, φ, hφ, hlim⟩

omit [DecidableEq ι] in
/-- The finite coordinate marginal of the empirical law is the law of the finite-dimensional
normalised sum. -/
theorem empiricalLaw_map_finiteCoords (F : Finset ι) (n : ℕ) :
    ((empiricalLaw hY hYm n).map (finiteCoords F).continuous.measurable.aemeasurable :
      Measure (EuclideanSpace ℝ F)) =
      P.map (normalisedSum (fun i ω => finiteCoords F (Y i ω)) P n) := by
  rw [ProbabilityMeasure.toMeasure_map, empiricalLaw_toMeasure,
    Measure.map_map (finiteCoords F).continuous.measurable (measurable_empiricalSum hY hYm n)]
  congr 1
  funext ω
  exact finiteCoords_empiricalSum (integrable_of_summableCoordL2 P hY) F n ω

include hindep hident in
/-- **Identification of the marginals**: if a subsequence of the empirical laws converges to `ν`,
every finite coordinate marginal of `ν` is the centred Gaussian with the covariance of the
projected observation. -/
theorem map_finiteCoords_eq_gaussianTarget {ν : ProbabilityMeasure (L1Seq ι)} {φ : ℕ → ℕ}
    (hφ : StrictMono φ) (hlim : Tendsto (fun i => empiricalLaw hY hYm (φ i)) atTop (𝓝 ν))
    (F : Finset ι) :
    (ν : Measure (L1Seq ι)).map (finiteCoords F) =
      gaussianTarget (fun ω => finiteCoords F (Y 0 ω)) P := by
  have h1 := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hlim
    (finiteCoords F).continuous
  have h2 := (tendstoInDistribution_normalisedSum_gaussian (memLp_finiteCoords_comp hY F)
    (iIndepFun_finiteCoords_comp hindep F) (identDistrib_finiteCoords_comp hident F)).tendsto
  have h3 := h2.comp hφ.tendsto_atTop
  have hXm : ∀ i, AEMeasurable (fun ω => finiteCoords F (Y i ω)) P := fun i =>
    ((finiteCoords F).continuous.measurable.comp (hYm i)).aemeasurable
  have heq : (fun i => (empiricalLaw hY hYm (φ i)).map
      (finiteCoords F).continuous.measurable.aemeasurable) = fun i =>
      (⟨P.map (normalisedSum (fun i ω => finiteCoords F (Y i ω)) P (φ i)),
        Measure.isProbabilityMeasure_map (aemeasurable_normalisedSum hXm (φ i))⟩ :
        ProbabilityMeasure (EuclideanSpace ℝ F)) := by
    funext i
    apply ProbabilityMeasure.toMeasure_injective
    exact empiricalLaw_map_finiteCoords hY hYm F (φ i)
  rw [heq] at h1
  have h4 := tendsto_nhds_unique h1 h3
  have h5 := congrArg ProbabilityMeasure.toMeasure h4
  simp only [ProbabilityMeasure.toMeasure_map, Measure.map_id] at h5
  exact h5

end Limit

/-! ### Tails of a weak limit -/

section Tails

variable (F : Finset ι)

/-- The truncated tail functional `x ↦ min ‖x − T_F x‖ M` as a bounded continuous function. -/
noncomputable def tailBCF (M : ℕ) : L1Seq ι →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun x => min ‖x - truncate F x‖ M,
      ((continuous_id.sub (truncate F).continuous).norm).min continuous_const⟩ M fun x y => by
    have h1 : 0 ≤ min ‖x - truncate F x‖ (M : ℝ) := le_min (norm_nonneg _) (Nat.cast_nonneg M)
    have h2 : 0 ≤ min ‖y - truncate F y‖ (M : ℝ) := le_min (norm_nonneg _) (Nat.cast_nonneg M)
    simp only [ContinuousMap.coe_mk, Real.dist_eq, abs_sub_le_iff]
    constructor <;> linarith [min_le_right ‖x - truncate F x‖ (M : ℝ),
      min_le_right ‖y - truncate F y‖ (M : ℝ)]

omit [Countable ι] in
@[simp] theorem tailBCF_apply (M : ℕ) (x : L1Seq ι) :
    tailBCF F M x = min ‖x - truncate F x‖ M := rfl

omit [Countable ι] [IsProbabilityMeasure P] in
theorem measurable_tail : Measurable fun x : L1Seq ι => x - truncate F x :=
  (continuous_id.sub (truncate F).continuous).measurable

omit [Countable ι] in
/-- The truncated tail functional integrates to at most the `L¹` tail. -/
theorem integral_tailBCF_le (Q : Measure (L1Seq ι)) [IsProbabilityMeasure Q] (M : ℕ) {t : ℝ}
    (ht0 : 0 ≤ t) (hQ : ∫⁻ x, ‖x - truncate F x‖ₑ ∂Q ≤ ENNReal.ofReal t) :
    ∫ x, tailBCF F M x ∂Q ≤ t := by
  have hint : Integrable (fun x => ‖x - truncate F x‖) Q := by
    refine ⟨(measurable_tail F).norm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    simp_rw [enorm_norm]
    exact lt_of_le_of_lt hQ ENNReal.ofReal_lt_top
  calc ∫ x, tailBCF F M x ∂Q ≤ ∫ x, ‖x - truncate F x‖ ∂Q :=
        integral_mono_ae ((tailBCF F M).integrable Q) hint
          (Eventually.of_forall fun x => min_le_left _ _)
    _ = (∫⁻ x, ‖x - truncate F x‖ₑ ∂Q).toReal := by
        rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => norm_nonneg _)
          (measurable_tail F).norm.aestronglyMeasurable]
        simp_rw [ofReal_norm]
    _ ≤ t := ENNReal.toReal_le_of_le_ofReal ht0 hQ

omit [Countable ι] [IsProbabilityMeasure P] in
theorem iSup_ofReal_min_natCast (a : ℝ) :
    ⨆ M : ℕ, ENNReal.ofReal (min a M) = ENNReal.ofReal a := by
  refine le_antisymm (iSup_le fun M => ENNReal.ofReal_le_ofReal (min_le_left _ _)) ?_
  refine le_iSup_of_le ⌈a⌉₊ ?_
  rw [min_eq_left (Nat.le_ceil a)]

omit [Countable ι] in
/-- **Tails pass to weak limits**: a uniform `L¹` tail bound along a weakly convergent sequence of
laws holds for the limit. -/
theorem lintegral_enorm_sub_truncate_le_of_tendsto {μs : ℕ → ProbabilityMeasure (L1Seq ι)}
    {ν : ProbabilityMeasure (L1Seq ι)} (hlim : Tendsto μs atTop (𝓝 ν)) {t : ℝ} (ht0 : 0 ≤ t)
    (hμ : ∀ i, ∫⁻ x, ‖x - truncate F x‖ₑ ∂(μs i : Measure (L1Seq ι)) ≤ ENNReal.ofReal t) :
    ∫⁻ x, ‖x - truncate F x‖ₑ ∂(ν : Measure (L1Seq ι)) ≤ ENNReal.ofReal t := by
  have hM : ∀ M : ℕ, ∫⁻ x, ENNReal.ofReal (tailBCF F M x) ∂(ν : Measure (L1Seq ι)) ≤
      ENNReal.ofReal t := fun M => by
    have h1 := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hlim) (tailBCF F M)
    have h2 : ∫ x, tailBCF F M x ∂(ν : Measure (L1Seq ι)) ≤ t :=
      le_of_tendsto' h1 fun i => integral_tailBCF_le F _ M ht0 (hμ i)
    rw [← ofReal_integral_eq_lintegral_ofReal ((tailBCF F M).integrable _)
      (Eventually.of_forall fun x => le_min (norm_nonneg _) (Nat.cast_nonneg M))]
    exact ENNReal.ofReal_le_ofReal h2
  have hsup : ∀ x : L1Seq ι, ‖x - truncate F x‖ₑ = ⨆ M : ℕ, ENNReal.ofReal (tailBCF F M x) :=
    fun x => by
      rw [← ofReal_norm, ← iSup_ofReal_min_natCast]
      rfl
  simp_rw [hsup]
  rw [lintegral_iSup (fun M => ((tailBCF F M).continuous.measurable).ennreal_ofReal)
    (fun M M' hMM' x => ENNReal.ofReal_le_ofReal
      (min_le_min le_rfl (Nat.cast_le.2 hMM')))]
  exact iSup_le hM

end Tails

/-! ### The Gaussian limit -/

section Existence

variable {Y : ℕ → Ω → L1Seq ι} (hY : SummableCoordL2 P (Y 0)) (hindep : iIndepFun Y P)
  (hident : ∀ i, IdentDistrib (Y i) (Y 0) P P) (hYm : ∀ i, Measurable (Y i))
include hY hindep hident hYm

/-- **Existence of the Gaussian limit in `ℓ¹`**: a probability law `ν` on `ℓ¹` all of whose finite
coordinate marginals are the centred Gaussians with the covariance of the corresponding
coordinates of `Y_0`, with the uniform tail bounds `∫ ‖x − T_F x‖ dν ≤ ∑_{j∉F} σ_j`. -/
theorem exists_gaussianLimit : ∃ ν : ProbabilityMeasure (L1Seq ι),
    (∀ F : Finset ι, (ν : Measure (L1Seq ι)).map (finiteCoords F) =
      gaussianTarget (fun ω => finiteCoords F (Y 0 ω)) P) ∧
    ∀ F : Finset ι, ∫⁻ x, ‖x - truncate F x‖ₑ ∂(ν : Measure (L1Seq ι)) ≤
      ENNReal.ofReal (sigmaTail P (Y 0) F) := by
  obtain ⟨ν, φ, hφ, hlim⟩ := exists_subseq_tendsto_empiricalLaw hY hindep hident hYm
  refine ⟨ν, fun F => map_finiteCoords_eq_gaussianTarget hY hindep hident hYm hφ hlim F,
    fun F => ?_⟩
  refine lintegral_enorm_sub_truncate_le_of_tendsto F hlim (sigmaTail_nonneg (Y 0) F) fun i => ?_
  rw [empiricalLaw_toMeasure, lintegral_map ((measurable_tail F).enorm)
    (measurable_empiricalSum hY hYm (φ i))]
  exact lintegral_enorm_sub_truncate_empirical_le hY hindep hident hYm F (φ i)

end Existence

end Grammar
