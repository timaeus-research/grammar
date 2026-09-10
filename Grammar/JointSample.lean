/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.SampleDatum
import Grammar.StochasticAssembly

/-!
# Joint charts from one sample: the stacked observation

The paper's empirical process is one process on the resolution manifold restricted to the charts;
the chart data are therefore **coupled through the common sample**.  Stacking the per-chart phase
observations of a single sample point into `ℓ¹` over the disjoint union of the chart indices
(`stack`), one application of the `ℓ¹` CLT gives joint convergence of all chart data with the
cross-chart covariance of the common sample (`jointSampleDatum_tendstoInDistribution`); the
chart marginals are the single-chart empirical sums (`unpack_empiricalSum_stack`).  Marginal
convergence of the charts separately would not recover this coupling.

A **reconstruction interface**: any continuous linear map `T` from the stacked `ℓ¹` into the joint
tangential data `JointData K n` transports the CLT (`reconstruct_tendstoInDistribution`), and with
the existing chart decomposition and residual hypotheses the assembled stochastic expansion
follows (`assembled_expansion_of_reconstruction`).

Non-claims: no construction of `T` from tangential analyticity (that needs a joint product-polydisc
presentation); the residual and decomposition hypotheses of the assembled theorem are retained.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace Grammar

open CoeffFamily

variable {M : ℕ} {n : Fin M → ℕ}

/-- The stacked index: the disjoint union of the chart data indices. -/
abbrev StackIdx (n : Fin M → ℕ) := Σ I : Fin M, DataIdx (n I + 1)

/-- Stacking finitely many `ℓ¹` data into `ℓ¹` over the disjoint union. -/
noncomputable def stack (y : ∀ I, L1Seq (DataIdx (n I + 1))) : L1Seq (StackIdx n) :=
  ⟨fun j => y j.1 j.2, by
    change Memℓp _ 1
    rw [memℓp_gen_iff (p := 1) (by simp)]
    simp only [ENNReal.toReal_one, Real.rpow_one, Real.norm_eq_abs]
    refine (summable_sigma_of_nonneg fun _ => abs_nonneg _).2 ⟨fun I => ?_, Summable.of_finite⟩
    exact L1Seq.summable_abs (y I)⟩

@[simp] theorem stack_apply (y : ∀ I, L1Seq (DataIdx (n I + 1))) (j : StackIdx n) :
    stack y j = y j.1 j.2 := rfl

/-- The chart `I` component of a stacked datum. -/
noncomputable def unpack (I : Fin M) : L1Seq (StackIdx n) →L[ℝ] DataSpace (n I + 1) :=
  LinearMap.mkContinuous
    { toFun := fun z => ⟨fun j => z ⟨I, j⟩, by
        change Memℓp _ 1
        rw [memℓp_gen_iff (p := 1) (by simp)]
        simp only [ENNReal.toReal_one, Real.rpow_one, Real.norm_eq_abs]
        exact (L1Seq.summable_abs z).comp_injective
          (fun a b h => eq_of_heq (Sigma.mk.inj_iff.1 h).2 :
            Function.Injective fun j : DataIdx (n I + 1) => (⟨I, j⟩ : StackIdx n))⟩
      map_add' := fun z w => by ext j; rfl
      map_smul' := fun c z => by ext j; rfl } 1 fun z => by
    rw [one_mul, L1Seq.norm_eq_tsum, L1Seq.norm_eq_tsum]
    have key : ∑' j : DataIdx (n I + 1), |z ⟨I, j⟩| ≤ ∑' c : StackIdx n, |z c| := by
      have hinj : Function.Injective fun j : DataIdx (n I + 1) => (⟨I, j⟩ : StackIdx n) :=
        fun a b h => eq_of_heq (Sigma.mk.inj_iff.1 h).2
      refine Summable.tsum_le_tsum_of_inj (fun j : DataIdx (n I + 1) => (⟨I, j⟩ : StackIdx n))
        hinj ?_ ?_ ?_ ?_
      · exact fun _ _ => abs_nonneg _
      · exact fun _ => le_rfl
      · exact (L1Seq.summable_abs z).comp_injective hinj
      · exact L1Seq.summable_abs z
    exact key

@[simp] theorem unpack_apply (I : Fin M) (z : L1Seq (StackIdx n)) (j : DataIdx (n I + 1)) :
    unpack I z j = z ⟨I, j⟩ := rfl

theorem unpack_stack (y : ∀ I, L1Seq (DataIdx (n I + 1))) (I : Fin M) :
    unpack I (stack y) = y I := by
  ext j; simp

/-- All chart components at once. -/
noncomputable def unpackAll : L1Seq (StackIdx n) →L[ℝ] ∀ I, DataSpace (n I + 1) :=
  ContinuousLinearMap.pi fun I => unpack I

@[simp] theorem unpackAll_apply (z : L1Seq (StackIdx n)) (I : Fin M) :
    unpackAll z I = unpack I z := rfl

section Sample

variable {𝓧 : Type*} [MeasurableSpace 𝓧] {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
  [IsProbabilityMeasure P] (Y : ∀ I, 𝓧 → L1Seq (DataIdx (n I + 1))) (X : ℕ → Ω → 𝓧)

/-- The stacked observation of one sample point. -/
noncomputable def stackObs (x : 𝓧) : L1Seq (StackIdx n) := stack fun I => Y I x

theorem measurable_stackObs (hY : ∀ I, Measurable (Y I)) : Measurable (stackObs Y) :=
  measurable_of_coords fun j => (measurable_coord j.2).comp (hY j.1)

omit [IsProbabilityMeasure P] in
/-- The moment hypothesis stacks: each chart's certificate gives the joint certificate. -/
theorem summableCoordL2_stackObs (hX0 : Measurable (X 0)) (hYm : ∀ I, Measurable (Y I))
    (hY : ∀ I, SummableCoordL2 P fun ω => Y I (X 0 ω)) :
    SummableCoordL2 P fun ω => stackObs Y (X 0 ω) where
  measurable := (measurable_stackObs Y hYm).comp hX0
  memLp_coord := fun j => (hY j.1).memLp_coord j.2
  summable := by
    refine (summable_sigma_of_nonneg fun j => coordL2_nonneg P _ j).2
      ⟨fun I => ?_, Summable.of_finite⟩
    exact (hY I).summable

/-- The joint sample datum: the unpacked stacked empirical sum plus the amplitude data. -/
noncomputable def jointSampleDatum (A : ∀ I, DataSpace (n I + 1)) (N : ℕ) (ω : Ω) :
    ∀ I, DataSpace (n I + 1) :=
  unpackAll (empiricalSum (fun i ω => stackObs Y (X i ω)) P N ω) + A

omit [MeasurableSpace 𝓧] [IsProbabilityMeasure P] in
/-- The chart marginal of the stacked empirical sum is the chart's own empirical sum. -/
theorem unpack_empiricalSum_stack (hint : Integrable (fun ω => stackObs Y (X 0 ω)) P) (I : Fin M)
    (N : ℕ) (ω : Ω) :
    unpack I (empiricalSum (fun i ω => stackObs Y (X i ω)) P N ω) =
      empiricalSum (fun i ω => Y I (X i ω)) P N ω := by
  unfold empiricalSum
  rw [map_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  dsimp only
  rw [map_sub, ← (unpack I).integral_comp_comm hint]
  simp only [stackObs, unpack_stack]

/-- **Joint convergence of all chart data from one sample** (the cross-chart covariance is that of
the common sample): the joint sample datum converges in distribution on `∀ I, DataSpace` to the
image of the stacked `ℓ¹` Gaussian limit. -/
theorem jointSampleDatum_tendstoInDistribution (hYm : ∀ I, Measurable (Y I))
    (hXm : ∀ i, Measurable (X i)) (hXind : iIndepFun X P)
    (hXid : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hY : ∀ I, SummableCoordL2 P fun ω => Y I (X 0 ω)) (A : ∀ I, DataSpace (n I + 1)) :
    ∃ ν : ProbabilityMeasure (L1Seq (StackIdx n)),
      TendstoInDistribution (jointSampleDatum P Y X A) atTop (fun z => unpackAll z + A)
        (fun _ => P) (ν : Measure (L1Seq (StackIdx n))) ∧
      ∀ F : Finset (StackIdx n), (ν : Measure (L1Seq (StackIdx n))).map (finiteCoords F) =
        gaussianTarget (fun ω => finiteCoords F (stackObs Y (X 0 ω))) P := by
  have hS : SummableCoordL2 P fun ω => stackObs Y (X 0 ω) :=
    summableCoordL2_stackObs P Y X (hXm 0) hYm hY
  obtain ⟨ν, hν, hmarg, -⟩ := clt_l1 hS
    (hXind.comp (fun _ => stackObs Y) fun _ => measurable_stackObs Y hYm)
    (fun i => (hXid i).comp (measurable_stackObs Y hYm))
    (fun i => (measurable_stackObs Y hYm).comp (hXm i))
  refine ⟨ν, ?_, hmarg⟩
  exact hν.continuous_comp ((continuous_add_const A).comp unpackAll.continuous)

end Sample

/-! ### Reconstruction into joint tangential data -/

section Reconstruct

variable {K : Fin M → Type*} [∀ I, TopologicalSpace (K I)] [∀ I, CompactSpace (K I)]
  [∀ I, T2Space (K I)] [∀ I, MeasurableSpace (K I)] [∀ I, OpensMeasurableSpace (K I)]
  {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

noncomputable instance : NormedSpace ℝ (JointData K n) :=
  inferInstanceAs (NormedSpace ℝ (∀ I, TangentialData (K I) (n I + 1)))

omit [∀ I, T2Space (K I)] [∀ I, MeasurableSpace (K I)] [∀ I, OpensMeasurableSpace (K I)] in
/-- **The reconstruction interface**: a continuous linear map from the stacked `ℓ¹` into the joint
tangential data transports the CLT of the stacked observations. -/
theorem reconstruct_tendstoInDistribution {J : Type*} [Countable J]
    {V : ℕ → Ω → L1Seq J} (hV : SummableCoordL2 P (V 0)) (hindep : iIndepFun V P)
    (hident : ∀ i, IdentDistrib (V i) (V 0) P P) (hVm : ∀ i, Measurable (V i))
    (T : L1Seq J →L[ℝ] JointData K n) (A : JointData K n) :
    ∃ ν : ProbabilityMeasure (L1Seq J),
      TendstoInDistribution (fun N ω => T (empiricalSum V P N ω) + A) atTop (fun z => T z + A)
        (fun _ => P) (ν : Measure (L1Seq J)) := by
  classical
  obtain ⟨ν, hν, -, -⟩ := clt_l1 hV hindep hident hVm
  exact ⟨ν, hν.continuous_comp ((continuous_add_const A).comp T.continuous)⟩

/-- **The assembled stochastic expansion under a reconstruction**: with the joint data given by
`T (S_N) + A`, the assembled normalised remainders converge in distribution to the assembled
coefficients at the reconstructed Gaussian limit, retaining the decomposition and residual
hypotheses of the assembled theorem. -/
theorem assembled_expansion_of_reconstruction (ν : (I : Fin M) → Measure (K I))
    [∀ I, IsFiniteMeasure (ν I)] (h k : (I : Fin M) → Fin (n I + 1) → ℕ) (β : ℝ) (b : Fin M → ℝ)
    (hk : ∀ I i, 0 < k I i) (hβ : 0 < β) (hb : ∀ I, 0 < b I) {μ₀ : ℝ}
    (hμ : ∃ m : ℕ, μ₀ = (m : ℝ) / commonQ k) {j : ℕ} (hj : j ≤ commonD n)
    {J : Type*} [Countable J] {V : ℕ → Ω → L1Seq J} (hV : SummableCoordL2 P (V 0))
    (hindep : iIndepFun V P) (hident : ∀ i, IdentDistrib (V i) (V 0) P P)
    (hVm : ∀ i, Measurable (V i)) (T : L1Seq J →L[ℝ] JointData K n) (A : JointData K n)
    (Nseq : ℕ → ℝ) (hN0 : ∀ i, 0 ≤ Nseq i) (hN : Tendsto Nseq atTop atTop) (Zg E : ℕ → Ω → ℝ)
    (hZm : ∀ i, Measurable (Zg i))
    (hdecomp : ∀ i ω, Zg i ω = gInt ν h k β b (T (empiricalSum V P i ω) + A) (Nseq i) + E i ω)
    (hE : TendstoInMeasure P (fun i ω => E i ω / (Nseq i ^ (-μ₀) * Real.log (Nseq i) ^ j)) atTop
      (fun _ => 0)) :
    ∃ Λ : ProbabilityMeasure (L1Seq J),
      TendstoInDistribution (fun i ω =>
        (Zg i ω - absPredSum (commonQ k) (commonD n)
          (gCoeff ν h k β b (T (empiricalSum V P i ω) + A)) μ₀ j (Nseq i)) /
          (Nseq i ^ (-μ₀) * Real.log (Nseq i) ^ j)) atTop
        (fun z => gCoeff ν h k β b (T z + A) μ₀ j) (fun _ => P) (Λ : Measure (L1Seq J)) := by
  obtain ⟨Λ, hΛ⟩ := reconstruct_tendstoInDistribution hV hindep hident hVm T A
  refine ⟨Λ, ?_⟩
  have hXm : ∀ i, Measurable fun ω => T (empiricalSum V P i ω) + A := fun i =>
    ((continuous_add_const A).comp T.continuous).measurable.comp (measurable_empiricalSum hV hVm i)
  exact tendstoInDistribution_assembled ν h k β b hk hβ hb hμ hj _ hXm _ hΛ Nseq hN0 hN Zg E hZm
    hdecomp hE

end Reconstruct

end Grammar
