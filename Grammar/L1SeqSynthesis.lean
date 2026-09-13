/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.L1SeqGaussianLaw
import Grammar.GaussianLinearCombination
import Grammar.CompactBaseGaussian

/-!
# The compact Gaussian field synthesised from the `ℓ¹` limit law (companion note, Rank 5, part 2)

Given basis functions `φ_r ∈ C(K,ℝ)` on a compact base with a uniform bound `‖φ_r‖ ≤ M`, the
synthesis map `T(a) = ∑_r a_r φ_r` is a bounded linear map `ℓ¹ → C(K,ℝ)` with `‖T a‖ ≤ M‖a‖`
(`synthesisCLM`, `norm_synthesisCLM_le`, `synthesisCLM_eval`). For a law `ν` on `ℓ¹` with a
finite second moment the covariance `C(y,z) = ∫ T(a)(y) T(a)(z) dν` is a continuous positive
semidefinite kernel (`synthesisKernel`), and when `ν` is a centred Gaussian measure (as the `ℓ¹`
CLT limit is, `clt_l1_isGaussian`) the random continuous function `T` under `ν` is a
`GaussianField` with that kernel (`GaussianField.ofL1TaylorLimit`), through the Banach-law
adapter `GaussianField.ofIsGaussianCertificates`. The compact-base identities then apply to it
(`integral_compactH_ofL1TaylorLimit`), and the field exists for the CLT limit law itself
(`exists_gaussianField_of_clt`).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Grammar

variable {ι : Type*} [Countable ι] {K : Type*} [MetricSpace K] [CompactSpace K]

/-- The Borel σ-algebra of the sup-norm topology on `C(K,ℝ)`. -/
local instance instMeasurableSpaceContinuousMapSyn : MeasurableSpace C(K, ℝ) := borel _

local instance instBorelSpaceContinuousMapSyn : BorelSpace C(K, ℝ) := ⟨rfl⟩

omit [MetricSpace K] [CompactSpace K] in
/-- A Gaussian measure on `ℓ¹` has a finite second moment (Fernique). -/
theorem integrable_norm_sq_of_isGaussian (ν : Measure (L1Seq ι)) [IsGaussian ν] :
    Integrable (fun a : L1Seq ι => ‖a‖ ^ 2) ν :=
  (memLp_two_iff_integrable_sq (IsGaussian.memLp_id ν 2 (by simp)).norm.aestronglyMeasurable).1
    (IsGaussian.memLp_id ν 2 (by simp)).norm

/-! ### The bounded synthesis map -/

section Synthesis

variable (φ : ι → C(K, ℝ)) {M : ℝ} (hφ : ∀ r, ‖φ r‖ ≤ M)
include hφ

omit [Countable ι] in
theorem summable_norm_synthesis (a : L1Seq ι) : Summable fun r => ‖a r • φ r‖ := by
  refine ((L1Seq.summable_abs a).mul_right M).of_nonneg_of_le (fun r => norm_nonneg _) fun r => ?_
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hφ r) (abs_nonneg _)

omit [Countable ι] in
theorem summable_synthesis (a : L1Seq ι) : Summable fun r => a r • φ r :=
  Summable.of_norm (summable_norm_synthesis φ hφ a)

omit [Countable ι] in
theorem norm_tsum_synthesis_le (a : L1Seq ι) : ‖∑' r, a r • φ r‖ ≤ M * ‖a‖ := by
  refine (norm_tsum_le_tsum_norm (summable_norm_synthesis φ hφ a)).trans ?_
  calc ∑' r, ‖a r • φ r‖ ≤ ∑' r, |a r| * M :=
        Summable.tsum_le_tsum (fun r => by
          rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (hφ r) (abs_nonneg _))
          (summable_norm_synthesis φ hφ a) ((L1Seq.summable_abs a).mul_right M)
    _ = M * ‖a‖ := by rw [tsum_mul_right, L1Seq.norm_eq_tsum, mul_comm]

omit [Countable ι] in
/-- The synthesis map `a ↦ ∑_r a_r φ_r` as a linear map. -/
noncomputable def synthesisₗ : L1Seq ι →ₗ[ℝ] C(K, ℝ) where
  toFun a := ∑' r, a r • φ r
  map_add' a b := by
    have h : ∀ r, (a + b) r • φ r = a r • φ r + b r • φ r := fun r => by
      rw [lp.coeFn_add, Pi.add_apply, add_smul]
    simp_rw [h]
    exact (summable_synthesis φ hφ a).tsum_add (summable_synthesis φ hφ b)
  map_smul' c a := by
    have h : ∀ r, (c • a) r • φ r = c • (a r • φ r) := fun r => by
      rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_smul]
    simp only [RingHom.id_apply]
    simp_rw [h]
    exact (summable_synthesis φ hφ a).tsum_const_smul c

omit [Countable ι] in
/-- ★ **The bounded synthesis map** `T : ℓ¹ → C(K,ℝ)`, `T(a) = ∑_r a_r φ_r`, `‖T a‖ ≤ M‖a‖`. -/
noncomputable def synthesisCLM : L1Seq ι →L[ℝ] C(K, ℝ) :=
  LinearMap.mkContinuous (synthesisₗ φ hφ) M fun a => norm_tsum_synthesis_le φ hφ a

omit [Countable ι] in
@[simp] theorem synthesisCLM_apply (a : L1Seq ι) : synthesisCLM φ hφ a = ∑' r, a r • φ r := rfl

omit [Countable ι] in
theorem norm_synthesisCLM_le (a : L1Seq ι) : ‖synthesisCLM φ hφ a‖ ≤ M * ‖a‖ :=
  norm_tsum_synthesis_le φ hφ a

omit [Countable ι] in
/-- Pointwise, `T(a)(y) = ∑_r a_r φ_r(y)`. -/
theorem synthesisCLM_eval (a : L1Seq ι) (y : K) :
    synthesisCLM φ hφ a y = ∑' r, a r * φ r y := by
  rw [synthesisCLM_apply]
  have h := (ContinuousMap.evalCLM ℝ y).map_tsum (summable_synthesis φ hφ a)
  simpa [ContinuousMap.evalCLM_apply] using h

omit [Countable ι] in
theorem abs_synthesisCLM_eval_le (a : L1Seq ι) (y : K) : |synthesisCLM φ hφ a y| ≤ M * ‖a‖ :=
  ((synthesisCLM φ hφ a).norm_coe_le_norm y).trans (norm_synthesisCLM_le φ hφ a)

omit [Countable ι] in
theorem continuous_synthesisCLM_eval (y : K) : Continuous fun a => synthesisCLM φ hφ a y :=
  (ContinuousMap.evalCLM ℝ y).continuous.comp (synthesisCLM φ hφ).continuous

/-! ### The covariance kernel of the synthesised field -/

section Kernel

variable (ν : Measure (L1Seq ι)) (hν : Integrable (fun a : L1Seq ι => ‖a‖ ^ 2) ν)
include hν

omit [Countable ι] in
theorem integrable_synthesis_mul (y z : K) :
    Integrable (fun a => synthesisCLM φ hφ a y * synthesisCLM φ hφ a z) ν := by
  have hc : Continuous fun a => synthesisCLM φ hφ a y * synthesisCLM φ hφ a z :=
    (continuous_synthesisCLM_eval φ hφ y).mul (continuous_synthesisCLM_eval φ hφ z)
  refine (hν.const_mul (M * M)).mono' hc.aestronglyMeasurable (Eventually.of_forall fun a => ?_)
  have h1 := abs_synthesisCLM_eval_le φ hφ a y
  have h2 := abs_synthesisCLM_eval_le φ hφ a z
  rw [Real.norm_eq_abs, abs_mul]
  calc |synthesisCLM φ hφ a y| * |synthesisCLM φ hφ a z| ≤ (M * ‖a‖) * (M * ‖a‖) :=
        mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1)
    _ = M * M * ‖a‖ ^ 2 := by ring

omit [Countable ι] in
/-- ★ **The covariance kernel of the synthesised field**, `C(y,z) = ∫ T(a)(y) T(a)(z) dν`: a
continuous positive semidefinite kernel on the compact base. -/
noncomputable def synthesisKernel : PSDKernel K where
  C y z := ∫ a, synthesisCLM φ hφ a y * synthesisCLM φ hφ a z ∂ν
  symm y z := by simp_rw [mul_comm]
  psd m x v := by
    have hint : ∀ i j, Integrable
        (fun a => synthesisCLM φ hφ a (x i) * synthesisCLM φ hφ a (x j) * v i * v j) ν :=
      fun i j => ((integrable_synthesis_mul φ hφ ν hν _ _).mul_const _).mul_const _
    have h : ∑ i, ∑ j, (∫ a, synthesisCLM φ hφ a (x i) * synthesisCLM φ hφ a (x j) ∂ν) * v i * v j
        = ∫ a, (∑ i, v i * synthesisCLM φ hφ a (x i)) ^ 2 ∂ν := by
      simp_rw [← integral_mul_const]
      have h1 : ∀ i,
          ∑ j, ∫ a, synthesisCLM φ hφ a (x i) * synthesisCLM φ hφ a (x j) * v i * v j ∂ν =
            ∫ a, ∑ j, synthesisCLM φ hφ a (x i) * synthesisCLM φ hφ a (x j) * v i * v j ∂ν :=
        fun i => (integral_finsetSum _ fun j _ => hint i j).symm
      simp_rw [h1]
      rw [← integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
      refine integral_congr_ae (Eventually.of_forall fun a => ?_)
      beta_reduce
      rw [sq, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [h]
    exact integral_nonneg fun a => sq_nonneg _
  continuous := by
    change Continuous fun p : K × K => ∫ a, synthesisCLM φ hφ a p.1 * synthesisCLM φ hφ a p.2 ∂ν
    refine continuous_of_dominated (bound := fun a => M * M * ‖a‖ ^ 2) (fun p => ?_)
      (fun p => Eventually.of_forall fun a => ?_) (hν.const_mul _)
      (Eventually.of_forall fun a => ?_)
    · exact ((continuous_synthesisCLM_eval φ hφ p.1).mul
        (continuous_synthesisCLM_eval φ hφ p.2)).aestronglyMeasurable
    · have h1 := abs_synthesisCLM_eval_le φ hφ a p.1
      have h2 := abs_synthesisCLM_eval_le φ hφ a p.2
      rw [Real.norm_eq_abs, abs_mul]
      calc |synthesisCLM φ hφ a p.1| * |synthesisCLM φ hφ a p.2| ≤ (M * ‖a‖) * (M * ‖a‖) :=
            mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1)
        _ = M * M * ‖a‖ ^ 2 := by ring
    · exact ((synthesisCLM φ hφ a).continuous.comp continuous_fst).mul
        ((synthesisCLM φ hφ a).continuous.comp continuous_snd)

omit [Countable ι] in
@[simp] theorem synthesisKernel_C (y z : K) :
    (synthesisKernel φ hφ ν hν).C y z = ∫ a, synthesisCLM φ hφ a y * synthesisCLM φ hφ a z ∂ν :=
  rfl

end Kernel

/-! ### The Gaussian field -/

section Field

variable (ν : Measure (L1Seq ι)) [IsGaussian ν]

/-- ★★ **The compact Gaussian field synthesised from a centred Gaussian law on `ℓ¹`**: the random
continuous function `T(a) = ∑ a_r φ_r` under `ν` is a `GaussianField` with covariance kernel
`∫ T(a)(y) T(a)(z) dν`, through the Banach-law adapter. -/
noncomputable def GaussianField.ofL1TaylorLimit
    (hmean : ∀ L : StrongDual ℝ (L1Seq ι), ∫ a, L a ∂ν = 0) :
    GaussianField (synthesisKernel φ hφ ν (integrable_norm_sq_of_isGaussian ν)) ν :=
  GaussianField.ofIsGaussianCertificates _ ν (synthesisCLM φ hφ)
    (synthesisCLM φ hφ).continuous.measurable
    (fun y => hmean ((ContinuousMap.evalCLM ℝ y).comp (synthesisCLM φ hφ)))
    (fun _ _ => rfl)

@[simp] theorem GaussianField.ofL1TaylorLimit_G
    (hmean : ∀ L : StrongDual ℝ (L1Seq ι), ∫ a, L a ∂ν = 0) :
    (GaussianField.ofL1TaylorLimit φ hφ ν hmean).G = synthesisCLM φ hφ := rfl

/-- **Gaussian integration by parts for the synthesised field**: `E H_ρ(T) = β E V_ρ(T)`. -/
theorem integral_compactH_ofL1TaylorLimit [MeasurableSpace K] [BorelSpace K] [Nonempty K]
    {β lam : ℝ} (ρ : Measure K)
    [IsFiniteMeasure ρ] (hβ : 0 < β) (hlam : 0 < lam) (hρ : ρ ≠ 0)
    (hmean : ∀ L : StrongDual ℝ (L1Seq ι), ∫ a, L a ∂ν = 0) :
    ∫ a, compactH β lam ρ (synthesisCLM φ hφ a) ∂ν =
      β * ∫ a, compactV ρ β lam (synthesisKernel φ hφ ν (integrable_norm_sq_of_isGaussian ν))
        (synthesisCLM φ hφ a) ∂ν :=
  (GaussianField.ofL1TaylorLimit φ hφ ν hmean).integral_compactH_eq ρ hβ hlam hρ

end Field

/-! ### The field of the `ℓ¹` CLT limit law -/

section CLT

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {Y : ℕ → Ω → L1Seq ι}

/-- ★★ **The compact Gaussian field of the `ℓ¹` CLT limit**: the limit law `ν` of the centred
normalised empirical sums is a Gaussian measure with a finite second moment, and `T` under `ν`
is a `GaussianField` with kernel `∫ T(a)(y) T(a)(z) dν`. -/
theorem exists_gaussianField_of_clt (hY : SummableCoordL2 P (Y 0))
    (hindep : iIndepFun Y P) (hident : ∀ i, IdentDistrib (Y i) (Y 0) P P)
    (hYm : ∀ i, Measurable (Y i)) :
    ∃ ν : ProbabilityMeasure (L1Seq ι),
      ∃ hν : Integrable (fun a : L1Seq ι => ‖a‖ ^ 2) (ν : Measure (L1Seq ι)),
      IsGaussian (ν : Measure (L1Seq ι)) ∧
      TendstoInDistribution (empiricalSum Y P) atTop id (fun _ => P) (ν : Measure (L1Seq ι)) ∧
      ∃ Γ : GaussianField (synthesisKernel φ hφ ν hν) (ν : Measure (L1Seq ι)),
        Γ.G = synthesisCLM φ hφ := by
  classical
  obtain ⟨ν, hG, hconv, hmarg, -⟩ := clt_l1_isGaussian hY hindep hident hYm
  have := hG
  exact ⟨ν, integrable_norm_sq_of_isGaussian (ν : Measure (L1Seq ι)), hG, hconv,
    GaussianField.ofL1TaylorLimit φ hφ ν (integral_dual_eq_zero_of_marginals hY hmarg), rfl⟩

end CLT

end Synthesis

end Grammar
