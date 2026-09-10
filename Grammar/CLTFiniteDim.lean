/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Probability.Moments.Covariance

/-!
# The i.i.d. central limit theorem in finite dimension (Cramér–Wold)

For i.i.d. square-integrable random vectors `X_i` in a finite-dimensional real inner product space,
the normalised centred sums `S_n = n^{−1/2} ∑_{k<n} (X_k − E X_0)` converge in distribution to any
probability measure `ν` whose characteristic function is `t ↦ exp(−Var⟪X_0, t⟫/2)`
(`tendstoInDistribution_normalisedSum`): Lévy's continuity theorem reduces this to the scalar CLT
for the projections `⟪X_i, t⟫`.  On `ℝ^κ` such a `ν` exists: the multivariate Gaussian with the
covariance matrix of `X_0` (`gaussianTarget`, `charFun_gaussianTarget`), whose quadratic form is
`Var⟪X_0, x⟫` (`variance_inner_eq_quadForm`) and which is positive semidefinite
(`covMat_posSemidef`).

Non-claim: no Banach-space CLT; the `ℓ¹` case is assembled from this theorem and the truncation
estimates of the following units.
-/

open MeasureTheory Filter Topology ProbabilityTheory Complex Matrix
open scoped ENNReal NNReal InnerProductSpace

namespace Grammar

section CramerWold

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The normalised centred sum `n^{−1/2} ∑_{k<n} (X_k − E X_0)`. -/
noncomputable def normalisedSum (X : ℕ → Ω → E) (P : Measure Ω) (n : ℕ) (ω : Ω) : E :=
  (Real.sqrt n)⁻¹ • ∑ k ∈ Finset.range n, (X k ω - ∫ ω, X 0 ω ∂P)

theorem inner_normalisedSum (X : ℕ → Ω → E) (hX : Integrable (X 0) P) (n : ℕ) (ω : Ω) (t : E) :
    ⟪normalisedSum X P n ω, t⟫_ℝ =
      (Real.sqrt n)⁻¹ * (∑ k ∈ Finset.range n, ⟪X k ω, t⟫_ℝ - n * ∫ ω, ⟪X 0 ω, t⟫_ℝ ∂P) := by
  unfold normalisedSum
  rw [real_inner_smul_left, sum_inner]
  simp_rw [inner_sub_left]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  congr 3
  have h := (innerSL ℝ t).integral_comp_comm hX
  simp only [innerSL_apply_apply] at h
  rw [real_inner_comm, ← h]
  simp_rw [real_inner_comm t]

/-- The scalar projection of the normalised sum. -/
noncomputable def scalarSum (X : ℕ → Ω → E) (P : Measure Ω) (t : E) (n : ℕ) (ω : Ω) : ℝ :=
  (Real.sqrt n)⁻¹ * (∑ k ∈ Finset.range n, ⟪X k ω, t⟫_ℝ - n * ∫ ω, ⟪X 0 ω, t⟫_ℝ ∂P)

theorem inner_normalisedSum_eq_scalarSum (X : ℕ → Ω → E) (hX : Integrable (X 0) P) (n : ℕ)
    (ω : Ω) (t : E) : ⟪normalisedSum X P n ω, t⟫_ℝ = scalarSum X P t n ω :=
  inner_normalisedSum X hX n ω t

variable [MeasurableSpace E] [BorelSpace E]

theorem aemeasurable_normalisedSum {X : ℕ → Ω → E} (hX : ∀ i, AEMeasurable (X i) P) (n : ℕ) :
    AEMeasurable (normalisedSum X P n) P := by
  unfold normalisedSum
  exact (Finset.aemeasurable_fun_sum _ fun k _ => (hX k).sub aemeasurable_const).const_smul _

omit [FiniteDimensional ℝ E] in
theorem aemeasurable_scalarSum {X : ℕ → Ω → E} (hX : ∀ i, AEMeasurable (X i) P) (t : E) (n : ℕ) :
    AEMeasurable (scalarSum X P t n) P := by
  unfold scalarSum
  have : ∀ i, AEMeasurable (fun ω => ⟪X i ω, t⟫_ℝ) P := fun i =>
    (continuous_id.inner continuous_const).measurable.comp_aemeasurable (hX i)
  exact ((Finset.aemeasurable_fun_sum _ fun k _ => this k).sub aemeasurable_const).const_mul _

/-- The characteristic function of the law of `S_n` at `t` is that of the scalar projection at
`1`. -/
theorem charFun_map_normalisedSum {X : ℕ → Ω → E} (hX : ∀ i, AEMeasurable (X i) P)
    (hint : Integrable (X 0) P) (t : E) (n : ℕ) :
    charFun (P.map (normalisedSum X P n)) t = charFun (P.map (scalarSum X P t n)) 1 := by
  rw [charFun_apply, charFun_apply, integral_map (aemeasurable_normalisedSum hX n) (by fun_prop),
    integral_map (aemeasurable_scalarSum hX t n) (by fun_prop)]
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  simp only [inner_normalisedSum_eq_scalarSum X hint n ω t, RCLike.inner_apply, conj_trivial,
    one_mul]

theorem charFun_gaussianReal_one_toNNReal (v : ℝ) (hv : 0 ≤ v) :
    charFun (gaussianReal 0 v.toNNReal) 1 = exp (-(v : ℂ) / 2) := by
  rw [charFun_gaussianReal, Real.coe_toNNReal _ hv]
  push_cast
  ring_nf

variable [IsProbabilityMeasure P]

omit [FiniteDimensional ℝ E] in
/-- The scalar CLT for the projections `⟪X_i, t⟫`. -/
theorem tendstoInDistribution_scalarSum {X : ℕ → Ω → E} (hX2 : MemLp (X 0) 2 P)
    (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P) (t : E) :
    TendstoInDistribution (scalarSum X P t) atTop id (fun _ => P)
      (gaussianReal 0 (Var[fun ω => ⟪X 0 ω, t⟫_ℝ; P]).toNNReal) := by
  have hcont : Measurable fun x : E => ⟪x, t⟫_ℝ := (continuous_id.inner continuous_const).measurable
  have hY2 : MemLp (fun ω => ⟪X 0 ω, t⟫_ℝ) 2 P := hX2.inner_const t
  have hYind : iIndepFun (fun i ω => ⟪X i ω, t⟫_ℝ) P :=
    hindep.comp (fun _ x => ⟪x, t⟫_ℝ) fun _ => hcont
  have hYid : ∀ i, IdentDistrib (fun ω => ⟪X i ω, t⟫_ℝ) (fun ω => ⟪X 0 ω, t⟫_ℝ) P P :=
    fun i => (hident i).comp hcont
  exact tendstoInDistribution_inv_sqrt_mul_sum_sub HasLaw.id hY2 hYind hYid

omit [FiniteDimensional ℝ E] in
/-- The scalar CLT in characteristic-function form. -/
theorem tendsto_charFun_scalarSum {X : ℕ → Ω → E} (hX2 : MemLp (X 0) 2 P)
    (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P) (t : E) :
    Tendsto (fun n => charFun (P.map (scalarSum X P t n)) 1) atTop
      (𝓝 (exp (-(Var[fun ω => ⟪X 0 ω, t⟫_ℝ; P] : ℂ) / 2))) := by
  have h1 := (Iff.mp ProbabilityMeasure.tendsto_iff_tendsto_charFun
    (tendstoInDistribution_scalarSum hX2 hindep hident t).tendsto) 1
  simp only [ProbabilityMeasure.coe_mk, Measure.map_id] at h1
  rwa [charFun_gaussianReal_one_toNNReal _ (variance_nonneg _ _)] at h1

/-- **The finite-dimensional i.i.d. CLT (Cramér–Wold form)**: the normalised centred sums converge
in distribution to any probability law `ν` with characteristic function `exp(−Var⟪X_0,t⟫/2)`. -/
theorem tendstoInDistribution_normalisedSum {X : ℕ → Ω → E} (hX2 : MemLp (X 0) 2 P)
    (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (ν : Measure E) [IsProbabilityMeasure ν]
    (hν : ∀ t, charFun ν t = exp (-(Var[fun ω => ⟪X 0 ω, t⟫_ℝ; P] : ℂ) / 2)) :
    TendstoInDistribution (normalisedSum X P) atTop id (fun _ => P) ν := by
  have hmeas : ∀ i, AEMeasurable (X i) P := fun i => (hident i).aemeasurable_fst
  have hint : Integrable (X 0) P := hX2.integrable one_le_two
  refine ⟨aemeasurable_normalisedSum hmeas, aemeasurable_id, ?_⟩
  refine Iff.mpr ProbabilityMeasure.tendsto_iff_tendsto_charFun fun t => ?_
  simp only [ProbabilityMeasure.coe_mk, Measure.map_id, hν t]
  simp_rw [charFun_map_normalisedSum hmeas hint t]
  exact tendsto_charFun_scalarSum hX2 hindep hident t

end CramerWold

/-! ### The Gaussian target on `ℝ^κ` -/

section Target

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ : Type*} [Fintype κ]

/-- The covariance matrix of a random vector. -/
noncomputable def covMat (X : Ω → EuclideanSpace ℝ κ) (P : Measure Ω) : Matrix κ κ ℝ :=
  Matrix.of fun i j => cov[fun ω => X ω i, fun ω => X ω j; P]

omit [IsProbabilityMeasure P] in
theorem memLp_coord_of_memLp {X : Ω → EuclideanSpace ℝ κ} (hX : MemLp X 2 P) (i : κ) :
    MemLp (fun ω => X ω i) 2 P := by
  exact (EuclideanSpace.proj (𝕜 := ℝ) i).comp_memLp' hX

theorem inner_euclid (x y : EuclideanSpace ℝ κ) : ⟪x, y⟫_ℝ = ∑ i, x i * y i := by
  simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]

/-- The quadratic form of the covariance matrix is the variance of the projection. -/
theorem variance_inner_eq_quadForm {X : Ω → EuclideanSpace ℝ κ} (hX : MemLp X 2 P)
    (x : EuclideanSpace ℝ κ) :
    Var[fun ω => ⟪X ω, x⟫_ℝ; P] = x ⬝ᵥ covMat X P *ᵥ x := by
  have hc : ∀ i, MemLp (fun ω => X ω i * x i) 2 P := fun i =>
    (memLp_coord_of_memLp hX i).mul_const _
  simp_rw [inner_euclid]
  rw [variance_fun_sum' (s := Finset.univ) fun i _ => hc i]
  simp only [dotProduct, Matrix.mulVec, covMat, Matrix.of_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have e1 : (fun ω => X ω i * x i) = fun ω => x i * X ω i := by funext ω; ring
  have e2 : (fun ω => X ω j * x j) = fun ω => x j * X ω j := by funext ω; ring
  rw [e1, e2, covariance_const_mul_left, covariance_const_mul_right]
  ring

theorem covMat_posSemidef {X : Ω → EuclideanSpace ℝ κ} (hX : MemLp X 2 P) :
    (covMat X P).PosSemidef := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.2
    ⟨Matrix.IsHermitian.ext fun i j => ?_, fun x => ?_⟩
  · simp [covMat, covariance_comm]
  · have := variance_nonneg (fun ω => ⟪X ω, (WithLp.toLp 2 x : EuclideanSpace ℝ κ)⟫_ℝ) P
    rw [variance_inner_eq_quadForm hX] at this
    simpa using this

variable [DecidableEq κ]

/-- The Gaussian target law on `ℝ^κ`: centred, with the covariance matrix of `X`. -/
noncomputable def gaussianTarget (X : Ω → EuclideanSpace ℝ κ) (P : Measure Ω) :
    Measure (EuclideanSpace ℝ κ) :=
  multivariateGaussian 0 (covMat X P)

instance (X : Ω → EuclideanSpace ℝ κ) : IsProbabilityMeasure (gaussianTarget X P) := by
  unfold gaussianTarget; infer_instance

/-- The characteristic function of the Gaussian target is `exp(−Var⟪X,x⟫/2)`. -/
theorem charFun_gaussianTarget {X : Ω → EuclideanSpace ℝ κ} (hX : MemLp X 2 P)
    (x : EuclideanSpace ℝ κ) :
    charFun (gaussianTarget X P) x = exp (-(Var[fun ω => ⟪X ω, x⟫_ℝ; P] : ℂ) / 2) := by
  rw [gaussianTarget, charFun_multivariateGaussian (covMat_posSemidef hX), inner_zero_right,
    variance_inner_eq_quadForm hX]
  simp [neg_div]

/-- **The i.i.d. CLT in `ℝ^κ`** with the explicit Gaussian target. -/
theorem tendstoInDistribution_normalisedSum_gaussian {X : ℕ → Ω → EuclideanSpace ℝ κ}
    (hX2 : MemLp (X 0) 2 P) (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P) :
    TendstoInDistribution (normalisedSum X P) atTop id (fun _ => P) (gaussianTarget (X 0) P) :=
  tendstoInDistribution_normalisedSum hX2 hindep hident _ (charFun_gaussianTarget hX2)

end Target

end Grammar
