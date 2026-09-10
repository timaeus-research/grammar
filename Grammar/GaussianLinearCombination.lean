import Grammar.GaussianFieldFernique
import Grammar.GaussianPMoment
import Grammar.GaussianTilted
import Mathlib.Probability.Distributions.Gaussian.CharFun

/-!
# Linear combinations of evaluations of a Gaussian random continuous function

For a Borel-measurable random element `G : Ω → C(K,ℝ)` whose law is Gaussian in Mathlib's sense
(`IsGaussian (P.map G)`: every continuous linear functional has a real Gaussian law), every finite
linear combination of evaluations `∑ θ_i G(x_i)` is a real Gaussian variable
(`map_evalCombination_eq_gaussianReal`); with the centring and covariance certificates
`E G(x) = 0`, `E[G(x)G(y)] = C(x,y)` its law is `N(0, ∑ θ_i θ_j C(x_i,x_j))`
(`map_evalCombination_eq_gaussianReal_of_certificates`).

Gaussian laws on `Fin m → ℝ` are determined by their first and second coordinate moments
(`isGaussian_ext_of_moments`, via the characteristic functional), and the kernel matrix of a
`PSDKernel` is positive semidefinite (`PSDKernel.kernelMatrix_posSemidef`) with the Gram factor
`gramFactor C = [√C | 0]` (`gramFactor_mul_transpose`, the matrix square root of the continuous
functional calculus). Together these replace the finite-dimensional-law certificate of
`GaussianField.ofIsGaussian` by mean/covariance certificates:
`GaussianField.ofIsGaussianCertificates`.

Non-claims: Gaussianity of the Banach law does not fix the mean or the covariance, so both
certificates remain inputs; the Gaussian law on `C(K,ℝ)` is a hypothesis, not constructed from
the kernel.
-/

open MeasureTheory ProbabilityTheory
open scoped MatrixOrder

namespace Grammar

section FiniteDim

variable {m : ℕ}

/-- Every continuous linear functional on `Fin m → ℝ` is a coordinate combination. -/
theorem strongDual_pi_apply (L : StrongDual ℝ (Fin m → ℝ)) (v : Fin m → ℝ) :
    L v = ∑ i, v i * L (Pi.single i 1) := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show Pi.single i (v i) = v i • (Pi.single i (1 : ℝ) : Fin m → ℝ) by
    rw [← Pi.single_smul, smul_eq_mul, mul_one], map_smul, smul_eq_mul]

theorem memLp_two_proj (μ : Measure (Fin m → ℝ)) [IsGaussian μ] (i : Fin m) :
    MemLp (fun v => v i) 2 μ :=
  IsGaussian.memLp_dual μ (ContinuousLinearMap.proj i) 2 (by norm_num)

theorem integrable_proj (μ : Measure (Fin m → ℝ)) [IsGaussian μ] (i : Fin m) :
    Integrable (fun v => v i) μ :=
  (memLp_two_proj μ i).integrable (by norm_num)

theorem integrable_proj_mul (μ : Measure (Fin m → ℝ)) [IsGaussian μ] (i j : Fin m) :
    Integrable (fun v => v i * v j) μ :=
  (memLp_two_proj μ i).integrable_mul (memLp_two_proj μ j)

theorem integral_strongDual_eq_sum (μ : Measure (Fin m → ℝ)) [IsGaussian μ]
    (L : StrongDual ℝ (Fin m → ℝ)) :
    ∫ v, L v ∂μ = ∑ i, L (Pi.single i 1) * ∫ v, v i ∂μ := by
  rw [integral_congr_ae (Filter.Eventually.of_forall fun v => strongDual_pi_apply L v),
    integral_finsetSum _ fun i _ => (integrable_proj μ i).mul_const _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_mul_const, mul_comm]

theorem integral_strongDual_sq_eq_sum (μ : Measure (Fin m → ℝ)) [IsGaussian μ]
    (L : StrongDual ℝ (Fin m → ℝ)) :
    ∫ v, (L v) ^ 2 ∂μ =
      ∑ i, ∑ j, L (Pi.single i 1) * L (Pi.single j 1) * ∫ v, v i * v j ∂μ := by
  have h : ∀ v, (L v) ^ 2 =
      ∑ i, ∑ j, L (Pi.single i 1) * L (Pi.single j 1) * (v i * v j) := by
    intro v
    rw [strongDual_pi_apply L v, sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall h),
    integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (integrable_proj_mul μ i j).const_mul _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => (integrable_proj_mul μ i j).const_mul _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul]

/-- **Gaussian laws on `Fin m → ℝ` are determined by their first and second coordinate
moments** (Cramér–Wold through the characteristic functional). -/
theorem isGaussian_ext_of_moments (μ ν : Measure (Fin m → ℝ)) [IsGaussian μ] [IsGaussian ν]
    (h1 : ∀ i, ∫ v, v i ∂μ = ∫ v, v i ∂ν)
    (h2 : ∀ i j, ∫ v, v i * v j ∂μ = ∫ v, v i * v j ∂ν) : μ = ν := by
  refine Measure.ext_of_charFunDual (funext fun L => ?_)
  rw [IsGaussian.charFunDual_eq, IsGaussian.charFunDual_eq]
  have hm : ∫ v, L v ∂μ = ∫ v, L v ∂ν := by
    rw [integral_strongDual_eq_sum, integral_strongDual_eq_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [h1]
  have hv : Var[L; μ] = Var[L; ν] := by
    rw [variance_eq_sub (IsGaussian.memLp_dual μ L 2 (by norm_num)),
      variance_eq_sub (IsGaussian.memLp_dual ν L 2 (by norm_num))]
    simp only [Pi.pow_apply]
    rw [integral_strongDual_sq_eq_sum, integral_strongDual_sq_eq_sum, hm]
    congr 1
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [h2]
  have hm' : ∫ v, (L v : ℂ) ∂μ = ∫ v, (L v : ℂ) ∂ν := by
    rw [integral_complex_ofReal, integral_complex_ofReal, hm]
  rw [hm', hv]

/-- The matrix `z ↦ A z` as a continuous linear map. -/
noncomputable def mulVecCLM {n : ℕ} (A : Matrix (Fin m) (Fin (n + 1)) ℝ) :
    (Fin (n + 1) → ℝ) →L[ℝ] (Fin m → ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.mulVecLin A)

theorem gaussianVector_eq_map_mulVecCLM {n : ℕ} (A : Matrix (Fin m) (Fin (n + 1)) ℝ) :
    gaussianVector A = (stdGaussianPi (n + 1)).map (mulVecCLM A) := rfl

instance isGaussian_gaussianVector {n : ℕ} (A : Matrix (Fin m) (Fin (n + 1)) ℝ) :
    IsGaussian (gaussianVector A) := by
  rw [gaussianVector_eq_map_mulVecCLM]
  infer_instance

/-- First coordinate moments of `gaussianVector A` vanish. -/
theorem integral_proj_gaussianVector {n : ℕ} (A : Matrix (Fin m) (Fin (n + 1)) ℝ) (i : Fin m) :
    ∫ v, v i ∂gaussianVector A = 0 := by
  rw [integral_gaussianVector A _ (measurable_pi_apply i)]
  exact integral_coordFunctional A i

/-- Second coordinate moments of `gaussianVector A` are the entries of `AAᵀ`. -/
theorem integral_proj_mul_gaussianVector {n : ℕ} (A : Matrix (Fin m) (Fin (n + 1)) ℝ)
    (i j : Fin m) :
    ∫ v, v i * v j ∂gaussianVector A = (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i j := by
  simpa using integral_mul_mul_exp_gaussianVector A 0 i j j

/-- The matrix square root of the continuous functional calculus. -/
noncomputable def matrixSqrt (C : Matrix (Fin m) (Fin m) ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  CFC.sqrt C

/-- The Gram factor `[√C | 0]` of a positive semidefinite matrix, padded by a zero column. -/
noncomputable def gramFactor (C : Matrix (Fin m) (Fin m) ℝ) : Matrix (Fin m) (Fin (m + 1)) ℝ :=
  Matrix.of fun i (j : Fin (m + 1)) =>
    Fin.snoc (α := fun _ => ℝ) (fun j' => matrixSqrt C i j') (0 : ℝ) j

theorem gramFactor_mul_transpose (C : Matrix (Fin m) (Fin m) ℝ) (hC : C.PosSemidef) :
    gramFactor C * (gramFactor C).transpose = C := by
  have hS : matrixSqrt C * matrixSqrt C = C := CFC.sqrt_mul_sqrt_self C (ha := hC.nonneg)
  have hT : (matrixSqrt C).transpose = matrixSqrt C := by
    have := (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg C)).star_eq
    rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  calc gramFactor C * (gramFactor C).transpose = matrixSqrt C * (matrixSqrt C).transpose := by
        ext i k
        simp only [Matrix.mul_apply, Matrix.transpose_apply, gramFactor, Matrix.of_apply]
        rw [Fin.sum_univ_castSucc]
        simp [Fin.snoc_castSucc, Fin.snoc_last]
    _ = C := by rw [hT, hS]

end FiniteDim

section Kernel

variable {K : Type*} [TopologicalSpace K]

/-- The kernel matrix of a `PSDKernel` is positive semidefinite. -/
theorem PSDKernel.kernelMatrix_posSemidef (𝒞 : PSDKernel K) {m : ℕ} (x : Fin m → K) :
    (𝒞.kernelMatrix x).PosSemidef := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.2 ⟨?_, fun v => ?_⟩
  · ext i j
    simp [PSDKernel.kernelMatrix, Matrix.conjTranspose_apply, 𝒞.symm]
  · have e : star v ⬝ᵥ (𝒞.kernelMatrix x).mulVec v = ∑ i, ∑ j, 𝒞.C (x i) (x j) * v i * v j := by
      simp only [star_trivial, dotProduct, Matrix.mulVec, PSDKernel.kernelMatrix, Matrix.of_apply,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [e]
    exact 𝒞.psd m x v

end Kernel

section Banach

variable {K : Type*} [MetricSpace K] [CompactSpace K]

/-- The Borel σ-algebra of the sup-norm topology on `C(K,ℝ)`. -/
local instance instMeasurableSpaceContinuousMap' : MeasurableSpace C(K, ℝ) := borel _

local instance instBorelSpaceContinuousMap' : BorelSpace C(K, ℝ) := ⟨rfl⟩

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {m : ℕ}

/-- The evaluation combination `f ↦ ∑ θ_i f(x_i)` as a continuous linear functional. -/
noncomputable def evalCombination (θ : Fin m → ℝ) (x : Fin m → K) : StrongDual ℝ C(K, ℝ) :=
  ∑ i, θ i • ContinuousMap.evalCLM ℝ (x i)

omit [CompactSpace K] in
theorem evalCombination_apply (θ : Fin m → ℝ) (x : Fin m → K) (f : C(K, ℝ)) :
    evalCombination θ x f = ∑ i, θ i * f (x i) := by
  simp [evalCombination]

/-- The evaluation vector `f ↦ (f(x_i))_i` as a continuous linear map. -/
noncomputable def evalVecCLM (x : Fin m → K) : C(K, ℝ) →L[ℝ] (Fin m → ℝ) :=
  ContinuousLinearMap.pi fun i => ContinuousMap.evalCLM ℝ (x i)

omit [CompactSpace K] in
theorem evalVecCLM_apply (x : Fin m → K) (f : C(K, ℝ)) : evalVecCLM x f = fun i => f (x i) := by
  ext i
  simp [evalVecCLM]

omit [CompactSpace K] in
/-- **Linear combinations of evaluations of a Gaussian random continuous function are
Gaussian.** -/
theorem map_evalCombination_eq_gaussianReal {G : Ω → C(K, ℝ)} (hG : Measurable G)
    [IsGaussian (P.map G)] (θ : Fin m → ℝ) (x : Fin m → K) :
    P.map (fun ω => ∑ i, θ i * G ω (x i)) =
      gaussianReal (∫ ω, ∑ i, θ i * G ω (x i) ∂P)
        (Var[fun ω => ∑ i, θ i * G ω (x i); P]).toNNReal := by
  have hfun : (fun ω => ∑ i, θ i * G ω (x i)) = evalCombination θ x ∘ G := by
    funext ω
    simp [evalCombination_apply]
  rw [hfun, ← Measure.map_map (evalCombination θ x).continuous.measurable hG,
    IsGaussian.map_eq_gaussianReal,
    integral_map hG.aemeasurable (evalCombination θ x).continuous.measurable.aestronglyMeasurable,
    variance_map (evalCombination θ x).continuous.measurable.aemeasurable hG.aemeasurable]
  rfl

omit [CompactSpace K] in
/-- A random element with a Gaussian law lives on a probability space. -/
theorem isProbabilityMeasure_of_isGaussian_map {G : Ω → C(K, ℝ)} (hG : Measurable G)
    [IsGaussian (P.map G)] : IsProbabilityMeasure P := by
  refine ⟨?_⟩
  have h := measure_univ (μ := P.map G)
  rwa [Measure.map_apply hG MeasurableSet.univ, Set.preimage_univ] at h

/-- Evaluations of a Gaussian random continuous function are in `L²`. -/
theorem memLp_two_eval_of_isGaussian {G : Ω → C(K, ℝ)} (hG : Measurable G)
    [IsGaussian (P.map G)] (y : K) : MemLp (fun ω => G ω y) 2 P :=
  (memLp_map_measure_iff (ContinuousMap.evalCLM ℝ y).continuous.measurable.aestronglyMeasurable
    hG.aemeasurable).1 (IsGaussian.memLp_dual (P.map G)
      (ContinuousMap.evalCLM ℝ y : StrongDual ℝ C(K, ℝ)) 2 (by norm_num))

theorem integrable_eval_of_isGaussian {G : Ω → C(K, ℝ)} (hG : Measurable G)
    [IsGaussian (P.map G)] (y : K) : Integrable (fun ω => G ω y) P :=
  haveI : IsProbabilityMeasure P := isProbabilityMeasure_of_isGaussian_map hG
  (memLp_two_eval_of_isGaussian hG y).integrable (by norm_num)

theorem integrable_eval_mul_eval_of_isGaussian {G : Ω → C(K, ℝ)} (hG : Measurable G)
    [IsGaussian (P.map G)] (y z : K) : Integrable (fun ω => G ω y * G ω z) P :=
  (memLp_two_eval_of_isGaussian hG y).integrable_mul (memLp_two_eval_of_isGaussian hG z)

/-- **With centring and covariance certificates, `∑ θ_i G(x_i) ~ N(0, ∑ θ_i θ_j C(x_i,x_j))`.** -/
theorem map_evalCombination_eq_gaussianReal_of_certificates (𝒞 : PSDKernel K) {G : Ω → C(K, ℝ)}
    (hG : Measurable G) [IsGaussian (P.map G)] (hmean : ∀ y, ∫ ω, G ω y ∂P = 0)
    (hcov : ∀ y z, ∫ ω, G ω y * G ω z ∂P = 𝒞.C y z) (θ : Fin m → ℝ) (x : Fin m → K) :
    P.map (fun ω => ∑ i, θ i * G ω (x i)) =
      gaussianReal 0 (∑ i, ∑ j, θ i * θ j * 𝒞.C (x i) (x j)).toNNReal := by
  rw [map_evalCombination_eq_gaussianReal hG θ x]
  have hm : ∫ ω, ∑ i, θ i * G ω (x i) ∂P = 0 := by
    rw [integral_finsetSum _ fun i _ => (integrable_eval_of_isGaussian hG (x i)).const_mul _]
    exact Finset.sum_eq_zero fun i _ => by rw [integral_const_mul, hmean, mul_zero]
  have hmeas : Measurable fun ω => ∑ i, θ i * G ω (x i) :=
    Finset.measurable_sum _ fun i _ => measurable_const.mul (measurable_eval_comp hG (x i))
  have hsq : ∀ ω, (∑ i, θ i * G ω (x i)) ^ 2 =
      ∑ i, ∑ j, θ i * θ j * (G ω (x i) * G ω (x j)) := by
    intro ω
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hv : Var[fun ω => ∑ i, θ i * G ω (x i); P] = ∑ i, ∑ j, θ i * θ j * 𝒞.C (x i) (x j) := by
    rw [variance_eq_integral hmeas.aemeasurable, hm]
    simp only [sub_zero]
    rw [integral_congr_ae (Filter.Eventually.of_forall hsq),
      integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
        (integrable_eval_mul_eval_of_isGaussian hG (x i) (x j)).const_mul _]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ =>
      (integrable_eval_mul_eval_of_isGaussian hG (x i) (x j)).const_mul _]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul, hcov]
  rw [hm, hv]

/-- **The finite-dimensional-law certificate from mean/covariance certificates**: the evaluation
vector of a Gaussian random continuous function with centring and kernel covariance has the law
`gaussianVector (gramFactor (kernelMatrix x))`. -/
theorem map_evalVec_eq_gaussianVector (𝒞 : PSDKernel K) {G : Ω → C(K, ℝ)} (hG : Measurable G)
    [IsGaussian (P.map G)] (hmean : ∀ y, ∫ ω, G ω y ∂P = 0)
    (hcov : ∀ y z, ∫ ω, G ω y * G ω z ∂P = 𝒞.C y z) (x : Fin m → K) :
    P.map (fun ω => fun i => G ω (x i)) = gaussianVector (gramFactor (𝒞.kernelMatrix x)) := by
  have hfun : (fun ω => fun i => G ω (x i)) = evalVecCLM x ∘ G := by
    funext ω
    rw [Function.comp_apply, evalVecCLM_apply]
  have : IsGaussian (P.map fun ω => fun i => G ω (x i)) := by
    rw [hfun, ← Measure.map_map (evalVecCLM x).continuous.measurable hG]
    infer_instance
  have hmeas : Measurable fun ω => fun i => G ω (x i) :=
    measurable_pi_lambda _ fun i => measurable_eval_comp hG (x i)
  refine isGaussian_ext_of_moments _ _ (fun i => ?_) (fun i j => ?_)
  · rw [integral_map hmeas.aemeasurable (measurable_pi_apply i).aestronglyMeasurable,
      integral_proj_gaussianVector]
    exact hmean (x i)
  · have hmul : Measurable fun v : Fin m → ℝ => v i * v j :=
      (measurable_pi_apply i).mul (measurable_pi_apply j)
    rw [integral_map hmeas.aemeasurable hmul.aestronglyMeasurable,
      integral_proj_mul_gaussianVector,
      gramFactor_mul_transpose _ (𝒞.kernelMatrix_posSemidef x)]
    simp only [PSDKernel.kernelMatrix, Matrix.of_apply]
    exact hcov (x i) (x j)

/-- **The Gaussian Banach-law adapter with mean/covariance certificates**: a Borel-measurable
`C(K,ℝ)`-valued random element with a Gaussian law, centred evaluations and kernel covariance is
a `GaussianField`; the finite-dimensional laws are identified through their moments and the
second sup-norm moment through Fernique. -/
noncomputable def GaussianField.ofIsGaussianCertificates (𝒞 : PSDKernel K) (P : Measure Ω)
    (G : Ω → C(K, ℝ)) (hG : Measurable G) [IsGaussian (P.map G)]
    (hmean : ∀ y, ∫ ω, G ω y ∂P = 0) (hcov : ∀ y z, ∫ ω, G ω y * G ω z ∂P = 𝒞.C y z) :
    GaussianField 𝒞 P :=
  GaussianField.ofIsGaussian 𝒞 P G hG fun m x =>
    ⟨m, gramFactor (𝒞.kernelMatrix x), gramFactor_mul_transpose _ (𝒞.kernelMatrix_posSemidef x),
      map_evalVec_eq_gaussianVector 𝒞 hG hmean hcov x⟩

@[simp] theorem GaussianField.ofIsGaussianCertificates_G (𝒞 : PSDKernel K) (P : Measure Ω)
    (G : Ω → C(K, ℝ)) (hG : Measurable G) [IsGaussian (P.map G)] (hmean) (hcov) :
    (GaussianField.ofIsGaussianCertificates 𝒞 P G hG hmean hcov).G = G := rfl

end Banach

end Grammar
