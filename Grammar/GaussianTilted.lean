/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.GaussianSteinVector
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Tilted Gaussian moments

For a standard Gaussian `Z`, `E e^{sZ} = e^{s²/2}`, `E[Z e^{sZ}] = s e^{s²/2}` and
`E[Z² e^{sZ}] = (1 + s²) e^{s²/2}` (`integral_exp_mul_std`, `integral_mul_exp_std`,
`integral_sq_mul_exp_std`, by differentiating the moment generating function).  For independent
standard Gaussians `Z = (Z_k)` and a weight vector `w`, with `⟪w,Z⟫ = ∑ w_k Z_k`,

  `E e^{⟪w,Z⟫} = e^{‖w‖²/2}`,  `E[Z_k e^{⟪w,Z⟫}] = w_k e^{‖w‖²/2}`,
  `E[Z_k Z_l e^{⟪w,Z⟫}] = (δ_{kl} + w_k w_l) e^{‖w‖²/2}`

(`integral_exp_dot`, `integral_coord_mul_exp_dot`, `integral_coord_mul_coord_mul_exp_dot`, by the
product formula on `Measure.pi`), hence for the Gaussian vector `G = A Z` with covariance
`b = A Aᵀ` the **tilted identities**

  `E e^{θ G_j} = e^{θ² b_{jj}/2}`,  `E[G_i e^{θ G_j}] = θ b_{ij} e^{θ² b_{jj}/2}`,
  `E[G_i G_{i'} e^{θ G_j}] = (b_{ii'} + θ² b_{ij} b_{i'j}) e^{θ² b_{jj}/2}`

(`integral_exp_gaussianVector`, `integral_mul_exp_gaussianVector`,
`integral_mul_mul_exp_gaussianVector`).  These are the inputs of the `Q = 0, 1, 2` insertion
formulas of the averaging note; no Isserlis theorem is needed.
-/

open MeasureTheory ProbabilityTheory Real Set Finset
open scoped ENNReal NNReal

namespace Grammar

/-! ### Scalar tilted moments -/

section Scalar

theorem integrableExpSet_std (t : ℝ) : t ∈ interior (integrableExpSet id (gaussianReal 0 1)) := by
  have : integrableExpSet id (gaussianReal 0 1) = univ := by
    ext s
    simp only [mem_univ, iff_true, integrableExpSet, Set.mem_ofPred_eq]
    simpa using integrable_exp_mul_gaussianReal (μ := 0) (v := 1) s
  rw [this, interior_univ]; exact mem_univ t

theorem mgf_std (s : ℝ) : mgf id (gaussianReal 0 1) s = Real.exp (s ^ 2 / 2) := by
  rw [mgf_gaussianReal (X := id) (p := gaussianReal 0 1) (μ := 0) (v := 1) (by simp) s]
  simp

theorem integral_exp_mul_std (s : ℝ) :
    ∫ z, Real.exp (s * z) ∂gaussianReal 0 1 = Real.exp (s ^ 2 / 2) := by
  have := mgf_std s
  simpa [mgf] using this

theorem integral_mul_exp_std (s : ℝ) :
    ∫ z, z * Real.exp (s * z) ∂gaussianReal 0 1 = s * Real.exp (s ^ 2 / 2) := by
  have h1 := hasDerivAt_mgf (X := id) (μ := gaussianReal 0 1) (integrableExpSet_std s)
  have h2 : HasDerivAt (fun t : ℝ => Real.exp (t ^ 2 / 2)) (s * Real.exp (s ^ 2 / 2)) s := by
    have := ((hasDerivAt_pow 2 s).div_const 2).exp
    convert this using 1
    ring
  have hfun : mgf id (gaussianReal 0 1) = fun t => Real.exp (t ^ 2 / 2) := funext mgf_std
  rw [hfun] at h1
  have := h1.unique h2
  simpa [id, mul_comm] using this

theorem integral_sq_mul_exp_std (s : ℝ) :
    ∫ z, z ^ 2 * Real.exp (s * z) ∂gaussianReal 0 1 = (1 + s ^ 2) * Real.exp (s ^ 2 / 2) := by
  have h1 := iteratedDeriv_mgf (X := id) (μ := gaussianReal 0 1) (integrableExpSet_std s) 2
  have hfun : mgf id (gaussianReal 0 1) = fun t => Real.exp (t ^ 2 / 2) := funext mgf_std
  rw [hfun] at h1
  -- second derivative of `e^{t²/2}` at `s`
  have hd1 : ∀ t : ℝ,
      HasDerivAt (fun t : ℝ => Real.exp (t ^ 2 / 2)) (t * Real.exp (t ^ 2 / 2)) t := by
    intro t
    have := ((hasDerivAt_pow 2 t).div_const 2).exp
    convert this using 1; ring
  have hderiv : deriv (fun t : ℝ => Real.exp (t ^ 2 / 2)) = fun t => t * Real.exp (t ^ 2 / 2) :=
    funext fun t => (hd1 t).deriv
  have hd2 : HasDerivAt (fun t : ℝ => t * Real.exp (t ^ 2 / 2))
      ((1 + s ^ 2) * Real.exp (s ^ 2 / 2)) s := by
    refine ((hasDerivAt_id' s).mul (hd1 s)).congr_deriv ?_
    ring
  rw [iteratedDeriv_succ, iteratedDeriv_one, hderiv, hd2.deriv] at h1
  simpa [id, mul_comm, mul_left_comm, pow_two] using h1.symm

/-- `z^k e^{wz}` is integrable against the standard Gaussian:
`|z|^k ≤ k! e^{|z|} ≤ k!(e^z + e^{−z})`. -/
theorem integrable_pow_mul_exp_std (k : ℕ) (w : ℝ) :
    Integrable (fun z : ℝ => z ^ k * Real.exp (w * z)) (gaussianReal 0 1) := by
  have h1 := integrable_exp_mul_gaussianReal (μ := 0) (v := 1) (w + 1)
  have h2 := integrable_exp_mul_gaussianReal (μ := 0) (v := 1) (w - 1)
  refine ((h1.add h2).const_mul (k.factorial : ℝ)).mono' (by fun_prop)
    (Filter.Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]
  have hb : |z| ^ k ≤ k.factorial * Real.exp |z| := by
    have := Real.pow_div_factorial_le_exp _ (abs_nonneg z) k
    rwa [div_le_iff₀ (by positivity), mul_comm] at this
  have he : Real.exp |z| ≤ Real.exp z + Real.exp (-z) := by
    rcases le_total 0 z with h | h
    · rw [abs_of_nonneg h]; linarith [Real.exp_pos (-z)]
    · rw [abs_of_nonpos h]; linarith [Real.exp_pos z]
  have hk : (0 : ℝ) ≤ k.factorial := by positivity
  calc |z| ^ k * Real.exp (w * z) ≤ k.factorial * Real.exp |z| * Real.exp (w * z) :=
        mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
    _ ≤ k.factorial * (Real.exp z + Real.exp (-z)) * Real.exp (w * z) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he hk) (Real.exp_pos _).le
    _ = k.factorial * (Real.exp ((w + 1) * z) + Real.exp ((w - 1) * z)) := by
        rw [mul_assoc, add_mul, ← Real.exp_add, ← Real.exp_add]; ring_nf

end Scalar

/-! ### Product identities for independent standard Gaussians -/

section Product

variable {n : ℕ}

/-- The linear functional `⟪w, z⟫ = ∑ w_k z_k`. -/
def dotW (w z : Fin n → ℝ) : ℝ := ∑ k, w k * z k

theorem exp_dotW (w z : Fin n → ℝ) : Real.exp (dotW w z) = ∏ k, Real.exp (w k * z k) := by
  rw [dotW, Real.exp_sum]

theorem integral_exp_dot (w : Fin n → ℝ) :
    ∫ z, Real.exp (dotW w z) ∂stdGaussianPi n = Real.exp ((∑ k, w k ^ 2) / 2) := by
  unfold stdGaussianPi
  simp_rw [exp_dotW]
  rw [integral_fintype_prod_eq_prod (fun k (z : ℝ) => Real.exp (w k * z))]
  simp_rw [integral_exp_mul_std, ← Real.exp_sum, Finset.sum_div]

/-- `∏_l (if l = k then f l * g l else g l) = f k * ∏_l g l`. -/
theorem prod_ite_eq_mul (f g : Fin n → ℝ) (k : Fin n) :
    ∏ l, (if l = k then f l * g l else g l) = f k * ∏ l, g l := by
  classical
  rw [← Finset.mul_prod_erase Finset.univ (fun l => g l) (Finset.mem_univ k),
    ← Finset.mul_prod_erase Finset.univ
      (fun l => if l = k then f l * g l else g l) (Finset.mem_univ k)]
  simp only [if_true]
  rw [Finset.prod_congr rfl fun l hl => if_neg (Finset.ne_of_mem_erase hl)]
  ring

theorem integral_coord_mul_exp_dot (w : Fin n → ℝ) (k : Fin n) :
    ∫ z, z k * Real.exp (dotW w z) ∂stdGaussianPi n = w k * Real.exp ((∑ l, w l ^ 2) / 2) := by
  classical
  unfold stdGaussianPi
  have hfun : ∀ z : Fin n → ℝ, z k * Real.exp (dotW w z) =
      ∏ l, (if l = k then z l * Real.exp (w l * z l) else Real.exp (w l * z l)) := by
    intro z
    rw [exp_dotW, prod_ite_eq_mul (fun l => z l) (fun l => Real.exp (w l * z l)) k]
  simp_rw [hfun]
  rw [integral_fintype_prod_eq_prod
    (fun l (z : ℝ) => if l = k then z * Real.exp (w l * z) else Real.exp (w l * z))]
  have hint : ∀ l, (∫ z, (if l = k then z * Real.exp (w l * z) else Real.exp (w l * z))
      ∂gaussianReal 0 1) =
      if l = k then w l * Real.exp (w l ^ 2 / 2) else Real.exp (w l ^ 2 / 2) := by
    intro l
    by_cases h : l = k
    · simp [h, integral_mul_exp_std]
    · simp [h, integral_exp_mul_std]
  simp_rw [hint]
  rw [prod_ite_eq_mul (fun l => w l) (fun l => Real.exp (w l ^ 2 / 2)) k, ← Real.exp_sum,
    Finset.sum_div]

/-- `E[Z_k Z_l e^{⟪w,Z⟫}] = (δ_{kl} + w_k w_l) e^{‖w‖²/2}`. -/
theorem integral_coord_mul_coord_mul_exp_dot (w : Fin n → ℝ) (k l : Fin n) :
    ∫ z, z k * z l * Real.exp (dotW w z) ∂stdGaussianPi n =
      ((if k = l then 1 else 0) + w k * w l) * Real.exp ((∑ i, w i ^ 2) / 2) := by
  classical
  unfold stdGaussianPi
  by_cases hkl : k = l
  · subst hkl
    have hfun : ∀ z : Fin n → ℝ, z k * z k * Real.exp (dotW w z) =
        ∏ i, (if i = k then z i ^ 2 * Real.exp (w i * z i) else Real.exp (w i * z i)) := by
      intro z
      rw [exp_dotW, prod_ite_eq_mul (fun i => z i ^ 2) (fun i => Real.exp (w i * z i)) k]
      ring
    simp_rw [hfun]
    rw [integral_fintype_prod_eq_prod
      (fun i (z : ℝ) => if i = k then z ^ 2 * Real.exp (w i * z) else Real.exp (w i * z))]
    have hint : ∀ i, (∫ z, (if i = k then z ^ 2 * Real.exp (w i * z) else Real.exp (w i * z))
        ∂gaussianReal 0 1) =
        if i = k then (1 + w i ^ 2) * Real.exp (w i ^ 2 / 2) else Real.exp (w i ^ 2 / 2) := by
      intro i
      by_cases h : i = k
      · simp [h, integral_sq_mul_exp_std]
      · simp [h, integral_exp_mul_std]
    simp_rw [hint]
    rw [prod_ite_eq_mul (fun i => 1 + w i ^ 2) (fun i => Real.exp (w i ^ 2 / 2)) k, ← Real.exp_sum,
      Finset.sum_div]
    simp [sq]
  · -- two distinct special coordinates: peel `k`, then `l`
    have hfun : ∀ z : Fin n → ℝ, z k * z l * Real.exp (dotW w z) =
        ∏ i, (if i = k then
          z i * (if i = l then z i * Real.exp (w i * z i) else Real.exp (w i * z i)) else
          (if i = l then z i * Real.exp (w i * z i) else Real.exp (w i * z i))) := by
      intro z
      rw [exp_dotW, prod_ite_eq_mul (fun i => z i)
        (fun i => if i = l then z i * Real.exp (w i * z i) else Real.exp (w i * z i)) k,
        prod_ite_eq_mul (fun i => z i) (fun i => Real.exp (w i * z i)) l]
      ring
    simp_rw [hfun]
    rw [integral_fintype_prod_eq_prod (fun i (z : ℝ) => if i = k then
      z * (if i = l then z * Real.exp (w i * z) else Real.exp (w i * z)) else
      (if i = l then z * Real.exp (w i * z) else Real.exp (w i * z)))]
    have hint : ∀ i, (∫ z, (if i = k then
        z * (if i = l then z * Real.exp (w i * z) else Real.exp (w i * z)) else
        (if i = l then z * Real.exp (w i * z) else Real.exp (w i * z))) ∂gaussianReal 0 1) =
        if i = k then w i * (if i = l then w i * Real.exp (w i ^ 2 / 2) else Real.exp (w i ^ 2 / 2))
        else (if i = l then w i * Real.exp (w i ^ 2 / 2) else Real.exp (w i ^ 2 / 2)) := by
      intro i
      by_cases h : i = k
      · simp [h, hkl, integral_mul_exp_std]
      · by_cases h' : i = l
        · simp [h', Ne.symm hkl, integral_mul_exp_std]
        · simp [h, h', integral_exp_mul_std]
    simp_rw [hint]
    rw [prod_ite_eq_mul (fun i => w i)
      (fun i => if i = l then w i * Real.exp (w i ^ 2 / 2) else Real.exp (w i ^ 2 / 2)) k,
      prod_ite_eq_mul (fun i => w i) (fun i => Real.exp (w i ^ 2 / 2)) l, ← Real.exp_sum,
      Finset.sum_div]
    simp only [hkl, if_false, zero_add]
    ring

theorem integrable_exp_dot (w : Fin n → ℝ) :
    Integrable (fun z => Real.exp (dotW w z)) (stdGaussianPi n) := by
  unfold stdGaussianPi
  simp_rw [exp_dotW]
  exact Integrable.fintype_prod (f := fun l (z : ℝ) => Real.exp (w l * z))
    fun l => integrable_exp_mul_gaussianReal _

theorem integrable_coord_mul_exp_dot (w : Fin n → ℝ) (k : Fin n) :
    Integrable (fun z => z k * Real.exp (dotW w z)) (stdGaussianPi n) := by
  classical
  unfold stdGaussianPi
  have hfun : ∀ z : Fin n → ℝ, z k * Real.exp (dotW w z) =
      ∏ l, (if l = k then z l * Real.exp (w l * z l) else Real.exp (w l * z l)) := by
    intro z
    rw [exp_dotW, prod_ite_eq_mul (fun l => z l) (fun l => Real.exp (w l * z l)) k]
  simp_rw [hfun]
  refine Integrable.fintype_prod
    (f := fun l (z : ℝ) => if l = k then z * Real.exp (w l * z) else Real.exp (w l * z)) fun l => ?_
  by_cases h : l = k
  · simp only [h, if_true]; simpa using integrable_pow_mul_exp_std 1 (w k)
  · simp only [h, if_false]; exact integrable_exp_mul_gaussianReal _

theorem integrable_coord_mul_coord_mul_exp_dot (w : Fin n → ℝ) (k l : Fin n) :
    Integrable (fun z => z k * z l * Real.exp (dotW w z)) (stdGaussianPi n) := by
  classical
  unfold stdGaussianPi
  by_cases hkl : k = l
  · subst hkl
    have hfun : ∀ z : Fin n → ℝ, z k * z k * Real.exp (dotW w z) =
        ∏ i, (if i = k then z i ^ 2 * Real.exp (w i * z i) else Real.exp (w i * z i)) := by
      intro z
      rw [exp_dotW, prod_ite_eq_mul (fun i => z i ^ 2) (fun i => Real.exp (w i * z i)) k]
      ring
    simp_rw [hfun]
    refine Integrable.fintype_prod
      (f := fun i (z : ℝ) => if i = k then z ^ 2 * Real.exp (w i * z) else Real.exp (w i * z))
      fun i => ?_
    by_cases h : i = k
    · simp only [h, if_true]; exact integrable_pow_mul_exp_std 2 (w k)
    · simp only [h, if_false]; exact integrable_exp_mul_gaussianReal _
  · have hfun : ∀ z : Fin n → ℝ, z k * z l * Real.exp (dotW w z) =
        ∏ i, (if i = k then
          z i * (if i = l then z i * Real.exp (w i * z i) else Real.exp (w i * z i)) else
          (if i = l then z i * Real.exp (w i * z i) else Real.exp (w i * z i))) := by
      intro z
      rw [exp_dotW, prod_ite_eq_mul (fun i => z i)
        (fun i => if i = l then z i * Real.exp (w i * z i) else Real.exp (w i * z i)) k,
        prod_ite_eq_mul (fun i => z i) (fun i => Real.exp (w i * z i)) l]
      ring
    simp_rw [hfun]
    refine Integrable.fintype_prod (f := fun i (z : ℝ) => if i = k then
      z * (if i = l then z * Real.exp (w i * z) else Real.exp (w i * z)) else
      (if i = l then z * Real.exp (w i * z) else Real.exp (w i * z))) fun i => ?_
    by_cases h : i = k
    · simp only [h, hkl, if_true, if_false]; simpa using integrable_pow_mul_exp_std 1 (w k)
    · by_cases h' : i = l
      · simp only [h', Ne.symm hkl, if_true, if_false]
        simpa using integrable_pow_mul_exp_std 1 (w l)
      · simp only [h, h', if_false]; exact integrable_exp_mul_gaussianReal _

end Product

/-! ### Tilted identities for the Gaussian vector `G = A Z` -/

section Vector

variable {m n : ℕ} (A : Matrix (Fin m) (Fin (n + 1)) ℝ)

/-- `θ G_j = ⟪θ A_{j·}, Z⟫`. -/
theorem mulVec_eq_dotW (θ : ℝ) (j : Fin m) (z : Fin (n + 1) → ℝ) :
    θ * A.mulVec z j = dotW (fun k => θ * A j k) z := by
  simp only [Matrix.mulVec, dotProduct, dotW, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem sum_sq_row (θ : ℝ) (j : Fin m) :
    ∑ k, (θ * A j k) ^ 2 = θ ^ 2 * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) j j := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem measurable_exp_mulVec (θ : ℝ) (j : Fin m) :
    Measurable fun g : Fin m → ℝ => Real.exp (θ * g j) :=
  Measurable.exp (measurable_const.mul (measurable_pi_apply j))

/-- **`E e^{θ G_j} = e^{θ² b_{jj}/2}`.** -/
theorem integral_exp_gaussianVector (θ : ℝ) (j : Fin m) :
    ∫ g, Real.exp (θ * g j) ∂gaussianVector A =
      Real.exp (θ ^ 2 * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) j j / 2) := by
  rw [integral_gaussianVector A (fun g => Real.exp (θ * g j)) (measurable_exp_mulVec θ j)]
  simp_rw [mulVec_eq_dotW A θ j]
  rw [integral_exp_dot, sum_sq_row]

/-- **`E[G_i e^{θ G_j}] = θ b_{ij} e^{θ² b_{jj}/2}`.** -/
theorem integral_mul_exp_gaussianVector (θ : ℝ) (i j : Fin m) :
    ∫ g, g i * Real.exp (θ * g j) ∂gaussianVector A =
      θ * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i j *
        Real.exp (θ ^ 2 * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) j j / 2) := by
  rw [integral_gaussianVector A (fun g => g i * Real.exp (θ * g j))
    ((measurable_pi_apply i).mul (measurable_exp_mulVec θ j))]
  simp_rw [mulVec_eq_dotW A θ j]
  have hexp : ∀ z : Fin (n + 1) → ℝ, A.mulVec z i * Real.exp (dotW (fun k => θ * A j k) z) =
      ∑ k, A i k * (z k * Real.exp (dotW (fun k => θ * A j k) z)) := by
    intro z
    simp only [Matrix.mulVec, dotProduct, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  simp_rw [hexp]
  rw [integral_finsetSum _ fun k _ => ?_]
  · simp_rw [integral_const_mul, integral_coord_mul_exp_dot, sum_sq_row]
    set E := Real.exp (θ ^ 2 * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) j j / 2)
    have hb : (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i j = ∑ k, A i k * A j k := by
      simp only [Matrix.mul_apply, Matrix.transpose_apply]
    rw [hb, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  · exact (integrable_coord_mul_exp_dot _ k).const_mul _

/-- **`E[G_i G_{i'} e^{θ G_j}] = (b_{ii'} + θ² b_{ij} b_{i'j}) e^{θ² b_{jj}/2}`.** -/
theorem integral_mul_mul_exp_gaussianVector (θ : ℝ) (i i' j : Fin m) :
    ∫ g, g i * g i' * Real.exp (θ * g j) ∂gaussianVector A =
      ((A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i i' +
        θ ^ 2 * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i j *
          (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i' j) *
        Real.exp (θ ^ 2 * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) j j / 2) := by
  rw [integral_gaussianVector A (fun g => g i * g i' * Real.exp (θ * g j))
    (((measurable_pi_apply i).mul (measurable_pi_apply i')).mul (measurable_exp_mulVec θ j))]
  simp_rw [mulVec_eq_dotW A θ j]
  set w : Fin (n + 1) → ℝ := fun k => θ * A j k with hw
  have hexp : ∀ z : Fin (n + 1) → ℝ,
      A.mulVec z i * A.mulVec z i' * Real.exp (dotW w z) =
      ∑ k, ∑ k', A i k * A i' k' * (z k * z k' * Real.exp (dotW w z)) := by
    intro z
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k' _ => ?_
    ring
  simp_rw [hexp]
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun k' _ =>
    (integrable_coord_mul_coord_mul_exp_dot w k k').const_mul _]
  have hrow : ∑ k, w k ^ 2 = θ ^ 2 * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) j j := by
    rw [hw]; exact sum_sq_row A θ j
  simp_rw [integral_finsetSum _ fun k' _ =>
    (integrable_coord_mul_coord_mul_exp_dot w _ k').const_mul _, integral_const_mul,
    integral_coord_mul_coord_mul_exp_dot, hrow]
  set E := Real.exp (θ ^ 2 * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) j j / 2)
  have hassoc : ∀ k k', A i k * A i' k' * (((if k = k' then (1 : ℝ) else 0) + w k * w k') * E) =
      A i k * A i' k' * ((if k = k' then (1 : ℝ) else 0) + w k * w k') * E := fun k k' => by ring
  simp_rw [hassoc, ← Finset.sum_mul]
  congr 1
  -- `∑_{k k'} A_{ik} A_{i'k'} (δ_{kk'} + w_k w_{k'}) = b_{ii'} + θ² b_{ij} b_{i'j}`
  have hδ : ∑ k, ∑ k', A i k * A i' k' * (if k = k' then (1 : ℝ) else 0) =
      (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i i' := by
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      Matrix.mul_apply, Matrix.transpose_apply]
  have hw2 : ∑ k, ∑ k', A i k * A i' k' * (w k * w k') =
      θ ^ 2 * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i j *
        (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i' j := by
    have hb : ∀ i₀ : Fin m, (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i₀ j =
        ∑ k, A i₀ k * A j k := fun i₀ => by
      simp only [Matrix.mul_apply, Matrix.transpose_apply]
    rw [hb, hb, hw, mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k' _ => ?_
    ring
  rw [← hδ, ← hw2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k' _ => ?_
  ring

end Vector

end Grammar
