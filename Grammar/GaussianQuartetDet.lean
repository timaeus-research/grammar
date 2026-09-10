/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.FluctuationSelfNormalised
import Grammar.GaussianSteinVector

/-!
# The self-normalised Gaussian posterior at finite resolution: deterministic identities

For weights `ρ_i > 0` and a field value `g : Fin m → ℝ` (the values of the Gaussian process at the
base points), the **denominator** `D(g) = ∑ ρ_i S_λ(g_i)`, the **posterior weights**
`W_i(g) = ρ_i S_{λ+1/2}(g_i)/D(g)`, the second moment `M₂(g) = ∑ ρ_i S_{λ+1}(g_i)/D(g)`, the
field–moment pairing `H(g) = ∑ g_i W_i(g)` and the **connected two-point function**
`V(g) = c M₂(g) − ∑_{ij} b_{ij} W_i(g) W_j(g)` for a covariance `b = A Aᵀ` with `b_{ii} = c`.

This file proves the pointwise facts: `D > 0` (`quartetD_pos`); the Schwinger–Dyson identity
`M₂ = λ/β + H/2` (`quartetM2_eq`, the Weber recurrence summed); the polynomial bounds making every
quantity integrable against any Gaussian law (`polyBoundedPi_quartetW`, `polyBoundedPi_quartetR`,
`polyBoundedPi_quartetM2`); the derivatives `∂_j W_i = β δ_{ij} ρ_i S_{λ+1}(g_i)/D − β W_i W_j`
(`hasFDerivAt_quartetW`); and `0 ≤ ∑_{ij} b_{ij} W_i W_j ≤ c M₂`, i.e. `0 ≤ V ≤ c M₂`
(`quartetV_nonneg`, by Cauchy–Schwarz and `fluctuation_half_sq_le`).  The expectations are taken in
`GaussianQuartet.lean`.
-/

open Real MeasureTheory Set

namespace Grammar

theorem continuous_fluctuation (β lam : ℝ) (hβ : 0 < β) (hlam : 0 < lam) :
    Continuous (fluctuation β lam) :=
  continuous_iff_continuousAt.2 fun a => (hasDerivAt_fluctuation β lam hβ hlam a).continuousAt

theorem sqrt_le_sqrt_add (a x : ℝ) (ha : 0 ≤ a) :
    Real.sqrt (a + x ^ 2 / 4) ≤ Real.sqrt a + |x| / 2 := by
  rw [Real.sqrt_le_left (by positivity)]
  have := Real.sq_sqrt ha
  nlinarith [Real.sqrt_nonneg a, abs_nonneg x, sq_abs x]

/-- The coordinate projection as a continuous linear map on `Fin m → ℝ`. -/
def coordProj {m : ℕ} (i : Fin m) : (Fin m → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i

@[simp] theorem coordProj_apply {m : ℕ} (i : Fin m) (v : Fin m → ℝ) : coordProj i v = v i := rfl

theorem hasFDerivAt_coord {m : ℕ} (i : Fin m) (g : Fin m → ℝ) :
    HasFDerivAt (fun v : Fin m → ℝ => v i) (coordProj i) g := hasFDerivAt_apply i g

section Det

variable {m : ℕ} (β lam : ℝ) (ρ : Fin m → ℝ)

/-- The denominator `D(g) = ∑ ρ_i S_λ(g_i)`. -/
noncomputable def quartetD (g : Fin m → ℝ) : ℝ := ∑ i, ρ i * fluctuation β lam (g i)

/-- The unnormalised first moments `N_i(g) = ρ_i S_{λ+1/2}(g_i)`. -/
noncomputable def quartetN (i : Fin m) (g : Fin m → ℝ) : ℝ :=
  ρ i * fluctuation β (lam + 1 / 2) (g i)

/-- The posterior weights `W_i(g) = ρ_i S_{λ+1/2}(g_i)/D(g)`. -/
noncomputable def quartetW (i : Fin m) (g : Fin m → ℝ) : ℝ :=
  quartetN β lam ρ i g / quartetD β lam ρ g

/-- The normalised second moments `R_i(g) = ρ_i S_{λ+1}(g_i)/D(g)`. -/
noncomputable def quartetR (i : Fin m) (g : Fin m → ℝ) : ℝ :=
  ρ i * fluctuation β (lam + 1) (g i) / quartetD β lam ρ g

/-- The posterior second moment `M₂(g) = ∑ R_i(g)`. -/
noncomputable def quartetM2 (g : Fin m → ℝ) : ℝ := ∑ i, quartetR β lam ρ i g

/-- The field–moment pairing `H(g) = ∑ g_i W_i(g)`. -/
noncomputable def quartetH (g : Fin m → ℝ) : ℝ := ∑ i, g i * quartetW β lam ρ i g

/-- The bilocal quadratic form `∑_{ij} b_{ij} W_i W_j`. -/
noncomputable def quartetQ (b : Matrix (Fin m) (Fin m) ℝ) (g : Fin m → ℝ) : ℝ :=
  ∑ i, ∑ j, b i j * quartetW β lam ρ i g * quartetW β lam ρ j g

/-- The connected two-point function `V(g) = c M₂(g) − ∑_{ij} b_{ij} W_i(g) W_j(g)`. -/
noncomputable def quartetV (b : Matrix (Fin m) (Fin m) ℝ) (c : ℝ) (g : Fin m → ℝ) : ℝ :=
  c * quartetM2 β lam ρ g - quartetQ β lam ρ b g

/-- The partial derivative `∂_j W_i = β δ_{ij} R_i − β W_i W_j`. -/
noncomputable def quartetW' (i j : Fin m) (g : Fin m → ℝ) : ℝ :=
  β * (if i = j then quartetR β lam ρ i g else 0) - β * quartetW β lam ρ i g * quartetW β lam ρ j g

variable {β lam} (hβ : 0 < β) (hlam : 0 < lam) {ρ} (hρ : ∀ i, 0 < ρ i) [Nonempty (Fin m)]
include hβ hlam hρ

theorem quartetD_pos (g : Fin m → ℝ) : 0 < quartetD β lam ρ g :=
  Finset.sum_pos (fun i _ => mul_pos (hρ i) (fluctuation_pos β lam (g i) hβ hlam))
    Finset.univ_nonempty

omit [Nonempty (Fin m)] in
theorem single_le_quartetD (i : Fin m) (g : Fin m → ℝ) :
    ρ i * fluctuation β lam (g i) ≤ quartetD β lam ρ g :=
  Finset.single_le_sum (fun j _ => (mul_pos (hρ j) (fluctuation_pos β lam (g j) hβ hlam)).le)
    (Finset.mem_univ i)

theorem quartetW_nonneg (i : Fin m) (g : Fin m → ℝ) : 0 ≤ quartetW β lam ρ i g :=
  div_nonneg (mul_pos (hρ i) (fluctuation_pos β _ (g i) hβ (by linarith))).le
    (quartetD_pos hβ hlam hρ g).le

theorem quartetR_nonneg (i : Fin m) (g : Fin m → ℝ) : 0 ≤ quartetR β lam ρ i g :=
  div_nonneg (mul_pos (hρ i) (fluctuation_pos β _ (g i) hβ (by linarith))).le
    (quartetD_pos hβ hlam hρ g).le

/-- **The Schwinger–Dyson identity**: `M₂(g) = λ/β + H(g)/2`. -/
theorem quartetM2_eq (g : Fin m → ℝ) :
    quartetM2 β lam ρ g = lam / β + quartetH β lam ρ g / 2 := by
  have hD := quartetD_pos hβ hlam hρ g
  have hsum : ∑ i, ρ i * fluctuation β (lam + 1) (g i) =
      (∑ i, g i * (ρ i * fluctuation β (lam + 1 / 2) (g i))) / 2 +
        lam / β * quartetD β lam ρ g := by
    unfold quartetD
    rw [Finset.sum_div, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [fluctuation_recurrence β lam hβ hlam]; ring
  unfold quartetM2 quartetR quartetH quartetW quartetN
  rw [← Finset.sum_div, hsum]
  simp_rw [← mul_div_assoc]
  rw [← Finset.sum_div]
  field_simp
  ring

/-! ### Polynomial bounds -/

theorem quartetW_le (i : Fin m) (g : Fin m → ℝ) :
    quartetW β lam ρ i g ≤ Real.sqrt (2 * lam / β) + |g i| / 2 := by
  have hD := quartetD_pos hβ hlam hρ g
  have h0 := fluctuation_pos β lam (g i) hβ hlam
  have hle := single_le_quartetD hβ hlam hρ i g
  have hhalf := fluctuation_half_le hβ hlam (g i)
  have hB : 0 ≤ 2 * lam / β := div_nonneg (by linarith) hβ.le
  unfold quartetW quartetN
  rw [div_le_iff₀ hD]
  calc ρ i * fluctuation β (lam + 1 / 2) (g i)
      ≤ ρ i * (Real.sqrt (2 * lam / β + max (g i) 0 ^ 2 / 4) * fluctuation β lam (g i)) :=
        mul_le_mul_of_nonneg_left hhalf (hρ i).le
    _ ≤ (Real.sqrt (2 * lam / β) + |g i| / 2) * (ρ i * fluctuation β lam (g i)) := by
        have h1 : Real.sqrt (2 * lam / β + max (g i) 0 ^ 2 / 4) ≤
            Real.sqrt (2 * lam / β) + |g i| / 2 := by
          refine (Real.sqrt_le_sqrt ?_).trans (sqrt_le_sqrt_add (2 * lam / β) (g i) hB)
          have : max (g i) 0 ^ 2 ≤ g i ^ 2 := by
            rcases le_total (g i) 0 with h | h
            · rw [max_eq_right h, zero_pow two_ne_zero]; positivity
            · rw [max_eq_left h]
          linarith
        nlinarith [mul_pos (hρ i) h0, Real.sqrt_nonneg (2 * lam / β), abs_nonneg (g i)]
    _ ≤ (Real.sqrt (2 * lam / β) + |g i| / 2) * quartetD β lam ρ g :=
        mul_le_mul_of_nonneg_left hle (add_nonneg (Real.sqrt_nonneg _) (by positivity))

theorem quartetR_le (i : Fin m) (g : Fin m → ℝ) :
    quartetR β lam ρ i g ≤ 2 * lam / β + g i ^ 2 / 4 := by
  have hD := quartetD_pos hβ hlam hρ g
  have h0 := fluctuation_pos β lam (g i) hβ hlam
  have hle := single_le_quartetD hβ hlam hρ i g
  have hsucc := fluctuation_succ_le hβ hlam (g i)
  have hmax : max (g i) 0 ^ 2 ≤ g i ^ 2 := by
    rcases le_total (g i) 0 with h | h
    · rw [max_eq_right h, zero_pow two_ne_zero]; positivity
    · rw [max_eq_left h]
  unfold quartetR
  rw [div_le_iff₀ hD]
  calc ρ i * fluctuation β (lam + 1) (g i)
      ≤ ρ i * ((2 * lam / β + max (g i) 0 ^ 2 / 4) * fluctuation β lam (g i)) :=
        mul_le_mul_of_nonneg_left hsucc (hρ i).le
    _ ≤ (2 * lam / β + g i ^ 2 / 4) * (ρ i * fluctuation β lam (g i)) := by
        nlinarith [mul_pos (hρ i) h0]
    _ ≤ (2 * lam / β + g i ^ 2 / 4) * quartetD β lam ρ g :=
        mul_le_mul_of_nonneg_left hle (add_nonneg (div_nonneg (by linarith) hβ.le) (by positivity))

theorem polyBoundedPi_quartetW (i : Fin m) : PolyBoundedPi (quartetW β lam ρ i) := by
  refine ⟨Real.sqrt (2 * lam / β) + 1 / 2, 1, fun g => ?_⟩
  rw [abs_of_nonneg (quartetW_nonneg hβ hlam hρ i g), pow_one]
  have h1 := quartetW_le hβ hlam hρ i g
  have h2 : |g i| ≤ ‖g‖ := by
    have := norm_le_pi_norm g i; rwa [Real.norm_eq_abs] at this
  nlinarith [Real.sqrt_nonneg (2 * lam / β), norm_nonneg g]

theorem polyBoundedPi_quartetR (i : Fin m) : PolyBoundedPi (quartetR β lam ρ i) := by
  refine ⟨2 * lam / β + 1 / 4, 2, fun g => ?_⟩
  rw [abs_of_nonneg (quartetR_nonneg hβ hlam hρ i g)]
  have h1 := quartetR_le hβ hlam hρ i g
  have h2 : |g i| ≤ ‖g‖ := by
    have := norm_le_pi_norm g i; rwa [Real.norm_eq_abs] at this
  have h3 : g i ^ 2 ≤ ‖g‖ ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h2 2
  have hB : 0 ≤ 2 * lam / β := div_nonneg (by linarith) hβ.le
  nlinarith [norm_nonneg g]

theorem polyBoundedPi_quartetM2 : PolyBoundedPi (quartetM2 β lam ρ) :=
  PolyBoundedPi.finset_sum _ fun i => polyBoundedPi_quartetR hβ hlam hρ i

theorem polyBoundedPi_quartetW' (i j : Fin m) : PolyBoundedPi (quartetW' β lam ρ i j) := by
  unfold quartetW'
  refine PolyBoundedPi.sub ?_ ?_
  · by_cases h : i = j
    · simp only [h, if_true]
      exact (polyBoundedPi_quartetR hβ hlam hρ j).const_mul β
    · simp only [h, if_false, mul_zero]
      exact PolyBoundedPi.const 0
  · exact ((polyBoundedPi_quartetW hβ hlam hρ i).const_mul β).mul
      (polyBoundedPi_quartetW hβ hlam hρ j)

/-! ### Continuity and measurability -/

omit hρ [Nonempty (Fin m)] in
theorem continuous_quartetD : Continuous (quartetD β lam ρ) := by
  unfold quartetD
  exact continuous_finsetSum _ fun i _ =>
    continuous_const.mul ((continuous_fluctuation β lam hβ hlam).comp (continuous_apply i))

theorem continuous_quartetW (i : Fin m) : Continuous (quartetW β lam ρ i) := by
  unfold quartetW quartetN
  exact (continuous_const.mul ((continuous_fluctuation β _ hβ (by linarith)).comp
    (continuous_apply i))).div (continuous_quartetD hβ hlam)
    fun g => (quartetD_pos hβ hlam hρ g).ne'

theorem continuous_quartetR (i : Fin m) : Continuous (quartetR β lam ρ i) := by
  unfold quartetR
  exact (continuous_const.mul ((continuous_fluctuation β _ hβ (by linarith)).comp
    (continuous_apply i))).div (continuous_quartetD hβ hlam)
    fun g => (quartetD_pos hβ hlam hρ g).ne'

theorem continuous_quartetW' (i j : Fin m) : Continuous (quartetW' β lam ρ i j) := by
  unfold quartetW'
  refine Continuous.sub (continuous_const.mul ?_)
    ((continuous_const.mul (continuous_quartetW hβ hlam hρ i)).mul
      (continuous_quartetW hβ hlam hρ j))
  by_cases h : i = j
  · simp only [h, if_true]; exact continuous_quartetR hβ hlam hρ j
  · simp only [h, if_false]; exact continuous_const

/-! ### Derivatives -/

omit hρ [Nonempty (Fin m)] in
/-- The derivative of the denominator. -/
theorem hasFDerivAt_quartetD (g : Fin m → ℝ) :
    HasFDerivAt (quartetD β lam ρ)
      (∑ i, (ρ i * (β * fluctuation β (lam + 1 / 2) (g i))) • coordProj i :
        (Fin m → ℝ) →L[ℝ] ℝ) g := by
  unfold quartetD
  have hsum := HasFDerivAt.sum (u := Finset.univ)
    (A := fun i (y : Fin m → ℝ) => ρ i * fluctuation β lam (y i))
    (A' := fun i => (ρ i * (β * fluctuation β (lam + 1 / 2) (g i))) • coordProj i) (x := g)
    fun i _ => by
      have h := ((hasDerivAt_fluctuation β lam hβ hlam (g i)).comp_hasFDerivAt g
        (hasFDerivAt_coord i g)).const_mul (ρ i)
      refine h.congr_fderiv ?_
      ext v; simp [mul_assoc]
  rw [Finset.sum_fn] at hsum
  exact hsum

omit hρ [Nonempty (Fin m)] in
theorem hasFDerivAt_quartetN (i : Fin m) (g : Fin m → ℝ) :
    HasFDerivAt (quartetN β lam ρ i)
      ((ρ i * (β * fluctuation β (lam + 1) (g i))) • coordProj i : (Fin m → ℝ) →L[ℝ] ℝ) g := by
  unfold quartetN
  have h := ((hasDerivAt_fluctuation β (lam + 1 / 2) hβ (by linarith) (g i)).comp_hasFDerivAt g
    (hasFDerivAt_coord i g)).const_mul (ρ i)
  rw [show lam + 1 / 2 + 1 / 2 = lam + 1 by ring] at h
  refine h.congr_fderiv ?_
  ext v; simp [mul_assoc]

/-- **The derivative of the posterior weights**: `∂_j W_i = β δ_{ij} R_i − β W_i W_j`. -/
theorem hasFDerivAt_quartetW (i : Fin m) (g : Fin m → ℝ) :
    HasFDerivAt (quartetW β lam ρ i)
      (∑ j, quartetW' β lam ρ i j g • coordProj j : (Fin m → ℝ) →L[ℝ] ℝ) g := by
  have hD := quartetD_pos hβ hlam hρ g
  have hN := hasFDerivAt_quartetN (ρ := ρ) hβ hlam i g
  have hDd := hasFDerivAt_quartetD (ρ := ρ) hβ hlam g
  have hinv := (hasDerivAt_inv hD.ne').comp_hasFDerivAt g hDd
  have h := hN.mul hinv
  have hfun : quartetW β lam ρ i =
      quartetN β lam ρ i * ((fun y : ℝ => y⁻¹) ∘ quartetD β lam ρ) := by
    funext x; simp [quartetW, div_eq_mul_inv]
  rw [hfun]
  refine h.congr_fderiv ?_
  have hDne : quartetD β lam ρ g ≠ 0 := hD.ne'
  have hRHS : ∀ v : Fin m → ℝ,
      (∑ j, quartetW' β lam ρ i j g • coordProj j : (Fin m → ℝ) →L[ℝ] ℝ) v =
        β * quartetR β lam ρ i g * v i -
          β * quartetW β lam ρ i g * ∑ j, quartetW β lam ρ j g * v j := by
    intro v
    simp only [sum_apply, smul_apply, coordProj_apply, smul_eq_mul, quartetW', sub_mul,
      Finset.sum_sub_distrib, mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  ext v
  rw [hRHS]
  simp only [add_apply, smul_apply, sum_apply, coordProj_apply, smul_eq_mul, Function.comp_apply]
  have hDsum : ∑ j, ρ j * (β * fluctuation β (lam + 1 / 2) (g j)) * v j =
      β * ∑ j, quartetN β lam ρ j g * v j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by unfold quartetN; ring
  have hWsum : ∑ j, quartetW β lam ρ j g * v j =
      (∑ j, quartetN β lam ρ j g * v j) / quartetD β lam ρ g := by
    unfold quartetW
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hDsum, hWsum]
  set T := ∑ j, quartetN β lam ρ j g * v j
  unfold quartetR quartetW quartetN
  field_simp
  ring

/-! ### `0 ≤ Q ≤ c M₂` -/

omit hβ hlam hρ [Nonempty (Fin m)] in
theorem quartetQ_eq_sum_sq {n : ℕ} (A : Matrix (Fin m) (Fin (n + 1)) ℝ) (g : Fin m → ℝ) :
    quartetQ β lam ρ (A * A.transpose) g = ∑ k, (∑ i, A i k * quartetW β lam ρ i g) ^ 2 := by
  unfold quartetQ
  have hterm : ∀ i j, (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i j * quartetW β lam ρ i g *
      quartetW β lam ρ j g =
      ∑ k, (A i k * quartetW β lam ρ i g) * (A j k * quartetW β lam ρ j g) := by
    intro i j
    rw [Matrix.mul_apply, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.transpose_apply]; ring
  simp_rw [hterm]
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [sq, Finset.sum_mul_sum]

omit hβ hlam hρ [Nonempty (Fin m)] in
theorem quartetQ_nonneg {n : ℕ} (A : Matrix (Fin m) (Fin (n + 1)) ℝ) (g : Fin m → ℝ) :
    0 ≤ quartetQ β lam ρ (A * A.transpose) g := by
  rw [quartetQ_eq_sum_sq]
  positivity

/-- **Cauchy–Schwarz for one column**: `(∑_i A_{ik} W_i)² ≤ ∑_i A_{ik}² R_i`. -/
theorem sq_sum_mul_quartetW_le {n : ℕ} (A : Matrix (Fin m) (Fin (n + 1)) ℝ) (k : Fin (n + 1))
    (g : Fin m → ℝ) :
    (∑ i, A i k * quartetW β lam ρ i g) ^ 2 ≤ ∑ i, A i k ^ 2 * quartetR β lam ρ i g := by
  have hD := quartetD_pos hβ hlam hρ g
  set D := quartetD β lam ρ g with hDdef
  -- weights `w_i = ρ_i S_λ(g_i)` and values `x_i = A_{ik} S_{λ+1/2}(g_i)/S_λ(g_i)`
  have hw : ∀ i, 0 < ρ i * fluctuation β lam (g i) := fun i =>
    mul_pos (hρ i) (fluctuation_pos β lam (g i) hβ hlam)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => Real.sqrt (ρ i * fluctuation β lam (g i)))
    (fun i => A i k * quartetN β lam ρ i g / Real.sqrt (ρ i * fluctuation β lam (g i)))
  have hfg : ∀ i, Real.sqrt (ρ i * fluctuation β lam (g i)) *
      (A i k * quartetN β lam ρ i g / Real.sqrt (ρ i * fluctuation β lam (g i))) =
      A i k * quartetN β lam ρ i g := fun i =>
    mul_div_cancel₀ _ (Real.sqrt_pos.2 (hw i)).ne'
  have hf2 : ∀ i, Real.sqrt (ρ i * fluctuation β lam (g i)) ^ 2 = ρ i * fluctuation β lam (g i) :=
    fun i => Real.sq_sqrt (hw i).le
  have hg2 : ∀ i, (A i k * quartetN β lam ρ i g / Real.sqrt (ρ i * fluctuation β lam (g i))) ^ 2 ≤
      A i k ^ 2 * (ρ i * fluctuation β (lam + 1) (g i)) := by
    intro i
    rw [div_pow, hf2, div_le_iff₀ (hw i)]
    have hcs' := fluctuation_half_sq_le hβ hlam (g i)
    unfold quartetN
    calc (A i k * (ρ i * fluctuation β (lam + 1 / 2) (g i))) ^ 2
        = A i k ^ 2 * ρ i * (ρ i * fluctuation β (lam + 1 / 2) (g i) ^ 2) := by ring
      _ ≤ A i k ^ 2 * ρ i * (ρ i * (fluctuation β lam (g i) * fluctuation β (lam + 1) (g i))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcs' (hρ i).le)
            (mul_nonneg (sq_nonneg _) (hρ i).le)
      _ = _ := by ring
  rw [Finset.sum_congr rfl fun i _ => hfg i, Finset.sum_congr rfl fun i _ => hf2 i] at hcs
  have hsumD : ∑ i, ρ i * fluctuation β lam (g i) = D := rfl
  rw [hsumD] at hcs
  have hbound : (∑ i, A i k * quartetN β lam ρ i g) ^ 2 ≤
      D * ∑ i, A i k ^ 2 * (ρ i * fluctuation β (lam + 1) (g i)) :=
    hcs.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hg2 i) hD.le)
  -- divide by `D²`
  have hW : ∑ i, A i k * quartetW β lam ρ i g = (∑ i, A i k * quartetN β lam ρ i g) / D := by
    unfold quartetW
    rw [← hDdef, Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hR : ∑ i, A i k ^ 2 * quartetR β lam ρ i g =
      (∑ i, A i k ^ 2 * (ρ i * fluctuation β (lam + 1) (g i))) / D := by
    unfold quartetR
    rw [← hDdef, Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hW, hR, div_pow, div_le_div_iff₀ (by positivity) hD]
  calc (∑ i, A i k * quartetN β lam ρ i g) ^ 2 * D
      ≤ (D * ∑ i, A i k ^ 2 * (ρ i * fluctuation β (lam + 1) (g i))) * D :=
        mul_le_mul_of_nonneg_right hbound hD.le
    _ = _ := by ring

/-- **`Q ≤ c M₂`** when the covariance has constant diagonal `c`: `∑_k A_{ik}² = c`. -/
theorem quartetQ_le {n : ℕ} (A : Matrix (Fin m) (Fin (n + 1)) ℝ) {c : ℝ}
    (hc : ∀ i, (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i i = c) (g : Fin m → ℝ) :
    quartetQ β lam ρ (A * A.transpose) g ≤ c * quartetM2 β lam ρ g := by
  rw [quartetQ_eq_sum_sq]
  calc ∑ k, (∑ i, A i k * quartetW β lam ρ i g) ^ 2
      ≤ ∑ k, ∑ i, A i k ^ 2 * quartetR β lam ρ i g :=
        Finset.sum_le_sum fun k _ => sq_sum_mul_quartetW_le hβ hlam hρ A k g
    _ = ∑ i, (∑ k, A i k ^ 2) * quartetR β lam ρ i g := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_mul]
    _ = c * quartetM2 β lam ρ g := by
        unfold quartetM2
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        have := hc i
        simp only [Matrix.mul_apply, Matrix.transpose_apply, ← sq] at this
        rw [this]

/-- **`0 ≤ V ≤ c M₂`**. -/
theorem quartetV_nonneg {n : ℕ} (A : Matrix (Fin m) (Fin (n + 1)) ℝ) {c : ℝ}
    (hc : ∀ i, (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i i = c) (g : Fin m → ℝ) :
    0 ≤ quartetV β lam ρ (A * A.transpose) c g ∧
      quartetV β lam ρ (A * A.transpose) c g ≤ c * quartetM2 β lam ρ g := by
  unfold quartetV
  constructor
  · linarith [quartetQ_le hβ hlam hρ A hc g]
  · linarith [quartetQ_nonneg (β := β) (lam := lam) (ρ := ρ) A g]

end Det

end Grammar
