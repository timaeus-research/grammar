/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.GaussianQuartet

/-!
# Gaussian integration by parts for finite-atom posterior averages (§20, Stein for `⟨f⟩`)

On a finite family of atoms with weights `ρ_i > 0` the limit posterior of `g : Fin m → ℝ` has the
weights `P_i(g) = ρ_i S_λ(g_i) / D(g)` (`postWt`) and the posterior average of `f : Fin m → ℝ` is
`⟨f⟩_g = Σ_i f_i P_i(g)` (`postAvg`).  Its derivative is
`∂_j ⟨f⟩_g = β W_j(g) (f_j − ⟨f⟩_g)` (`hasFDerivAt_postAvg`, with the `√t`-weights
`W_j = ρ_j S_{λ+1/2}(g_j)/D` of the quartet).  Adjoining an external coordinate `v 0` and applying
the Gaussian-vector Stein identity (`gaussianVector_stein`) to the joint vector gives

★★ `integral_coord_mul_postAvg_tail`:
`E[v₀ ⟨f⟩_{v'}] = β Σ_i b_{0,i} E[W_i(v') (f_i − ⟨f⟩_{v'})]`, `v' = (v₁, …, v_m)`, `b = A Aᵀ`,

the finite-atom form of `E[G(x₀)⟨f⟩_G] = E[D⟨f⟩_G[C(x₀,·)]]` (Astra #162 §5); the compact base is
`CompactBaseStein`.

Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set

namespace Grammar

section Det

variable {m : ℕ} (β lam : ℝ) (ρ : Fin m → ℝ)

/-- The posterior weights `P_i(g) = ρ_i S_λ(g_i) / D(g)`. -/
noncomputable def postWt (i : Fin m) (g : Fin m → ℝ) : ℝ :=
  ρ i * fluctuation β lam (g i) / quartetD β lam ρ g

/-- The posterior average `⟨f⟩_g = Σ_i f_i P_i(g)`. -/
noncomputable def postAvg (f : Fin m → ℝ) (g : Fin m → ℝ) : ℝ :=
  ∑ i, f i * postWt β lam ρ i g

/-- The partial derivative `∂_j P_i = β δ_{ij} W_i − β P_i W_j`. -/
noncomputable def postWt' (i j : Fin m) (g : Fin m → ℝ) : ℝ :=
  β * (if i = j then quartetW β lam ρ i g else 0) - β * postWt β lam ρ i g * quartetW β lam ρ j g

variable {β lam} (hβ : 0 < β) (hlam : 0 < lam) {ρ} (hρ : ∀ i, 0 < ρ i) [Nonempty (Fin m)]
include hβ hlam hρ

theorem postWt_nonneg (i : Fin m) (g : Fin m → ℝ) : 0 ≤ postWt β lam ρ i g :=
  div_nonneg (mul_nonneg (hρ i).le (fluctuation_pos β lam _ hβ hlam).le)
    (quartetD_pos hβ hlam hρ g).le

theorem sum_postWt (g : Fin m → ℝ) : ∑ i, postWt β lam ρ i g = 1 := by
  unfold postWt
  rw [← Finset.sum_div]
  exact div_self (quartetD_pos hβ hlam hρ g).ne'

/-- `|⟨f⟩_g| ≤ ‖f‖`. -/
theorem abs_postAvg_le (f : Fin m → ℝ) (g : Fin m → ℝ) : |postAvg β lam ρ f g| ≤ ‖f‖ := by
  unfold postAvg
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i, |f i * postWt β lam ρ i g| ≤ ∑ i, ‖f‖ * postWt β lam ρ i g := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul, abs_of_nonneg (postWt_nonneg hβ hlam hρ i g)]
        refine mul_le_mul_of_nonneg_right ?_ (postWt_nonneg hβ hlam hρ i g)
        have := norm_le_pi_norm f i
        rwa [Real.norm_eq_abs] at this
    _ = ‖f‖ := by rw [← Finset.mul_sum, sum_postWt hβ hlam hρ g, mul_one]

theorem continuous_postWt (i : Fin m) : Continuous (postWt β lam ρ i) :=
  (continuous_const.mul ((continuous_fluctuation β lam hβ hlam).comp (continuous_apply i))).div
    (continuous_quartetD hβ hlam) fun g => (quartetD_pos hβ hlam hρ g).ne'

theorem continuous_postAvg (f : Fin m → ℝ) : Continuous (postAvg β lam ρ f) :=
  continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_postWt hβ hlam hρ i)

theorem polyBoundedPi_postAvg (f : Fin m → ℝ) : PolyBoundedPi (postAvg β lam ρ f) :=
  ⟨‖f‖, 0, fun g => by simpa using abs_postAvg_le hβ hlam hρ f g⟩

/-- **The derivative of the posterior weights**: `∂_j P_i = β δ_{ij} W_i − β P_i W_j`. -/
theorem hasFDerivAt_postWt (i : Fin m) (g : Fin m → ℝ) :
    HasFDerivAt (postWt β lam ρ i)
      (∑ j, postWt' β lam ρ i j g • coordProj j : (Fin m → ℝ) →L[ℝ] ℝ) g := by
  have hD := quartetD_pos hβ hlam hρ g
  have hN : HasFDerivAt (fun y : Fin m → ℝ => ρ i * fluctuation β lam (y i))
      ((ρ i * (β * fluctuation β (lam + 1 / 2) (g i))) • coordProj i : (Fin m → ℝ) →L[ℝ] ℝ) g := by
    have h := ((hasDerivAt_fluctuation β lam hβ hlam (g i)).comp_hasFDerivAt g
      (hasFDerivAt_coord i g)).const_mul (ρ i)
    refine h.congr_fderiv ?_
    ext v; simp [mul_assoc]
  have hDd := hasFDerivAt_quartetD (ρ := ρ) hβ hlam g
  have hinv := (hasDerivAt_inv hD.ne').comp_hasFDerivAt g hDd
  have h := hN.mul hinv
  have hfun : postWt β lam ρ i =
      (fun y : Fin m → ℝ => ρ i * fluctuation β lam (y i)) *
        ((fun y : ℝ => y⁻¹) ∘ quartetD β lam ρ) := by
    funext x; simp [postWt, div_eq_mul_inv]
  rw [hfun]
  refine h.congr_fderiv ?_
  have hDne : quartetD β lam ρ g ≠ 0 := hD.ne'
  have hRHS : ∀ v : Fin m → ℝ,
      (∑ j, postWt' β lam ρ i j g • coordProj j : (Fin m → ℝ) →L[ℝ] ℝ) v =
        β * quartetW β lam ρ i g * v i -
          β * postWt β lam ρ i g * ∑ j, quartetW β lam ρ j g * v j := by
    intro v
    simp only [sum_apply, smul_apply, coordProj_apply,
      smul_eq_mul, postWt', sub_mul, Finset.sum_sub_distrib, mul_ite, mul_zero, ite_mul,
      zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  ext v
  rw [hRHS]
  simp only [add_apply, smul_apply,
    sum_apply, coordProj_apply, smul_eq_mul, Function.comp_apply]
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
  unfold quartetW quartetN postWt
  field_simp
  ring

/-- ★ **The derivative of the posterior average**: `∂_j ⟨f⟩_g = β W_j(g) (f_j − ⟨f⟩_g)`. -/
theorem hasFDerivAt_postAvg (f : Fin m → ℝ) (g : Fin m → ℝ) :
    HasFDerivAt (postAvg β lam ρ f)
      (∑ j, (β * quartetW β lam ρ j g * (f j - postAvg β lam ρ f g)) • coordProj j :
        (Fin m → ℝ) →L[ℝ] ℝ) g := by
  have hsum := HasFDerivAt.sum (u := Finset.univ)
    (A := fun i (y : Fin m → ℝ) => f i * postWt β lam ρ i y)
    (A' := fun i => f i • (∑ j, postWt' β lam ρ i j g • coordProj j : (Fin m → ℝ) →L[ℝ] ℝ))
    (x := g) fun i _ => (hasFDerivAt_postWt hβ hlam hρ i g).const_mul (f i)
  rw [Finset.sum_fn] at hsum
  refine hsum.congr_fderiv ?_
  ext v
  simp only [sum_apply, smul_apply, coordProj_apply, smul_eq_mul, postWt', sub_mul,
    Finset.sum_sub_distrib, mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  unfold postAvg
  have h1 : ∑ x, f x * (β * quartetW β lam ρ x g * v x -
      ∑ y, β * postWt β lam ρ x g * quartetW β lam ρ y g * v y) =
        ∑ x, f x * (β * quartetW β lam ρ x g * v x) -
          ∑ x, ∑ y, f x * (β * postWt β lam ρ x g * quartetW β lam ρ y g * v y) := by
    simp only [mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
  have h2 : ∀ i, β * quartetW β lam ρ i g * (f i - ∑ x, f x * postWt β lam ρ x g) * v i =
      β * quartetW β lam ρ i g * f i * v i -
        ∑ x, f x * (β * postWt β lam ρ x g * quartetW β lam ρ i g * v i) := by
    intro i
    simp only [mul_sub, sub_mul, Finset.mul_sum, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [h1, Finset.sum_congr rfl fun i _ => h2 i, Finset.sum_sub_distrib, Finset.sum_comm]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

end Det

section Tail

variable {m : ℕ}

/-- The tail projection `(v₀, v₁, …, v_m) ↦ (v₁, …, v_m)`. -/
noncomputable def tailCLM (m : ℕ) : (Fin (m + 1) → ℝ) →L[ℝ] (Fin m → ℝ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj i.succ

@[simp] theorem tailCLM_apply (v : Fin (m + 1) → ℝ) : tailCLM m v = fun i => v i.succ := rfl

theorem norm_tailCLM_apply_le (v : Fin (m + 1) → ℝ) : ‖tailCLM m v‖ ≤ ‖v‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => norm_le_pi_norm v i.succ

theorem PolyBoundedPi.nonneg_const {H : (Fin m → ℝ) → ℝ} {C : ℝ} {k : ℕ}
    (h : ∀ z, |H z| ≤ C * (1 + ‖z‖) ^ k) : 0 ≤ C := by
  have := (abs_nonneg _).trans (h 0)
  simp only [norm_zero, add_zero, one_pow, mul_one] at this
  exact this

theorem PolyBoundedPi.comp_tail {H : (Fin m → ℝ) → ℝ} (hH : PolyBoundedPi H) :
    PolyBoundedPi fun v : Fin (m + 1) → ℝ => H (tailCLM m v) := by
  obtain ⟨C, k, hC⟩ := hH
  refine ⟨C, k, fun v => (hC _).trans ?_⟩
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
    (by linarith [norm_tailCLM_apply_le v]) k) (PolyBoundedPi.nonneg_const hC)

end Tail

section Stein

variable {m n : ℕ} {β lam : ℝ} {ρ : Fin m → ℝ} (hβ : 0 < β) (hlam : 0 < lam) (hρ : ∀ i, 0 < ρ i)
  [Nonempty (Fin m)]
include hβ hlam hρ

omit hβ hlam hρ [Nonempty (Fin m)] in
/-- The derivative of `v ↦ ⟨f⟩_{v'}` in the direction `w`:
`Σ_k β W_k(v') (f_k − ⟨f⟩_{v'}) w_{k+1}`. -/
theorem postAvg_tail_deriv_apply (f : Fin m → ℝ) (v w : Fin (m + 1) → ℝ) :
    ((∑ j, (β * quartetW β lam ρ j (tailCLM m v) * (f j - postAvg β lam ρ f (tailCLM m v))) •
      coordProj j : (Fin m → ℝ) →L[ℝ] ℝ) ∘L tailCLM m) w =
      ∑ k, β * quartetW β lam ρ k (tailCLM m v) * (f k - postAvg β lam ρ f (tailCLM m v)) *
        w k.succ := by
  simp only [ContinuousLinearMap.comp_apply, sum_apply,
    smul_apply, coordProj_apply, smul_eq_mul, tailCLM_apply]

omit hβ hlam hρ [Nonempty (Fin m)] in
theorem postAvg_tail_deriv_single_zero (f : Fin m → ℝ) (v : Fin (m + 1) → ℝ) :
    ((∑ j, (β * quartetW β lam ρ j (tailCLM m v) * (f j - postAvg β lam ρ f (tailCLM m v))) •
      coordProj j : (Fin m → ℝ) →L[ℝ] ℝ) ∘L tailCLM m) (Pi.single 0 1) = 0 := by
  rw [postAvg_tail_deriv_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [Pi.single_eq_of_ne (Fin.succ_ne_zero k), mul_zero]

omit hβ hlam hρ [Nonempty (Fin m)] in
theorem postAvg_tail_deriv_single_succ (f : Fin m → ℝ) (v : Fin (m + 1) → ℝ) (i : Fin m) :
    ((∑ j, (β * quartetW β lam ρ j (tailCLM m v) * (f j - postAvg β lam ρ f (tailCLM m v))) •
      coordProj j : (Fin m → ℝ) →L[ℝ] ℝ) ∘L tailCLM m) (Pi.single i.succ 1) =
      β * quartetW β lam ρ i (tailCLM m v) * (f i - postAvg β lam ρ f (tailCLM m v)) := by
  rw [postAvg_tail_deriv_apply]
  rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same, mul_one]
  · intro k _ hk
    rw [Pi.single_eq_of_ne (fun h => hk (Fin.succ_injective _ h)), mul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem continuous_postAvg_tail_deriv (f : Fin m → ℝ) (w : Fin (m + 1) → ℝ) :
    Continuous fun v : Fin (m + 1) → ℝ =>
      ∑ k, β * quartetW β lam ρ k (tailCLM m v) * (f k - postAvg β lam ρ f (tailCLM m v)) *
        w k.succ :=
  continuous_finsetSum _ fun k _ =>
    ((continuous_const.mul ((continuous_quartetW hβ hlam hρ k).comp (tailCLM m).continuous)).mul
      (continuous_const.sub ((continuous_postAvg hβ hlam hρ f).comp
        (tailCLM m).continuous))).mul continuous_const

theorem polyBoundedPi_postAvg_tail_deriv (f : Fin m → ℝ) (w : Fin (m + 1) → ℝ) :
    PolyBoundedPi fun v : Fin (m + 1) → ℝ =>
      ∑ k, β * quartetW β lam ρ k (tailCLM m v) * (f k - postAvg β lam ρ f (tailCLM m v)) *
        w k.succ :=
  PolyBoundedPi.finset_sum _ fun k =>
    (((PolyBoundedPi.const β).mul (polyBoundedPi_quartetW hβ hlam hρ k).comp_tail).mul
      ((PolyBoundedPi.const (f k)).sub (polyBoundedPi_postAvg hβ hlam hρ f).comp_tail)).mul
      (PolyBoundedPi.const (w k.succ))

/-- ★★ **Gaussian integration by parts for the posterior average with an external coordinate**:
for the joint Gaussian vector `v = (v₀, v')` with covariance `b = A Aᵀ`,
`E[v₀ ⟨f⟩_{v'}] = β Σ_i b_{0,i+1} E[W_i(v') (f_i − ⟨f⟩_{v'})]`. -/
theorem integral_coord_mul_postAvg_tail (A : Matrix (Fin (m + 1)) (Fin (n + 1)) ℝ)
    (f : Fin m → ℝ) :
    ∫ v, v 0 * postAvg β lam ρ f (tailCLM m v) ∂gaussianVector A =
      β * ∑ i, (A * A.transpose : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) 0 i.succ *
        ∫ v, quartetW β lam ρ i (tailCLM m v) * (f i - postAvg β lam ρ f (tailCLM m v))
          ∂gaussianVector A := by
  have hF : ∀ v : Fin (m + 1) → ℝ, HasFDerivAt (fun v => postAvg β lam ρ f (tailCLM m v))
      ((∑ j, (β * quartetW β lam ρ j (tailCLM m v) *
        (f j - postAvg β lam ρ f (tailCLM m v))) • coordProj j : (Fin m → ℝ) →L[ℝ] ℝ) ∘L
          tailCLM m) v := fun v =>
    (hasFDerivAt_postAvg hβ hlam hρ f (tailCLM m v)).comp v (tailCLM m).hasFDerivAt
  have h := gaussianVector_stein A 0 hF
    (fun j => by
      simp only [postAvg_tail_deriv_apply]
      exact (continuous_postAvg_tail_deriv hβ hlam hρ f _).measurable)
    ((polyBoundedPi_postAvg hβ hlam hρ f).comp_tail)
    (fun j => by
      simp only [postAvg_tail_deriv_apply]
      exact polyBoundedPi_postAvg_tail_deriv hβ hlam hρ f _)
  rw [h, Fin.sum_univ_succ]
  simp only [postAvg_tail_deriv_single_zero, postAvg_tail_deriv_single_succ,
    integral_zero, mul_zero, zero_add, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hβint : ∫ v, β * quartetW β lam ρ i (tailCLM m v) *
      (f i - postAvg β lam ρ f (tailCLM m v)) ∂gaussianVector A =
        β * ∫ v, quartetW β lam ρ i (tailCLM m v) * (f i - postAvg β lam ρ f (tailCLM m v))
          ∂gaussianVector A := by
    rw [← integral_const_mul]
    congr 1
    funext v
    ring
  rw [hβint]
  ring

end Stein

end Grammar
