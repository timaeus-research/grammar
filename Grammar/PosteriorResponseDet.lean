/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.PosteriorWeightStein
import Grammar.GaussianQuartetGeneral

/-!
# Covariance interpolation for finite-atom posterior averages (§20, three replicas)

For the finite-atom posterior average `⟨f⟩_g = Σ f_i P_i(g)` and a centred Gaussian vector `G` with
covariance `b = AAᵀ`, the averaged posterior mean along the covariance scale
`A(s) = E⟨f⟩_{√s G}` (`postInterp`) satisfies

★★ `hasDerivAt_postInterp`: `A'(s) = E[H_b(√s G)]` on `(0,1)`, with the **mean response**
`H_b(g) = (β²/2) [Σ_j b_jj R_j (f_j − ⟨f⟩_g) − 2 Σ_ij b_ij W_i W_j (f_j − ⟨f⟩_g)]` (`postResp`),

★★★ `integral_postAvg_eq`: `E⟨f⟩_G = Σ f_i ρ_i / Σ ρ_i + ∫₀¹ E[H_b(√s G)] ds`.

Mechanism: the chain rule `∂_s ⟨f⟩_{√s g} = (β/(2s)) Σ_i (√s g)_i W_i (f_i − ⟨f⟩)` (`postPair`), the
Gaussian-vector Stein identity applied to the field-dependent factor `postH_i = W_i(f_i − ⟨f⟩)`
(derivative `postH'`, second derivative of `⟨f⟩`:
`∂_j∂_i⟨f⟩ = β²[δ_ij R_i(f_i − ⟨f⟩) − W_iW_j(f_i − ⟨f⟩) − W_iW_j(f_j − ⟨f⟩)]`), the symmetry of the
covariance, and differentiation under the Gaussian integral with polynomial dominations
(Astra #163 §1).  In replica language the diagonal term is `f(x₁)(R₁₁ − R₂₂)` and the bilocal
term `f(x₁)(R₁₂ − R₂₃)`: three replicas.  The compact base is `CompactBaseResponse`.

Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Filter Topology

namespace Grammar

section Det

variable {m : ℕ} (β lam : ℝ) (ρ : Fin m → ℝ) (f : Fin m → ℝ)

/-- The first-derivative factor `H_i(g) = W_i(g) (f_i − ⟨f⟩_g)` (so `∂_i⟨f⟩ = β H_i`). -/
noncomputable def postH (i : Fin m) (g : Fin m → ℝ) : ℝ :=
  quartetW β lam ρ i g * (f i - postAvg β lam ρ f g)

/-- The pairing `Σ_i g_i H_i(g)` (so `∂_s ⟨f⟩_{√s g} = (β/(2s)) Σ_i (√s g)_i H_i(√s g)`). -/
noncomputable def postPair (g : Fin m → ℝ) : ℝ := ∑ i, g i * postH β lam ρ f i g

/-- `∂_j H_i = β δ_ij R_i (f_i − ⟨f⟩) − β W_i W_j (f_i − ⟨f⟩) − β W_i W_j (f_j − ⟨f⟩)`. -/
noncomputable def postH' (i j : Fin m) (g : Fin m → ℝ) : ℝ :=
  β * (if i = j then quartetR β lam ρ i g else 0) * (f i - postAvg β lam ρ f g) -
    β * quartetW β lam ρ i g * quartetW β lam ρ j g * (f i - postAvg β lam ρ f g) -
    β * quartetW β lam ρ i g * quartetW β lam ρ j g * (f j - postAvg β lam ρ f g)

/-- The **mean response**
`H_b(g) = (β²/2)[Σ_j b_jj R_j(f_j − ⟨f⟩) − 2 Σ_ij b_ij W_i W_j (f_j − ⟨f⟩)]`. -/
noncomputable def postResp (b : Matrix (Fin m) (Fin m) ℝ) (g : Fin m → ℝ) : ℝ :=
  β ^ 2 / 2 * (∑ j, b j j * quartetR β lam ρ j g * (f j - postAvg β lam ρ f g) -
    2 * ∑ i, ∑ j, b i j * quartetW β lam ρ i g * quartetW β lam ρ j g * (f j - postAvg β lam ρ f g))

variable {β lam} (hβ : 0 < β) (hlam : 0 < lam) {ρ} (hρ : ∀ i, 0 < ρ i) [Nonempty (Fin m)]
include hβ hlam hρ

theorem continuous_postH (i : Fin m) : Continuous (postH β lam ρ f i) :=
  (continuous_quartetW hβ hlam hρ i).mul (continuous_const.sub (continuous_postAvg hβ hlam hρ f))

theorem polyBoundedPi_postH (i : Fin m) : PolyBoundedPi (postH β lam ρ f i) :=
  (polyBoundedPi_quartetW hβ hlam hρ i).mul
    ((PolyBoundedPi.const (f i)).sub (polyBoundedPi_postAvg hβ hlam hρ f))

theorem continuous_postPair : Continuous (postPair β lam ρ f) :=
  continuous_finsetSum _ fun i _ => (continuous_apply i).mul (continuous_postH f hβ hlam hρ i)

theorem polyBoundedPi_postPair : PolyBoundedPi (postPair β lam ρ f) :=
  PolyBoundedPi.finset_sum _ fun i =>
    (PolyBoundedPi.coord i).mul (polyBoundedPi_postH f hβ hlam hρ i)

theorem continuous_postH' (i j : Fin m) : Continuous (postH' β lam ρ f i j) := by
  unfold postH'
  have hite : Continuous fun g : Fin m → ℝ => if i = j then quartetR β lam ρ i g else 0 := by
    by_cases h : i = j
    · simp only [h, if_true]; exact continuous_quartetR hβ hlam hρ j
    · simp only [h, if_false]; exact continuous_const
  exact (((continuous_const.mul hite).mul (continuous_const.sub
    (continuous_postAvg hβ hlam hρ f))).sub (((continuous_const.mul
    (continuous_quartetW hβ hlam hρ i)).mul (continuous_quartetW hβ hlam hρ j)).mul
    (continuous_const.sub (continuous_postAvg hβ hlam hρ f)))).sub (((continuous_const.mul
    (continuous_quartetW hβ hlam hρ i)).mul (continuous_quartetW hβ hlam hρ j)).mul
    (continuous_const.sub (continuous_postAvg hβ hlam hρ f)))

theorem polyBoundedPi_postH' (i j : Fin m) : PolyBoundedPi (postH' β lam ρ f i j) := by
  unfold postH'
  have hite : PolyBoundedPi fun g : Fin m → ℝ => if i = j then quartetR β lam ρ i g else 0 := by
    by_cases h : i = j
    · simp only [h, if_true]; exact polyBoundedPi_quartetR hβ hlam hρ j
    · simp only [h, if_false]; exact PolyBoundedPi.const 0
  exact ((((PolyBoundedPi.const β).mul hite).mul ((PolyBoundedPi.const (f i)).sub
    (polyBoundedPi_postAvg hβ hlam hρ f))).sub ((((PolyBoundedPi.const β).mul
    (polyBoundedPi_quartetW hβ hlam hρ i)).mul (polyBoundedPi_quartetW hβ hlam hρ j)).mul
    ((PolyBoundedPi.const (f i)).sub (polyBoundedPi_postAvg hβ hlam hρ f)))).sub
    ((((PolyBoundedPi.const β).mul (polyBoundedPi_quartetW hβ hlam hρ i)).mul
    (polyBoundedPi_quartetW hβ hlam hρ j)).mul ((PolyBoundedPi.const (f j)).sub
    (polyBoundedPi_postAvg hβ hlam hρ f)))

theorem continuous_postResp (b : Matrix (Fin m) (Fin m) ℝ) : Continuous (postResp β lam ρ f b) := by
  unfold postResp
  refine continuous_const.mul ((continuous_finsetSum _ fun j _ => ?_).sub
    (continuous_const.mul (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_)))
  · exact (continuous_const.mul (continuous_quartetR hβ hlam hρ j)).mul
      (continuous_const.sub (continuous_postAvg hβ hlam hρ f))
  · exact ((continuous_const.mul (continuous_quartetW hβ hlam hρ i)).mul
      (continuous_quartetW hβ hlam hρ j)).mul
      (continuous_const.sub (continuous_postAvg hβ hlam hρ f))

theorem polyBoundedPi_postResp (b : Matrix (Fin m) (Fin m) ℝ) :
    PolyBoundedPi (postResp β lam ρ f b) := by
  unfold postResp
  refine (PolyBoundedPi.const _).mul ((PolyBoundedPi.finset_sum _ fun j => ?_).sub
    ((PolyBoundedPi.const 2).mul (PolyBoundedPi.finset_sum _ fun i =>
      PolyBoundedPi.finset_sum _ fun j => ?_)))
  · exact ((PolyBoundedPi.const _).mul (polyBoundedPi_quartetR hβ hlam hρ j)).mul
      ((PolyBoundedPi.const (f j)).sub (polyBoundedPi_postAvg hβ hlam hρ f))
  · exact (((PolyBoundedPi.const _).mul (polyBoundedPi_quartetW hβ hlam hρ i)).mul
      (polyBoundedPi_quartetW hβ hlam hρ j)).mul
      ((PolyBoundedPi.const (f j)).sub (polyBoundedPi_postAvg hβ hlam hρ f))

/-- ★ **The derivative of the first-derivative factor**: `∂_j H_i = postH' i j`. -/
theorem hasFDerivAt_postH (i : Fin m) (g : Fin m → ℝ) :
    HasFDerivAt (postH β lam ρ f i)
      (∑ j, postH' β lam ρ f i j g • coordProj j : (Fin m → ℝ) →L[ℝ] ℝ) g := by
  have h := (hasFDerivAt_quartetW hβ hlam hρ i g).mul
    ((hasFDerivAt_const (f i) g).sub (hasFDerivAt_postAvg hβ hlam hρ f g))
  refine h.congr_fderiv ?_
  ext v
  simp only [add_apply, smul_apply, neg_apply, sum_apply, coordProj_apply, smul_eq_mul,
    Pi.sub_apply, zero_sub, mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold postH' quartetW'
  ring

omit hlam hρ [Nonempty (Fin m)] in
/-- The pointwise Stein contraction: `Σ_ij b_ij ∂_j H_i = (2/β) H_b` for symmetric `b`. -/
theorem sum_postH'_eq (b : Matrix (Fin m) (Fin m) ℝ) (hb : ∀ i j, b i j = b j i)
    (g : Fin m → ℝ) :
    ∑ i, ∑ j, b i j * postH' β lam ρ f i j g = 2 / β * postResp β lam ρ f b g := by
  unfold postResp
  have hβ' : β ≠ 0 := hβ.ne'
  have hsw : ∑ i, ∑ j, b i j * (β * quartetW β lam ρ i g * quartetW β lam ρ j g *
      (f i - postAvg β lam ρ f g)) =
        ∑ i, ∑ j, b i j * (β * quartetW β lam ρ i g * quartetW β lam ρ j g *
          (f j - postAvg β lam ρ f g)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hb j i]; ring
  have hdiag : ∑ i, ∑ j, b i j * (β * (if i = j then quartetR β lam ρ i g else 0) *
      (f i - postAvg β lam ρ f g)) =
        ∑ j, b j j * (β * quartetR β lam ρ j g * (f j - postAvg β lam ρ f g)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [Ne.symm hji]
    · intro h; exact absurd (Finset.mem_univ i) h
  have key : ∀ i j, b i j * postH' β lam ρ f i j g =
      b i j * (β * (if i = j then quartetR β lam ρ i g else 0) * (f i - postAvg β lam ρ f g)) -
      b i j * (β * quartetW β lam ρ i g * quartetW β lam ρ j g * (f i - postAvg β lam ρ f g)) -
      b i j * (β * quartetW β lam ρ i g * quartetW β lam ρ j g * (f j - postAvg β lam ρ f g)) := by
    intro i j; unfold postH'; ring
  simp only [key, Finset.sum_sub_distrib]
  rw [hdiag, hsw]
  have e1 : ∑ j, b j j * (β * quartetR β lam ρ j g * (f j - postAvg β lam ρ f g)) =
      β * ∑ j, b j j * quartetR β lam ρ j g * (f j - postAvg β lam ρ f g) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have e2 : ∑ i, ∑ j, b i j * (β * quartetW β lam ρ i g * quartetW β lam ρ j g *
      (f j - postAvg β lam ρ f g)) =
        β * ∑ i, ∑ j, b i j * quartetW β lam ρ i g * quartetW β lam ρ j g *
          (f j - postAvg β lam ρ f g) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e1, e2]
  field_simp
  ring

end Det

section Interp

variable {m n : ℕ} {β lam : ℝ} {ρ : Fin m → ℝ} (f : Fin m → ℝ)

/-- `A(s) = E⟨f⟩_{√s G}`. -/
noncomputable def postInterp (β lam : ℝ) (ρ f : Fin m → ℝ) (A : Matrix (Fin m) (Fin (n + 1)) ℝ)
    (s : ℝ) : ℝ :=
  ∫ z, postAvg β lam ρ f (Real.sqrt s • A.mulVec z) ∂stdGaussianPi (n + 1)

/-- `E[H_b(√s G)]` with `b = AAᵀ`. -/
noncomputable def postInterpResp (β lam : ℝ) (ρ f : Fin m → ℝ)
    (A : Matrix (Fin m) (Fin (n + 1)) ℝ) (s : ℝ) : ℝ :=
  ∫ z, postResp β lam ρ f (A * A.transpose) (Real.sqrt s • A.mulVec z) ∂stdGaussianPi (n + 1)

variable (A : Matrix (Fin m) (Fin (n + 1)) ℝ) (hβ : 0 < β) (hlam : 0 < lam) (hρ : ∀ i, 0 < ρ i)
  [Nonempty (Fin m)]
include hβ hlam hρ

theorem postInterp_eq (s : ℝ) :
    postInterp β lam ρ f A s = ∫ g, postAvg β lam ρ f g ∂gaussianVector (Real.sqrt s • A) := by
  rw [integral_gaussianVector _ _ (continuous_postAvg hβ hlam hρ f).measurable]
  simp_rw [Matrix.smul_mulVec]
  rfl

theorem postInterpResp_eq (s : ℝ) :
    postInterpResp β lam ρ f A s =
      ∫ g, postResp β lam ρ f (A * A.transpose) g ∂gaussianVector (Real.sqrt s • A) := by
  rw [integral_gaussianVector _ _ (continuous_postResp f hβ hlam hρ _).measurable]
  simp_rw [Matrix.smul_mulVec]
  rfl

theorem postInterp_one : postInterp β lam ρ f A 1 = ∫ g, postAvg β lam ρ f g ∂gaussianVector A := by
  rw [postInterp_eq f A hβ hlam hρ 1, Real.sqrt_one, one_smul]

/-- `⟨f⟩_0 = Σ f_i ρ_i / Σ ρ_i`. -/
theorem postAvg_zero : postAvg β lam ρ f 0 = (∑ i, f i * ρ i) / ∑ i, ρ i := by
  have hS := fluctuation_pos β lam 0 hβ hlam
  have hsum : 0 < ∑ i, ρ i := Finset.sum_pos (fun i _ => hρ i) Finset.univ_nonempty
  have hD : quartetD β lam ρ 0 = fluctuation β lam 0 * ∑ i, ρ i := by
    unfold quartetD
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [Pi.zero_apply]; ring
  unfold postAvg postWt
  rw [hD, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.zero_apply]
  field_simp

theorem postInterp_zero : postInterp β lam ρ f A 0 = (∑ i, f i * ρ i) / ∑ i, ρ i := by
  unfold postInterp
  simp only [Real.sqrt_zero, zero_smul]
  rw [integral_const, probReal_univ, one_smul, postAvg_zero f hβ hlam hρ]

/-- The chain rule in the covariance scale:
`∂_s ⟨f⟩_{√s g} = (β/(2s)) Σ_i (√s g)_i H_i(√s g)`. -/
theorem hasDerivAt_postAvg_sqrt_smul (g : Fin m → ℝ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun s => postAvg β lam ρ f (Real.sqrt s • g))
      (β / (2 * s) * postPair β lam ρ f (Real.sqrt s • g)) s := by
  have hin : HasDerivAt (fun s => Real.sqrt s • g) ((1 / (2 * Real.sqrt s)) • g) s :=
    (Real.hasDerivAt_sqrt hs.ne').smul_const g
  have hF := (hasFDerivAt_postAvg hβ hlam hρ f (Real.sqrt s • g)).comp_hasDerivAt
    (f := fun s => Real.sqrt s • g) s hin
  refine hF.congr_deriv ?_
  simp only [sum_apply, smul_apply, coordProj_apply, Pi.smul_apply, smul_eq_mul, postPair, postH]
  have hss : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt hs.le
  have hsq : Real.sqrt s ≠ 0 := (Real.sqrt_pos.2 hs).ne'
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show β / (2 * s) = β / (2 * (Real.sqrt s * Real.sqrt s)) by rw [hss]]
  field_simp

/-- ★ **Stein for the pairing at the scaled covariance**:
`E[Σ_i G_i H_i(G)] = (2s/β) E[H_b(G)]` under `gaussianVector (√s A)`, `b = AAᵀ`. -/
theorem integral_postPair_scaled {s : ℝ} (hs : 0 ≤ s) :
    ∫ g, postPair β lam ρ f g ∂gaussianVector (Real.sqrt s • A) =
      2 * s / β *
        ∫ g, postResp β lam ρ f (A * A.transpose) g ∂gaussianVector (Real.sqrt s • A) := by
  set A' := Real.sqrt s • A with hA'
  have hb : ∀ i j, (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i j = (A * A.transpose) j i := by
    intro i j
    rw [Matrix.mul_apply, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun k _ => by rw [Matrix.transpose_apply, Matrix.transpose_apply,
      mul_comm]
  have hint' : ∀ i j, Integrable (postH' β lam ρ f i j) (gaussianVector A') := fun i j =>
    integrable_gaussianVector_of_polyBoundedPi A' (continuous_postH' f hβ hlam hρ i j).measurable
      (polyBoundedPi_postH' f hβ hlam hρ i j)
  have hstein : ∀ i, ∫ g, g i * postH β lam ρ f i g ∂gaussianVector A' =
      ∑ j, s * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i j *
        ∫ g, postH' β lam ρ f i j g ∂gaussianVector A' := by
    intro i
    have h := gaussianVector_stein A' i (F := postH β lam ρ f i)
      (F' := fun g => ∑ k, postH' β lam ρ f i k g • coordProj k)
      (fun g => hasFDerivAt_postH f hβ hlam hρ i g)
      (fun j => by
        simp only [sum_apply, smul_apply, coordProj_apply, Pi.single_apply, smul_eq_mul,
          mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        exact (continuous_postH' f hβ hlam hρ i j).measurable)
      (polyBoundedPi_postH f hβ hlam hρ i)
      (fun j => by
        simp only [sum_apply, smul_apply, coordProj_apply, Pi.single_apply, smul_eq_mul,
          mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        exact polyBoundedPi_postH' f hβ hlam hρ i j)
    rw [h, hA', scaled_cov A hs]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.smul_apply, smul_eq_mul, sum_apply, smul_apply, coordProj_apply,
      Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  unfold postPair
  rw [integral_finsetSum _ fun i _ => integrable_gaussianVector_of_polyBoundedPi A'
    (F := fun g => g i * postH β lam ρ f i g)
    ((measurable_pi_apply i).mul (continuous_postH f hβ hlam hρ i).measurable)
    ((PolyBoundedPi.coord i).mul (polyBoundedPi_postH f hβ hlam hρ i))]
  simp_rw [hstein]
  have hsum : ∑ i, ∑ j, s * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i j *
      ∫ g, postH' β lam ρ f i j g ∂gaussianVector A' =
        s * ∫ g, ∑ i, ∑ j, (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i j *
          postH' β lam ρ f i j g ∂gaussianVector A' := by
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (hint' i j).const_mul ((A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i j), Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ =>
      (hint' i j).const_mul ((A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i j), Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul]
    ring
  rw [hsum]
  simp_rw [sum_postH'_eq f hβ (A * A.transpose) hb]
  rw [integral_const_mul]
  field_simp

/-! ### Differentiation under the Gaussian integral -/

theorem measurable_postAvg_sqrt (s : ℝ) :
    Measurable fun z : Fin (n + 1) → ℝ => postAvg β lam ρ f (Real.sqrt s • A.mulVec z) :=
  ((continuous_postAvg hβ hlam hρ f).comp
    ((continuous_const (y := Real.sqrt s)).smul (continuous_mulVec A))).measurable

/-- ★★ **`A'(s) = E[H_b(√s G)]` on `(0,1)`.** -/
theorem hasDerivAt_postInterp {s₀ : ℝ} (hs₀ : s₀ ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (postInterp β lam ρ f A) (postInterpResp β lam ρ f A s₀) s₀ := by
  obtain ⟨hs₀0, hs₀1⟩ := hs₀
  obtain ⟨C, k, hCk⟩ := (polyBoundedPi_postPair f hβ hlam hρ).smul_bound
  have hnhds : Ioo (s₀ / 2) 2 ∈ nhds s₀ := Ioo_mem_nhds (by linarith) (by linarith)
  have hF_int : Integrable (fun z : Fin (n + 1) → ℝ =>
      postAvg β lam ρ f (Real.sqrt s₀ • A.mulVec z)) (stdGaussianPi (n + 1)) := by
    obtain ⟨C', k', hC'⟩ := (polyBoundedPi_postAvg hβ hlam hρ f).smul_bound
    exact integrable_of_polyBoundedPi (measurable_postAvg_sqrt f A hβ hlam hρ s₀)
      (polyBoundedPi_comp_mulVec A
        (F := fun g : Fin m → ℝ => postAvg β lam ρ f (Real.sqrt s₀ • g))
        ⟨C', k', fun g => hC' _ (sqrt_abs_le_two (by linarith)) g⟩)
  have hPm : ∀ s : ℝ, Measurable fun z : Fin (n + 1) → ℝ =>
      postPair β lam ρ f (Real.sqrt s • A.mulVec z) := fun s =>
    ((continuous_postPair f hβ hlam hρ).comp
      ((continuous_const (y := Real.sqrt s)).smul (continuous_mulVec A))).measurable
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s (z : Fin (n + 1) → ℝ) => postAvg β lam ρ f (Real.sqrt s • A.mulVec z))
    (F' := fun s (z : Fin (n + 1) → ℝ) =>
      β / (2 * s) * postPair β lam ρ f (Real.sqrt s • A.mulVec z))
    (bound := fun z => β / s₀ * (C * (1 + ‖A.mulVec z‖) ^ k)) hnhds
    (Filter.Eventually.of_forall fun s =>
      (measurable_postAvg_sqrt f A hβ hlam hρ s).aestronglyMeasurable)
    hF_int (measurable_const.mul (hPm s₀)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z s hs => ?_) (integrable_polyBound A C k _)
    (Filter.Eventually.of_forall fun z s hs =>
      hasDerivAt_postAvg_sqrt_smul f hβ hlam hρ (A.mulVec z) (by linarith [hs.1]))
  · refine key.2.congr_deriv ?_
    have hPint : ∫ z, postPair β lam ρ f (Real.sqrt s₀ • A.mulVec z) ∂stdGaussianPi (n + 1) =
        ∫ g, postPair β lam ρ f g ∂gaussianVector (Real.sqrt s₀ • A) := by
      rw [integral_gaussianVector _ _ (continuous_postPair f hβ hlam hρ).measurable]
      simp_rw [Matrix.smul_mulVec]
    rw [integral_const_mul, hPint, integral_postPair_scaled f A hβ hlam hρ hs₀0.le,
      ← postInterpResp_eq f A hβ hlam hρ s₀]
    field_simp
  · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (div_pos hβ (by linarith [hs.1] : 0 < 2 * s))]
    have h1 : β / (2 * s) ≤ β / s₀ :=
      div_le_div_of_nonneg_left hβ.le hs₀0 (by linarith [hs.1])
    exact mul_le_mul h1 (hCk _ (sqrt_abs_le_two hs.2.le) _) (abs_nonneg _) (div_pos hβ hs₀0).le

theorem continuousOn_postInterp : ContinuousOn (postInterp β lam ρ f A) (Icc 0 1) := by
  obtain ⟨C, k, hCk⟩ := (polyBoundedPi_postAvg hβ hlam hρ f).smul_bound
  refine continuousOn_of_dominated
    (F := fun s (z : Fin (n + 1) → ℝ) => postAvg β lam ρ f (Real.sqrt s • A.mulVec z))
    (bound := fun z => 1 * (C * (1 + ‖A.mulVec z‖) ^ k))
    (fun s _ => (measurable_postAvg_sqrt f A hβ hlam hρ s).aestronglyMeasurable)
    (fun s hs => Filter.Eventually.of_forall fun z => ?_) (integrable_polyBound A C k 1)
    (Filter.Eventually.of_forall fun z => ?_)
  · rw [Real.norm_eq_abs, one_mul]
    exact hCk _ (sqrt_abs_le_two (by linarith [hs.2])) _
  · exact ((continuous_postAvg hβ hlam hρ f).comp
      (Real.continuous_sqrt.smul continuous_const)).continuousOn

theorem continuousOn_postInterpResp : ContinuousOn (postInterpResp β lam ρ f A) (Icc 0 1) := by
  obtain ⟨C, k, hCk⟩ := (polyBoundedPi_postResp f hβ hlam hρ (A * A.transpose)).smul_bound
  refine continuousOn_of_dominated
    (F := fun s (z : Fin (n + 1) → ℝ) =>
      postResp β lam ρ f (A * A.transpose) (Real.sqrt s • A.mulVec z))
    (bound := fun z => 1 * (C * (1 + ‖A.mulVec z‖) ^ k))
    (fun s _ => ((continuous_postResp f hβ hlam hρ _).comp
      ((continuous_const (y := Real.sqrt s)).smul
        (continuous_mulVec A))).measurable.aestronglyMeasurable)
    (fun s hs => Filter.Eventually.of_forall fun z => ?_) (integrable_polyBound A C k 1)
    (Filter.Eventually.of_forall fun z => ?_)
  · rw [Real.norm_eq_abs, one_mul]
    exact hCk _ (sqrt_abs_le_two (by linarith [hs.2])) _
  · exact ((continuous_postResp f hβ hlam hρ _).comp
      (Real.continuous_sqrt.smul continuous_const)).continuousOn

/-- ★★★ **Covariance interpolation for the averaged posterior mean (finite atoms)**:
`E⟨f⟩_G = Σ f_i ρ_i / Σ ρ_i + ∫₀¹ E[H_b(√s G)] ds`, `b = AAᵀ`. -/
theorem integral_postAvg_eq :
    ∫ g, postAvg β lam ρ f g ∂gaussianVector A =
      (∑ i, f i * ρ i) / (∑ i, ρ i) + ∫ s in (0 : ℝ)..1, postInterpResp β lam ρ f A s := by
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one
    (continuousOn_postInterp f A hβ hlam hρ) (fun s hs => hasDerivAt_postInterp f A hβ hlam hρ hs)
    ?_
  · rw [hFTC, postInterp_one f A hβ hlam hρ, postInterp_zero f A hβ hlam hρ]
    ring
  · have h := continuousOn_postInterpResp f A hβ hlam hρ
    rw [← Set.uIcc_of_le (zero_le_one' ℝ)] at h
    exact h.intervalIntegrable

end Interp

end Grammar
