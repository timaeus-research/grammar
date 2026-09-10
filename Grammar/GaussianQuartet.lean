/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.GaussianQuartetDet

/-!
# The self-normalised Gaussian quartet at finite resolution

Let `G = A Z` be a centred Gaussian vector with covariance `b = A Aᵀ`, `b_{ii} = c`, and let
`D, W_i, M₂, H, V` be the self-normalised posterior quantities of `GaussianQuartetDet.lean` for
weights `ρ_i > 0`.  Then, for **every** `β, λ > 0`:

* every quantity is integrable (`integrable_quartetH`, `integrable_quartetM2`,
  `integrable_quartetV`), because it is polynomially bounded;
* **Gaussian integration by parts**: `E[H(G)] = β E[V(G)]` (`integral_quartetH_eq`), from the
  finite-dimensional Stein identity applied to the posterior weights `W_i` with
  `∂_j W_i = β δ_{ij} R_i − β W_i W_j`;
* with the **singular fluctuation** `ν := E[H(G)]/2`: `ν ≥ 0`, `E[V] = 2ν/β` and
  `E[M₂] = λ/β + ν` (`quartet_identities`), the last by integrating the Schwinger–Dyson identity;
* the **Bayes quartet algebra** (`bayes_quartet`): the four coefficients `λ/β ± ν` and
  `(λ − ν)/β ± ν` obtained from `E[M₂]`, `E[M₂ − H]` and the correction `−E[V]/2`.

These are Gaussian-limit posterior identities at finite resolution (finitely many base points);
the identification of `ν` with the statistical singular fluctuation and the finite-sample error
expansions require the posterior transfer and uniform-integrability theorems, which are separate.
-/

open Real MeasureTheory Set

namespace Grammar

section Quartet

variable {m n : ℕ} {β lam : ℝ} {ρ : Fin m → ℝ} (hβ : 0 < β) (hlam : 0 < lam) (hρ : ∀ i, 0 < ρ i)
  [Nonempty (Fin m)] (A : Matrix (Fin m) (Fin (n + 1)) ℝ)
include hβ hlam hρ

omit hβ hlam hρ [Nonempty (Fin m)] in
theorem integrable_gaussianVector_of_polyBoundedPi {F : (Fin m → ℝ) → ℝ} (hFm : Measurable F)
    (hF : PolyBoundedPi F) : Integrable F (gaussianVector A) :=
  (integrable_map_measure hFm.aestronglyMeasurable (measurable_mulVec A).aemeasurable).2
    (integrable_of_polyBoundedPi (hFm.comp (measurable_mulVec A)) (polyBoundedPi_comp_mulVec A hF))

theorem integrable_quartetW (i : Fin m) : Integrable (quartetW β lam ρ i) (gaussianVector A) :=
  integrable_gaussianVector_of_polyBoundedPi A (continuous_quartetW hβ hlam hρ i).measurable
    (polyBoundedPi_quartetW hβ hlam hρ i)

theorem integrable_quartetR (i : Fin m) : Integrable (quartetR β lam ρ i) (gaussianVector A) :=
  integrable_gaussianVector_of_polyBoundedPi A (continuous_quartetR hβ hlam hρ i).measurable
    (polyBoundedPi_quartetR hβ hlam hρ i)

theorem integrable_quartetW' (i j : Fin m) :
    Integrable (quartetW' β lam ρ i j) (gaussianVector A) :=
  integrable_gaussianVector_of_polyBoundedPi A
    (continuous_quartetW' hβ hlam hρ i j).measurable (polyBoundedPi_quartetW' hβ hlam hρ i j)

theorem integrable_quartetM2 : Integrable (quartetM2 β lam ρ) (gaussianVector A) :=
  integrable_finsetSum _ fun i _ => integrable_quartetR hβ hlam hρ A i

theorem integrable_coord_mul_quartetW (i : Fin m) :
    Integrable (fun g => g i * quartetW β lam ρ i g) (gaussianVector A) :=
  integrable_gaussianVector_of_polyBoundedPi A
    ((measurable_pi_apply i).mul (continuous_quartetW hβ hlam hρ i).measurable)
    ((PolyBoundedPi.coord i).mul (polyBoundedPi_quartetW hβ hlam hρ i))

theorem integrable_quartetH : Integrable (quartetH β lam ρ) (gaussianVector A) :=
  integrable_finsetSum _ fun i _ => integrable_coord_mul_quartetW hβ hlam hρ A i

theorem integrable_quartetW_mul (i j : Fin m) :
    Integrable (fun g => quartetW β lam ρ i g * quartetW β lam ρ j g) (gaussianVector A) :=
  integrable_gaussianVector_of_polyBoundedPi A
    ((continuous_quartetW hβ hlam hρ i).measurable.mul
      (continuous_quartetW hβ hlam hρ j).measurable)
    ((polyBoundedPi_quartetW hβ hlam hρ i).mul (polyBoundedPi_quartetW hβ hlam hρ j))

theorem integrable_quartetQ (b : Matrix (Fin m) (Fin m) ℝ) :
    Integrable (quartetQ β lam ρ b) (gaussianVector A) :=
  integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => by
    have := (integrable_quartetW_mul hβ hlam hρ A i j).const_mul (b i j)
    refine this.congr (Filter.Eventually.of_forall fun g => ?_)
    ring

theorem integrable_quartetV (b : Matrix (Fin m) (Fin m) ℝ) (c : ℝ) :
    Integrable (quartetV β lam ρ b c) (gaussianVector A) :=
  ((integrable_quartetM2 hβ hlam hρ A).const_mul c).sub (integrable_quartetQ hβ hlam hρ A b)

omit hβ hlam hρ [Nonempty (Fin m)] in
/-- Evaluation of the derivative of `W_i` on the `j`-th basis vector. -/
theorem quartetW'_eval (i j : Fin m) (g : Fin m → ℝ) :
    (∑ k, quartetW' β lam ρ i k g • coordProj k : (Fin m → ℝ) →L[ℝ] ℝ) (Pi.single j 1) =
      quartetW' β lam ρ i j g := by
  simp [sum_apply, smul_apply, coordProj_apply, Pi.single_apply, Finset.sum_ite_eq']

/-- **Stein's identity for the posterior weights**: `E[G_i W_i(G)] = ∑_j b_{ij} E[∂_j W_i(G)]`. -/
theorem integral_coord_mul_quartetW (i : Fin m) :
    ∫ g, g i * quartetW β lam ρ i g ∂gaussianVector A =
      ∑ j, (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i j *
        ∫ g, quartetW' β lam ρ i j g ∂gaussianVector A := by
  have h := gaussianVector_stein A i (F := quartetW β lam ρ i)
    (F' := fun g => ∑ k, quartetW' β lam ρ i k g • coordProj k)
    (fun g => hasFDerivAt_quartetW hβ hlam hρ i g)
    (fun j => by simpa only [quartetW'_eval] using (continuous_quartetW' hβ hlam hρ i j).measurable)
    (polyBoundedPi_quartetW hβ hlam hρ i)
    (fun j => by simpa only [quartetW'_eval] using polyBoundedPi_quartetW' hβ hlam hρ i j)
  simpa only [quartetW'_eval] using h

/-- **Gaussian integration by parts for the quartet**: `E[H(G)] = β E[V(G)]` when the covariance
`A Aᵀ` has constant diagonal `c`. -/
theorem integral_quartetH_eq {c : ℝ}
    (hc : ∀ i, (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i i = c) :
    ∫ g, quartetH β lam ρ g ∂gaussianVector A =
      β * ∫ g, quartetV β lam ρ (A * A.transpose) c g ∂gaussianVector A := by
  set b : Matrix (Fin m) (Fin m) ℝ := A * A.transpose with hb
  -- `E[H] = ∑_i E[g_i W_i] = ∑_i ∑_j b_ij E[W'_ij]`
  have hH : ∫ g, quartetH β lam ρ g ∂gaussianVector A =
      ∑ i, ∑ j, b i j * ∫ g, quartetW' β lam ρ i j g ∂gaussianVector A := by
    unfold quartetH
    rw [integral_finsetSum _ fun i _ => integrable_coord_mul_quartetW hβ hlam hρ A i]
    exact Finset.sum_congr rfl fun i _ => integral_coord_mul_quartetW hβ hlam hρ A i
  -- `E[W'_ij] = β δ_ij E[R_i] − β E[W_i W_j]`
  have hW' : ∀ i j, ∫ g, quartetW' β lam ρ i j g ∂gaussianVector A =
      β * (if i = j then ∫ g, quartetR β lam ρ i g ∂gaussianVector A else 0) -
        β * ∫ g, quartetW β lam ρ i g * quartetW β lam ρ j g ∂gaussianVector A := by
    intro i j
    unfold quartetW'
    have h1 : Integrable (fun g => β * (if i = j then quartetR β lam ρ i g else 0))
        (gaussianVector A) := by
      by_cases h : i = j
      · simp only [h, if_true]; exact (integrable_quartetR hβ hlam hρ A j).const_mul β
      · simp only [h, if_false, mul_zero]; exact integrable_const 0
    have h2 : Integrable (fun g => β * quartetW β lam ρ i g * quartetW β lam ρ j g)
        (gaussianVector A) := by
      have := (integrable_quartetW_mul hβ hlam hρ A i j).const_mul β
      refine this.congr (Filter.Eventually.of_forall fun g => ?_); ring
    rw [integral_sub h1 h2]
    congr 1
    · by_cases h : i = j
      · simp only [h, if_true, integral_const_mul]
      · simp only [h, if_false, mul_zero, integral_zero]
    · rw [← integral_const_mul]
      congr 1; funext g; ring
  -- assemble
  rw [hH]
  simp_rw [hW']
  have hQ : ∫ g, quartetQ β lam ρ b g ∂gaussianVector A =
      ∑ i, ∑ j, b i j * ∫ g, quartetW β lam ρ i g * quartetW β lam ρ j g ∂gaussianVector A := by
    unfold quartetQ
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => by
      have := (integrable_quartetW_mul hβ hlam hρ A i j).const_mul (b i j)
      refine this.congr (Filter.Eventually.of_forall fun g => ?_); ring]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => by
      have := (integrable_quartetW_mul hβ hlam hρ A i j).const_mul (b i j)
      refine this.congr (Filter.Eventually.of_forall fun g => ?_); ring]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← integral_const_mul]
    congr 1; funext g; ring
  have hM : ∫ g, quartetM2 β lam ρ g ∂gaussianVector A =
      ∑ i, ∫ g, quartetR β lam ρ i g ∂gaussianVector A := by
    unfold quartetM2
    exact integral_finsetSum _ fun i _ => integrable_quartetR hβ hlam hρ A i
  unfold quartetV
  rw [integral_sub ((integrable_quartetM2 hβ hlam hρ A).const_mul c)
    (integrable_quartetQ hβ hlam hρ A b), integral_const_mul, hQ, hM, mul_sub, Finset.mul_sum,
    Finset.mul_sum]
  simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    if_true, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [hc i]; ring
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring

/-- **The self-normalised Gaussian quartet at finite resolution**: with the singular fluctuation
`ν := E[H(G)]/2`, for every `β, λ > 0`: `0 ≤ ν`, `E[V] = 2ν/β`, and `E[M₂] = λ/β + ν`. -/
theorem quartet_identities {c : ℝ}
    (hc : ∀ i, (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i i = c) :
    let ν := (∫ g, quartetH β lam ρ g ∂gaussianVector A) / 2
    0 ≤ ν ∧
      ∫ g, quartetV β lam ρ (A * A.transpose) c g ∂gaussianVector A = 2 * ν / β ∧
      ∫ g, quartetM2 β lam ρ g ∂gaussianVector A = lam / β + ν := by
  intro ν
  have hHV := integral_quartetH_eq hβ hlam hρ A hc
  have hVnn : 0 ≤ ∫ g, quartetV β lam ρ (A * A.transpose) c g ∂gaussianVector A :=
    integral_nonneg fun g => (quartetV_nonneg hβ hlam hρ A hc g).1
  refine ⟨?_, ?_, ?_⟩
  · have : 0 ≤ ∫ g, quartetH β lam ρ g ∂gaussianVector A := by rw [hHV]; positivity
    positivity
  · rw [show ν = (∫ g, quartetH β lam ρ g ∂gaussianVector A) / 2 from rfl, hHV]
    field_simp
  · have hpt : ∀ g, quartetM2 β lam ρ g = lam / β + quartetH β lam ρ g / 2 :=
      fun g => quartetM2_eq hβ hlam hρ g
    simp_rw [hpt]
    rw [integral_add (integrable_const _) ((integrable_quartetH hβ hlam hρ A).div_const 2),
      integral_div, integral_const]
    simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
    rw [integral_div]

end Quartet

/-- **The Bayes-quartet algebra**: from the two-leg amplitude `λ/β + ν`, the training correction
`−2ν` and the predictive-variance correction `−E[V]/2 = −ν/β`, the four coefficients are
`λ/β + ν`, `λ/β − ν`, `(λ − ν)/β + ν`, `(λ − ν)/β − ν`. -/
theorem bayes_quartet (β lam ν EV : ℝ) (hβ : β ≠ 0) (hEV : EV = 2 * ν / β) :
    (lam / β + ν) - 2 * ν = lam / β - ν ∧
      (lam / β + ν) - EV / 2 = (lam - ν) / β + ν ∧
      (lam / β - ν) - EV / 2 = (lam - ν) / β - ν := by
  subst hEV
  refine ⟨by ring, ?_, ?_⟩ <;> · field_simp; ring

end Grammar
