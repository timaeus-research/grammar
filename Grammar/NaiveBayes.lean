/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# The two-leaf naive Bayes model: moment coordinates and the label symmetry

Parameters `θ = (t, (a₁, b₁), (a₂, b₂))`: `t = P(H = 1)`, `aᵢ = P(Xᵢ = 1 | H = 0)`,
`bᵢ = P(Xᵢ = 1 | H = 1)`, for a hidden binary class `H` and two binary leaves.  The cell
probabilities `p_θ(x₁, x₂)` are polynomials in the moment coordinates
`λᵢ = (1 − t)aᵢ + t bᵢ` (the means), `ηᵢ = bᵢ − aᵢ` and `μ = t(1 − t)η₁η₂` (the covariance):

  `p(1,1) = λ₁λ₂ + μ`, `p(1,0) = λ₁(1 − λ₂) − μ`, `p(0,1) = (1 − λ₁)λ₂ − μ`,
  `p(0,0) = (1 − λ₁)(1 − λ₂) + μ`   (`nbCell_true_true`, …)

so the likelihood of a sample factors through the moment map `θ ↦ (t, (λ₁, η₁), (λ₂, η₂))`.
Two measure-theoretic facts about this map are proved (examples_slop §5):

* ★★ `measurePreserving_nbMomentMap`: the moment map preserves Lebesgue measure on the parameter
  space (for fixed `t` the map `(a, b) ↦ ((1 − t)a + t b, b − a)` is a shear of determinant one),
  and hence pushes the uniform prior on the cube to Lebesgue measure on the image region
  (`map_nbMomentMap_restrict_nbBox`); the pushforward density of the prior along the
  observable moments `(λ₁, λ₂, μ)` is therefore a fibre volume of `μ = t(1 − t)η₁η₂`.
* ★★ `integral_fst_nbLik`: the label involution `(t, a, b) ↦ (1 − t, b, a)` fixes every cell
  probability and preserves the prior, so for every sample and every sample size the posterior
  mean of the class probability `t` is exactly `1/2`, and every label-antisymmetric observable
  has posterior mean zero (`integral_nbLik_antisymm`).
* The Fisher information of the saturated model in moment coordinates at an independent truth is
  `diag(1/v₁, 1/v₂, 1/(v₁v₂))` (`nbFisher_mu_mu`, `nbFisher_l₁_mu`, …), and the cubic coefficient
  of the phase in the covariance direction is `V² Σ_x s_x/p*(x)² = (1 − 2λ₁)(1 − 2λ₂)`
  (`nbCubic_mu`): the data of the leading Laplace expansion and of its `N^{−2}` correction.

Zero `sorry`/`axiom`.
-/

open MeasureTheory Set

namespace Grammar

/-- Parameters `(t, (a₁, b₁), (a₂, b₂))` of the two-leaf naive Bayes model. -/
abbrev NBParam := ℝ × (ℝ × ℝ) × (ℝ × ℝ)

/-- The Bernoulli weight `p^x (1 − p)^{1 − x}`. -/
def bern (p : ℝ) (x : Bool) : ℝ := if x then p else 1 - p

/-- The cell probability `p_θ(x₁, x₂) = (1 − t) a₁^{x₁}… + t b₁^{x₁}…`. -/
def nbCell (θ : NBParam) (x : Bool × Bool) : ℝ :=
  (1 - θ.1) * bern θ.2.1.1 x.1 * bern θ.2.2.1 x.2 + θ.1 * bern θ.2.1.2 x.1 * bern θ.2.2.2 x.2

/-- The mean of the first leaf, `λ₁ = (1 − t)a₁ + t b₁`. -/
def nbMean₁ (θ : NBParam) : ℝ := (1 - θ.1) * θ.2.1.1 + θ.1 * θ.2.1.2

/-- The mean of the second leaf, `λ₂ = (1 − t)a₂ + t b₂`. -/
def nbMean₂ (θ : NBParam) : ℝ := (1 - θ.1) * θ.2.2.1 + θ.1 * θ.2.2.2

/-- The edge effect of the first leaf, `η₁ = b₁ − a₁`. -/
def nbEta₁ (θ : NBParam) : ℝ := θ.2.1.2 - θ.2.1.1

/-- The edge effect of the second leaf, `η₂ = b₂ − a₂`. -/
def nbEta₂ (θ : NBParam) : ℝ := θ.2.2.2 - θ.2.2.1

/-- The covariance of the two leaves, `μ = t(1 − t)η₁η₂`. -/
def nbCov (θ : NBParam) : ℝ := θ.1 * (1 - θ.1) * nbEta₁ θ * nbEta₂ θ

theorem nbCell_true_true (θ : NBParam) :
    nbCell θ (true, true) = nbMean₁ θ * nbMean₂ θ + nbCov θ := by
  simp only [nbCell, bern, nbMean₁, nbMean₂, nbCov, nbEta₁, nbEta₂, if_true]; ring

theorem nbCell_true_false (θ : NBParam) :
    nbCell θ (true, false) = nbMean₁ θ * (1 - nbMean₂ θ) - nbCov θ := by
  simp only [nbCell, bern, nbMean₁, nbMean₂, nbCov, nbEta₁, nbEta₂, if_true, Bool.false_eq_true,
    if_false]; ring

theorem nbCell_false_true (θ : NBParam) :
    nbCell θ (false, true) = (1 - nbMean₁ θ) * nbMean₂ θ - nbCov θ := by
  simp only [nbCell, bern, nbMean₁, nbMean₂, nbCov, nbEta₁, nbEta₂, if_true, Bool.false_eq_true,
    if_false]; ring

theorem nbCell_false_false (θ : NBParam) :
    nbCell θ (false, false) = (1 - nbMean₁ θ) * (1 - nbMean₂ θ) + nbCov θ := by
  simp only [nbCell, bern, nbMean₁, nbMean₂, nbCov, nbEta₁, nbEta₂, Bool.false_eq_true,
    if_false]; ring

/-- The cell probabilities sum to one. -/
theorem sum_nbCell (θ : NBParam) : ∑ x : Bool × Bool, nbCell θ x = 1 := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, nbCell_true_true, nbCell_true_false,
    nbCell_false_true, nbCell_false_false]; ring

/-- The first mean is the first marginal. -/
theorem nbMean₁_eq (θ : NBParam) : nbMean₁ θ = nbCell θ (true, true) + nbCell θ (true, false) := by
  rw [nbCell_true_true, nbCell_true_false]; ring

/-- The second mean is the second marginal. -/
theorem nbMean₂_eq (θ : NBParam) : nbMean₂ θ = nbCell θ (true, true) + nbCell θ (false, true) := by
  rw [nbCell_true_true, nbCell_false_true]; ring

/-- The covariance parameter is the covariance of the leaves. -/
theorem nbCov_eq (θ : NBParam) : nbCov θ = nbCell θ (true, true) - nbMean₁ θ * nbMean₂ θ := by
  rw [nbCell_true_true]; ring

theorem continuous_nbCell (x : Bool × Bool) : Continuous fun θ : NBParam => nbCell θ x := by
  obtain ⟨x₁, x₂⟩ := x
  cases x₁ <;> cases x₂ <;> simp only [nbCell, bern, Bool.false_eq_true, if_false, if_true] <;>
    fun_prop

/-- The likelihood of a sample with cell counts `c`. -/
def nbLik (c : Bool × Bool → ℕ) (θ : NBParam) : ℝ := ∏ x, nbCell θ x ^ c x

theorem continuous_nbLik (c : Bool × Bool → ℕ) : Continuous (nbLik c) :=
  continuous_finsetProd _ fun x _ => (continuous_nbCell x).pow _

/-! ### The label involution -/

/-- The label involution `(t, a, b) ↦ (1 − t, b, a)`. -/
def nbSwap (θ : NBParam) : NBParam := (1 - θ.1, (θ.2.1.2, θ.2.1.1), (θ.2.2.2, θ.2.2.1))

@[simp] theorem nbSwap_nbSwap (θ : NBParam) : nbSwap (nbSwap θ) = θ := by
  simp [nbSwap]

theorem nbCell_nbSwap (θ : NBParam) (x : Bool × Bool) : nbCell (nbSwap θ) x = nbCell θ x := by
  simp only [nbCell, nbSwap]; ring

theorem nbLik_nbSwap (c : Bool × Bool → ℕ) (θ : NBParam) : nbLik c (nbSwap θ) = nbLik c θ := by
  simp only [nbLik, nbCell_nbSwap]

theorem nbMean₁_nbSwap (θ : NBParam) : nbMean₁ (nbSwap θ) = nbMean₁ θ := by
  simp only [nbMean₁, nbSwap]; ring

theorem nbMean₂_nbSwap (θ : NBParam) : nbMean₂ (nbSwap θ) = nbMean₂ θ := by
  simp only [nbMean₂, nbSwap]; ring

theorem nbCov_nbSwap (θ : NBParam) : nbCov (nbSwap θ) = nbCov θ := by
  simp only [nbCov, nbEta₁, nbEta₂, nbSwap]; ring

theorem measurable_nbSwap : Measurable nbSwap := by
  unfold nbSwap; fun_prop

/-- The label involution as a measurable equivalence. -/
def nbSwapEquiv : NBParam ≃ᵐ NBParam where
  toFun := nbSwap
  invFun := nbSwap
  left_inv := nbSwap_nbSwap
  right_inv := nbSwap_nbSwap
  measurable_toFun := measurable_nbSwap
  measurable_invFun := measurable_nbSwap

theorem nbSwap_eq_prodMap :
    nbSwap = Prod.map (fun t : ℝ => 1 - t) (Prod.map Prod.swap Prod.swap) := rfl

/-- The label involution preserves Lebesgue measure. -/
theorem measurePreserving_nbSwap : MeasurePreserving nbSwap volume volume := by
  rw [nbSwap_eq_prodMap]
  exact (Measure.measurePreserving_sub_left volume 1).prod
    (Measure.measurePreserving_swap.prod Measure.measurePreserving_swap)

/-- The prior region: the unit cube. -/
def nbBox : Set NBParam :=
  Icc (0 : ℝ) 1 ×ˢ ((Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ×ˢ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1))

theorem measurableSet_nbBox : MeasurableSet nbBox :=
  measurableSet_Icc.prod ((measurableSet_Icc.prod measurableSet_Icc).prod
    (measurableSet_Icc.prod measurableSet_Icc))

theorem isCompact_nbBox : IsCompact nbBox :=
  isCompact_Icc.prod ((isCompact_Icc.prod isCompact_Icc).prod (isCompact_Icc.prod isCompact_Icc))

theorem nbSwap_preimage_nbBox : nbSwap ⁻¹' nbBox = nbBox := by
  ext θ
  simp only [mem_preimage, nbBox, nbSwap, mem_prod, mem_Icc]
  constructor <;>
    rintro ⟨⟨h1, h2⟩, ⟨⟨h3, h4⟩, ⟨h5, h6⟩⟩, ⟨⟨h7, h8⟩, ⟨h9, h10⟩⟩⟩ <;>
    refine ⟨⟨?_, ?_⟩, ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩⟩ <;> linarith

/-- Integrals over the cube are invariant under the label involution. -/
theorem setIntegral_nbSwap (f : NBParam → ℝ) :
    ∫ θ in nbBox, f (nbSwap θ) = ∫ θ in nbBox, f θ := by
  have h := measurePreserving_nbSwap.restrict_preimage measurableSet_nbBox
  rw [nbSwap_preimage_nbBox] at h
  exact h.integral_comp nbSwapEquiv.measurableEmbedding f

/-- ★★ A label-antisymmetric observable has posterior mean zero, for every sample. -/
theorem integral_nbLik_antisymm (c : Bool × Bool → ℕ) (f : NBParam → ℝ)
    (hf : ∀ θ, f (nbSwap θ) = -f θ) : ∫ θ in nbBox, f θ * nbLik c θ = 0 := by
  have h := setIntegral_nbSwap (fun θ => f θ * nbLik c θ)
  simp only [hf, nbLik_nbSwap, neg_mul, integral_neg] at h
  linarith

/-- ★★ The posterior mean of the class probability is exactly `1/2` for every sample. -/
theorem integral_fst_nbLik (c : Bool × Bool → ℕ) :
    ∫ θ in nbBox, θ.1 * nbLik c θ = (1 / 2) * ∫ θ in nbBox, nbLik c θ := by
  have h := integral_nbLik_antisymm c (fun θ => θ.1 - 1 / 2) (by intro θ; simp [nbSwap]; ring)
  beta_reduce at h
  have hℓ : IntegrableOn (nbLik c) nbBox :=
    (continuous_nbLik c).continuousOn.integrableOn_compact isCompact_nbBox
  have ht : IntegrableOn (fun θ : NBParam => θ.1 * nbLik c θ) nbBox :=
    (continuous_fst.mul (continuous_nbLik c)).continuousOn.integrableOn_compact isCompact_nbBox
  have hsplit : ∫ θ in nbBox, (θ.1 - 1 / 2) * nbLik c θ =
      (∫ θ in nbBox, θ.1 * nbLik c θ) - ∫ θ in nbBox, (1 / 2) * nbLik c θ := by
    rw [← integral_sub ht (hℓ.const_mul _)]
    congr 1; funext θ; ring
  rw [integral_const_mul] at hsplit
  linarith

/-- The posterior mean of `t` is `1/2` (ratio form). -/
theorem nbPosteriorMean_fst (c : Bool × Bool → ℕ) (hZ : ∫ θ in nbBox, nbLik c θ ≠ 0) :
    (∫ θ in nbBox, θ.1 * nbLik c θ) / ∫ θ in nbBox, nbLik c θ = 1 / 2 := by
  rw [integral_fst_nbLik, mul_div_assoc, div_self hZ, mul_one]

/-! ### The moment map preserves Lebesgue measure -/

/-- For fixed `t`, the leaf map `(a, b) ↦ ((1 − t)a + t b, b − a)` (mean, edge effect). -/
def nbLeafMap (t : ℝ) (ab : ℝ × ℝ) : ℝ × ℝ := ((1 - t) * ab.1 + t * ab.2, ab.2 - ab.1)

/-- The leaf map is a shear of determinant one: it preserves Lebesgue measure. -/
theorem measurePreserving_nbLeafMap (t : ℝ) : MeasurePreserving (nbLeafMap t) volume volume := by
  have h1 : MeasurePreserving (fun z : ℝ × ℝ => (z.1, z.2 - z.1)) volume volume :=
    measurePreserving_prod_sub volume volume
  have h2 : MeasurePreserving (fun z : ℝ × ℝ => (z.1, z.2 + t * z.1)) volume volume :=
    (MeasurePreserving.id (volume : Measure ℝ)).skew_product (g := fun η a => a + t * η)
      (by fun_prop) (Filter.Eventually.of_forall fun η => map_add_right_eq_self volume (t * η))
  have hsw : MeasurePreserving (Prod.swap : ℝ × ℝ → ℝ × ℝ) volume volume :=
    Measure.measurePreserving_swap
  have h3 := hsw.comp (h2.comp (hsw.comp h1))
  convert h3 using 1
  ext ab <;> simp [nbLeafMap, Function.comp]; ring

/-- The moment map `θ ↦ (t, (λ₁, η₁), (λ₂, η₂))`. -/
def nbMomentMap (θ : NBParam) : NBParam := (θ.1, nbLeafMap θ.1 θ.2.1, nbLeafMap θ.1 θ.2.2)

theorem nbMomentMap_apply (θ : NBParam) :
    nbMomentMap θ = (θ.1, (nbMean₁ θ, nbEta₁ θ), (nbMean₂ θ, nbEta₂ θ)) := rfl

/-- ★★ The moment map preserves Lebesgue measure on the parameter space. -/
theorem measurePreserving_nbMomentMap : MeasurePreserving nbMomentMap volume volume := by
  have := (MeasurePreserving.id (volume : Measure ℝ)).skew_product
    (g := fun t (ab : (ℝ × ℝ) × (ℝ × ℝ)) => (nbLeafMap t ab.1, nbLeafMap t ab.2))
    (by unfold nbLeafMap; fun_prop)
    (Filter.Eventually.of_forall fun t =>
      ((measurePreserving_nbLeafMap t).prod (measurePreserving_nbLeafMap t)).map_eq)
  exact this

/-- The inverse of the moment map: `(t, (λ, η)) ↦ (t, (λ − tη, λ + (1 − t)η))`. -/
def nbMomentInv (ζ : NBParam) : NBParam :=
  (ζ.1, (ζ.2.1.1 - ζ.1 * ζ.2.1.2, ζ.2.1.1 + (1 - ζ.1) * ζ.2.1.2),
    (ζ.2.2.1 - ζ.1 * ζ.2.2.2, ζ.2.2.1 + (1 - ζ.1) * ζ.2.2.2))

theorem nbMomentInv_nbMomentMap (θ : NBParam) : nbMomentInv (nbMomentMap θ) = θ := by
  simp only [nbMomentInv, nbMomentMap, nbLeafMap]
  ext <;> simp <;> ring

theorem nbMomentMap_nbMomentInv (ζ : NBParam) : nbMomentMap (nbMomentInv ζ) = ζ := by
  simp only [nbMomentInv, nbMomentMap, nbLeafMap]
  ext <;> simp <;> ring

theorem measurable_nbMomentMap : Measurable nbMomentMap := by
  unfold nbMomentMap nbLeafMap; fun_prop

theorem measurable_nbMomentInv : Measurable nbMomentInv := by
  unfold nbMomentInv; fun_prop

/-- The moment map as a measurable equivalence. -/
def nbMomentEquiv : NBParam ≃ᵐ NBParam where
  toFun := nbMomentMap
  invFun := nbMomentInv
  left_inv := nbMomentInv_nbMomentMap
  right_inv := nbMomentMap_nbMomentInv
  measurable_toFun := measurable_nbMomentMap
  measurable_invFun := measurable_nbMomentInv

/-- ★★ The uniform prior on the cube pushes forward along the moment map to Lebesgue measure on
the image region. -/
theorem map_nbMomentMap_restrict_nbBox :
    Measure.map nbMomentMap (volume.restrict nbBox) = volume.restrict (nbMomentMap '' nbBox) :=
  (measurePreserving_nbMomentMap.restrict_image_emb nbMomentEquiv.measurableEmbedding nbBox).map_eq

/-- The image of the cube under the moment map: `t ∈ [0,1]` and, for each leaf,
`λ − tη ∈ [0,1]` and `λ + (1 − t)η ∈ [0,1]`. -/
theorem nbMomentMap_image_nbBox : nbMomentMap '' nbBox = nbMomentInv ⁻¹' nbBox :=
  congrFun (Set.image_eq_preimage_of_inverse nbMomentInv_nbMomentMap nbMomentMap_nbMomentInv) nbBox

/-! ### The cells as polynomials in the moments, and the Fisher information at an independent
truth -/

/-- The sign pattern `(+, −, −, +)` of the covariance in the four cells. -/
def nbSign : Bool × Bool → ℝ
  | (true, true) => 1
  | (false, false) => 1
  | (true, false) => -1
  | (false, true) => -1

@[simp] theorem bern_true (p : ℝ) : bern p true = p := rfl
@[simp] theorem bern_false (p : ℝ) : bern p false = 1 - p := rfl

/-- The cell probabilities as polynomials in the moment coordinates `(λ₁, λ₂, μ)`. -/
def nbCellY (l₁ l₂ μ : ℝ) (x : Bool × Bool) : ℝ :=
  bern l₁ x.1 * bern l₂ x.2 + nbSign x * μ

/-- The likelihood factors through the moment map. -/
theorem nbCell_eq_nbCellY (θ : NBParam) (x : Bool × Bool) :
    nbCell θ x = nbCellY (nbMean₁ θ) (nbMean₂ θ) (nbCov θ) x := by
  obtain ⟨x₁, x₂⟩ := x
  cases x₁ <;> cases x₂ <;>
    simp only [nbCellY, nbSign, bern_true, bern_false, nbCell_true_true, nbCell_true_false,
      nbCell_false_true, nbCell_false_false] <;> ring

/-- The `λ₁`-derivative of the cells: `(λ₂, 1 − λ₂, −λ₂, −(1 − λ₂))`. -/
def nbDl₁ (l₂ : ℝ) (x : Bool × Bool) : ℝ := (if x.1 then 1 else -1) * bern l₂ x.2

/-- The `λ₂`-derivative of the cells: `(λ₁, −λ₁, 1 − λ₁, −(1 − λ₁))`. -/
def nbDl₂ (l₁ : ℝ) (x : Bool × Bool) : ℝ := bern l₁ x.1 * (if x.2 then 1 else -1)

theorem hasDerivAt_nbCellY_mu (l₁ l₂ μ : ℝ) (x : Bool × Bool) :
    HasDerivAt (fun μ => nbCellY l₁ l₂ μ x) (nbSign x) μ := by
  have h := ((hasDerivAt_id μ).const_mul (nbSign x)).const_add (bern l₁ x.1 * bern l₂ x.2)
  simpa [nbCellY] using h

theorem hasDerivAt_nbCellY_l₁ (l₁ l₂ μ : ℝ) (x : Bool × Bool) :
    HasDerivAt (fun l₁ => nbCellY l₁ l₂ μ x) (nbDl₁ l₂ x) l₁ := by
  obtain ⟨x₁, x₂⟩ := x
  cases x₁
  · have h := (((hasDerivAt_id l₁).const_sub 1).mul_const (bern l₂ x₂)).add_const
      (nbSign (false, x₂) * μ)
    simpa [nbCellY, nbDl₁] using h
  · have h := ((hasDerivAt_id l₁).mul_const (bern l₂ x₂)).add_const (nbSign (true, x₂) * μ)
    simpa [nbCellY, nbDl₁] using h

theorem hasDerivAt_nbCellY_l₂ (l₁ l₂ μ : ℝ) (x : Bool × Bool) :
    HasDerivAt (fun l₂ => nbCellY l₁ l₂ μ x) (nbDl₂ l₁ x) l₂ := by
  obtain ⟨x₁, x₂⟩ := x
  cases x₂
  · have h := (((hasDerivAt_id l₂).const_sub 1).const_mul (bern l₁ x₁)).add_const
      (nbSign (x₁, false) * μ)
    simpa [nbCellY, nbDl₂] using h
  · have h := ((hasDerivAt_id l₂).const_mul (bern l₁ x₁)).add_const (nbSign (x₁, true) * μ)
    simpa [nbCellY, nbDl₂] using h

section Fisher

variable {l₁ l₂ : ℝ} (h₁ : 0 < l₁) (h₁' : l₁ < 1) (h₂ : 0 < l₂) (h₂' : l₂ < 1)
include h₁ h₁' h₂ h₂'

/-- The `(μ, μ)` entry of the Fisher information at an independent truth is `1/(v₁v₂)`. -/
theorem nbFisher_mu_mu :
    ∑ x : Bool × Bool, nbSign x * nbSign x / nbCellY l₁ l₂ 0 x =
      1 / (l₁ * (1 - l₁) * (l₂ * (1 - l₂))) := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, nbCellY, nbSign, bern_true, bern_false,
    mul_zero, add_zero]
  have := sub_pos.mpr h₁'; have := sub_pos.mpr h₂'
  field_simp; ring

/-- The `(λ₁, μ)` entry of the Fisher information at an independent truth vanishes. -/
theorem nbFisher_l₁_mu :
    ∑ x : Bool × Bool, nbDl₁ l₂ x * nbSign x / nbCellY l₁ l₂ 0 x = 0 := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, nbCellY, nbSign, nbDl₁, bern_true,
    bern_false, mul_zero, add_zero, if_true, Bool.false_eq_true, if_false]
  have := sub_pos.mpr h₁'; have := sub_pos.mpr h₂'
  field_simp; ring

/-- The `(λ₂, μ)` entry of the Fisher information at an independent truth vanishes. -/
theorem nbFisher_l₂_mu :
    ∑ x : Bool × Bool, nbDl₂ l₁ x * nbSign x / nbCellY l₁ l₂ 0 x = 0 := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, nbCellY, nbSign, nbDl₂, bern_true,
    bern_false, mul_zero, add_zero, if_true, Bool.false_eq_true, if_false]
  have := sub_pos.mpr h₁'; have := sub_pos.mpr h₂'
  field_simp; ring

/-- The `(λ₁, λ₂)` entry of the Fisher information at an independent truth vanishes. -/
theorem nbFisher_l₁_l₂ :
    ∑ x : Bool × Bool, nbDl₁ l₂ x * nbDl₂ l₁ x / nbCellY l₁ l₂ 0 x = 0 := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, nbCellY, nbSign, nbDl₁, nbDl₂,
    bern_true, bern_false, mul_zero, add_zero, if_true, Bool.false_eq_true, if_false]
  have := sub_pos.mpr h₁'; have := sub_pos.mpr h₂'
  field_simp; ring

omit h₂ in
/-- The `(λ₁, λ₁)` entry of the Fisher information at an independent truth is `1/v₁`. -/
theorem nbFisher_l₁_l₁ :
    ∑ x : Bool × Bool, nbDl₁ l₂ x * nbDl₁ l₂ x / nbCellY l₁ l₂ 0 x = 1 / (l₁ * (1 - l₁)) := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, nbCellY, nbSign, nbDl₁, bern_true,
    bern_false, mul_zero, add_zero, if_true, Bool.false_eq_true, if_false]
  have := sub_pos.mpr h₁'; have := sub_pos.mpr h₂'
  field_simp; ring

omit h₁ in
/-- The `(λ₂, λ₂)` entry of the Fisher information at an independent truth is `1/v₂`. -/
theorem nbFisher_l₂_l₂ :
    ∑ x : Bool × Bool, nbDl₂ l₁ x * nbDl₂ l₁ x / nbCellY l₁ l₂ 0 x = 1 / (l₂ * (1 - l₂)) := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, nbCellY, nbSign, nbDl₂, bern_true,
    bern_false, mul_zero, add_zero, if_true, Bool.false_eq_true, if_false]
  have := sub_pos.mpr h₁'; have := sub_pos.mpr h₂'
  field_simp; ring

/-- The cubic coefficient of the phase in the covariance direction:
`V² Σ_x s_x / p*(x)² = (1 − 2λ₁)(1 − 2λ₂)`. -/
theorem nbCubic_mu :
    (l₁ * (1 - l₁) * (l₂ * (1 - l₂))) ^ 2 *
      ∑ x : Bool × Bool, nbSign x / nbCellY l₁ l₂ 0 x ^ 2 = (1 - 2 * l₁) * (1 - 2 * l₂) := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, nbCellY, nbSign, bern_true, bern_false,
    mul_zero, add_zero]
  have := sub_pos.mpr h₁'; have := sub_pos.mpr h₂'
  field_simp; ring

end Fisher

end Grammar
