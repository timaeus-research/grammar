/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.StripLocalExpansion
import Monomialize.Analytic.Structural.Terminal
import Monomialize.Analytic.BM89.BaseEndChart

/-!
# Analytic units of a monomial chart (towards the chart-level local theorem)

hironaka's `IsMonomialChart` records its phase unit `u` and Jacobian unit `v` as **continuous**
nonvanishing functions. For the analytic amplitude of a core presentation both must be analytic.

* The determinant is an analytic function on the endomorphisms of `ℝ^d` (`analyticAt_det`: it is
  the polynomial `∑_σ ε(σ) ∏_i L(e_i)_{σ i}` in the matrix entries, each entry a continuous linear
  functional of `L`), so the Jacobian `det Dφ` of an analytic chart is analytic
  (`analyticAt_det_fderiv`).
* hironaka's division lemma `analyticOnNhd_of_eq_continuousOn_mul_monomial` then upgrades both
  units to analytic ones (`MonomialChart.exists_analytic_unit`,
  `MonomialChart.exists_analytic_jacUnit`) — the phase unit on the open set where the chart maps
  into the analyticity domain of the phase.
* At a centre `y₀` the Jacobian monomial splits into the coordinates vanishing at `y₀` and a
  positive analytic factor absorbing the others (`absDet_eq_reducedJac_mul`,
  `reducedJac_pos`, `analyticAt_reducedJac`), the Jacobian analogue of `MonomialParity`'s reduced
  form.

Non-claims: no chart-level expansion yet; the phase unit is analytic only on `W ∩ φ⁻¹(U)`.
-/

open Set Filter Topology Monomialize.Analytic Monomialize.VolumeScaling

namespace Grammar

variable {d : ℕ}

/-! ### The determinant is analytic -/

/-- **The determinant is analytic** on the endomorphisms of `ℝ^d`. -/
theorem analyticAt_det (L₀ : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) :
    AnalyticAt ℝ (fun L : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) => L.det) L₀ := by
  classical
  have h : (fun L : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) => L.det) =
      ∑ σ : Equiv.Perm (Fin d), fun L : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) =>
        ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, L (Pi.single i 1) (σ i) := by
    funext L
    rw [Finset.sum_apply]
    unfold ContinuousLinearMap.det
    rw [← LinearMap.det_toMatrix', Matrix.det_apply']
    refine Finset.sum_congr rfl fun σ _ => ?_
    congr 1
  rw [h]
  refine Finset.analyticAt_sum _ fun σ _ => analyticAt_const.mul ?_
  have h3 : (fun L : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) => ∏ i, L (Pi.single i 1) (σ i)) =
      ∏ i : Fin d, fun L : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) => L (Pi.single i 1) (σ i) := by
    funext L
    rw [Finset.prod_apply]
  rw [h3]
  refine Finset.analyticAt_prod _ fun i _ => ?_
  exact ((ContinuousLinearMap.proj (σ i) : (Fin d → ℝ) →L[ℝ] ℝ).comp
    (ContinuousLinearMap.apply ℝ (Fin d → ℝ) (Pi.single i 1))).analyticAt L₀

/-- The Jacobian of an analytic map is analytic. -/
theorem analyticAt_det_fderiv {φ : (Fin d → ℝ) → (Fin d → ℝ)} {y : Fin d → ℝ}
    (hφ : AnalyticAt ℝ φ y) : AnalyticAt ℝ (fun y => (fderiv ℝ φ y).det) y :=
  (analyticAt_det _).comp hφ.fderiv

theorem analyticOnNhd_det_fderiv {φ : (Fin d → ℝ) → (Fin d → ℝ)} {W : Set (Fin d → ℝ)}
    (hφ : AnalyticOnNhd ℝ φ W) : AnalyticOnNhd ℝ (fun y => (fderiv ℝ φ y).det) W :=
  fun y hy => analyticAt_det_fderiv (hφ y hy)

/-! ### Analytic units of a monomial chart -/

namespace MonomialChart

variable {K : (Fin d → ℝ) → ℝ} {φ : (Fin d → ℝ) → (Fin d → ℝ)} {dom : Set (Fin d → ℝ)}
  {e h : Fin d →₀ ℕ} {W : Set (Fin d → ℝ)}

/-- The chart maps the open set `W ∩ φ⁻¹(U)` into the analyticity domain `U` of the phase. -/
theorem isOpen_inter_preimage (hc : IsMonomialChart K φ dom e h W) {U : Set (Fin d → ℝ)}
    (hU : IsOpen U) : IsOpen (W ∩ φ ⁻¹' U) :=
  hc.analyticOnNhd.continuousOn.isOpen_inter_preimage hc.isOpen hU

/-- **The analytic phase unit**: on `W ∩ φ⁻¹(U)` the unit of `K∘φ = u · y^e` is analytic. -/
theorem exists_analytic_unit (hc : IsMonomialChart K φ dom e h W) {U : Set (Fin d → ℝ)}
    (hU : IsOpen U) (hK : AnalyticOnNhd ℝ K U) :
    ∃ u : (Fin d → ℝ) → ℝ, AnalyticOnNhd ℝ u (W ∩ φ ⁻¹' U) ∧ (∀ y ∈ W ∩ φ ⁻¹' U, u y ≠ 0) ∧
      ∀ y ∈ W ∩ φ ⁻¹' U, K (φ y) = u y * monomialEval y e := by
  obtain ⟨u, hu, hu0, hKu⟩ := hc.exists_unit
  refine ⟨u, ?_, fun y hy => hu0 y hy.1, fun y hy => hKu y hy.1⟩
  refine analyticOnNhd_of_eq_continuousOn_mul_monomial (isOpen_inter_preimage hc hU)
    (hu.mono inter_subset_left) e (fun y => K (φ y)) (fun y hy => ?_) (fun y hy => hKu y hy.1)
  exact (hK _ hy.2).comp (hc.analyticOnNhd y hy.1)

/-- **The analytic Jacobian unit**: the unit of `det Dφ = v · y^h` is analytic on `W`. -/
theorem exists_analytic_jacUnit (hc : IsMonomialChart K φ dom e h W) :
    ∃ v : (Fin d → ℝ) → ℝ, AnalyticOnNhd ℝ v W ∧ (∀ y ∈ W, v y ≠ 0) ∧
      ∀ y ∈ W, (fderiv ℝ φ y).det = v y * monomialEval y h := by
  obtain ⟨v, hv, hv0, hdet⟩ := hc.exists_jacUnit
  refine ⟨v, ?_, hv0, hdet⟩
  exact analyticOnNhd_of_eq_continuousOn_mul_monomial hc.isOpen hv h _
    (analyticOnNhd_det_fderiv hc.analyticOnNhd) hdet

end MonomialChart

/-! ### The reduced Jacobian at a centre -/

open scoped Classical in
/-- The reduced Jacobian factor at the centre `y₀`: `|v| · ∏_{y₀_j ≠ 0} |y_j|^{h_j}`. -/
noncomputable def reducedJac (v : (Fin d → ℝ) → ℝ) (h : Fin d →₀ ℕ) (y₀ y : Fin d → ℝ) : ℝ :=
  |v y| * ∏ j ∈ Finset.univ.filter (fun j => y₀ j ≠ 0), |y j| ^ h j

theorem prod_abs_pow_reducedExp (h : Fin d →₀ ℕ) (y₀ y : Fin d → ℝ) :
    ∏ j, |y j| ^ reducedExp h y₀ j =
      ∏ j ∈ Finset.univ.filter (fun j => y₀ j = 0), |y j| ^ h j := by
  classical
  rw [Finset.prod_filter]
  refine Finset.prod_congr rfl fun j _ => ?_
  by_cases hj : y₀ j = 0
  · simp [reducedExp_apply_of_eq hj, hj]
  · simp [reducedExp_apply_of_ne hj, hj]

/-- `|det Dφ| = reducedJac · ∏_j |y_j|^{h'_j}` with `h'` the exponents at the coordinates vanishing
at the centre. -/
theorem absDet_eq_reducedJac_mul {φ : (Fin d → ℝ) → (Fin d → ℝ)} {v : (Fin d → ℝ) → ℝ}
    {h : Fin d →₀ ℕ} {y₀ y : Fin d → ℝ} (hdet : (fderiv ℝ φ y).det = v y * monomialEval y h) :
    |(fderiv ℝ φ y).det| = reducedJac v h y₀ y * ∏ j, |y j| ^ (reducedExp h y₀ j) := by
  classical
  rw [hdet, abs_mul, monomialEval_eq_prod, Finset.abs_prod, prod_abs_pow_reducedExp, reducedJac,
    mul_assoc]
  congr 1
  rw [Finset.prod_congr rfl fun j _ => abs_pow (y j) (h j),
    ← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun j => y₀ j ≠ 0)]
  congr 1
  refine Finset.prod_congr ?_ fun _ _ => rfl
  ext j
  simp

theorem reducedJac_pos {v : (Fin d → ℝ) → ℝ} (h : Fin d →₀ ℕ) {y₀ : Fin d → ℝ} (hv0 : v y₀ ≠ 0) :
    0 < reducedJac v h y₀ y₀ := by
  classical
  exact mul_pos (abs_pos.2 hv0)
    (Finset.prod_pos fun j hj => pow_pos (abs_pos.2 (Finset.mem_filter.1 hj).2) _)

/-- The absolute value of an analytic function is analytic where the function does not vanish. -/
theorem analyticAt_abs_of_ne_zero {g : (Fin d → ℝ) → ℝ} {y₀ : Fin d → ℝ} (hg : AnalyticAt ℝ g y₀)
    (hg0 : g y₀ ≠ 0) : AnalyticAt ℝ (fun y => |g y|) y₀ := by
  rcases lt_or_gt_of_ne hg0 with hneg | hpos
  · refine hg.neg.congr ?_
    filter_upwards [hg.continuousAt (Iio_mem_nhds hneg)] with y hy
    simp only [Pi.neg_apply]
    exact (abs_of_neg hy).symm
  · refine hg.congr ?_
    filter_upwards [hg.continuousAt (Ioi_mem_nhds hpos)] with y hy
    exact (abs_of_pos hy).symm

theorem analyticAt_reducedJac {v : (Fin d → ℝ) → ℝ} (h : Fin d →₀ ℕ) {y₀ : Fin d → ℝ}
    (hv : AnalyticAt ℝ v y₀) (hv0 : v y₀ ≠ 0) : AnalyticAt ℝ (reducedJac v h y₀) y₀ := by
  classical
  have hprod : AnalyticAt ℝ (∏ j ∈ Finset.univ.filter (fun j => y₀ j ≠ 0),
      fun y : Fin d → ℝ => |y j| ^ h j) y₀ := by
    refine Finset.analyticAt_prod _ fun j hj => ?_
    exact (analyticAt_abs_of_ne_zero
      ((ContinuousLinearMap.proj j : (Fin d → ℝ) →L[ℝ] ℝ).analyticAt y₀)
      (Finset.mem_filter.1 hj).2).pow _
  have h2 : AnalyticAt ℝ (fun y : Fin d → ℝ =>
      ∏ j ∈ Finset.univ.filter (fun j => y₀ j ≠ 0), |y j| ^ h j) y₀ :=
    hprod.congr (Filter.Eventually.of_forall fun y => by simp [Finset.prod_apply])
  exact (analyticAt_abs_of_ne_zero hv hv0).mul h2

end Grammar
