/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.ProductChartHypotheses

/-!
# The uniform piece atlases of a product chart and the end-to-end leading-term theorem

Units 2–3 of consult #78 (`tide-log/gpt6_bigpicture_v78.md`). For a `ProductMonomialChart`, the
hypotheses of the piece constructor CCXXXVIII hold for EVERY nonempty stratum `I ⊆ supp e` with a
common threshold `ε ≤ b`: the foot set `T'_I` is closed, the domain is fibre-saturated on the piece,
the cover weight is fibre-constant with the measurable bounded factor `r ∘ P_J`, the unit is
normal-independent, and the inactive base supplies the zero point
(`ProductMonomialChart.exists_pieceAtlas`). Choosing an atlas for each piece once
(`ProductMonomialChart.pieceAtlas'`, with its cell pair recorded, `pieceAtlas'_cell_lam/_mult`)
gives the uniform family `productAtlases` for a cover all of whose charts are product charts, and
the conditional global theorem becomes the **end-to-end theorem**
`hasLeadingTerm_boltzmannIntegral_of_productCharts`: the resolved Boltzmann integral of such a cover
has the leading-term certificate at any pair `(λ₀, k₀)` dominating every chart–stratum pair
`(min_a (h_{ν(a)}+1)/(2k_a), #min − 1)`, with coefficient the sum over all chart–stratum pairs
of the
tied cell coefficients — under geometric hypotheses only (product domains, normal-independent
units, factored cover weights, continuous pulled-back observable and prior).

Non-claims: the coefficient may be zero (the pair is the geometric extremal pair once identified,
not necessarily the actual leading pair); positivity is unit 5; the pair identification in terms of
the divisor ratios `(h_j+1)/e_j` is unit 4.
-/

open MeasureTheory Set Filter Topology Monomialize.Analytic Monomialize.VolumeScaling
open scoped ENNReal

namespace Grammar

namespace ProductMonomialChart

variable {d : ℕ} {ι : Type*} [Fintype ι] {R : ResolutionCover d ι} {i : ι} {K : (Fin d → ℝ) → ℝ}
  (P : ProductMonomialChart R i K)

/-- The foot set of stratum `I` for the chart. -/
def pieceFootSet (I : Finset (Fin d)) : Set (Fin d → ℝ) := footSet P.e.support P.T P.b I

/-- The inactive weight factor as a function on the ambient space. -/
def pieceWeight (x : Fin d → ℝ) : ℝ := P.r (zeroOn P.e.support x)

theorem mem_productDom_of_mem_dom {y : Fin d → ℝ} (hy : y ∈ (R.chart i).dom) :
    y ∈ productDom P.e.support P.T P.b := P.dom_eq ▸ hy

theorem mem_dom_of_mem_productDom {y : Fin d → ℝ} (hy : y ∈ productDom P.e.support P.T P.b) :
    y ∈ (R.chart i).dom := P.dom_eq.symm ▸ hy

/-- **The piece atlas of a product chart**, for every nonempty stratum, from the geometric package
alone (plus continuity of the pulled-back observable and prior). -/
theorem exists_pieceAtlas (hK0 : ∀ x, 0 ≤ K x) {ε : ℝ} (hε : 0 < ε) (hεb : ε ≤ P.b)
    {D : ι → Finset (Fin d)} (hD : D i = P.e.support) {F : (Fin d → ℝ) → ℝ} {p : TubeWeight d}
    (hFc : ContinuousOn (fun y => F ((R.chart i).φ y)) P.W)
    (hpc : ContinuousOn (fun y => p.w ((R.chart i).φ y)) P.W) (hFm : Measurable F)
    (hF : Integrable (fun x => F x * p.w x) (volume.restrict (⋃ i, R.image i)))
    (hK : Measurable K) (I : Finset (Fin d)) (hI : I ⊆ P.e.support) (hne : I.Nonempty) :
    ∃ At : FiniteScalarUnitAtlas (d - (I.card - 1 + 1)) (R.pieceIntegral D ε i I F K p),
      (∀ σ, (At.cell σ).lam = minRatio (normalExp I hne P.h) (normalHalfExp I hne P.e)) ∧
      ∀ σ, (At.cell σ).mult =
        multCount (ratioExp (normalExp I hne P.h) (normalHalfExp I hne P.e))
          (minRatio (normalExp I hne P.h) (normalHalfExp I hne P.e)) := by
  have hind : ∀ y ∈ (R.chart i).dom, P.u y = P.u (planeFoot (stratumSplit I hne) y) :=
    fun y hy => unit_indep_piece P.e.support P.T P.b P.u
      (fun y hy' => P.unit_indep y (P.mem_dom_of_mem_productDom hy')) I hne hI
      (P.mem_productDom_of_mem_dom hy)
  have hdom : ∀ y ∈ sizePiece (D i) ε I,
      y ∈ (R.chart i).dom ↔ planeFoot (stratumSplit I hne) y ∈ P.pieceFootSet I := fun y hy => by
    rw [P.dom_eq]
    exact mem_productDom_iff_foot_mem_footSet P.e.support P.T P.b I hne hI hεb (hD ▸ hy)
  have hρ : ∀ y ∈ sizePiece (D i) ε I, y ∈ (R.chart i).dom →
      R.weight i ((R.chart i).Φ y) = P.pieceWeight (planeFoot (stratumSplit I hne) y) :=
    fun y _ hy => weight_factor_piece P.e.support P.T P.b (fun y => R.weight i ((R.chart i).Φ y))
      P.r (fun y hy' => P.weight_eq y (P.mem_dom_of_mem_productDom hy')) I hne hI
      (P.mem_productDom_of_mem_dom hy)
  have hy₀ : ∃ y₀ ∈ P.W, ∀ j ∈ I, y₀ j = 0 := by
    obtain ⟨y₀, hy₀, hz⟩ := exists_zeroPoint P.e.support P.T P.b P.T_nonempty P.T_zero P.b_pos.le
    exact ⟨y₀, P.dom_subset (P.mem_dom_of_mem_productDom hy₀), fun j hj => hz j (hI hj)⟩
  exact R.exists_pieceAtlas_of_chart i D hε I hne P.e P.h hD hI hK0 P.W_open P.dom_subset P.u P.v
    P.u_cont P.u_ne P.phase_eq P.v_cont P.det_eq hind (P.pieceFootSet I)
    (isClosed_footSet _ _ _ P.T_compact.isClosed I) P.pieceWeight
    (P.r_meas.comp (continuous_zeroOn _).measurable) (fun x => P.r_bound _) hdom hρ hFc hpc hFm hF
    hK hy₀

/-- **The chosen piece atlas** (classical choice, once). -/
noncomputable def pieceAtlas' (hK0 : ∀ x, 0 ≤ K x) {ε : ℝ} (hε : 0 < ε) (hεb : ε ≤ P.b)
    {D : ι → Finset (Fin d)} (hD : D i = P.e.support) {F : (Fin d → ℝ) → ℝ} {p : TubeWeight d}
    (hFc : ContinuousOn (fun y => F ((R.chart i).φ y)) P.W)
    (hpc : ContinuousOn (fun y => p.w ((R.chart i).φ y)) P.W) (hFm : Measurable F)
    (hF : Integrable (fun x => F x * p.w x) (volume.restrict (⋃ i, R.image i)))
    (hK : Measurable K) (I : Finset (Fin d)) (hI : I ⊆ P.e.support) (hne : I.Nonempty) :
    FiniteScalarUnitAtlas (d - (I.card - 1 + 1)) (R.pieceIntegral D ε i I F K p) :=
  Classical.choose (P.exists_pieceAtlas hK0 hε hεb hD hFc hpc hFm hF hK I hI hne)

theorem pieceAtlas'_cell_lam (hK0 : ∀ x, 0 ≤ K x) {ε : ℝ} (hε : 0 < ε) (hεb : ε ≤ P.b)
    {D : ι → Finset (Fin d)} (hD : D i = P.e.support) {F : (Fin d → ℝ) → ℝ} {p : TubeWeight d}
    (hFc : ContinuousOn (fun y => F ((R.chart i).φ y)) P.W)
    (hpc : ContinuousOn (fun y => p.w ((R.chart i).φ y)) P.W) (hFm : Measurable F)
    (hF : Integrable (fun x => F x * p.w x) (volume.restrict (⋃ i, R.image i)))
    (hK : Measurable K) (I : Finset (Fin d)) (hI : I ⊆ P.e.support) (hne : I.Nonempty) (σ) :
    ((P.pieceAtlas' hK0 hε hεb hD hFc hpc hFm hF hK I hI hne).cell σ).lam =
      minRatio (normalExp I hne P.h) (normalHalfExp I hne P.e) :=
  (Classical.choose_spec (P.exists_pieceAtlas hK0 hε hεb hD hFc hpc hFm hF hK I hI hne)).1 σ

theorem pieceAtlas'_cell_mult (hK0 : ∀ x, 0 ≤ K x) {ε : ℝ} (hε : 0 < ε) (hεb : ε ≤ P.b)
    {D : ι → Finset (Fin d)} (hD : D i = P.e.support) {F : (Fin d → ℝ) → ℝ} {p : TubeWeight d}
    (hFc : ContinuousOn (fun y => F ((R.chart i).φ y)) P.W)
    (hpc : ContinuousOn (fun y => p.w ((R.chart i).φ y)) P.W) (hFm : Measurable F)
    (hF : Integrable (fun x => F x * p.w x) (volume.restrict (⋃ i, R.image i)))
    (hK : Measurable K) (I : Finset (Fin d)) (hI : I ⊆ P.e.support) (hne : I.Nonempty) (σ) :
    ((P.pieceAtlas' hK0 hε hεb hD hFc hpc hFm hF hK I hI hne).cell σ).mult =
      multCount (ratioExp (normalExp I hne P.h) (normalHalfExp I hne P.e))
        (minRatio (normalExp I hne P.h) (normalHalfExp I hne P.e)) :=
  (Classical.choose_spec (P.exists_pieceAtlas hK0 hε hεb hD hFc hpc hFm hF hK I hI hne)).2 σ

end ProductMonomialChart

/-! ### The end-to-end theorem for a cover of product charts -/

namespace ResolutionCover

variable {d : ℕ} {ι : Type*} [Fintype ι] (R : ResolutionCover d ι) {K : (Fin d → ℝ) → ℝ}
  (Ps : ∀ i, ProductMonomialChart R i K) (hK0 : ∀ x, 0 ≤ K x) {ε : ℝ} (hε : 0 < ε)
  (hεb : ∀ i, ε ≤ (Ps i).b) {F : (Fin d → ℝ) → ℝ} {p : TubeWeight d}
  (hFc : ∀ i, ContinuousOn (fun y => F ((R.chart i).φ y)) (Ps i).W)
  (hpc : ∀ i, ContinuousOn (fun y => p.w ((R.chart i).φ y)) (Ps i).W) (hFm : Measurable F)
  (hF : Integrable (fun x => F x * p.w x) (volume.restrict (⋃ i, R.image i))) (hK : Measurable K)

/-- The geometric pair of the chart–stratum piece `(i, I)`: `(min_a (h_{ν(a)}+1)/(2k_a), #min −
1)`. -/
noncomputable def productPieceLam (i : ι) (I : Finset (Fin d)) (hne : I.Nonempty) : ℝ :=
  minRatio (normalExp I hne (Ps i).h) (normalHalfExp I hne (Ps i).e)

noncomputable def productPieceMult (i : ι) (I : Finset (Fin d)) (hne : I.Nonempty) : ℕ :=
  multCount (ratioExp (normalExp I hne (Ps i).h) (normalHalfExp I hne (Ps i).e))
    (R.productPieceLam Ps i I hne)

include hK0 hε hεb hFc hpc hFm hF hK in
/-- **The uniform family of piece atlases** of a cover of product charts. -/
noncomputable def productAtlases : ∀ (i : ι) (I : Finset (Fin d)), I ⊆ (Ps i).e.support →
    I.Nonempty → FiniteScalarUnitAtlas (d - (I.card - 1 + 1))
      (R.pieceIntegral (fun i => (Ps i).e.support) ε i I F K p) :=
  fun i I hI hne => (Ps i).pieceAtlas' hK0 hε (hεb i) rfl (hFc i) (hpc i) hFm hF hK I hI hne

include hK0 hε hεb hFc hpc hFm hF hK in
/-- **The end-to-end theorem**: the resolved Boltzmann integral of a cover of product monomial
charts (normal-independent units, factored cover weights, continuous pulled-back observable and
prior) has the leading-term certificate at any pair `(λ₀, k₀)` dominating every chart–stratum pair,
with coefficient the sum of the tied cell coefficients over all chart–stratum pairs. -/
theorem hasLeadingTerm_boltzmannIntegral_of_productCharts (lam₀ : ℝ) (k₀ : ℕ)
    (hlam : ∀ i I, I ⊆ (Ps i).e.support → ∀ hne : I.Nonempty, lam₀ ≤ R.productPieceLam Ps i I hne)
    (hk : ∀ i I, I ⊆ (Ps i).e.support → ∀ hne : I.Nonempty,
      R.productPieceLam Ps i I hne = lam₀ → R.productPieceMult Ps i I hne - 1 ≤ k₀) :
    HasLeadingTerm (R.boltzmannIntegral F K p)
      (∑ i, ∑ I ∈ (Ps i).e.support.powerset.filter (fun I => I.Nonempty),
        scalarAtlasPieceCoeff' (R.productAtlases Ps hK0 hε hεb hFc hpc hFm hF hK) lam₀ k₀ i I)
      lam₀ k₀ :=
  R.hasLeadingTerm_boltzmannIntegral_of_scalarAtlases' (fun i => (Ps i).e) (fun i => (Ps i).h)
    (fun i => (Ps i).W) (fun i => (Ps i).monomial) hε hFm hF hK hK0
    (fun _ I => d - (I.card - 1 + 1)) (R.productAtlases Ps hK0 hε hεb hFc hpc hFm hF hK) lam₀ k₀
    (fun i I hI hne j =>
      (hlam i I hI hne).trans_eq
        ((Ps i).pieceAtlas'_cell_lam hK0 hε (hεb i) rfl (hFc i) (hpc i) hFm hF hK I hI hne j).symm)
    (fun i I hI hne j hj => by
      have hj' : R.productPieceLam Ps i I hne = lam₀ :=
        ((Ps i).pieceAtlas'_cell_lam hK0 hε (hεb i) rfl (hFc i) (hpc i) hFm hF hK I hI hne
          j).symm.trans hj
      have hm := (Ps i).pieceAtlas'_cell_mult hK0 hε (hεb i) rfl (hFc i) (hpc i) hFm hF hK I hI
        hne j
      calc ((R.productAtlases Ps hK0 hε hεb hFc hpc hFm hF hK i I hI hne).cell j).mult - 1
          = R.productPieceMult Ps i I hne - 1 := by
            change (((Ps i).pieceAtlas' hK0 hε (hεb i) rfl (hFc i) (hpc i) hFm hF hK I hI
              hne).cell j).mult - 1 = _
            rw [hm]
            rfl
        _ ≤ k₀ := hk i I hI hne hj')

end ResolutionCover

end Grammar
