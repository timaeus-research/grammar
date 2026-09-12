/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.ProductChartVarPosterior

/-!
# Compatibility of the variable-unit and the scalar product-chart theorems (CCLXIII)

Under the independence hypothesis `unit_indep`, the variable-unit construction applied to the
forgetful image `P.toVar` of a scalar package `P` reproduces the scalar construction exactly:

* the variable phase equals the scalar phase on the piece (`varPhase_eq_scalarPhase_of_indep`);
* extension independence transfers to the orthant cells (`VarUnitCell.withData_reflected_coeff`),
  so the reflected coefficients of the variable piece cell and of the scalar piece cell agree
  whenever their (Tietze-extended) amplitudes and units agree on the base times the closed ball
  (`ResolutionCover.reflected_coeff_compat`);
* hence the chosen atlases have the same tied sums (`ProductMonomialChart.tiedSum_toVar_eq`) and
  ★ `productCoeffV_toVar_eq`: `productCoeffV (P.toVar) = productCoeffD P` at every pair — the
  new theorem specialises to the old one, coefficient included, and the normaliser and the
  posterior limit agree as well (`normaliserCoeffV_toVar_eq`).
-/

open MeasureTheory Set Filter Topology Asymptotics Monomialize.Analytic Monomialize.VolumeScaling
open scoped ENNReal

namespace Grammar

/-! ### The variable phase under independence -/

section Indep

variable {d : ℕ} (I : Finset (Fin d)) (hne : I.Nonempty) (u : (Fin d → ℝ) → ℝ) (e : Fin d →₀ ℕ)

/-- Where the unit is independent of the normal coordinates, the variable phase is the scalar
phase. -/
theorem varPhase_eq_scalarPhase_of_indep {z : Fin (d - (I.card - 1 + 1)) → ℝ}
    {n : Fin (I.card - 1 + 1) → ℝ}
    (hind : u (planeSplit (stratumSplit I hne) (z, n)) =
      u (planeFoot (stratumSplit I hne) (planeSplit (stratumSplit I hne) (z, n)))) :
    varPhase I hne u e z n = scalarPhase I hne u e z := by
  unfold varPhase scalarPhase tangentialUnit
  rw [hind, planeFoot_planeSplit]

end Indep

/-! ### Extension independence of the orthant cells -/

namespace VarUnitCell

variable {t : ℕ} (c : VarUnitCell t)
  (A' u' : (Fin t → ℝ) → (Fin (c.n + 1) → ℝ) → ℝ) (hA' : Continuous (Function.uncurry A'))
  (hu' : Continuous (Function.uncurry u'))
  (hu'_pos : ∀ z ∈ c.base, ∀ v ∈ Metric.closedBall (0 : Fin (c.n + 1) → ℝ) c.b, 0 < u' z v)
  (hA : ∀ z ∈ c.base, ∀ v ∈ Metric.closedBall (0 : Fin (c.n + 1) → ℝ) c.b, A' z v = c.A z v)
  (hu : ∀ z ∈ c.base, ∀ v ∈ Metric.closedBall (0 : Fin (c.n + 1) → ℝ) c.b, u' z v = c.u z v)

include hA hu in
/-- **Extension independence of the reflected coefficients.** -/
theorem withData_reflected_coeff (σ : Fin (c.n + 1) → Bool) :
    ((c.withData A' u' hA' hu' hu'_pos).reflected σ).coeff = (c.reflected σ).coeff :=
  (c.reflected σ).withData_coeff (reflectAmp c.n A' σ) (reflectAmp c.n u' σ)
    (continuous_reflectAmp c.n A' hA' σ) (continuous_reflectAmp c.n u' hu' σ)
    (fun z hz v hv =>
      hu'_pos z hz _ ((ScalarUnitCell.reflect_mem_closedBall_iff σ c.b_pos.le v).2 hv))
    (fun z hz v hv => hA z hz _ ((ScalarUnitCell.reflect_mem_closedBall_iff σ c.b_pos.le v).2 hv))
    (fun z hz v hv => hu z hz _ ((ScalarUnitCell.reflect_mem_closedBall_iff σ c.b_pos.le v).2 hv))

end VarUnitCell

/-! ### The variable and the scalar piece cells -/

namespace ResolutionCover

variable {d : ℕ} {ι : Type*} [Fintype ι] (R : ResolutionCover d ι) (i : ι)
  (D : ι → Finset (Fin d)) {ε : ℝ} (hε : 0 < ε) (I : Finset (Fin d)) (hne : I.Nonempty)
  {F K : (Fin d → ℝ) → ℝ} {p : TubeWeight d}
  (Ad : AdaptedProductDensity (stratumSplit I hne) (R.boltzmannChartDensity i 0 K p)
    (sizePiece (D i) ε I))
  (hbase : IsCompact Ad.base) (hβ : IntegrableOn Ad.beta Ad.base)
  (h k : Fin (I.card - 1 + 1) → ℕ) (hk : ∀ j, 0 < k j)
  (q : (Fin (d - (I.card - 1 + 1)) → ℝ) → ℝ) (hq : Continuous q) (hq_pos : ∀ z ∈ Ad.base, 0 < q z)
  (A : (Fin (d - (I.card - 1 + 1)) → ℝ) → (Fin (I.card - 1 + 1) → ℝ) → ℝ)
  (hA : Continuous (Function.uncurry A))
  (qv : (Fin (d - (I.card - 1 + 1)) → ℝ) → (Fin (I.card - 1 + 1) → ℝ) → ℝ)
  (hqv : Continuous (Function.uncurry qv))
  (hqv_pos : ∀ z ∈ Ad.base, ∀ n ∈ Metric.closedBall (0 : Fin (I.card - 1 + 1) → ℝ) ε, 0 < qv z n)
  (A' : (Fin (d - (I.card - 1 + 1)) → ℝ) → (Fin (I.card - 1 + 1) → ℝ) → ℝ)
  (hA' : Continuous (Function.uncurry A'))

/-- The variable piece cell is the scalar piece cell (as a variable-unit cell) with replaced data.
-/
theorem varPieceCell_eq_withData :
    R.varPieceCell i D hε I hne Ad hbase hβ h k hk qv hqv hqv_pos A' hA' =
      (R.pieceCell i D hε I hne Ad hbase hβ h k hk q hq hq_pos A hA).toVar.withData A' qv hA' hqv
        hqv_pos := rfl

/-- **The reflected coefficients of the variable and the scalar piece cells agree** when the
amplitudes agree and the unit is the scalar unit on the base times the closed ball. -/
theorem reflected_coeff_compat
    (hAA : ∀ z ∈ Ad.base, ∀ v ∈ Metric.closedBall (0 : Fin (I.card - 1 + 1) → ℝ) ε, A' z v = A z v)
    (hqq : ∀ z ∈ Ad.base, ∀ v ∈ Metric.closedBall (0 : Fin (I.card - 1 + 1) → ℝ) ε, qv z v = q z)
    (σ : Fin (I.card - 1 + 1) → Bool) :
    ((R.varPieceCell i D hε I hne Ad hbase hβ h k hk qv hqv hqv_pos A' hA').reflected σ).coeff =
      ((R.pieceCell i D hε I hne Ad hbase hβ h k hk q hq hq_pos A hA).reflected σ).coeff := by
  have h1 := (R.pieceCell i D hε I hne Ad hbase hβ h k hk q hq hq_pos
    A hA).toVar.withData_reflected_coeff A' qv hA' hqv hqv_pos hAA hqq σ
  exact h1.trans (ScalarUnitCell.toVar_coeff
    ((R.pieceCell i D hε I hne Ad hbase hβ h k hk q hq hq_pos A hA).reflected σ))

end ResolutionCover

/-! ### The tied sums of the chosen atlases agree -/

namespace ProductMonomialChart

variable {d : ℕ} {ι : Type*} [Fintype ι] {R : ResolutionCover d ι} {i : ι} {K : (Fin d → ℝ) → ℝ}
  (P : ProductMonomialChart R i K) (hK0 : ∀ x, 0 ≤ K x) {ε : ℝ} (hε : 0 < ε) (hεb : ε ≤ P.b)
  {D : ι → Finset (Fin d)} (hD : D i = P.e.support) {F : (Fin d → ℝ) → ℝ} {p : TubeWeight d}
  (hFc : ContinuousOn (fun y => F ((R.chart i).φ y)) P.W)
  (hpc : ContinuousOn (fun y => p.w ((R.chart i).φ y)) P.W) (hFm : Measurable F)
  (hF : Integrable (fun x => F x * p.w x) (volume.restrict (⋃ i, R.image i)))
  (hK : Measurable K) (I : Finset (Fin d)) (hI : I ⊆ P.e.support) (hne : I.Nonempty)

/-- On the piece, the variable phase of the scalar package is its scalar phase. -/
theorem varPhase_eq_scalarPhase {z : Fin (d - (I.card - 1 + 1)) → ℝ}
    (hz : z ∈ (P.pieceDensity hε hεb hD I hI hne p).base) {n : Fin (I.card - 1 + 1) → ℝ}
    (hn : n ∈ Metric.closedBall (0 : Fin (I.card - 1 + 1) → ℝ) ε) :
    varPhase I hne P.u P.e z n = scalarPhase I hne P.u P.e z := by
  have hdom : planeSplit (stratumSplit I hne) (z, n) ∈ (R.chart i).dom :=
    R.mem_dom_of_mem_base_closedBall i D hε I hne P.e hD hI K p (P.pieceFootSet I)
      (P.isClosed_pieceFootSet I) P.pieceWeight (P.piece_dom_iff hεb hD I hI hne)
      (P.piece_weight_eq I hI hne) hz hn
  exact varPhase_eq_scalarPhase_of_indep I hne P.u P.e
    (unit_indep_piece P.e.support P.T P.b P.u
      (fun y hy' => P.unit_indep y (P.mem_dom_of_mem_productDom hy')) I hne hI
      (P.mem_productDom_of_mem_dom hdom))

/-- **The tied sums of the chosen variable-unit and scalar atlases agree** at every pair. -/
theorem tiedSum_toVar_eq (lam₀ : ℝ) (k₀ : ℕ) :
    ∑ j ∈ (P.toVar.pieceAtlasV hK0 hε hεb hD hFc hpc hFm hF hK I hI hne).toLeading.tied lam₀ k₀,
        ((P.toVar.pieceAtlasV hK0 hε hεb hD hFc hpc hFm hF hK I hI hne).toLeading.cell j).coeff =
      ∑ j ∈ (P.pieceAtlasD hK0 hε hεb hD hFc hpc hFm hF hK I hI hne).tied lam₀ k₀,
        ((P.pieceAtlasD hK0 hε hεb hD hFc hpc hFm hF hK I hI hne).cell j).coeff := by
  obtain ⟨q', A', hq'c, hq'pos, hA'c, hk, hbase, hβ, hamp', hphase', hq', hA', hAtD⟩ :=
    P.pieceAtlasD_data hK0 hε hεb hD hFc hpc hFm hF hK I hI hne
  obtain ⟨qv, A'', hqv, hqv_pos, hA''c, hk', hbase', hβ', hamp'', hphase'', hqv', hA'', hAtV⟩ :=
    P.toVar.pieceAtlasV_data hK0 hε hεb hD hFc hpc hFm hF hK I hI hne
  rw [hAtD, hAtV]
  refine Finset.sum_congr rfl fun σ _ => ?_
  exact R.reflected_coeff_compat i D hε I hne (P.pieceDensity hε hεb hD I hI hne p) hbase hβ
    (normalExp I hne P.h) (normalHalfExp I hne P.e) hk q' hq'c hq'pos A' hA'c qv hqv hqv_pos A''
    hA''c
    (fun z hz v hv => (hA'' z hz v hv).trans (hA' z hz v hv).symm)
    (fun z hz v hv => (hqv' z hz v hv).trans
      ((P.varPhase_eq_scalarPhase hε hεb hD I hI hne hz hv).trans (hq' z hz).symm)) σ

end ProductMonomialChart

/-! ### The total coefficients agree -/

namespace ResolutionCover

variable {d : ℕ} {ι : Type*} [Fintype ι] (R : ResolutionCover d ι) {K : (Fin d → ℝ) → ℝ}
  (Ps : ∀ i, ProductMonomialChart R i K) (hK0 : ∀ x, 0 ≤ K x) {ε : ℝ} (hε : 0 < ε)
  (hεb : ∀ i, ε ≤ (Ps i).b) {F : (Fin d → ℝ) → ℝ} {p : TubeWeight d}
  (hFc : ∀ i, ContinuousOn (fun y => F ((R.chart i).φ y)) (Ps i).W)
  (hpc : ∀ i, ContinuousOn (fun y => p.w ((R.chart i).φ y)) (Ps i).W) (hFm : Measurable F)
  (hF : Integrable (fun x => F x * p.w x) (volume.restrict (⋃ i, R.image i))) (hK : Measurable K)

include hK0 hε hεb hFc hpc hFm hF hK in
/-- ★ **The variable-unit total coefficient of the forgetful image is the scalar total
coefficient**, at every pair: the new theorem specialises to the old one, coefficient included. -/
theorem productCoeffV_toVar_eq (lam₀ : ℝ) (k₀ : ℕ) :
    R.productCoeffV (fun i => (Ps i).toVar) hK0 hε hεb hFc hpc hFm hF hK lam₀ k₀ =
      R.productCoeffD Ps hK0 hε hεb hFc hpc hFm hF hK lam₀ k₀ := by
  unfold productCoeffV productCoeffD
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun I hI => ?_
  obtain ⟨hpow, hne⟩ := Finset.mem_filter.1 hI
  have hIsub : I ⊆ (Ps i).e.support := Finset.mem_powerset.1 hpow
  rw [leadingAtlasPieceCoeff_of_mem _ lam₀ k₀ i I hIsub hne,
    scalarAtlasPieceCoeff'_of_mem _ lam₀ k₀ i I hIsub hne]
  exact (Ps i).tiedSum_toVar_eq hK0 hε (hεb i) rfl (hFc i) (hpc i) hFm hF hK I hIsub hne lam₀ k₀

omit hFc hFm hF in
include hK0 hε hεb hpc hK in
/-- The normalising coefficients agree. -/
theorem normaliserCoeffV_toVar_eq (hp : Integrable p.w (volume.restrict (⋃ i, R.image i)))
    (lam₀ : ℝ) (k₀ : ℕ) :
    R.normaliserCoeffV (fun i => (Ps i).toVar) hK0 hε hεb hpc hp hK lam₀ k₀ =
      R.normaliserCoeff Ps hK0 hε hεb hpc hp hK lam₀ k₀ :=
  R.productCoeffV_toVar_eq Ps hK0 hε hεb (fun _ => continuousOn_const) hpc measurable_const
    (R.integrable_one_mul_weight hp) hK lam₀ k₀

end ResolutionCover

end Grammar
