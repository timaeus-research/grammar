/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.ProductChartExtremalPair
import Grammar.ScalarCellNonneg

/-!
# Positivity of the leading coefficient for a cover of product charts

Unit 5(b) of consult #78 (`tide-log/gpt6_bigpicture_v78.md`): the end-to-end certificate of
CCXLII–CCXLIII holds at the geometric extremal pair `(λ*, k*)`, but it identifies the actual
leading pair only when the summed tied coefficient is nonzero. This module supplies the missing
positivity under a **dominant-face positive-mass hypothesis**.

* Every stratum piece of a product chart has a piece atlas **with exposed cells**
  (`ProductMonomialChart.IsPieceAtlasData`, `exists_pieceAtlas_data`, `pieceAtlasD`): the atlas is
  the constructed atlas of CCXXXVIII, whose amplitude is `pieceAmp = |v|·|tangential monomial|·
  p∘φ·F∘φ` on the base and whose base weight is the cover-weight factor `r∘P_J` on the foot set.
* With `F ≥ 0`, `p ≥ 0` and `r ≥ 0`, **every cell coefficient is nonnegative**
  (`cell_coeff_nonneg_of_data`).
* The **dominant face** of a stratum piece (`dominantFace`) is the set of foot points `Ψ(z, 0)` of
  the piece lying in the chart domain where `r`, `p∘φ`, `F∘φ` are positive and the Jacobian unit and
  the tangential Jacobian monomial are nonzero. For an **all-minimal** stratum (every divisor ratio
  over `I` equal to the stratum exponent) with a dominant face of positive measure, some cell
  coefficient is positive (`exists_cell_coeff_pos_of_data`, via `coeff_pos_of_all_minimal`).
* **The total coefficient is positive** (`productCoeffD_pos`) and hence the resolved Boltzmann
  integral is genuinely asymptotically equivalent to `c · N^{−λ₀} (log N)^{k₀}`
  (`boltzmannIntegral_isEquivalent_of_productCharts`); at the extremal pair, with an extremal
  stratum `I₀` (all ratios `= λ*`, `|I₀| − 1 = k*`) of positive dominant-face measure, this is the
  identified leading pair (`boltzmannIntegral_isEquivalent_of_productCharts_extremal`). Such a
  stratum always exists (`exists_extremal_stratum`); the positive-mass hypothesis is the only
  additional input, and it cannot be dropped (`K = x²`, `F = x²` is negligible at `(1/2, 0)`).
-/

open MeasureTheory Set Filter Topology Asymptotics Monomialize.Analytic Monomialize.VolumeScaling
open scoped ENNReal

namespace Grammar

namespace ResolutionCover

/-- The piece coefficient of a chart–stratum pair, unfolded. -/
theorem scalarAtlasPieceCoeff'_of_mem {e : ι → Fin d →₀ ℕ} {Z : ι → Finset (Fin d) → ℝ → ℝ}
    {tdim : ι → Finset (Fin d) → ℕ}
    (At : ∀ (i : ι) (I : Finset (Fin d)), I ⊆ (e i).support → I.Nonempty →
      FiniteScalarUnitAtlas (tdim i I) (Z i I))
    (lam₀ : ℝ) (k₀ : ℕ) (i : ι) (I : Finset (Fin d)) (hI : I ⊆ (e i).support)
    (hne : I.Nonempty) :
    scalarAtlasPieceCoeff' At lam₀ k₀ i I =
      ∑ j ∈ (At i I hI hne).tied lam₀ k₀, ((At i I hI hne).cell j).coeff :=
  dif_pos ⟨hI, hne⟩

variable {d : ℕ} {ι : Type*} [Fintype ι] (R : ResolutionCover d ι) (i : ι) (I : Finset (Fin d))
  (hne : I.Nonempty)

theorem pieceAmp_nonneg (h : Fin d →₀ ℕ) (v : (Fin d → ℝ) → ℝ) {F : (Fin d → ℝ) → ℝ}
    {p : TubeWeight d} (hF0 : ∀ x, 0 ≤ F x) (hp0 : ∀ x, 0 ≤ p.w x)
    (z : Fin (d - (I.card - 1 + 1)) → ℝ) (n : Fin (I.card - 1 + 1) → ℝ) :
    0 ≤ R.pieceAmp i I hne h v (F := F) (p := p) z n :=
  mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (hp0 _)) (hF0 _)

end ResolutionCover

namespace ProductMonomialChart

variable {d : ℕ} {ι : Type*} [Fintype ι] {R : ResolutionCover d ι} {i : ι} {K : (Fin d → ℝ) → ℝ}
  (P : ProductMonomialChart R i K)

/-! ### The dominant face of a stratum piece -/

section Face

variable (D : ι → Finset (Fin d)) (ε : ℝ) (I : Finset (Fin d)) (hne : I.Nonempty)

/-- **The dominant face of the stratum piece `I`** in base coordinates: the foot points
`Ψ(z, 0)` satisfying the piece's foot condition (the other active coordinates at least `ε`), lying
in the chart domain, where the cover-weight factor, the prior and the observable are positive and
the Jacobian unit and the tangential Jacobian monomial are nonzero. -/
def dominantFace (F : (Fin d → ℝ) → ℝ) (p : TubeWeight d) :
    Set (Fin (d - (I.card - 1 + 1)) → ℝ) :=
  {z | planeSplit (stratumSplit I hne) (z, 0) ∈ footCondition (D i) (ε := ε) I ∧
    planeSplit (stratumSplit I hne) (z, 0) ∈ (R.chart i).dom ∧
    0 < P.pieceWeight (planeSplit (stratumSplit I hne) (z, 0)) ∧
    0 < p.w ((R.chart i).φ (planeSplit (stratumSplit I hne) (z, 0))) ∧
    0 < F ((R.chart i).φ (planeSplit (stratumSplit I hne) (z, 0))) ∧
    P.v (planeSplit (stratumSplit I hne) (z, 0)) ≠ 0 ∧
    tangentialMonomial I hne P.h z ≠ 0}

end Face

/-! ### The adapted density of a stratum piece -/

section Density

variable {ε : ℝ} (hε : 0 < ε) (hεb : ε ≤ P.b) {D : ι → Finset (Fin d)} (hD : D i = P.e.support)
  (I : Finset (Fin d)) (hI : I ⊆ P.e.support) (hne : I.Nonempty)

include hεb hD hI in
/-- The piece is fibre-saturated: on the piece, membership in the domain is the foot condition. -/
theorem piece_dom_iff : ∀ y ∈ sizePiece (D i) ε I,
    y ∈ (R.chart i).dom ↔ planeFoot (stratumSplit I hne) y ∈ P.pieceFootSet I := fun y hy => by
  rw [P.dom_eq]
  exact mem_productDom_iff_foot_mem_footSet P.e.support P.T P.b I hne hI hεb (hD ▸ hy)

theorem isClosed_pieceFootSet : IsClosed (P.pieceFootSet I) :=
  isClosed_footSet _ _ _ P.T_compact.isClosed I

include hI in
/-- The cover weight on the piece is the inactive factor at the foot. -/
theorem piece_weight_eq : ∀ y ∈ sizePiece (D i) ε I, y ∈ (R.chart i).dom →
    R.weight i ((R.chart i).Φ y) = P.pieceWeight (planeFoot (stratumSplit I hne) y) :=
  fun _ _ hy => weight_factor_piece P.e.support P.T P.b (fun y => R.weight i ((R.chart i).Φ y))
    P.r (fun y hy' => P.weight_eq y (P.mem_dom_of_mem_productDom hy')) I hne hI
    (P.mem_productDom_of_mem_dom hy)

include hεb hD hI in
/-- **The adapted product density of the stratum piece of a product chart** (CCXXXVIII, with the
foot set `T'_I` and the weight factor `r∘P_J`). -/
noncomputable def pieceDensity (p : TubeWeight d) :
    AdaptedProductDensity (stratumSplit I hne) (R.boltzmannChartDensity i 0 K p)
      (sizePiece (D i) ε I) :=
  R.chartPieceDensity i D hε I hne P.e hD hI K p (P.pieceFootSet I) (P.isClosed_pieceFootSet I)
    P.pieceWeight (P.piece_dom_iff hεb hD I hI hne) (P.piece_weight_eq I hI hne)

include hεb hD hI in
theorem pieceDensity_beta (p : TubeWeight d) (z : Fin (d - (I.card - 1 + 1)) → ℝ) :
    (P.pieceDensity hε hεb hD I hI hne p).beta z =
      (P.pieceFootSet I).indicator P.pieceWeight (planeSplit (stratumSplit I hne) (z, 0)) := rfl

include hεb hD hI in
/-- The base weight is nonnegative when the cover-weight factor is. -/
theorem pieceDensity_beta_nonneg (p : TubeWeight d) (hr0 : ∀ x, 0 ≤ P.r x)
    (z : Fin (d - (I.card - 1 + 1)) → ℝ) : 0 ≤ (P.pieceDensity hε hεb hD I hI hne p).beta z := by
  rw [pieceDensity_beta]
  exact Set.indicator_nonneg (fun _ _ => hr0 _) _

include hεb hD hI in
theorem foot_mem_pieceFootSet_of_mem_base (p : TubeWeight d) {z : Fin (d - (I.card - 1 + 1)) → ℝ}
    (hz : z ∈ (P.pieceDensity hε hεb hD I hI hne p).base) :
    planeSplit (stratumSplit I hne) (z, 0) ∈ P.pieceFootSet I := by
  unfold pieceDensity at hz
  rw [ResolutionCover.chartPieceDensity_base] at hz
  exact hz.2

include hεb hD hI in
/-- Dominant-face points lie in the base of the piece density. -/
theorem mem_pieceDensity_base_of_mem_dominantFace {F : (Fin d → ℝ) → ℝ} (p : TubeWeight d)
    {z : Fin (d - (I.card - 1 + 1)) → ℝ} (hz : z ∈ P.dominantFace D ε I hne F p) :
    z ∈ (P.pieceDensity hε hεb hD I hI hne p).base := by
  obtain ⟨hfoot, hdom, -, -, -, -, -⟩ := hz
  have hpiece : planeSplit (stratumSplit I hne) (z, 0) ∈ sizePiece (D i) ε I := by
    have htube : planeSplit (stratumSplit I hne) (z, 0) ∈
        (coordPlaneTube (stratumSplit I hne) ε hε).U := by
      change ‖planeSplit (stratumSplit I hne) (z, 0) -
        planeFoot (stratumSplit I hne) (planeSplit (stratumSplit I hne) (z, 0))‖ < ε
      rw [norm_planeSplit_sub_foot, norm_zero]
      exact hε
    refine (mem_sizePiece_iff_of_mem_tube (D i) hε I hne htube).2 ?_
    rwa [planeFoot_planeSplit]
  have hT' := (P.piece_dom_iff hεb hD I hI hne _ hpiece).1 hdom
  rw [planeFoot_planeSplit] at hT'
  unfold pieceDensity
  rw [ResolutionCover.chartPieceDensity_base]
  exact ⟨⟨hfoot, mem_tangentialCarrier_of_mem (stratumSplit I hne) hdom⟩, hT'⟩

end Density

/-! ### Piece atlases with exposed cells -/

section Atlas

variable (hK0 : ∀ x, 0 ≤ K x) {ε : ℝ} (hε : 0 < ε) (hεb : ε ≤ P.b)
  {D : ι → Finset (Fin d)} (hD : D i = P.e.support) {F : (Fin d → ℝ) → ℝ} {p : TubeWeight d}
  (hFc : ContinuousOn (fun y => F ((R.chart i).φ y)) P.W)
  (hpc : ContinuousOn (fun y => p.w ((R.chart i).φ y)) P.W) (hFm : Measurable F)
  (hF : Integrable (fun x => F x * p.w x) (volume.restrict (⋃ i, R.image i)))
  (hK : Measurable K) (I : Finset (Fin d)) (hI : I ⊆ P.e.support) (hne : I.Nonempty)

/-- **The data certificate of a piece atlas**: it is the constructed atlas of CCXXXVIII over the
piece density, with an amplitude equal to `pieceAmp` on the base and the closed normal ball. -/
def IsPieceAtlasData
    (At : FiniteScalarUnitAtlas (d - (I.card - 1 + 1)) (R.pieceIntegral D ε i I F K p)) : Prop :=
  ∃ (q' : (Fin (d - (I.card - 1 + 1)) → ℝ) → ℝ)
    (A' : (Fin (d - (I.card - 1 + 1)) → ℝ) → (Fin (I.card - 1 + 1) → ℝ) → ℝ)
    (hq'c : Continuous q')
    (hq'pos : ∀ z ∈ (P.pieceDensity hε hεb hD I hI hne p).base, 0 < q' z)
    (hA'c : Continuous (Function.uncurry A'))
    (hk : ∀ a, 0 < normalHalfExp I hne P.e a)
    (hbase : IsCompact (P.pieceDensity hε hεb hD I hI hne p).base)
    (hβ : IntegrableOn (P.pieceDensity hε hεb hD I hI hne p).beta
      (P.pieceDensity hε hεb hD I hI hne p).base)
    (hamp' : ∀ z ∈ (P.pieceDensity hε hεb hD I hI hne p).base,
      ∀ n ∈ Metric.ball (0 : Fin (I.card - 1 + 1) → ℝ) ε,
        (P.pieceDensity hε hεb hD I hI hne p).amp z n *
          F ((R.chart i).φ (planeSplit (stratumSplit I hne) (z, n))) =
          A' z n * ∏ a, |n a| ^ normalExp I hne P.h a)
    (hphase' : ∀ z ∈ (P.pieceDensity hε hεb hD I hI hne p).base,
      ∀ n ∈ Metric.ball (0 : Fin (I.card - 1 + 1) → ℝ) ε,
        K ((R.chart i).Φ (planeSplit (stratumSplit I hne) (z, n))) =
          q' z * ∏ a, n a ^ (2 * normalHalfExp I hne P.e a)),
    (∀ z ∈ (P.pieceDensity hε hεb hD I hI hne p).base,
      ∀ n ∈ Metric.closedBall (0 : Fin (I.card - 1 + 1) → ℝ) ε,
        A' z n = R.pieceAmp i I hne P.h P.v (F := F) (p := p) z n) ∧
    At = R.pieceAtlas i D hε I hne (P.pieceDensity hε hεb hD I hI hne p) hbase hβ rfl
      (normalExp I hne P.h) (normalHalfExp I hne P.e) hk q' hq'c hq'pos A' hA'c hamp' hphase' hFm
      hF hK hK0

include hFc hpc in
/-- **Every stratum piece of a product chart has a piece atlas with exposed cells**, all at the
divisor pair of the stratum. -/
theorem exists_pieceAtlas_data :
    ∃ At : FiniteScalarUnitAtlas (d - (I.card - 1 + 1)) (R.pieceIntegral D ε i I F K p),
      (∀ σ, (At.cell σ).lam = P.pieceLam I hne) ∧ (∀ σ, (At.cell σ).mult = P.pieceMult I hne) ∧
      P.IsPieceAtlasData hK0 hε hεb hD hFm hF hK I hI hne At := by
  have hind : ∀ y ∈ (R.chart i).dom, P.u y = P.u (planeFoot (stratumSplit I hne) y) :=
    fun y hy => unit_indep_piece P.e.support P.T P.b P.u
      (fun y hy' => P.unit_indep y (P.mem_dom_of_mem_productDom hy')) I hne hI
      (P.mem_productDom_of_mem_dom hy)
  have hy₀ : ∃ y₀ ∈ P.W, ∀ j ∈ I, y₀ j = 0 := by
    obtain ⟨y₀, hy₀, hz⟩ := exists_zeroPoint P.e.support P.T P.b P.T_nonempty P.T_zero P.b_pos.le
    exact ⟨y₀, P.dom_subset (P.mem_dom_of_mem_productDom hy₀), fun j hj => hz j (hI hj)⟩
  obtain ⟨At, hlam, hmult, q', A', hq'c, hq'pos, hA'c, hk, hbase, hβ, hamp', hphase', -, hA',
      hAt⟩ :=
    R.exists_pieceAtlas_of_chart_data i D hε I hne P.e P.h hD hI hK0 P.W_open P.dom_subset P.u P.v
      P.u_cont P.u_ne P.phase_eq P.v_cont P.det_eq hind (P.pieceFootSet I)
      (P.isClosed_pieceFootSet I) P.pieceWeight
      (P.r_meas.comp (continuous_zeroOn _).measurable) (fun x => P.r_bound _)
      (P.piece_dom_iff hεb hD I hI hne) (P.piece_weight_eq I hI hne) hFc hpc hFm hF hK hy₀
  exact ⟨At, fun σ => (hlam σ).trans (P.pieceLam_eq hK0 I hI hne),
    fun σ => (hmult σ).trans (P.pieceMult_eq hK0 I hI hne),
    q', A', hq'c, hq'pos, hA'c, hk, hbase, hβ, hamp', hphase', hA', hAt⟩

/-- **The chosen piece atlas with exposed cells** (classical choice, once). -/
noncomputable def pieceAtlasD :
    FiniteScalarUnitAtlas (d - (I.card - 1 + 1)) (R.pieceIntegral D ε i I F K p) :=
  Classical.choose (P.exists_pieceAtlas_data hK0 hε hεb hD hFc hpc hFm hF hK I hI hne)

theorem pieceAtlasD_cell_lam (σ) :
    ((P.pieceAtlasD hK0 hε hεb hD hFc hpc hFm hF hK I hI hne).cell σ).lam = P.pieceLam I hne :=
  (Classical.choose_spec (P.exists_pieceAtlas_data hK0 hε hεb hD hFc hpc hFm hF hK I hI hne)).1 σ

theorem pieceAtlasD_cell_mult (σ) :
    ((P.pieceAtlasD hK0 hε hεb hD hFc hpc hFm hF hK I hI hne).cell σ).mult = P.pieceMult I hne :=
  (Classical.choose_spec
    (P.exists_pieceAtlas_data hK0 hε hεb hD hFc hpc hFm hF hK I hI hne)).2.1 σ

theorem pieceAtlasD_data :
    P.IsPieceAtlasData hK0 hε hεb hD hFm hF hK I hI hne
      (P.pieceAtlasD hK0 hε hεb hD hFc hpc hFm hF hK I hI hne) :=
  (Classical.choose_spec
    (P.exists_pieceAtlas_data hK0 hε hεb hD hFc hpc hFm hF hK I hI hne)).2.2

/-! ### Nonnegativity and positivity of the exposed cells -/

/-- **Every cell coefficient of a certified piece atlas is nonnegative** when the observable, the
prior and the cover-weight factor are nonnegative. -/
theorem cell_coeff_nonneg_of_data (hF0 : ∀ x, 0 ≤ F x) (hp0 : ∀ x, 0 ≤ p.w x)
    (hr0 : ∀ x, 0 ≤ P.r x)
    {At : FiniteScalarUnitAtlas (d - (I.card - 1 + 1)) (R.pieceIntegral D ε i I F K p)}
    (hAt : P.IsPieceAtlasData hK0 hε hεb hD hFm hF hK I hI hne At) (σ : At.ι) :
    0 ≤ (At.cell σ).coeff := by
  obtain ⟨q', A', hq'c, hq'pos, hA'c, hk, hbase, hβ, hamp', hphase', hA', rfl⟩ := hAt
  exact ScalarUnitCell.reflected_coeff_nonneg
    (R.pieceCell i D hε I hne (P.pieceDensity hε hεb hD I hI hne p) hbase hβ (normalExp I hne P.h)
      (normalHalfExp I hne P.e) hk q' hq'c hq'pos A' hA'c)
    (Eventually.of_forall fun z => P.pieceDensity_beta_nonneg hε hεb hD I hI hne p hr0 z)
    (fun z hz u hu => by
      change 0 ≤ A' z u
      rw [hA' z hz u hu]
      exact R.pieceAmp_nonneg i I hne P.h P.v hF0 hp0 z u) σ

/-- **Some cell coefficient of a certified piece atlas is positive** for an all-minimal stratum
whose dominant face has positive measure. -/
theorem exists_cell_coeff_pos_of_data (hF0 : ∀ x, 0 ≤ F x) (hp0 : ∀ x, 0 ≤ p.w x)
    (hr0 : ∀ x, 0 ≤ P.r x) (hall : ∀ j ∈ I, P.ratio j = P.pieceLam I hne)
    (hpos : 0 < volume (P.dominantFace D ε I hne F p))
    {At : FiniteScalarUnitAtlas (d - (I.card - 1 + 1)) (R.pieceIntegral D ε i I F K p)}
    (hAt : P.IsPieceAtlasData hK0 hε hεb hD hFm hF hK I hI hne At) :
    ∃ σ, 0 < (At.cell σ).coeff := by
  obtain ⟨q', A', hq'c, hq'pos, hA'c, hk, hbase, hβ, hamp', hphase', hA', rfl⟩ := hAt
  have hallc : ∀ a, ratioExp (normalExp I hne P.h) (normalHalfExp I hne P.e) a =
      minRatio (normalExp I hne P.h) (normalHalfExp I hne P.e) := fun a => by
    rw [ratioExp_normal_eq I hne P.e P.h (P.normalExp_eq_two_mul hK0 I hI hne) a,
      P.pieceLam_eq hK0 I hI hne]
    exact hall _ (stratumSplit_symm_inr_mem I hne a)
  have hbaseM : MeasurableSet (P.pieceDensity hε hεb hD I hI hne p).base :=
    hbase.isClosed.measurableSet
  refine ⟨(fun _ => false : Fin (I.card - 1 + 1) → Bool), lt_of_lt_of_eq
    (ScalarUnitCell.coeff_pos_of_all_minimal
      (R.pieceCell i D hε I hne (P.pieceDensity hε hεb hD I hI hne p) hbase hβ
        (normalExp I hne P.h) (normalHalfExp I hne P.e) hk q' hq'c hq'pos A' hA'c) hallc
      (Eventually.of_forall fun z => P.pieceDensity_beta_nonneg hε hεb hD I hI hne p hr0 z) ?_ ?_)
    (ScalarUnitCell.reflected_coeff_of_all_minimal _ hallc _).symm⟩
  · refine (ae_restrict_iff' hbaseM).2 (Eventually.of_forall fun z hz => ?_)
    change 0 ≤ A' z 0
    rw [hA' z hz 0 (Metric.mem_closedBall_self hε.le)]
    exact R.pieceAmp_nonneg i I hne P.h P.v hF0 hp0 z 0
  · refine lt_of_lt_of_le hpos (measure_mono fun z hz => ?_)
    have hzb := P.mem_pieceDensity_base_of_mem_dominantFace hε hεb hD I hI hne p hz
    obtain ⟨-, -, hr, hp, hFz, hv, ht⟩ := hz
    refine ⟨hzb, ?_, ?_⟩
    · change 0 < (P.pieceFootSet I).indicator P.pieceWeight (planeSplit (stratumSplit I hne) (z, 0))
      rw [Set.indicator_of_mem (P.foot_mem_pieceFootSet_of_mem_base hε hεb hD I hI hne p hzb)]
      exact hr
    · change 0 < A' z 0
      rw [hA' z hzb 0 (Metric.mem_closedBall_self hε.le)]
      exact mul_pos (mul_pos (mul_pos (abs_pos.2 hv) (abs_pos.2 ht)) hp) hFz

end Atlas

/-- The exponent of an all-minimal stratum. -/
theorem pieceLam_eq_of_forall {I : Finset (Fin d)} (hne : I.Nonempty) {lam₀ : ℝ}
    (hall : ∀ j ∈ I, P.ratio j = lam₀) : P.pieceLam I hne = lam₀ := by
  obtain ⟨j₀, hj₀⟩ := hne
  exact le_antisymm ((Finset.inf'_le _ hj₀).trans_eq (hall j₀ hj₀))
    (Finset.le_inf' _ _ fun j hj => (hall j hj).ge)

/-- The multiplicity of an all-minimal stratum is its cardinality. -/
theorem pieceMult_eq_card_of_forall {I : Finset (Fin d)} (hne : I.Nonempty) {lam₀ : ℝ}
    (hall : ∀ j ∈ I, P.ratio j = lam₀) : P.pieceMult I hne = I.card := by
  unfold pieceMult
  rw [Finset.filter_true_of_mem fun j hj =>
    (hall j hj).trans (P.pieceLam_eq_of_forall hne hall).symm]

end ProductMonomialChart

/-! ### The positive total coefficient of a cover of product charts -/

namespace ResolutionCover

variable {d : ℕ} {ι : Type*} [Fintype ι] (R : ResolutionCover d ι) {K : (Fin d → ℝ) → ℝ}
  (Ps : ∀ i, ProductMonomialChart R i K) (hK0 : ∀ x, 0 ≤ K x) {ε : ℝ} (hε : 0 < ε)
  (hεb : ∀ i, ε ≤ (Ps i).b) {F : (Fin d → ℝ) → ℝ} {p : TubeWeight d}
  (hFc : ∀ i, ContinuousOn (fun y => F ((R.chart i).φ y)) (Ps i).W)
  (hpc : ∀ i, ContinuousOn (fun y => p.w ((R.chart i).φ y)) (Ps i).W) (hFm : Measurable F)
  (hF : Integrable (fun x => F x * p.w x) (volume.restrict (⋃ i, R.image i))) (hK : Measurable K)

include hK0 hε hεb hFc hpc hFm hF hK in
/-- **The uniform family of piece atlases with exposed cells.** -/
noncomputable def productAtlasesD : ∀ (i : ι) (I : Finset (Fin d)), I ⊆ (Ps i).e.support →
    I.Nonempty → FiniteScalarUnitAtlas (d - (I.card - 1 + 1))
      (R.pieceIntegral (fun i => (Ps i).e.support) ε i I F K p) :=
  fun i I hI hne => (Ps i).pieceAtlasD hK0 hε (hεb i) rfl (hFc i) (hpc i) hFm hF hK I hI hne

include hK0 hε hεb hFc hpc hFm hF hK in
/-- **The total coefficient** at `(λ₀, k₀)`: the sum over all chart–stratum pairs of the tied cell
coefficients of the exposed atlases. -/
noncomputable def productCoeffD (lam₀ : ℝ) (k₀ : ℕ) : ℝ :=
  ∑ i, ∑ I ∈ (Ps i).e.support.powerset.filter (fun I => I.Nonempty),
    scalarAtlasPieceCoeff' (R.productAtlasesD Ps hK0 hε hεb hFc hpc hFm hF hK) lam₀ k₀ i I

include hK0 hε hεb hFc hpc hFm hF hK in
/-- **The end-to-end theorem with exposed atlases** (CCXLII with `productAtlasesD`). -/
theorem hasLeadingTerm_boltzmannIntegral_of_productChartsD (lam₀ : ℝ) (k₀ : ℕ)
    (hlam : ∀ i I, I ⊆ (Ps i).e.support → ∀ hne : I.Nonempty, lam₀ ≤ R.productPieceLam Ps i I hne)
    (hk : ∀ i I, I ⊆ (Ps i).e.support → ∀ hne : I.Nonempty,
      R.productPieceLam Ps i I hne = lam₀ → R.productPieceMult Ps i I hne - 1 ≤ k₀) :
    HasLeadingTerm (R.boltzmannIntegral F K p)
      (R.productCoeffD Ps hK0 hε hεb hFc hpc hFm hF hK lam₀ k₀) lam₀ k₀ :=
  R.hasLeadingTerm_boltzmannIntegral_of_scalarAtlases' (fun i => (Ps i).e) (fun i => (Ps i).h)
    (fun i => (Ps i).W) (fun i => (Ps i).monomial) hε hFm hF hK hK0
    (fun _ I => d - (I.card - 1 + 1)) (R.productAtlasesD Ps hK0 hε hεb hFc hpc hFm hF hK) lam₀ k₀
    (fun i I hI hne j =>
      (hlam i I hI hne).trans_eq ((R.productPieceLam_eq Ps hK0 i I hI hne).trans
        ((Ps i).pieceAtlasD_cell_lam hK0 hε (hεb i) rfl (hFc i) (hpc i) hFm hF hK I hI hne
          j).symm))
    (fun i I hI hne j hj => by
      have hj' : R.productPieceLam Ps i I hne = lam₀ :=
        (R.productPieceLam_eq Ps hK0 i I hI hne).trans
          (((Ps i).pieceAtlasD_cell_lam hK0 hε (hεb i) rfl (hFc i) (hpc i) hFm hF hK I hI hne
            j).symm.trans hj)
      have hm := (Ps i).pieceAtlasD_cell_mult hK0 hε (hεb i) rfl (hFc i) (hpc i) hFm hF hK I hI
        hne j
      calc ((R.productAtlasesD Ps hK0 hε hεb hFc hpc hFm hF hK i I hI hne).cell j).mult - 1
          = R.productPieceMult Ps i I hne - 1 := by
            change (((Ps i).pieceAtlasD hK0 hε (hεb i) rfl (hFc i) (hpc i) hFm hF hK I hI
              hne).cell j).mult - 1 = _
            rw [hm, R.productPieceMult_eq Ps hK0 i I hI hne]
        _ ≤ k₀ := hk i I hI hne hj')

include hK0 hε hεb hFc hpc hFm hF hK in
/-- **Every piece coefficient is nonnegative** for nonnegative `F`, `p` and cover-weight factors.
-/
theorem scalarAtlasPieceCoeff'_productAtlasesD_nonneg (hF0 : ∀ x, 0 ≤ F x)
    (hp0 : ∀ x, 0 ≤ p.w x) (hr0 : ∀ i x, 0 ≤ (Ps i).r x) (lam₀ : ℝ) (k₀ : ℕ) (i : ι)
    (I : Finset (Fin d)) :
    0 ≤ scalarAtlasPieceCoeff' (R.productAtlasesD Ps hK0 hε hεb hFc hpc hFm hF hK) lam₀ k₀ i I := by
  unfold scalarAtlasPieceCoeff'
  split_ifs with hI
  · exact Finset.sum_nonneg fun σ _ =>
      (Ps i).cell_coeff_nonneg_of_data hK0 hε (hεb i) rfl hFm hF hK I hI.1 hI.2 hF0 hp0 (hr0 i)
        ((Ps i).pieceAtlasD_data hK0 hε (hεb i) rfl (hFc i) (hpc i) hFm hF hK I hI.1 hI.2) σ
  · exact le_rfl

include hK0 hε hεb hFc hpc hFm hF hK in
/-- **The piece coefficient of an all-minimal stratum at its own pair is positive** when its
dominant face has positive measure. -/
theorem scalarAtlasPieceCoeff'_productAtlasesD_pos (hF0 : ∀ x, 0 ≤ F x) (hp0 : ∀ x, 0 ≤ p.w x)
    (hr0 : ∀ i x, 0 ≤ (Ps i).r x) {lam₀ : ℝ} {k₀ : ℕ} (i₀ : ι) (I₀ : Finset (Fin d))
    (hI₀ : I₀ ⊆ (Ps i₀).e.support) (hne₀ : I₀.Nonempty)
    (hall : ∀ j ∈ I₀, (Ps i₀).ratio j = lam₀) (hdeg : I₀.card - 1 = k₀)
    (hpos : 0 < volume ((Ps i₀).dominantFace (fun i => (Ps i).e.support) ε I₀ hne₀ F p)) :
    0 < scalarAtlasPieceCoeff' (R.productAtlasesD Ps hK0 hε hεb hFc hpc hFm hF hK) lam₀ k₀ i₀
      I₀ := by
  have hlam := (Ps i₀).pieceLam_eq_of_forall hne₀ hall
  have hall' : ∀ j ∈ I₀, (Ps i₀).ratio j = (Ps i₀).pieceLam I₀ hne₀ :=
    fun j hj => (hall j hj).trans hlam.symm
  rw [scalarAtlasPieceCoeff'_of_mem _ lam₀ k₀ i₀ I₀ hI₀ hne₀]
  refine FiniteScalarUnitAtlas.tiedCoeff_pos _ lam₀ k₀ (fun σ _ =>
    (Ps i₀).cell_coeff_nonneg_of_data hK0 hε (hεb i₀) rfl hFm hF hK I₀ hI₀ hne₀ hF0 hp0 (hr0 i₀)
      ((Ps i₀).pieceAtlasD_data hK0 hε (hεb i₀) rfl (hFc i₀) (hpc i₀) hFm hF hK I₀ hI₀ hne₀) σ) ?_
  obtain ⟨σ, hσ⟩ := (Ps i₀).exists_cell_coeff_pos_of_data hK0 hε (hεb i₀) rfl hFm hF hK I₀ hI₀
    hne₀ hF0 hp0 (hr0 i₀) hall' hpos
    ((Ps i₀).pieceAtlasD_data hK0 hε (hεb i₀) rfl (hFc i₀) (hpc i₀) hFm hF hK I₀ hI₀ hne₀)
  have h1 : ((R.productAtlasesD Ps hK0 hε hεb hFc hpc hFm hF hK i₀ I₀ hI₀ hne₀).cell σ).lam =
      lam₀ :=
    ((Ps i₀).pieceAtlasD_cell_lam hK0 hε (hεb i₀) rfl (hFc i₀) (hpc i₀) hFm hF hK I₀ hI₀ hne₀
      σ).trans hlam
  have h2 : ((R.productAtlasesD Ps hK0 hε hεb hFc hpc hFm hF hK i₀ I₀ hI₀ hne₀).cell σ).mult - 1 =
      k₀ := by
    change (((Ps i₀).pieceAtlasD hK0 hε (hεb i₀) rfl (hFc i₀) (hpc i₀) hFm hF hK I₀ hI₀
      hne₀).cell σ).mult - 1 = k₀
    rw [(Ps i₀).pieceAtlasD_cell_mult hK0 hε (hεb i₀) rfl (hFc i₀) (hpc i₀) hFm hF hK I₀ hI₀ hne₀
      σ, (Ps i₀).pieceMult_eq_card_of_forall hne₀ hall, hdeg]
  exact ⟨σ, Finset.mem_filter.2 ⟨Finset.mem_univ _, h1, h2⟩, hσ⟩

include hK0 hε hεb hFc hpc hFm hF hK in
/-- **The total coefficient is positive** under the dominant-face positive-mass hypothesis for one
all-minimal chart–stratum pair at `(λ₀, k₀)`. -/
theorem productCoeffD_pos (hF0 : ∀ x, 0 ≤ F x) (hp0 : ∀ x, 0 ≤ p.w x)
    (hr0 : ∀ i x, 0 ≤ (Ps i).r x) {lam₀ : ℝ} {k₀ : ℕ} (i₀ : ι) (I₀ : Finset (Fin d))
    (hI₀ : I₀ ⊆ (Ps i₀).e.support) (hne₀ : I₀.Nonempty)
    (hall : ∀ j ∈ I₀, (Ps i₀).ratio j = lam₀) (hdeg : I₀.card - 1 = k₀)
    (hpos : 0 < volume ((Ps i₀).dominantFace (fun i => (Ps i).e.support) ε I₀ hne₀ F p)) :
    0 < R.productCoeffD Ps hK0 hε hεb hFc hpc hFm hF hK lam₀ k₀ :=
  Finset.sum_pos'
    (fun i _ => Finset.sum_nonneg fun I _ =>
      R.scalarAtlasPieceCoeff'_productAtlasesD_nonneg Ps hK0 hε hεb hFc hpc hFm hF hK hF0 hp0 hr0
        lam₀ k₀ i I)
    ⟨i₀, Finset.mem_univ _, Finset.sum_pos'
      (fun I _ => R.scalarAtlasPieceCoeff'_productAtlasesD_nonneg Ps hK0 hε hεb hFc hpc hFm hF hK
        hF0 hp0 hr0 lam₀ k₀ i₀ I)
      ⟨I₀, Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hI₀, hne₀⟩,
        R.scalarAtlasPieceCoeff'_productAtlasesD_pos Ps hK0 hε hεb hFc hpc hFm hF hK hF0 hp0 hr0 i₀
          I₀ hI₀ hne₀ hall hdeg hpos⟩⟩

include hK0 hε hεb hFc hpc hFm hF hK in
/-- **Genuine asymptotic equivalence** `Z_N[F] ~ c · N^{−λ₀} (log N)^{k₀}` with `c > 0`: the
end-to-end certificate at a dominating pair `(λ₀, k₀)` together with one all-minimal chart–stratum
pair at `(λ₀, k₀)` whose dominant face has positive measure. -/
theorem boltzmannIntegral_isEquivalent_of_productCharts (lam₀ : ℝ) (k₀ : ℕ)
    (hlam : ∀ i I, I ⊆ (Ps i).e.support → ∀ hne : I.Nonempty, lam₀ ≤ R.productPieceLam Ps i I hne)
    (hk : ∀ i I, I ⊆ (Ps i).e.support → ∀ hne : I.Nonempty,
      R.productPieceLam Ps i I hne = lam₀ → R.productPieceMult Ps i I hne - 1 ≤ k₀)
    (hF0 : ∀ x, 0 ≤ F x) (hp0 : ∀ x, 0 ≤ p.w x) (hr0 : ∀ i x, 0 ≤ (Ps i).r x) (i₀ : ι)
    (I₀ : Finset (Fin d)) (hI₀ : I₀ ⊆ (Ps i₀).e.support) (hne₀ : I₀.Nonempty)
    (hall : ∀ j ∈ I₀, (Ps i₀).ratio j = lam₀) (hdeg : I₀.card - 1 = k₀)
    (hpos : 0 < volume ((Ps i₀).dominantFace (fun i => (Ps i).e.support) ε I₀ hne₀ F p)) :
    0 < R.productCoeffD Ps hK0 hε hεb hFc hpc hFm hF hK lam₀ k₀ ∧
      R.boltzmannIntegral F K p ~[atTop] fun N =>
        R.productCoeffD Ps hK0 hε hεb hFc hpc hFm hF hK lam₀ k₀ * powLogScale lam₀ k₀ N :=
  have hc := R.productCoeffD_pos Ps hK0 hε hεb hFc hpc hFm hF hK hF0 hp0 hr0 i₀ I₀ hI₀ hne₀ hall
    hdeg hpos
  ⟨hc, (R.hasLeadingTerm_boltzmannIntegral_of_productChartsD Ps hK0 hε hεb hFc hpc hFm hF hK lam₀
    k₀ hlam hk).isEquivalent hc.ne'⟩

/-- **An extremal stratum exists**: a chart `i₀` and a nonempty `I₀ ⊆ supp e_{i₀}` with every ratio
equal to `λ*` and `|I₀| − 1 = k*`. -/
theorem exists_extremal_stratum (hact : (R.activeCoords Ps).Nonempty) :
    ∃ (i₀ : ι) (I₀ : Finset (Fin d)), I₀ ⊆ (Ps i₀).e.support ∧ I₀.Nonempty ∧
      (∀ j ∈ I₀, (Ps i₀).ratio j = R.coverLam Ps hact) ∧ I₀.card - 1 = R.coverDeg Ps hact := by
  classical
  obtain ⟨⟨i₁, j₁⟩, hmem, hmin⟩ :=
    Finset.exists_mem_eq_inf' hact fun x : Σ _ : ι, Fin d => (Ps x.1).ratio x.2
  have hne : (Finset.univ.filter fun i => ∃ j ∈ (Ps i).e.support,
      (Ps i).ratio j = R.coverLam Ps hact).Nonempty :=
    ⟨i₁, Finset.mem_filter.2 ⟨Finset.mem_univ _, j₁, (Finset.mem_sigma.1 hmem).2, hmin.symm⟩⟩
  obtain ⟨i₀, hi₀, hsup⟩ := Finset.exists_mem_eq_sup _ hne
    fun i => ((Ps i).e.support.filter fun j => (Ps i).ratio j = R.coverLam Ps hact).card - 1
  obtain ⟨-, j₀, hj₀, hj₀'⟩ := Finset.mem_filter.1 hi₀
  exact ⟨i₀, (Ps i₀).e.support.filter fun j => (Ps i₀).ratio j = R.coverLam Ps hact,
    Finset.filter_subset _ _, ⟨j₀, Finset.mem_filter.2 ⟨hj₀, hj₀'⟩⟩,
    fun j hj => (Finset.mem_filter.1 hj).2, hsup.symm⟩

include hK0 hε hεb hFc hpc hFm hF hK in
/-- **THE IDENTIFIED LEADING PAIR OF A COVER OF PRODUCT CHARTS**: with an active divisor
coordinate, nonnegative `F`, `p` and cover-weight factors, and an extremal stratum `I₀` of chart
`i₀` (all divisor ratios `= λ*`, `|I₀| − 1 = k*`) whose dominant face has positive measure,
`Z_N[F] ~ c · N^{−λ*} (log N)^{k*}` with `c > 0`. -/
theorem boltzmannIntegral_isEquivalent_of_productCharts_extremal
    (hact : (R.activeCoords Ps).Nonempty) (hF0 : ∀ x, 0 ≤ F x) (hp0 : ∀ x, 0 ≤ p.w x)
    (hr0 : ∀ i x, 0 ≤ (Ps i).r x) (i₀ : ι) (I₀ : Finset (Fin d)) (hI₀ : I₀ ⊆ (Ps i₀).e.support)
    (hne₀ : I₀.Nonempty) (hall : ∀ j ∈ I₀, (Ps i₀).ratio j = R.coverLam Ps hact)
    (hdeg : I₀.card - 1 = R.coverDeg Ps hact)
    (hpos : 0 < volume ((Ps i₀).dominantFace (fun i => (Ps i).e.support) ε I₀ hne₀ F p)) :
    0 < R.productCoeffD Ps hK0 hε hεb hFc hpc hFm hF hK (R.coverLam Ps hact) (R.coverDeg Ps hact) ∧
      R.boltzmannIntegral F K p ~[atTop] fun N =>
        R.productCoeffD Ps hK0 hε hεb hFc hpc hFm hF hK (R.coverLam Ps hact) (R.coverDeg Ps hact) *
          powLogScale (R.coverLam Ps hact) (R.coverDeg Ps hact) N :=
  R.boltzmannIntegral_isEquivalent_of_productCharts Ps hK0 hε hεb hFc hpc hFm hF hK
    (R.coverLam Ps hact) (R.coverDeg Ps hact)
    (fun i I hI hne => by
      rw [R.productPieceLam_eq Ps hK0 i I hI hne]
      exact R.coverLam_le_pieceLam Ps hact i I hI hne)
    (fun i I hI hne hlam => by
      rw [R.productPieceLam_eq Ps hK0 i I hI hne] at hlam
      rw [R.productPieceMult_eq Ps hK0 i I hI hne]
      exact R.pieceMult_le_coverDeg Ps hact i I hI hne hlam)
    hF0 hp0 hr0 i₀ I₀ hI₀ hne₀ hall hdeg hpos

end ResolutionCover

end Grammar
