/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.VariableUnitPieceAtlas
import Grammar.ProductChartPositivity

/-!
# Product charts with normal-dependent units (CCLX)

The product-chart hypothesis package **without** `unit_indep`, and the end-to-end leading-term,
positivity and asymptotic-equivalence theorems for a cover of such charts.

* `ProductMonomialChartVar`: the fields of `ProductMonomialChart` minus the independence of the
  phase unit from the active coordinates; the forgetful map `ProductMonomialChart.toVar`; the
  exponent bookkeeping (`ratio`, `pieceLam`, `pieceMult`, cover-level `coverLamV`, `coverDegV`)
  agrees with the scalar package under the forgetful map (`rfl`).
* **Variable-unit cells are nonnegative** for nonnegative weight and amplitude
  (`VarUnitCell.coeff_nonneg`, `reflected_coeff_nonneg`), and in the all-minimal case the
  coefficient is that of the **frozen scalar cell** with unit `u(z, 0)`
  (`VarUnitCell.frozen`, `coeff_eq_frozen_of_all_minimal`), so positivity reduces to CCXL
  (`coeff_pos_of_all_minimal`).
* **Piece atlases with exposed cells** for every stratum of a variable-unit product chart
  (`IsVarPieceAtlasData`, `exists_varPieceAtlas_data`, `pieceAtlasV`), nonnegativity and
  positivity of the exposed coefficients, the uniform family `productAtlasesV`, the total
  coefficient `productCoeffV`, and ★★ `boltzmannIntegral_isEquivalent_of_productChartsV(_extremal)`:
  `Z_N[F] ~ c · N^{−λ*} (log N)^{k*}` with `c > 0` for a cover of product monomial charts whose
  phase units depend on all coordinates — the `unit_indep` hypothesis of CCXLV is removed.
-/

open MeasureTheory Set Filter Topology Asymptotics Monomialize.Analytic Monomialize.VolumeScaling
open scoped ENNReal

namespace Grammar

/-! ### The package -/

/-- **A centred product monomial chart with compatible cover weight and a general phase unit**:
`ProductMonomialChart` without the field `unit_indep`. -/
structure ProductMonomialChartVar {d : ℕ} {ι : Type*} [Fintype ι] (R : ResolutionCover d ι)
    (i : ι) (K : (Fin d → ℝ) → ℝ) where
  /-- The phase exponents. -/
  e : Fin d →₀ ℕ
  /-- The Jacobian exponents. -/
  h : Fin d →₀ ℕ
  /-- The open monomial neighbourhood of the domain. -/
  W : Set (Fin d → ℝ)
  W_open : IsOpen W
  dom_subset : (R.chart i).dom ⊆ W
  /-- hironaka's monomial-chart certificate. -/
  monomial : IsMonomialChart K (R.chart i).φ (R.chart i).dom e h W
  /-- The phase unit (continuous, nonvanishing; no independence hypothesis). -/
  u : (Fin d → ℝ) → ℝ
  u_cont : ContinuousOn u W
  u_ne : ∀ y ∈ W, u y ≠ 0
  phase_eq : ∀ y ∈ W, K ((R.chart i).φ y) = u y * monomialEval y e
  /-- The Jacobian unit. -/
  v : (Fin d → ℝ) → ℝ
  v_cont : ContinuousOn v W
  det_eq : ∀ y ∈ W, (fderiv ℝ (R.chart i).φ y).det = v y * monomialEval y h
  /-- The compact inactive base. -/
  T : Set (Fin d → ℝ)
  T_compact : IsCompact T
  T_nonempty : T.Nonempty
  T_zero : ∀ x ∈ T, ∀ j ∈ e.support, x j = 0
  /-- The normal radius. -/
  b : ℝ
  b_pos : 0 < b
  dom_eq : (R.chart i).dom = productDom e.support T b
  /-- The inactive factor of the cover weight. -/
  r : (Fin d → ℝ) → ℝ
  r_meas : Measurable r
  /-- A bound of the weight factor. -/
  Cr : ℝ
  r_bound : ∀ x, |r x| ≤ Cr
  weight_eq : ∀ y ∈ (R.chart i).dom, R.weight i ((R.chart i).Φ y) = r (zeroOn e.support y)

/-- The forgetful map: a product chart with a normal-independent unit is a product chart. -/
def ProductMonomialChart.toVar {d : ℕ} {ι : Type*} [Fintype ι] {R : ResolutionCover d ι} {i : ι}
    {K : (Fin d → ℝ) → ℝ} (P : ProductMonomialChart R i K) : ProductMonomialChartVar R i K where
  e := P.e
  h := P.h
  W := P.W
  W_open := P.W_open
  dom_subset := P.dom_subset
  monomial := P.monomial
  u := P.u
  u_cont := P.u_cont
  u_ne := P.u_ne
  phase_eq := P.phase_eq
  v := P.v
  v_cont := P.v_cont
  det_eq := P.det_eq
  T := P.T
  T_compact := P.T_compact
  T_nonempty := P.T_nonempty
  T_zero := P.T_zero
  b := P.b
  b_pos := P.b_pos
  dom_eq := P.dom_eq
  r := P.r
  r_meas := P.r_meas
  Cr := P.Cr
  r_bound := P.r_bound
  weight_eq := P.weight_eq

namespace ProductMonomialChartVar

variable {d : ℕ} {ι : Type*} [Fintype ι] {R : ResolutionCover d ι} {i : ι} {K : (Fin d → ℝ) → ℝ}
  (P : ProductMonomialChartVar R i K)

/-- The normal-form ratio `(h_j+1)/e_j` of an active coordinate. -/
noncomputable def ratio (j : Fin d) : ℝ := ((P.h j : ℝ) + 1) / (P.e j : ℝ)

/-- The geometric exponent of stratum `I`: `min_{j ∈ I} (h_j+1)/e_j`. -/
noncomputable def pieceLam (I : Finset (Fin d)) (hne : I.Nonempty) : ℝ := I.inf' hne P.ratio

/-- The geometric multiplicity of stratum `I`: `#{j ∈ I : (h_j+1)/e_j = pieceLam}`. -/
noncomputable def pieceMult (I : Finset (Fin d)) (hne : I.Nonempty) : ℕ :=
  (I.filter fun j => P.ratio j = P.pieceLam I hne).card

theorem ratio_eq (j : Fin d) : P.ratio j = divisorRatio P.e P.h j := rfl

theorem mem_productDom_of_mem_dom {y : Fin d → ℝ} (hy : y ∈ (R.chart i).dom) :
    y ∈ productDom P.e.support P.T P.b := P.dom_eq ▸ hy

theorem mem_dom_of_mem_productDom {y : Fin d → ℝ} (hy : y ∈ productDom P.e.support P.T P.b) :
    y ∈ (R.chart i).dom := P.dom_eq.symm ▸ hy

/-- The foot set of stratum `I` for the chart. -/
def pieceFootSet (I : Finset (Fin d)) : Set (Fin d → ℝ) := footSet P.e.support P.T P.b I

/-- The inactive weight factor as a function on the ambient space. -/
def pieceWeight (x : Fin d → ℝ) : ℝ := P.r (zeroOn P.e.support x)

/-- Parity of the normal exponents of every stratum, from `K ≥ 0`. -/
theorem normalExp_eq_two_mul (hK0 : ∀ x, 0 ≤ K x) (I : Finset (Fin d)) (hI : I ⊆ P.e.support)
    (hne : I.Nonempty) (a : Fin (I.card - 1 + 1)) :
    normalExp I hne P.e a = 2 * normalHalfExp I hne P.e a := by
  obtain ⟨y₀, hy₀, hz⟩ := exists_zeroPoint P.e.support P.T P.b P.T_nonempty P.T_zero P.b_pos.le
  have hy₀W : y₀ ∈ P.W := P.dom_subset (P.mem_dom_of_mem_productDom hy₀)
  exact normalExp_eq_two_mul_halfExp I hne P.e P.W_open (K := fun y => K ((R.chart i).φ y))
    P.phase_eq (fun y _ => hK0 _) hy₀W (P.u_cont.continuousAt (P.W_open.mem_nhds hy₀W))
    (P.u_ne y₀ hy₀W) (fun j hj => hz j (hI hj)) a

theorem pieceLam_eq (hK0 : ∀ x, 0 ≤ K x) (I : Finset (Fin d)) (hI : I ⊆ P.e.support)
    (hne : I.Nonempty) :
    minRatio (normalExp I hne P.h) (normalHalfExp I hne P.e) = P.pieceLam I hne :=
  minRatio_normal_eq I hne P.e P.h (P.normalExp_eq_two_mul hK0 I hI hne)

theorem pieceMult_eq (hK0 : ∀ x, 0 ≤ K x) (I : Finset (Fin d)) (hI : I ⊆ P.e.support)
    (hne : I.Nonempty) :
    multCount (ratioExp (normalExp I hne P.h) (normalHalfExp I hne P.e))
      (minRatio (normalExp I hne P.h) (normalHalfExp I hne P.e)) = P.pieceMult I hne := by
  rw [multCount_normal_eq I hne P.e P.h (P.normalExp_eq_two_mul hK0 I hI hne),
    P.pieceLam_eq hK0 I hI hne]
  rfl

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

/-! ### The dominant face and the piece density -/

section Face

variable (D : ι → Finset (Fin d)) (ε : ℝ) (I : Finset (Fin d)) (hne : I.Nonempty)

/-- **The dominant face of the stratum piece `I`** in base coordinates (as for the scalar package).
-/
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

section Density

variable {ε : ℝ} (hε : 0 < ε) (hεb : ε ≤ P.b) {D : ι → Finset (Fin d)} (hD : D i = P.e.support)
  (I : Finset (Fin d)) (hI : I ⊆ P.e.support) (hne : I.Nonempty)

include hεb hD hI in
theorem piece_dom_iff : ∀ y ∈ sizePiece (D i) ε I,
    y ∈ (R.chart i).dom ↔ planeFoot (stratumSplit I hne) y ∈ P.pieceFootSet I := fun y hy => by
  rw [P.dom_eq]
  exact mem_productDom_iff_foot_mem_footSet P.e.support P.T P.b I hne hI hεb (hD ▸ hy)

theorem isClosed_pieceFootSet : IsClosed (P.pieceFootSet I) :=
  isClosed_footSet _ _ _ P.T_compact.isClosed I

include hI in
theorem piece_weight_eq : ∀ y ∈ sizePiece (D i) ε I, y ∈ (R.chart i).dom →
    R.weight i ((R.chart i).Φ y) = P.pieceWeight (planeFoot (stratumSplit I hne) y) :=
  fun _ _ hy => weight_factor_piece P.e.support P.T P.b (fun y => R.weight i ((R.chart i).Φ y))
    P.r (fun y hy' => P.weight_eq y (P.mem_dom_of_mem_productDom hy')) I hne hI
    (P.mem_productDom_of_mem_dom hy)

include hεb hD hI in
/-- **The adapted product density of the stratum piece** (as for the scalar package). -/
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

end ProductMonomialChartVar

/-! ### Nonnegativity and all-minimal positivity of variable-unit cells -/

namespace VarUnitCell

variable {t : ℕ} (c : VarUnitCell t)

/-- **Every variable-unit cell coefficient is nonnegative** for a nonnegative base weight and an
amplitude nonnegative on the base times the closed normal ball. -/
theorem coeff_nonneg (hβ : ∀ᵐ z ∂volume.restrict c.base, 0 ≤ c.βw z)
    (hA : ∀ z ∈ c.base, ∀ v ∈ Metric.closedBall (0 : Fin (c.n + 1) → ℝ) c.b, 0 ≤ c.A z v) :
    0 ≤ c.coeff := by
  have hbaseM : MeasurableSet c.base := c.base_compact.isClosed.measurableSet
  unfold coeff
  refine setIntegral_nonneg_of_ae_restrict ?_
  filter_upwards [hβ, (ae_restrict_iff' hbaseM).2 (Eventually.of_forall fun z (hz : z ∈ c.base) =>
    hz)] with z h1 hz
  refine mul_nonneg h1 ?_
  unfold varBoxFaceCoeff
  refine boxFaceCoeff_nonneg' c.k_pos c.lam_le c.lam_pos one_pos c.b_pos ?_ ?_
  · refine ContinuousOn.mul (c.A_cont.comp (continuous_const.prodMk continuous_id)).continuousOn ?_
    exact (c.u_cont.comp (continuous_const.prodMk continuous_id)).continuousOn.rpow_const
      fun v hv => Or.inl (c.u_pos_box hz hv).ne'
  · intro v hv
    exact mul_nonneg (hA z hz v (piBox_Icc_subset_closedBall c.b_pos.le hv))
      (Real.rpow_nonneg (c.u_pos_box hz hv).le _)

/-- The orthant cells inherit nonnegativity. -/
theorem reflected_coeff_nonneg (hβ : ∀ᵐ z ∂volume.restrict c.base, 0 ≤ c.βw z)
    (hA : ∀ z ∈ c.base, ∀ v ∈ Metric.closedBall (0 : Fin (c.n + 1) → ℝ) c.b, 0 ≤ c.A z v)
    (σ : Fin (c.n + 1) → Bool) : 0 ≤ (c.reflected σ).coeff :=
  (c.reflected σ).coeff_nonneg hβ fun z hz v hv =>
    hA z hz _ ((ScalarUnitCell.reflect_mem_closedBall_iff σ c.b_pos.le v).2 hv)

/-- **The frozen scalar cell**: the unit evaluated at the normal origin. -/
noncomputable def frozen : ScalarUnitCell t where
  n := c.n
  h := c.h
  k := c.k
  k_pos := c.k_pos
  b := c.b
  b_pos := c.b_pos
  A := c.A
  A_cont := c.A_cont
  base := c.base
  base_compact := c.base_compact
  βw := c.βw
  βw_int := c.βw_int
  q := fun z => c.u z 0
  q_cont := c.u_cont.comp (continuous_id.prodMk continuous_const)
  q_pos := fun z hz => c.u_pos z hz 0 (Metric.mem_closedBall_self c.b_pos.le)

theorem frozen_lam : c.frozen.lam = c.lam := rfl

theorem frozen_mult : c.frozen.mult = c.mult := rfl

/-- **In the all-minimal case the coefficient is that of the frozen cell**: the face is the
normal origin, so freezing the unit there loses nothing. -/
theorem coeff_eq_frozen_of_all_minimal (hall : ∀ i, ratioExp c.h c.k i = c.lam) :
    c.coeff = c.frozen.coeff := by
  unfold coeff ScalarUnitCell.coeff
  refine setIntegral_congr_fun c.base_compact.isClosed.measurableSet fun z _ => ?_
  congr 1
  change varBoxFaceCoeff c.n c.h c.k c.b c.u c.A c.lam z =
    scalarBoxFaceCoeff c.n c.h c.k c.b (fun z => c.u z 0) c.A c.lam z
  unfold varBoxFaceCoeff scalarBoxFaceCoeff
  rw [boxFaceCoeff_of_all_minimal c.h c.k hall 1 c.b _ z,
    boxFaceCoeff_of_all_minimal c.h c.k hall 1 c.b c.A z]
  ring

/-- In the all-minimal case the reflected coefficients all equal the coefficient. -/
theorem reflected_coeff_of_all_minimal (hall : ∀ i, ratioExp c.h c.k i = c.lam)
    (σ : Fin (c.n + 1) → Bool) : (c.reflected σ).coeff = c.coeff := by
  have hall' : ∀ i, ratioExp (c.reflected σ).h (c.reflected σ).k i = (c.reflected σ).lam := hall
  rw [(c.reflected σ).coeff_eq_frozen_of_all_minimal hall', c.coeff_eq_frozen_of_all_minimal hall,
    (c.reflected σ).frozen.coeff_of_all_minimal' hall', c.frozen.coeff_of_all_minimal' hall]
  congr 1
  refine setIntegral_congr_fun c.base_compact.isClosed.measurableSet fun z _ => ?_
  change c.βw z * (c.u z (reflect σ 0) ^ (-c.lam) * c.A z (reflect σ 0)) =
    c.βw z * (c.u z 0 ^ (-c.lam) * c.A z 0)
  rw [ScalarUnitCell.reflect_zero]

/-- **Positivity of the all-minimal coefficient** (through the frozen cell, CCXL). -/
theorem coeff_pos_of_all_minimal (hall : ∀ i, ratioExp c.h c.k i = c.lam)
    (hβ : ∀ᵐ z ∂volume.restrict c.base, 0 ≤ c.βw z)
    (hA : ∀ᵐ z ∂volume.restrict c.base, 0 ≤ c.A z 0)
    (hpos : 0 < volume (c.base ∩ {z | 0 < c.βw z ∧ 0 < c.A z 0})) : 0 < c.coeff := by
  rw [c.coeff_eq_frozen_of_all_minimal hall]
  exact c.frozen.coeff_pos_of_all_minimal hall hβ hA hpos

end VarUnitCell

/-- **Positive tied sums** of a variable-unit atlas. -/
theorem FiniteVarUnitAtlas.tiedCoeff_pos {t : ℕ} {Z : ℝ → ℝ} (At : FiniteVarUnitAtlas t Z)
    (lam₀ : ℝ) (k₀ : ℕ) (hnn : ∀ i ∈ At.tied lam₀ k₀, 0 ≤ (At.cell i).coeff)
    (hex : ∃ i ∈ At.tied lam₀ k₀, 0 < (At.cell i).coeff) :
    0 < ∑ i ∈ At.tied lam₀ k₀, (At.cell i).coeff :=
  Finset.sum_pos' hnn hex

/-! ### Piece atlases with exposed cells -/

namespace ProductMonomialChartVar

variable {d : ℕ} {ι : Type*} [Fintype ι] {R : ResolutionCover d ι} {i : ι} {K : (Fin d → ℝ) → ℝ}
  (P : ProductMonomialChartVar R i K)

section Atlas

variable (hK0 : ∀ x, 0 ≤ K x) {ε : ℝ} (hε : 0 < ε) (hεb : ε ≤ P.b)
  {D : ι → Finset (Fin d)} (hD : D i = P.e.support) {F : (Fin d → ℝ) → ℝ} {p : TubeWeight d}
  (hFc : ContinuousOn (fun y => F ((R.chart i).φ y)) P.W)
  (hpc : ContinuousOn (fun y => p.w ((R.chart i).φ y)) P.W) (hFm : Measurable F)
  (hF : Integrable (fun x => F x * p.w x) (volume.restrict (⋃ i, R.image i)))
  (hK : Measurable K) (I : Finset (Fin d)) (hI : I ⊆ P.e.support) (hne : I.Nonempty)

/-- **The data certificate of a variable-unit piece atlas**: the orthant atlas of CCLIX over the
piece density, with unit equal to the variable phase and amplitude equal to `pieceAmp` on the base
times the closed normal ball. -/
def IsVarPieceAtlasData
    (At : FiniteVarUnitAtlas (d - (I.card - 1 + 1)) (R.pieceIntegral D ε i I F K p)) : Prop :=
  ∃ (qv : (Fin (d - (I.card - 1 + 1)) → ℝ) → (Fin (I.card - 1 + 1) → ℝ) → ℝ)
    (A' : (Fin (d - (I.card - 1 + 1)) → ℝ) → (Fin (I.card - 1 + 1) → ℝ) → ℝ)
    (hqv : Continuous (Function.uncurry qv))
    (hqv_pos : ∀ z ∈ (P.pieceDensity hε hεb hD I hI hne p).base,
      ∀ n ∈ Metric.closedBall (0 : Fin (I.card - 1 + 1) → ℝ) ε, 0 < qv z n)
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
          qv z n * ∏ a, n a ^ (2 * normalHalfExp I hne P.e a)),
    (∀ z ∈ (P.pieceDensity hε hεb hD I hI hne p).base,
      ∀ n ∈ Metric.closedBall (0 : Fin (I.card - 1 + 1) → ℝ) ε,
        qv z n = varPhase I hne P.u P.e z n) ∧
    (∀ z ∈ (P.pieceDensity hε hεb hD I hI hne p).base,
      ∀ n ∈ Metric.closedBall (0 : Fin (I.card - 1 + 1) → ℝ) ε,
        A' z n = R.pieceAmp i I hne P.h P.v (F := F) (p := p) z n) ∧
    At = R.varPieceAtlas i D hε I hne (P.pieceDensity hε hεb hD I hI hne p) hbase hβ rfl
      (normalExp I hne P.h) (normalHalfExp I hne P.e) hk qv hqv hqv_pos A' hA'c hamp' hphase' hFm
      hF hK hK0

include hFc hpc in
/-- **Every stratum piece of a variable-unit product chart has a piece atlas with exposed cells**,
all at the divisor pair of the stratum — no independence hypothesis on the unit. -/
theorem exists_varPieceAtlas_data :
    ∃ At : FiniteVarUnitAtlas (d - (I.card - 1 + 1)) (R.pieceIntegral D ε i I F K p),
      (∀ σ, (At.cell σ).lam = P.pieceLam I hne) ∧ (∀ σ, (At.cell σ).mult = P.pieceMult I hne) ∧
      P.IsVarPieceAtlasData hK0 hε hεb hD hFm hF hK I hI hne At := by
  have hy₀ : ∃ y₀ ∈ P.W, ∀ j ∈ I, y₀ j = 0 := by
    obtain ⟨y₀, hy₀, hz⟩ := exists_zeroPoint P.e.support P.T P.b P.T_nonempty P.T_zero P.b_pos.le
    exact ⟨y₀, P.dom_subset (P.mem_dom_of_mem_productDom hy₀), fun j hj => hz j (hI hj)⟩
  obtain ⟨At, hlam, hmult, qv, A', hqv, hqv_pos, hA'c, hk, hbase, hβ, hamp', hphase', hq', hA',
      hAt⟩ :=
    R.exists_varPieceAtlas_of_chart_data i D hε I hne P.e P.h hD hI hK0 P.W_open P.dom_subset P.u
      P.v P.u_cont P.u_ne P.phase_eq P.v_cont P.det_eq (P.pieceFootSet I)
      (P.isClosed_pieceFootSet I) P.pieceWeight
      (P.r_meas.comp (continuous_zeroOn _).measurable) (fun x => P.r_bound _)
      (P.piece_dom_iff hεb hD I hI hne) (P.piece_weight_eq I hI hne) hFc hpc hFm hF hK hy₀
  exact ⟨At, fun σ => (hlam σ).trans (P.pieceLam_eq hK0 I hI hne),
    fun σ => (hmult σ).trans (P.pieceMult_eq hK0 I hI hne),
    qv, A', hqv, hqv_pos, hA'c, hk, hbase, hβ, hamp', hphase', hq', hA', hAt⟩

/-- **The chosen piece atlas with exposed cells** (classical choice, once). -/
noncomputable def pieceAtlasV :
    FiniteVarUnitAtlas (d - (I.card - 1 + 1)) (R.pieceIntegral D ε i I F K p) :=
  Classical.choose (P.exists_varPieceAtlas_data hK0 hε hεb hD hFc hpc hFm hF hK I hI hne)

theorem pieceAtlasV_cell_lam (σ) :
    ((P.pieceAtlasV hK0 hε hεb hD hFc hpc hFm hF hK I hI hne).cell σ).lam = P.pieceLam I hne :=
  (Classical.choose_spec
    (P.exists_varPieceAtlas_data hK0 hε hεb hD hFc hpc hFm hF hK I hI hne)).1 σ

theorem pieceAtlasV_cell_mult (σ) :
    ((P.pieceAtlasV hK0 hε hεb hD hFc hpc hFm hF hK I hI hne).cell σ).mult = P.pieceMult I hne :=
  (Classical.choose_spec
    (P.exists_varPieceAtlas_data hK0 hε hεb hD hFc hpc hFm hF hK I hI hne)).2.1 σ

theorem pieceAtlasV_data :
    P.IsVarPieceAtlasData hK0 hε hεb hD hFm hF hK I hI hne
      (P.pieceAtlasV hK0 hε hεb hD hFc hpc hFm hF hK I hI hne) :=
  (Classical.choose_spec
    (P.exists_varPieceAtlas_data hK0 hε hεb hD hFc hpc hFm hF hK I hI hne)).2.2

/-- **Every cell coefficient of a certified piece atlas is nonnegative** when the observable, the
prior and the cover-weight factor are nonnegative. -/
theorem cell_coeff_nonneg_of_data (hF0 : ∀ x, 0 ≤ F x) (hp0 : ∀ x, 0 ≤ p.w x)
    (hr0 : ∀ x, 0 ≤ P.r x)
    {At : FiniteVarUnitAtlas (d - (I.card - 1 + 1)) (R.pieceIntegral D ε i I F K p)}
    (hAt : P.IsVarPieceAtlasData hK0 hε hεb hD hFm hF hK I hI hne At) (σ : At.ι) :
    0 ≤ (At.cell σ).coeff := by
  obtain ⟨qv, A', hqv, hqv_pos, hA'c, hk, hbase, hβ, hamp', hphase', -, hA', rfl⟩ := hAt
  exact VarUnitCell.reflected_coeff_nonneg
    (R.varPieceCell i D hε I hne (P.pieceDensity hε hεb hD I hI hne p) hbase hβ
      (normalExp I hne P.h) (normalHalfExp I hne P.e) hk qv hqv hqv_pos A' hA'c)
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
    {At : FiniteVarUnitAtlas (d - (I.card - 1 + 1)) (R.pieceIntegral D ε i I F K p)}
    (hAt : P.IsVarPieceAtlasData hK0 hε hεb hD hFm hF hK I hI hne At) :
    ∃ σ, 0 < (At.cell σ).coeff := by
  obtain ⟨qv, A', hqv, hqv_pos, hA'c, hk, hbase, hβ, hamp', hphase', -, hA', rfl⟩ := hAt
  have hallc : ∀ a, ratioExp (normalExp I hne P.h) (normalHalfExp I hne P.e) a =
      minRatio (normalExp I hne P.h) (normalHalfExp I hne P.e) := fun a => by
    rw [ratioExp_normal_eq I hne P.e P.h (P.normalExp_eq_two_mul hK0 I hI hne) a,
      P.pieceLam_eq hK0 I hI hne]
    exact hall _ (stratumSplit_symm_inr_mem I hne a)
  have hbaseM : MeasurableSet (P.pieceDensity hε hεb hD I hI hne p).base :=
    hbase.isClosed.measurableSet
  refine ⟨(fun _ => false : Fin (I.card - 1 + 1) → Bool), lt_of_lt_of_eq
    (VarUnitCell.coeff_pos_of_all_minimal
      (R.varPieceCell i D hε I hne (P.pieceDensity hε hεb hD I hI hne p) hbase hβ
        (normalExp I hne P.h) (normalHalfExp I hne P.e) hk qv hqv hqv_pos A' hA'c) hallc
      (Eventually.of_forall fun z => P.pieceDensity_beta_nonneg hε hεb hD I hI hne p hr0 z) ?_ ?_)
    (VarUnitCell.reflected_coeff_of_all_minimal _ hallc _).symm⟩
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

end ProductMonomialChartVar

/-! ### The cover-level theorems -/

namespace ResolutionCover

variable {d : ℕ} {ι : Type*} [Fintype ι] (R : ResolutionCover d ι) {K : (Fin d → ℝ) → ℝ}

omit [Fintype ι] in
/-- The leading piece coefficient of a chart–stratum pair, unfolded. -/
theorem leadingAtlasPieceCoeff_of_mem {e : ι → Fin d →₀ ℕ} {Z : ι → Finset (Fin d) → ℝ → ℝ}
    (At : ∀ (i : ι) (I : Finset (Fin d)), I ⊆ (e i).support → I.Nonempty →
      FiniteLeadingAtlas (Z i I))
    (lam₀ : ℝ) (k₀ : ℕ) (i : ι) (I : Finset (Fin d)) (hI : I ⊆ (e i).support)
    (hne : I.Nonempty) :
    leadingAtlasPieceCoeff At lam₀ k₀ i I =
      ∑ j ∈ (At i I hI hne).tied lam₀ k₀, ((At i I hI hne).cell j).coeff :=
  dif_pos ⟨hI, hne⟩

variable (Ps : ∀ i, ProductMonomialChartVar R i K) (hK0 : ∀ x, 0 ≤ K x)

/-- The geometric pair of the chart–stratum piece `(i, I)`. -/
noncomputable def productPieceLamV (i : ι) (I : Finset (Fin d)) (hne : I.Nonempty) : ℝ :=
  minRatio (normalExp I hne (Ps i).h) (normalHalfExp I hne (Ps i).e)

noncomputable def productPieceMultV (i : ι) (I : Finset (Fin d)) (hne : I.Nonempty) : ℕ :=
  multCount (ratioExp (normalExp I hne (Ps i).h) (normalHalfExp I hne (Ps i).e))
    (R.productPieceLamV Ps i I hne)

include hK0 in
theorem productPieceLamV_eq (i : ι) (I : Finset (Fin d)) (hI : I ⊆ (Ps i).e.support)
    (hne : I.Nonempty) : R.productPieceLamV Ps i I hne = (Ps i).pieceLam I hne :=
  (Ps i).pieceLam_eq hK0 I hI hne

include hK0 in
theorem productPieceMultV_eq (i : ι) (I : Finset (Fin d)) (hI : I ⊆ (Ps i).e.support)
    (hne : I.Nonempty) : R.productPieceMultV Ps i I hne = (Ps i).pieceMult I hne :=
  (Ps i).pieceMult_eq hK0 I hI hne

/-- The active coordinates of the cover: pairs `(i, j)` with `j ∈ supp e_i`. -/
def activeCoordsV : Finset (Σ _ : ι, Fin d) := Finset.univ.sigma fun i => (Ps i).e.support

/-- **The extremal exponent** `λ* = min_{i, j ∈ J_i} (h_{ij}+1)/e_{ij}`. -/
noncomputable def coverLamV (hact : (R.activeCoordsV Ps).Nonempty) : ℝ :=
  (R.activeCoordsV Ps).inf' hact fun x => (Ps x.1).ratio x.2

/-- **The extremal log degree** `k*`. -/
noncomputable def coverDegV (hact : (R.activeCoordsV Ps).Nonempty) : ℕ :=
  (Finset.univ.filter fun i => ∃ j ∈ (Ps i).e.support, (Ps i).ratio j = R.coverLamV Ps hact).sup
    fun i => ((Ps i).e.support.filter fun j => (Ps i).ratio j = R.coverLamV Ps hact).card - 1

theorem mem_activeCoordsV {i : ι} {j : Fin d} (hj : j ∈ (Ps i).e.support) :
    (⟨i, j⟩ : Σ _ : ι, Fin d) ∈ R.activeCoordsV Ps :=
  Finset.mem_sigma.2 ⟨Finset.mem_univ i, hj⟩

theorem coverLamV_le_ratio (hact) {i : ι} {j : Fin d} (hj : j ∈ (Ps i).e.support) :
    R.coverLamV Ps hact ≤ (Ps i).ratio j :=
  Finset.inf'_le (fun x : Σ _ : ι, Fin d => (Ps x.1).ratio x.2) (R.mem_activeCoordsV Ps hj)

theorem coverLamV_le_pieceLam (hact) (i : ι) (I : Finset (Fin d)) (hI : I ⊆ (Ps i).e.support)
    (hne : I.Nonempty) : R.coverLamV Ps hact ≤ (Ps i).pieceLam I hne :=
  Finset.le_inf' hne _ fun _ hj => R.coverLamV_le_ratio Ps hact (hI hj)

theorem pieceMult_le_coverDegV (hact) (i : ι) (I : Finset (Fin d)) (hI : I ⊆ (Ps i).e.support)
    (hne : I.Nonempty) (hlam : (Ps i).pieceLam I hne = R.coverLamV Ps hact) :
    (Ps i).pieceMult I hne - 1 ≤ R.coverDegV Ps hact := by
  classical
  obtain ⟨j₀, hj₀, hmin⟩ := Finset.exists_mem_eq_inf' hne (Ps i).ratio
  have hattains : i ∈ Finset.univ.filter fun i => ∃ j ∈ (Ps i).e.support,
      (Ps i).ratio j = R.coverLamV Ps hact :=
    Finset.mem_filter.2 ⟨Finset.mem_univ i, j₀, hI hj₀, by
      unfold ProductMonomialChartVar.pieceLam at hlam
      rw [← hmin]
      exact hlam⟩
  refine le_trans ?_ (Finset.le_sup (f := fun i =>
    ((Ps i).e.support.filter fun j => (Ps i).ratio j = R.coverLamV Ps hact).card - 1) hattains)
  unfold ProductMonomialChartVar.pieceMult
  rw [hlam]
  exact Nat.sub_le_sub_right (Finset.card_le_card fun j hj => by
    rw [Finset.mem_filter] at hj ⊢
    exact ⟨hI hj.1, hj.2⟩) 1

/-- **An extremal stratum exists.** -/
theorem exists_extremal_stratumV (hact : (R.activeCoordsV Ps).Nonempty) :
    ∃ (i₀ : ι) (I₀ : Finset (Fin d)), I₀ ⊆ (Ps i₀).e.support ∧ I₀.Nonempty ∧
      (∀ j ∈ I₀, (Ps i₀).ratio j = R.coverLamV Ps hact) ∧ I₀.card - 1 = R.coverDegV Ps hact := by
  classical
  obtain ⟨⟨i₁, j₁⟩, hmem, hmin⟩ :=
    Finset.exists_mem_eq_inf' hact fun x : Σ _ : ι, Fin d => (Ps x.1).ratio x.2
  have hne : (Finset.univ.filter fun i => ∃ j ∈ (Ps i).e.support,
      (Ps i).ratio j = R.coverLamV Ps hact).Nonempty :=
    ⟨i₁, Finset.mem_filter.2 ⟨Finset.mem_univ _, j₁, (Finset.mem_sigma.1 hmem).2, hmin.symm⟩⟩
  obtain ⟨i₀, hi₀, hsup⟩ := Finset.exists_mem_eq_sup _ hne
    fun i => ((Ps i).e.support.filter fun j => (Ps i).ratio j = R.coverLamV Ps hact).card - 1
  obtain ⟨-, j₀, hj₀, hj₀'⟩ := Finset.mem_filter.1 hi₀
  exact ⟨i₀, (Ps i₀).e.support.filter fun j => (Ps i₀).ratio j = R.coverLamV Ps hact,
    Finset.filter_subset _ _, ⟨j₀, Finset.mem_filter.2 ⟨hj₀, hj₀'⟩⟩,
    fun j hj => (Finset.mem_filter.1 hj).2, hsup.symm⟩

variable {ε : ℝ} (hε : 0 < ε) (hεb : ∀ i, ε ≤ (Ps i).b) {F : (Fin d → ℝ) → ℝ} {p : TubeWeight d}
  (hFc : ∀ i, ContinuousOn (fun y => F ((R.chart i).φ y)) (Ps i).W)
  (hpc : ∀ i, ContinuousOn (fun y => p.w ((R.chart i).φ y)) (Ps i).W) (hFm : Measurable F)
  (hF : Integrable (fun x => F x * p.w x) (volume.restrict (⋃ i, R.image i))) (hK : Measurable K)

include hK0 hε hεb hFc hpc hFm hF hK in
/-- **The uniform family of variable-unit piece atlases with exposed cells.** -/
noncomputable def productAtlasesV : ∀ (i : ι) (I : Finset (Fin d)), I ⊆ (Ps i).e.support →
    I.Nonempty → FiniteVarUnitAtlas (d - (I.card - 1 + 1))
      (R.pieceIntegral (fun i => (Ps i).e.support) ε i I F K p) :=
  fun i I hI hne => (Ps i).pieceAtlasV hK0 hε (hεb i) rfl (hFc i) (hpc i) hFm hF hK I hI hne

include hK0 hε hεb hFc hpc hFm hF hK in
/-- **The total coefficient** at `(λ₀, k₀)`: the sum over all chart–stratum pairs of the tied cell
coefficients. -/
noncomputable def productCoeffV (lam₀ : ℝ) (k₀ : ℕ) : ℝ :=
  ∑ i, ∑ I ∈ (Ps i).e.support.powerset.filter (fun I => I.Nonempty),
    leadingAtlasPieceCoeff
      (fun i I hI hne => (R.productAtlasesV Ps hK0 hε hεb hFc hpc hFm hF hK i I hI hne).toLeading)
      lam₀ k₀ i I

include hK0 hε hεb hFc hpc hFm hF hK in
/-- **The end-to-end leading-term theorem for variable-unit product charts** (signed observable):
at any pair `(λ₀, k₀)` dominating every chart–stratum pair. -/
theorem hasLeadingTerm_boltzmannIntegral_of_productChartsV (lam₀ : ℝ) (k₀ : ℕ)
    (hlam : ∀ i I, I ⊆ (Ps i).e.support → ∀ hne : I.Nonempty,
      lam₀ ≤ R.productPieceLamV Ps i I hne)
    (hk : ∀ i I, I ⊆ (Ps i).e.support → ∀ hne : I.Nonempty,
      R.productPieceLamV Ps i I hne = lam₀ → R.productPieceMultV Ps i I hne - 1 ≤ k₀) :
    HasLeadingTerm (R.boltzmannIntegral F K p)
      (R.productCoeffV Ps hK0 hε hεb hFc hpc hFm hF hK lam₀ k₀) lam₀ k₀ :=
  R.hasLeadingTerm_boltzmannIntegral_of_leadingAtlases (fun i => (Ps i).e) (fun i => (Ps i).h)
    (fun i => (Ps i).W) (fun i => (Ps i).monomial) hε hFm hF hK hK0
    (fun i I hI hne => (R.productAtlasesV Ps hK0 hε hεb hFc hpc hFm hF hK i I hI hne).toLeading)
    lam₀ k₀
    (fun i I hI hne j =>
      (hlam i I hI hne).trans_eq ((R.productPieceLamV_eq Ps hK0 i I hI hne).trans
        ((Ps i).pieceAtlasV_cell_lam hK0 hε (hεb i) rfl (hFc i) (hpc i) hFm hF hK I hI hne
          j).symm))
    (fun i I hI hne j hj => by
      have hj' : R.productPieceLamV Ps i I hne = lam₀ :=
        (R.productPieceLamV_eq Ps hK0 i I hI hne).trans
          (((Ps i).pieceAtlasV_cell_lam hK0 hε (hεb i) rfl (hFc i) (hpc i) hFm hF hK I hI hne
            j).symm.trans hj)
      have hm := (Ps i).pieceAtlasV_cell_mult hK0 hε (hεb i) rfl (hFc i) (hpc i) hFm hF hK I hI
        hne j
      calc ((R.productAtlasesV Ps hK0 hε hεb hFc hpc hFm hF hK i I hI hne).toLeading.cell j).mult
            - 1 = R.productPieceMultV Ps i I hne - 1 := by
            change (((Ps i).pieceAtlasV hK0 hε (hεb i) rfl (hFc i) (hpc i) hFm hF hK I hI
              hne).cell j).mult - 1 = _
            rw [hm, R.productPieceMultV_eq Ps hK0 i I hI hne]
        _ ≤ k₀ := hk i I hI hne hj')

include hK0 hε hεb hFc hpc hFm hF hK in
/-- **Every piece coefficient is nonnegative** for nonnegative `F`, `p` and cover-weight factors.
-/
theorem leadingAtlasPieceCoeff_productAtlasesV_nonneg (hF0 : ∀ x, 0 ≤ F x)
    (hp0 : ∀ x, 0 ≤ p.w x) (hr0 : ∀ i x, 0 ≤ (Ps i).r x) (lam₀ : ℝ) (k₀ : ℕ) (i : ι)
    (I : Finset (Fin d)) :
    0 ≤ leadingAtlasPieceCoeff
      (fun i I hI hne => (R.productAtlasesV Ps hK0 hε hεb hFc hpc hFm hF hK i I hI hne).toLeading)
      lam₀ k₀ i I := by
  unfold leadingAtlasPieceCoeff
  split_ifs with hI
  · exact Finset.sum_nonneg fun σ _ =>
      (Ps i).cell_coeff_nonneg_of_data hK0 hε (hεb i) rfl hFm hF hK I hI.1 hI.2 hF0 hp0 (hr0 i)
        ((Ps i).pieceAtlasV_data hK0 hε (hεb i) rfl (hFc i) (hpc i) hFm hF hK I hI.1 hI.2) σ
  · exact le_rfl

include hK0 hε hεb hFc hpc hFm hF hK in
/-- **The piece coefficient of an all-minimal stratum at its own pair is positive** when its
dominant face has positive measure. -/
theorem leadingAtlasPieceCoeff_productAtlasesV_pos (hF0 : ∀ x, 0 ≤ F x) (hp0 : ∀ x, 0 ≤ p.w x)
    (hr0 : ∀ i x, 0 ≤ (Ps i).r x) {lam₀ : ℝ} {k₀ : ℕ} (i₀ : ι) (I₀ : Finset (Fin d))
    (hI₀ : I₀ ⊆ (Ps i₀).e.support) (hne₀ : I₀.Nonempty)
    (hall : ∀ j ∈ I₀, (Ps i₀).ratio j = lam₀) (hdeg : I₀.card - 1 = k₀)
    (hpos : 0 < volume ((Ps i₀).dominantFace (fun i => (Ps i).e.support) ε I₀ hne₀ F p)) :
    0 < leadingAtlasPieceCoeff
      (fun i I hI hne => (R.productAtlasesV Ps hK0 hε hεb hFc hpc hFm hF hK i I hI hne).toLeading)
      lam₀ k₀ i₀ I₀ := by
  have hlam := (Ps i₀).pieceLam_eq_of_forall hne₀ hall
  have hall' : ∀ j ∈ I₀, (Ps i₀).ratio j = (Ps i₀).pieceLam I₀ hne₀ :=
    fun j hj => (hall j hj).trans hlam.symm
  rw [leadingAtlasPieceCoeff_of_mem _ lam₀ k₀ i₀ I₀ hI₀ hne₀]
  refine FiniteVarUnitAtlas.tiedCoeff_pos
    (R.productAtlasesV Ps hK0 hε hεb hFc hpc hFm hF hK i₀ I₀ hI₀ hne₀) lam₀ k₀ (fun σ _ =>
    (Ps i₀).cell_coeff_nonneg_of_data hK0 hε (hεb i₀) rfl hFm hF hK I₀ hI₀ hne₀ hF0 hp0 (hr0 i₀)
      ((Ps i₀).pieceAtlasV_data hK0 hε (hεb i₀) rfl (hFc i₀) (hpc i₀) hFm hF hK I₀ hI₀ hne₀) σ) ?_
  obtain ⟨σ, hσ⟩ := (Ps i₀).exists_cell_coeff_pos_of_data hK0 hε (hεb i₀) rfl hFm hF hK I₀ hI₀
    hne₀ hF0 hp0 (hr0 i₀) hall' hpos
    ((Ps i₀).pieceAtlasV_data hK0 hε (hεb i₀) rfl (hFc i₀) (hpc i₀) hFm hF hK I₀ hI₀ hne₀)
  have h1 : ((R.productAtlasesV Ps hK0 hε hεb hFc hpc hFm hF hK i₀ I₀ hI₀ hne₀).cell σ).lam =
      lam₀ :=
    ((Ps i₀).pieceAtlasV_cell_lam hK0 hε (hεb i₀) rfl (hFc i₀) (hpc i₀) hFm hF hK I₀ hI₀ hne₀
      σ).trans hlam
  have h2 : ((R.productAtlasesV Ps hK0 hε hεb hFc hpc hFm hF hK i₀ I₀ hI₀ hne₀).cell σ).mult - 1 =
      k₀ := by
    change (((Ps i₀).pieceAtlasV hK0 hε (hεb i₀) rfl (hFc i₀) (hpc i₀) hFm hF hK I₀ hI₀
      hne₀).cell σ).mult - 1 = k₀
    rw [(Ps i₀).pieceAtlasV_cell_mult hK0 hε (hεb i₀) rfl (hFc i₀) (hpc i₀) hFm hF hK I₀ hI₀ hne₀
      σ, (Ps i₀).pieceMult_eq_card_of_forall hne₀ hall, hdeg]
  exact ⟨σ, Finset.mem_filter.2 ⟨Finset.mem_univ _, h1, h2⟩, hσ⟩

include hK0 hε hεb hFc hpc hFm hF hK in
/-- **The total coefficient is positive** under the dominant-face positive-mass hypothesis for one
all-minimal chart–stratum pair at `(λ₀, k₀)`. -/
theorem productCoeffV_pos (hF0 : ∀ x, 0 ≤ F x) (hp0 : ∀ x, 0 ≤ p.w x)
    (hr0 : ∀ i x, 0 ≤ (Ps i).r x) {lam₀ : ℝ} {k₀ : ℕ} (i₀ : ι) (I₀ : Finset (Fin d))
    (hI₀ : I₀ ⊆ (Ps i₀).e.support) (hne₀ : I₀.Nonempty)
    (hall : ∀ j ∈ I₀, (Ps i₀).ratio j = lam₀) (hdeg : I₀.card - 1 = k₀)
    (hpos : 0 < volume ((Ps i₀).dominantFace (fun i => (Ps i).e.support) ε I₀ hne₀ F p)) :
    0 < R.productCoeffV Ps hK0 hε hεb hFc hpc hFm hF hK lam₀ k₀ :=
  Finset.sum_pos'
    (fun i _ => Finset.sum_nonneg fun I _ =>
      R.leadingAtlasPieceCoeff_productAtlasesV_nonneg Ps hK0 hε hεb hFc hpc hFm hF hK hF0 hp0 hr0
        lam₀ k₀ i I)
    ⟨i₀, Finset.mem_univ _, Finset.sum_pos'
      (fun I _ => R.leadingAtlasPieceCoeff_productAtlasesV_nonneg Ps hK0 hε hεb hFc hpc hFm hF hK
        hF0 hp0 hr0 lam₀ k₀ i₀ I)
      ⟨I₀, Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hI₀, hne₀⟩,
        R.leadingAtlasPieceCoeff_productAtlasesV_pos Ps hK0 hε hεb hFc hpc hFm hF hK hF0 hp0 hr0 i₀
          I₀ hI₀ hne₀ hall hdeg hpos⟩⟩

include hK0 hε hεb hFc hpc hFm hF hK in
/-- **Asymptotic equivalence for variable-unit product charts**: `Z_N[F] ~ c · N^{−λ₀} (log N)^{k₀}`
with `c > 0`. -/
theorem boltzmannIntegral_isEquivalent_of_productChartsV (lam₀ : ℝ) (k₀ : ℕ)
    (hlam : ∀ i I, I ⊆ (Ps i).e.support → ∀ hne : I.Nonempty,
      lam₀ ≤ R.productPieceLamV Ps i I hne)
    (hk : ∀ i I, I ⊆ (Ps i).e.support → ∀ hne : I.Nonempty,
      R.productPieceLamV Ps i I hne = lam₀ → R.productPieceMultV Ps i I hne - 1 ≤ k₀)
    (hF0 : ∀ x, 0 ≤ F x) (hp0 : ∀ x, 0 ≤ p.w x) (hr0 : ∀ i x, 0 ≤ (Ps i).r x) (i₀ : ι)
    (I₀ : Finset (Fin d)) (hI₀ : I₀ ⊆ (Ps i₀).e.support) (hne₀ : I₀.Nonempty)
    (hall : ∀ j ∈ I₀, (Ps i₀).ratio j = lam₀) (hdeg : I₀.card - 1 = k₀)
    (hpos : 0 < volume ((Ps i₀).dominantFace (fun i => (Ps i).e.support) ε I₀ hne₀ F p)) :
    0 < R.productCoeffV Ps hK0 hε hεb hFc hpc hFm hF hK lam₀ k₀ ∧
      R.boltzmannIntegral F K p ~[atTop] fun N =>
        R.productCoeffV Ps hK0 hε hεb hFc hpc hFm hF hK lam₀ k₀ * powLogScale lam₀ k₀ N :=
  have hc := R.productCoeffV_pos Ps hK0 hε hεb hFc hpc hFm hF hK hF0 hp0 hr0 i₀ I₀ hI₀ hne₀ hall
    hdeg hpos
  ⟨hc, (R.hasLeadingTerm_boltzmannIntegral_of_productChartsV Ps hK0 hε hεb hFc hpc hFm hF hK lam₀
    k₀ hlam hk).isEquivalent hc.ne'⟩

include hK0 hε hεb hFc hpc hFm hF hK in
/-- **The certificate at the extremal pair** for variable-unit product charts (signed observable).
-/
theorem hasLeadingTerm_boltzmannIntegral_of_productChartsV_extremal
    (hact : (R.activeCoordsV Ps).Nonempty) :
    HasLeadingTerm (R.boltzmannIntegral F K p)
      (R.productCoeffV Ps hK0 hε hεb hFc hpc hFm hF hK (R.coverLamV Ps hact) (R.coverDegV Ps hact))
      (R.coverLamV Ps hact) (R.coverDegV Ps hact) :=
  R.hasLeadingTerm_boltzmannIntegral_of_productChartsV Ps hK0 hε hεb hFc hpc hFm hF hK
    (R.coverLamV Ps hact) (R.coverDegV Ps hact)
    (fun i I hI hne => by
      rw [R.productPieceLamV_eq Ps hK0 i I hI hne]
      exact R.coverLamV_le_pieceLam Ps hact i I hI hne)
    (fun i I hI hne hlam => by
      rw [R.productPieceLamV_eq Ps hK0 i I hI hne] at hlam
      rw [R.productPieceMultV_eq Ps hK0 i I hI hne]
      exact R.pieceMult_le_coverDegV Ps hact i I hI hne hlam)

include hK0 hε hεb hFc hpc hFm hF hK in
/-- ★★ **THE IDENTIFIED LEADING PAIR OF A COVER OF PRODUCT CHARTS WITH NORMAL-DEPENDENT UNITS**:
with an active divisor coordinate, nonnegative `F`, `p` and cover-weight factors, and an extremal
stratum `I₀` of chart `i₀` whose dominant face has positive measure,
`Z_N[F] ~ c · N^{−λ*} (log N)^{k*}` with `c > 0` — the phase units may depend on all coordinates. -/
theorem boltzmannIntegral_isEquivalent_of_productChartsV_extremal
    (hact : (R.activeCoordsV Ps).Nonempty) (hF0 : ∀ x, 0 ≤ F x) (hp0 : ∀ x, 0 ≤ p.w x)
    (hr0 : ∀ i x, 0 ≤ (Ps i).r x) (i₀ : ι) (I₀ : Finset (Fin d)) (hI₀ : I₀ ⊆ (Ps i₀).e.support)
    (hne₀ : I₀.Nonempty) (hall : ∀ j ∈ I₀, (Ps i₀).ratio j = R.coverLamV Ps hact)
    (hdeg : I₀.card - 1 = R.coverDegV Ps hact)
    (hpos : 0 < volume ((Ps i₀).dominantFace (fun i => (Ps i).e.support) ε I₀ hne₀ F p)) :
    0 < R.productCoeffV Ps hK0 hε hεb hFc hpc hFm hF hK (R.coverLamV Ps hact)
        (R.coverDegV Ps hact) ∧
      R.boltzmannIntegral F K p ~[atTop] fun N =>
        R.productCoeffV Ps hK0 hε hεb hFc hpc hFm hF hK (R.coverLamV Ps hact)
          (R.coverDegV Ps hact) * powLogScale (R.coverLamV Ps hact) (R.coverDegV Ps hact) N :=
  R.boltzmannIntegral_isEquivalent_of_productChartsV Ps hK0 hε hεb hFc hpc hFm hF hK
    (R.coverLamV Ps hact) (R.coverDegV Ps hact)
    (fun i I hI hne => by
      rw [R.productPieceLamV_eq Ps hK0 i I hI hne]
      exact R.coverLamV_le_pieceLam Ps hact i I hI hne)
    (fun i I hI hne hlam => by
      rw [R.productPieceLamV_eq Ps hK0 i I hI hne] at hlam
      rw [R.productPieceMultV_eq Ps hK0 i I hI hne]
      exact R.pieceMult_le_coverDegV Ps hact i I hI hne hlam)
    hF0 hp0 hr0 i₀ I₀ hI₀ hne₀ hall hdeg hpos

/-! ### Compatibility with the scalar package -/

variable (Qs : ∀ i, ProductMonomialChart R i K)

theorem activeCoordsV_toVar : R.activeCoordsV (fun i => (Qs i).toVar) = R.activeCoords Qs := rfl

theorem coverLamV_toVar (hact : (R.activeCoords Qs).Nonempty) :
    R.coverLamV (fun i => (Qs i).toVar) hact = R.coverLam Qs hact := rfl

theorem coverDegV_toVar (hact : (R.activeCoords Qs).Nonempty) :
    R.coverDegV (fun i => (Qs i).toVar) hact = R.coverDeg Qs hact := rfl

theorem productPieceLamV_toVar (i : ι) (I : Finset (Fin d)) (hne : I.Nonempty) :
    R.productPieceLamV (fun i => (Qs i).toVar) i I hne = R.productPieceLam Qs i I hne := rfl

theorem productPieceMultV_toVar (i : ι) (I : Finset (Fin d)) (hne : I.Nonempty) :
    R.productPieceMultV (fun i => (Qs i).toVar) i I hne = R.productPieceMult Qs i I hne := rfl

end ResolutionCover

end Grammar
