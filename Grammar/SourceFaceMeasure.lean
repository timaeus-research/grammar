/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.FacePieceMeasure
import Grammar.SourceAmplitudeLeadingTerm

/-!
# The source cell coefficient is an integral against a face measure (CCXCII)

Unit 2b of the global programme (consult #89). For a one-chart variable-unit product package `P`
on a monomial chart `C`, a stratum `I` and the orthants `σ`, the library's tied cell coefficients
of the source-weighted piece integral (`sourceAtlases`, a classical choice depending on the source
amplitude `G`) are shown to be integrals of `G` against measures that do NOT depend on `G`:

`Σ_σ ((P.sourceAtlases … I hI hne).cell σ).coeff
  = Σ_σ ∫ q, G (facePoint σ q) ∂(P.faceData … σ).measure`

(`sum_cell_coeff_eq`, summed over the orthants since the chosen cell index type is opaque), where
`facePoint σ (z, w) = Ψ(z, σ · (ε · faceProj w))` is the face point in
chart coordinates (tangential coordinate `z`, normal coordinate on the minimal face reflected into
the orthant `σ`) and the face measure `faceData` (CCXCI) has density
`β_w(z) · ε^{E} faceLeadConst · |v| |y_tang^h| (p∘φ) varPhase^{−λ} · residualWeight(u)`
on `base × unitBox`: the piece weight, the Jacobian unit, the tangential Jacobian monomial, the
prior, the frozen phase unit and the residual face weight. The `G`-free facts about the piece
(compact base, integrable weight, positive normal exponents, positive phase unit on the closed
normal ball) are read off the chosen atlas of the constant amplitude `G = 1`.

The pushforward of this measure along the face point map is the chart-level leading face piece
`facePiece σ : LeadingFacePiece d`; the next unit sums the tied pieces into the leading measure.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

namespace ProductMonomialChartVar

open ResolutionCover (ofChart)

variable {d : ℕ} {C : ResolutionChart d} {K : (Fin d → ℝ) → ℝ}
  (P : ProductMonomialChartVar (ofChart C) () K) (hK0 : ∀ x, 0 ≤ K x) (ε : ℝ) (hε : 0 < ε)
  (hεb : ε ≤ P.b) {p : TubeWeight d} (hpc : ContinuousOn (fun y => p.w (C.φ y)) P.W)
  (hK : Measurable K) (I : Finset (Fin d)) (hI : I ⊆ P.e.support) (hne : I.Nonempty)

/-- The normal face coordinate of the orthant `σ`: `σ · (ε · faceProj w)`. -/
noncomputable def faceNormal (σ : Fin (I.card - 1 + 1) → Bool) (w : Fin (I.card - 1 + 1) → ℝ) :
    Fin (I.card - 1 + 1) → ℝ :=
  reflect σ (ε • faceProj (normalExp I hne P.h) (normalHalfExp I hne P.e) (P.pieceLam I hne) w)

/-- The face point in chart coordinates. -/
noncomputable def facePoint (σ : Fin (I.card - 1 + 1) → Bool)
    (q : (Fin (d - (I.card - 1 + 1)) → ℝ) × (Fin (I.card - 1 + 1) → ℝ)) : Fin d → ℝ :=
  planeSplit (stratumSplit I hne) (q.1, P.faceNormal ε I hne σ q.2)

theorem continuous_faceNormal (σ : Fin (I.card - 1 + 1) → Bool) :
    Continuous (P.faceNormal ε I hne σ) :=
  (continuous_reflect σ).comp ((continuous_faceProj_pop _ _ _).const_smul ε)

theorem continuous_facePoint (σ : Fin (I.card - 1 + 1) → Bool) :
    Continuous (P.facePoint ε I hne σ) :=
  (planeSplit (stratumSplit I hne)).continuous.comp
    (continuous_fst.prodMk ((P.continuous_faceNormal ε I hne σ).comp continuous_snd))

include hε in
/-- The face normal of a point of the closed cube lies in the closed normal ball. -/
theorem faceNormal_mem_closedBall (σ : Fin (I.card - 1 + 1) → Bool)
    {w : Fin (I.card - 1 + 1) → ℝ} (hw : w ∈ closedCube (I.card - 1 + 1)) :
    P.faceNormal ε I hne σ w ∈ Metric.closedBall (0 : Fin (I.card - 1 + 1) → ℝ) ε := by
  unfold faceNormal
  rw [ScalarUnitCell.reflect_mem_closedBall_iff σ hε.le, mem_closedBall_zero_iff, norm_smul,
    Real.norm_eq_abs,
    abs_of_pos hε]
  refine (mul_le_of_le_one_right hε.le ?_)
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intro a
  simp only [faceProj, Real.norm_eq_abs]
  split_ifs
  · simp
  · exact abs_le.2 ⟨by linarith [(hw a (mem_univ a)).1], (hw a (mem_univ a)).2⟩

theorem measurable_pieceWeight : Measurable P.pieceWeight :=
  P.r_meas.comp (continuous_zeroOn _).measurable

section Facts

variable {ε}
include hK0 hε hεb hpc hK hI

/-- **The `G`-free facts about the piece**, read off the chosen atlas of the amplitude `1`. -/
theorem pieceFacts :
    IsCompact (P.pieceDensity hε hεb (D := fun _ => P.e.support) rfl I hI hne p).base ∧
      IntegrableOn (P.pieceDensity hε hεb (D := fun _ => P.e.support) rfl I hI hne p).beta
        (P.pieceDensity hε hεb (D := fun _ => P.e.support) rfl I hI hne p).base ∧
      (∀ a, 0 < normalHalfExp I hne P.e a) ∧
      ∀ z ∈ (P.pieceDensity hε hεb (D := fun _ => P.e.support) rfl I hI hne p).base,
        ∀ n ∈ Metric.closedBall (0 : Fin (I.card - 1 + 1) → ℝ) ε,
          0 < varPhase I hne P.u P.e z n := by
  obtain ⟨_, -, -, qv, A', hqv, hqv_pos, hA'c, hk, hbase, hβ, hamp', hphase', hq', hA', hAt⟩ :=
    P.exists_sourceVarPieceAtlas_data hK0 hε hεb (D := fun _ => P.e.support) rfl hpc
      (G := fun _ => (1 : ℝ)) measurable_const continuousOn_const hK I hI hne
  exact ⟨hbase, hβ, hk, fun z hz n hn => by rw [← hq' z hz n hn]; exact hqv_pos z hz n hn⟩

omit hK0 hpc hK in
/-- Face points over the base with normal coordinate in the closed ball lie in the chart domain. -/
theorem mem_dom_of_mem_base {z : Fin (d - (I.card - 1 + 1)) → ℝ}
    (hz : z ∈ (P.pieceDensity hε hεb (D := fun _ => P.e.support) rfl I hI hne p).base)
    {n : Fin (I.card - 1 + 1) → ℝ} (hn : n ∈ Metric.closedBall (0 : Fin (I.card - 1 + 1) → ℝ) ε) :
    planeSplit (stratumSplit I hne) (z, n) ∈ C.dom :=
  (ofChart C).mem_dom_of_mem_base_closedBall () (fun _ => P.e.support) hε I hne P.e rfl hI K p
    (P.pieceFootSet I) (P.isClosed_pieceFootSet I) P.pieceWeight
    (P.piece_dom_iff hεb (D := fun _ => P.e.support) rfl I hI hne)
    (P.piece_weight_eq (D := fun _ => P.e.support) (ε := ε) I hI hne) hz hn

end Facts

/-- **The `G`-free amplitude factor of the face density**: box constants, Jacobian unit,
tangential Jacobian monomial, prior and the frozen phase unit `|varPhase|^{−λ}`. -/
noncomputable def faceAmp (σ : Fin (I.card - 1 + 1) → Bool) (z : Fin (d - (I.card - 1 + 1)) → ℝ)
    (w : Fin (I.card - 1 + 1) → ℝ) : ℝ :=
  ε ^ (∑ a ∈ Finset.univ.filter (fun a => ¬ ratioExp (normalExp I hne P.h) (normalHalfExp I hne P.e)
        a = P.pieceLam I hne),
      (residualExponent (normalExp I hne P.h) (normalHalfExp I hne P.e) (P.pieceLam I hne) a + 1)) *
    (faceLeadConst (normalExp I hne P.h) (normalHalfExp I hne P.e) (P.pieceLam I hne) 1 *
      (|P.v (planeSplit (stratumSplit I hne) (z, P.faceNormal ε I hne σ w))| *
        |tangentialMonomial I hne P.h z| *
        p.w (((ofChart C).chart ()).φ
          (planeSplit (stratumSplit I hne) (z, P.faceNormal ε I hne σ w))) *
        |varPhase I hne P.u P.e z (P.faceNormal ε I hne σ w)| ^ (-(P.pieceLam I hne))))

variable {ε}

include hε in
theorem faceAmp_nonneg (hlam : 0 < P.pieceLam I hne) (hk : ∀ a, 0 < normalHalfExp I hne P.e a)
    (σ : Fin (I.card - 1 + 1) → Bool) (z : Fin (d - (I.card - 1 + 1)) → ℝ)
    (w : Fin (I.card - 1 + 1) → ℝ) : 0 ≤ P.faceAmp ε (p := p) I hne σ z w := by
  unfold faceAmp
  exact mul_nonneg (Real.rpow_nonneg hε.le _) (mul_nonneg
    (faceLeadConst_pos _ _ hk _ _ hlam one_pos).le (mul_nonneg (mul_nonneg (mul_nonneg
      (abs_nonneg _) (abs_nonneg _)) (p.nonneg _)) (Real.rpow_nonneg (abs_nonneg _) _)))

section Data

include hK0 hε hεb hpc hK hI

omit hK0 hpc hK in
/-- The face point map sends `base × closedCube` into the chart domain. -/
theorem mapsTo_facePoint (σ : Fin (I.card - 1 + 1) → Bool) :
    MapsTo (P.facePoint ε I hne σ)
      ((P.pieceDensity hε hεb (D := fun _ => P.e.support) rfl I hI hne p).base ×ˢ
        closedCube (I.card - 1 + 1)) C.dom := fun _ hq =>
  P.mem_dom_of_mem_base hε hεb I hI hne hq.1
    (P.faceNormal_mem_closedBall ε hε I hne σ hq.2)

/-- The amplitude factor is continuous on `base × closedCube`. -/
theorem continuousOn_faceAmp (σ : Fin (I.card - 1 + 1) → Bool) :
    ContinuousOn (Function.uncurry (P.faceAmp ε (p := p) I hne σ))
      ((P.pieceDensity hε hεb (D := fun _ => P.e.support) rfl I hI hne p).base ×ˢ
        closedCube (I.card - 1 + 1)) := by
  have hmaps := P.mapsTo_facePoint hε hεb (p := p) I hI hne σ
  have hmapsW : MapsTo (P.facePoint ε I hne σ) _ P.W := hmaps.mono_right P.dom_subset
  have hpos := (P.pieceFacts hK0 hε hεb hpc hK I hI hne).2.2.2
  refine continuousOn_const.mul (continuousOn_const.mul
    (ContinuousOn.mul (ContinuousOn.mul (ContinuousOn.mul ?_ ?_) ?_) ?_))
  · exact (P.v_cont.comp (P.continuous_facePoint ε I hne σ).continuousOn hmapsW).abs
  · exact ((continuous_tangentialMonomial I hne P.h).comp continuous_fst).continuousOn.abs
  · exact hpc.comp (P.continuous_facePoint ε I hne σ).continuousOn hmapsW
  · refine ContinuousOn.rpow_const ?_ fun q hq => Or.inl ?_
    · refine ContinuousOn.abs ?_
      unfold varPhase
      exact (P.u_cont.comp (P.continuous_facePoint ε I hne σ).continuousOn hmapsW).mul
        ((continuous_tangentialMonomial I hne P.e).comp continuous_fst).continuousOn
    · exact (abs_pos.2 (hpos q.1 hq.1 _
        (P.faceNormal_mem_closedBall ε hε I hne σ hq.2)).ne').ne'

/-- A bound for the amplitude factor on `base × closedCube`. -/
theorem exists_bound_faceAmp (σ : Fin (I.card - 1 + 1) → Bool) :
    ∃ M : ℝ, ∀ q ∈ (P.pieceDensity hε hεb (D := fun _ => P.e.support) rfl I hI hne p).base ×ˢ
      closedCube (I.card - 1 + 1), |P.faceAmp ε (p := p) I hne σ q.1 q.2| ≤ M := by
  obtain ⟨M, hM⟩ := ((P.pieceFacts hK0 hε hεb hpc hK I hI hne).1.prod
    (isCompact_closedCube _)).exists_bound_of_continuousOn
    (P.continuousOn_faceAmp hK0 hε hεb hpc hK I hI hne σ)
  exact ⟨M, fun q hq => by have := hM q hq; rwa [Real.norm_eq_abs] at this⟩

theorem pieceLam_pos : 0 < P.pieceLam I hne := by
  rw [← P.pieceLam_eq hK0 I hI hne]
  exact minRatio_pos _ _ (P.pieceFacts hK0 hε hεb hpc hK I hI hne).2.2.1

/-- ★ **The face weight data of the orthant `σ` of the stratum piece `I`.** -/
noncomputable def faceData (hr0 : ∀ x, 0 ≤ P.r x) (σ : Fin (I.card - 1 + 1) → Bool) :
    FaceWeightData (d - (I.card - 1 + 1)) (I.card - 1 + 1) where
  base := (P.pieceDensity hε hεb (D := fun _ => P.e.support) rfl I hI hne p).base
  base_compact := (P.pieceFacts hK0 hε hεb hpc hK I hI hne).1
  βw := (P.pieceDensity hε hεb (D := fun _ => P.e.support) rfl I hI hne p).beta
  βw_meas := by
    have : (P.pieceDensity hε hεb (D := fun _ => P.e.support) rfl I hI hne p).beta =
        fun z => (P.pieceFootSet I).indicator P.pieceWeight
          (planeSplit (stratumSplit I hne) (z, 0)) := rfl
    rw [this]
    exact (P.measurable_pieceWeight.indicator (P.isClosed_pieceFootSet I).measurableSet).comp
      ((planeSplit (stratumSplit I hne)).continuous.comp
        (continuous_id.prodMk continuous_const)).measurable
  βw_nonneg := P.pieceDensity_beta_nonneg hε hεb rfl I hI hne p hr0
  βw_int := (P.pieceFacts hK0 hε hεb hpc hK I hI hne).2.1
  h := normalExp I hne P.h
  k := normalHalfExp I hne P.e
  k_pos := (P.pieceFacts hK0 hε hεb hpc hK I hI hne).2.2.1
  l := P.pieceLam I hne
  l_le := fun a => by
    rw [← P.pieceLam_eq hK0 I hI hne]
    exact minRatio_le _ _ a
  B := P.faceAmp ε (p := p) I hne σ
  B_cont := (P.continuousOn_faceAmp hK0 hε hεb hpc hK I hI hne σ).mono
    (prod_mono_right (unitBox_subset_closedCube _))
  B_nonneg := P.faceAmp_nonneg hε I hne (P.pieceLam_pos hK0 hε hεb hpc hK I hI hne)
    (P.pieceFacts hK0 hε hεb hpc hK I hI hne).2.2.1 σ
  M := (P.exists_bound_faceAmp hK0 hε hεb hpc hK I hI hne σ).choose
  B_le := fun z hz u hu => (le_abs_self _).trans
    ((P.exists_bound_faceAmp hK0 hε hεb hpc hK I hI hne σ).choose_spec (z, u)
      ⟨hz, unitBox_subset_closedCube _ hu⟩)

theorem faceData_B (hr0 : ∀ x, 0 ≤ P.r x) (σ : Fin (I.card - 1 + 1) → Bool) :
    (P.faceData hK0 hε hεb hpc hK I hI hne hr0 σ).B = P.faceAmp ε (p := p) I hne σ := rfl

theorem faceData_h (hr0 : ∀ x, 0 ≤ P.r x) (σ : Fin (I.card - 1 + 1) → Bool) :
    (P.faceData hK0 hε hεb hpc hK I hI hne hr0 σ).h = normalExp I hne P.h := rfl

theorem faceData_k (hr0 : ∀ x, 0 ≤ P.r x) (σ : Fin (I.card - 1 + 1) → Bool) :
    (P.faceData hK0 hε hεb hpc hK I hI hne hr0 σ).k = normalHalfExp I hne P.e := rfl

theorem faceData_l (hr0 : ∀ x, 0 ≤ P.r x) (σ : Fin (I.card - 1 + 1) → Bool) :
    (P.faceData hK0 hε hεb hpc hK I hI hne hr0 σ).l = P.pieceLam I hne := rfl

/-- **The chart-level leading face piece of the orthant `σ` of the stratum piece `I`**: the face
measure pushed along the face point map into chart coordinates. -/
noncomputable def facePiece (hr0 : ∀ x, 0 ≤ P.r x) (σ : Fin (I.card - 1 + 1) → Bool) :
    LeadingFacePiece d where
  α := (Fin (d - (I.card - 1 + 1)) → ℝ) × (Fin (I.card - 1 + 1) → ℝ)
  measure := (P.faceData hK0 hε hεb hpc hK I hI hne hr0 σ).measure
  toTarget := P.facePoint ε I hne σ
  measurable_toTarget := (P.continuous_facePoint ε I hne σ).measurable

/-- ★★ **The orthant sum of the cell coefficients is the sum of the integrals of the source
amplitude against the face measures**: the chosen atlas depends on `G`, the measures do not. -/
theorem sum_cell_coeff_eq {G : (Fin d → ℝ) → ℝ} (hGm : Measurable G)
    (hGc : ContinuousOn G C.dom) (hr0 : ∀ x, 0 ≤ P.r x) :
    ∑ σ, ((P.sourceAtlases hK0 hε hεb hpc hGm hGc hK I hI hne).cell σ).coeff =
      ∑ σ : Fin (I.card - 1 + 1) → Bool, ∫ q, G (P.facePoint ε I hne σ q)
        ∂(P.faceData hK0 hε hεb hpc hK I hI hne hr0 σ).measure := by
  change ∑ σ, ((P.sourcePieceAtlasV hK0 hε hεb (D := fun _ => P.e.support) rfl hpc hGm hGc hK I hI
    hne).cell σ).coeff = _
  unfold sourcePieceAtlasV
  obtain ⟨-, -, qv, A', hqv, hqv_pos, hA'c, hk, hbase, hβ, hamp', hphase', hq', hA', hAt⟩ :=
    Classical.choose_spec (P.exists_sourceVarPieceAtlas_data hK0 hε hεb
      (D := fun _ => P.e.support) rfl hpc hGm hGc hK I hI hne)
  generalize Classical.choose (P.exists_sourceVarPieceAtlas_data hK0 hε hεb
      (D := fun _ => P.e.support) rfl hpc hGm hGc hK I hI hne) = At at hAt ⊢
  subst hAt
  refine Finset.sum_congr rfl fun (σ : Fin (I.card - 1 + 1) → Bool) _ => ?_
  have hcoeff := VarUnitCell.reflected_coeff_eq ((ofChart C).varPieceCell () (fun _ => P.e.support)
    hε I hne _ hbase hβ (normalExp I hne P.h) (normalHalfExp I hne P.e) hk qv hqv hqv_pos A' hA'c) σ
  change (((ofChart C).varPieceCell () (fun _ => P.e.support) hε I hne _ hbase hβ
    (normalExp I hne P.h) (normalHalfExp I hne P.e) hk qv hqv hqv_pos A' hA'c).reflected σ).coeff =
    _
  rw [hcoeff]
  obtain ⟨Mg, hMg⟩ := C.dom_compact.exists_bound_of_continuousOn hGc
  have hmaps := P.mapsTo_facePoint hε hεb (p := p) I hI hne σ
  rw [(P.faceData hK0 hε hεb hpc hK I hI hne hr0 σ).integral_measure
    (g := fun q => G (P.facePoint ε I hne σ q))
    (hGm.comp (P.continuous_facePoint ε I hne σ).measurable).aestronglyMeasurable (Mg := Mg)
    (fun q hq => by
      rw [← Real.norm_eq_abs]
      exact hMg _ (hmaps ⟨hq.1, unitBox_subset_closedCube _ hq.2⟩))]
  have hpos := (P.pieceFacts hK0 hε hεb hpc hK I hI hne).2.2.2
  dsimp only [ResolutionCover.varPieceCell, VarUnitCell.lam]
  simp only [P.pieceLam_eq hK0 I hI hne]
  refine setIntegral_congr_fun hbase.isClosed.measurableSet fun z hz => ?_
  congr 1
  have key : ∀ w ∈ unitBox (I.card - 1 + 1),
      ε ^ (∑ a ∈ Finset.univ.filter (fun a => ¬ ratioExp (normalExp I hne P.h)
          (normalHalfExp I hne P.e) a = P.pieceLam I hne),
        (residualExponent (normalExp I hne P.h) (normalHalfExp I hne P.e) (P.pieceLam I hne) a +
          1)) *
      (faceLeadConst (normalExp I hne P.h) (normalHalfExp I hne P.e) (P.pieceLam I hne) 1 *
        (A' z (P.faceNormal ε I hne σ w) *
          qv z (P.faceNormal ε I hne σ w) ^ (-P.pieceLam I hne) *
          residualWeight (normalExp I hne P.h) (normalHalfExp I hne P.e) (P.pieceLam I hne) w)) =
      (P.faceData hK0 hε hεb hpc hK I hI hne hr0 σ).B z w *
        residualWeight (P.faceData hK0 hε hεb hpc hK I hI hne hr0 σ).h
          (P.faceData hK0 hε hεb hpc hK I hI hne hr0 σ).k
          (P.faceData hK0 hε hεb hpc hK I hI hne hr0 σ).l w *
        G (P.facePoint ε I hne σ (z, w)) := by
    intro w hw
    have hmem : P.faceNormal ε I hne σ w ∈ Metric.closedBall (0 : Fin (I.card - 1 + 1) → ℝ) ε :=
      P.faceNormal_mem_closedBall ε hε I hne σ (unitBox_subset_closedCube _ hw)
    have h1 := hA' z hz _ hmem
    have h2 := hq' z hz _ hmem
    have h3 := hpos z hz _ hmem
    rw [h1, h2, P.faceData_B, P.faceData_h, P.faceData_k, P.faceData_l]
    unfold faceAmp facePoint ResolutionCover.sourcePieceAmp
    rw [abs_of_pos h3]
    ring
  calc ε ^ (∑ a ∈ Finset.univ.filter (fun a => ¬ ratioExp (normalExp I hne P.h)
          (normalHalfExp I hne P.e) a = P.pieceLam I hne),
        (residualExponent (normalExp I hne P.h) (normalHalfExp I hne P.e) (P.pieceLam I hne) a +
          1)) *
      (faceLeadConst (normalExp I hne P.h) (normalHalfExp I hne P.e) (P.pieceLam I hne) 1 *
        ∫ w in unitBox (I.card - 1 + 1), A' z (P.faceNormal ε I hne σ w) *
          qv z (P.faceNormal ε I hne σ w) ^ (-P.pieceLam I hne) *
          residualWeight (normalExp I hne P.h) (normalHalfExp I hne P.e) (P.pieceLam I hne) w)
      = ∫ w in unitBox (I.card - 1 + 1), ε ^ (∑ a ∈ Finset.univ.filter
          (fun a => ¬ ratioExp (normalExp I hne P.h) (normalHalfExp I hne P.e) a =
            P.pieceLam I hne),
          (residualExponent (normalExp I hne P.h) (normalHalfExp I hne P.e) (P.pieceLam I hne) a +
            1)) *
        (faceLeadConst (normalExp I hne P.h) (normalHalfExp I hne P.e) (P.pieceLam I hne) 1 *
          (A' z (P.faceNormal ε I hne σ w) *
            qv z (P.faceNormal ε I hne σ w) ^ (-P.pieceLam I hne) *
            residualWeight (normalExp I hne P.h) (normalHalfExp I hne P.e) (P.pieceLam I hne)
              w)) := by
        rw [integral_const_mul, integral_const_mul]
    _ = _ := setIntegral_congr_fun (measurableSet_unitBox _) key

/-- **The tied piece coefficient of the stratum `I`** at a nominated pair: the orthant sum of the
face integrals when the stratum pair is the nominated pair, `0` otherwise. -/
theorem sourceAtlasPieceCoeff_eq {G : (Fin d → ℝ) → ℝ} (hGm : Measurable G)
    (hGc : ContinuousOn G C.dom) (hr0 : ∀ x, 0 ≤ P.r x) (lam₀ : ℝ) (k₀ : ℕ) :
    ResolutionCover.sourceAtlasPieceCoeff
      (fun I hI hne => (P.sourceAtlases hK0 hε hεb hpc hGm hGc hK I hI hne).toLeading) lam₀ k₀ I =
      if P.pieceLam I hne = lam₀ ∧ P.pieceMult I hne - 1 = k₀ then
        ∑ σ : Fin (I.card - 1 + 1) → Bool, ∫ q, G (P.facePoint ε I hne σ q)
          ∂(P.faceData hK0 hε hεb hpc hK I hI hne hr0 σ).measure
      else 0 := by
  rw [ResolutionCover.sourceAtlasPieceCoeff_of_mem _ lam₀ k₀ I hI hne,
    FiniteVarUnitAtlas.toLeading_tied]
  have hlam : ∀ σ, ((P.sourceAtlases hK0 hε hεb hpc hGm hGc hK I hI hne).cell σ).lam =
      P.pieceLam I hne := fun σ =>
    P.sourcePieceAtlasV_cell_lam hK0 hε hεb rfl hpc hGm hGc hK I hI hne σ
  have hmult : ∀ σ, ((P.sourceAtlases hK0 hε hεb hpc hGm hGc hK I hI hne).cell σ).mult =
      P.pieceMult I hne := fun σ =>
    P.sourcePieceAtlasV_cell_mult hK0 hε hεb rfl hpc hGm hGc hK I hI hne σ
  unfold FiniteVarUnitAtlas.tied
  split_ifs with htied
  · rw [Finset.filter_true_of_mem fun σ _ => by rw [hlam, hmult]; exact htied]
    exact P.sum_cell_coeff_eq hK0 hε hεb hpc hK I hI hne hGm hGc hr0
  · rw [Finset.filter_false_of_mem fun σ _ => by rw [hlam, hmult]; exact htied]
    exact Finset.sum_empty

end Data

end ProductMonomialChartVar

end Grammar
