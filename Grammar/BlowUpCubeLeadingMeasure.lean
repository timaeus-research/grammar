/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.ChartLeadingMeasure
import Grammar.BlowUpCubeGaussian
import Grammar.CertifiedResolutionExplicitCoefficient

/-!
# The leading measure of the Gaussian cube is `π^{d/2} δ₀`; leading measures of partial
resolutions (CCXCV)

Two consequences of CCXCIII.

* **Regression.** For the blow-up cover of the unit cube `[−1,1]^d` (CCLXXXIII–CCLXXXIV) with the
  phase `K = |x|²`, every tied face piece is pushed by the blow-up chart to the origin (the face
  is the exceptional divisor `{y_β = 0}`, which the blow-up collapses), so the leading measure is a
  point mass: ★★★ `BlowUpCube.leadingMeasure_eq : leadingMeasure = π^{d/2} · δ₀`, and the classical
  Laplace statement follows from the general machine for every bounded continuous test
  `a`: `∫_{[−1,1]^d} a(x) e^{−t|x|²} dx / t^{−d/2} → π^{d/2} a(0)` (`tendsto_cube_laplace`).
* **Partial resolutions.** A hironaka monomial partial resolution of a compact set `N` with
  a.e.-disjoint chart images and supplied product packages has a leading measure on `N` itself
  (`hasLeadingMeasure_ofPartialResolution`, via the a.e.-equality of `N` and the union of the chart
  images and `HasLeadingMeasure.of_ae_eq_set`).
-/

open MeasureTheory Set Filter Topology BoundedContinuousFunction

namespace Grammar

variable {d : ℕ}

/-- A leading measure transfers between regions equal up to a null set. -/
theorem HasLeadingMeasure.of_ae_eq_set {A B : Set (Fin d → ℝ)} (hAB : A =ᵐ[volume] B)
    {K : (Fin d → ℝ) → ℝ} {lam : ℝ} {q : ℕ} {σ : Measure (Fin d → ℝ)}
    (h : HasLeadingMeasure A K lam q σ) : HasLeadingMeasure B K lam q σ := fun a =>
  (h a).congr' (Eventually.of_forall fun _ => setIntegral_congr_set hAB)

/-! ### Partial resolutions -/

namespace ResolutionCover

open Monomialize.VolumeScaling

variable {K : (Fin d → ℝ) → ℝ} {N : Set (Fin d → ℝ)} (R : PartialResolution d K N)
  (Ps : ∀ i, ProductMonomialChartVar (ofChart ((ofPartialResolution R).chart i)) () K)
  (hK0 : ∀ x, 0 ≤ K x) {ε : ℝ} (hε : 0 < ε) (hεb : ∀ i, ε ≤ (Ps i).b) (hK : Measurable K)
  (hne : ((ofPartialResolution R).activeCharts Ps).Nonempty) (hr0 : ∀ i x, 0 ≤ (Ps i).r x)

/-- The union of the chart images of a partial resolution is a.e. equal to the resolved set. -/
theorem iUnion_image_ofPartialResolution_ae_eq :
    (⋃ i, (ofPartialResolution R).image i) =ᵐ[volume] N :=
  ae_eq_set.2 ⟨by rw [sdiff_eq_empty.2 (iUnion_image_ofPartialResolution_subset R), measure_empty],
    R.cover⟩

include hK0 hε hεb hK hne hr0 in
/-- ★★ **The leading measure of a certified partial resolution** lives on the resolved compact set
`N` itself: `∫_N a e^{−tK} / (t^{−λ*} (log t)^{k*}) → ∫ a dσ` for every bounded continuous `a`. -/
theorem hasLeadingMeasure_ofPartialResolution (hdisj : (ofPartialResolution R).AEDisjointImages) :
    HasLeadingMeasure N K ((ofPartialResolution R).partitionLam' Ps hne)
      ((ofPartialResolution R).partitionDeg' Ps hne)
      ((ofPartialResolution R).leadingMeasure Ps hK0 hε hεb (p := TubeWeight.one d)
        ((ofPartialResolution R).continuousOn_one_w Ps) hK hne hr0) :=
  ((ofPartialResolution R).hasLeadingMeasure_of_aeDisjoint Ps hK0 hε hεb hK hne hr0
    hdisj).of_ae_eq_set (iUnion_image_ofPartialResolution_ae_eq R)

end ResolutionCover

/-! ### The Gaussian cube -/

namespace BlowUpCube

variable (hd : 1 < d) [NeZero d]

omit [NeZero d] in
theorem hr0 : ∀ β x, 0 ≤ (Ps hd β).r x := fun β x => by rw [Ps_r]; exact zero_le_one

/-- The leading measure of the blow-up cover of the cube (trivial tube weight). -/
noncomputable def leadingMeasure : Measure (Fin d → ℝ) :=
  (R hd).leadingMeasure (Ps hd) K_nonneg one_pos (hεb hd) (p := TubeWeight.one d)
    ((R hd).continuousOn_one_w (Ps hd)) continuous_K.measurable (hne hd) (hr0 hd)

omit [NeZero d] in
/-- The blow-up chart collapses the divisor `{y_β = 0}` to the origin. -/
theorem φ_eq_zero (β : Fin d) {y : Fin d → ℝ} (hy : y β = 0) : φ β y = 0 := by
  funext γ
  by_cases hγ : γ = β
  · subst hγ; rw [φ_self, hy]; rfl
  · rw [φ_other β y hγ, hy, zero_mul]; rfl

omit [NeZero d] in
/-- **The face points of the stratum `{β}` are sent to the origin by the blow-up chart**, almost
everywhere for the face measure. -/
theorem ae_Φ_facePoint_eq_zero (β : Fin d) (hIs : ({β} : Finset (Fin d)) ⊆ (Ps hd β).e.support)
    (hne : ({β} : Finset (Fin d)).Nonempty)
    (σ : Fin (({β} : Finset (Fin d)).card - 1 + 1) → Bool) :
    ∀ᵐ q ∂((Ps hd β).faceData K_nonneg one_pos (hεb hd β) ((R hd).continuousOn_one_w (Ps hd) β)
        continuous_K.measurable {β} hIs hne (hr0 hd β) σ).measure,
      ((R hd).chart β).Φ ((Ps hd β).facePoint 1 {β} hne σ q) = 0 := by
  rw [ae_iff]
  refine measure_mono_null ?_ ((Ps hd β).faceData K_nonneg one_pos (hεb hd β)
    ((R hd).continuousOn_one_w (Ps hd) β) continuous_K.measurable {β} hIs hne
    (hr0 hd β) σ).measure_compl_region
  intro q hq hqr
  refine hq ?_
  -- the face point has vanishing `β`-coordinate
  have hsub : Subsingleton (Fin (({β} : Finset (Fin d)).card - 1 + 1)) := by
    rw [Finset.card_singleton]
    exact Fin.subsingleton_iff_le_one.2 (by norm_num)
  have hface : (Ps hd β).faceNormal 1 {β} hne σ q.2 = 0 := by
    unfold ProductMonomialChartVar.faceNormal
    have hfp : faceProj (normalExp {β} hne (Ps hd β).h) (normalHalfExp {β} hne (Ps hd β).e)
        ((Ps hd β).pieceLam {β} hne) q.2 = 0 := by
      funext a
      have hmin : ratioExp (normalExp {β} hne (Ps hd β).h) (normalHalfExp {β} hne (Ps hd β).e) a =
          (Ps hd β).pieceLam {β} hne := by
        obtain ⟨a', ha'⟩ := exists_ratioExp_eq_minRatio (normalExp {β} hne (Ps hd β).h)
          (normalHalfExp {β} hne (Ps hd β).e)
        rw [← (Ps hd β).pieceLam_eq K_nonneg {β} hIs hne, ← ha', Subsingleton.elim a a']
      simp only [faceProj]
      rw [if_pos hmin]
      rfl
    rw [hfp, smul_zero]
    funext a
    simp [reflect]
  have hmem : (Ps hd β).facePoint 1 {β} hne σ q ∈ ((R hd).chart β).dom :=
    (Ps hd β).mapsTo_facePoint one_pos (hεb hd β) (p := TubeWeight.one d) {β} hIs hne σ
      ⟨hqr.1, unitBox_subset_closedCube _ hqr.2⟩
  have hβ : (Ps hd β).facePoint 1 {β} hne σ q β = 0 := by
    unfold ProductMonomialChartVar.facePoint
    rw [hface]
    obtain ⟨a, ha⟩ := exists_inr_of_mem {β} hne (Finset.mem_singleton_self β)
    have := planeSplit_stratum_inr {β} hne q.1 0 a
    rw [← ha] at this
    exact this
  rw [((R hd).chart β).Φ_eqOn hmem]
  exact φ_eq_zero β hβ

omit [NeZero d] in
/-- The target measure of the chart-level face piece is the pushforward of the face measure. -/
theorem facePiece_targetMeasure (β : Fin d) (hIs : ({β} : Finset (Fin d)) ⊆ (Ps hd β).e.support)
    (hne : ({β} : Finset (Fin d)).Nonempty)
    (σ : Fin (({β} : Finset (Fin d)).card - 1 + 1) → Bool) :
    ((Ps hd β).facePiece K_nonneg one_pos (hεb hd β) ((R hd).continuousOn_one_w (Ps hd) β)
        continuous_K.measurable {β} hIs hne (hr0 hd β) σ).targetMeasure =
      ((Ps hd β).faceData K_nonneg one_pos (hεb hd β) ((R hd).continuousOn_one_w (Ps hd) β)
        continuous_K.measurable {β} hIs hne (hr0 hd β) σ).measure.map
        ((Ps hd β).facePoint 1 {β} hne σ) := rfl

/-- The target measure of every tied piece is a point mass at the origin. -/
theorem coverPieces_targetMeasure_eq {x : ResolutionCover.CoverPieceIdx d (Fin d)}
    (hx : x ∈ (R hd).tiedCoverPieces (Ps hd) (hne hd)) :
    ((R hd).coverPieces (Ps hd) K_nonneg one_pos (hεb hd) (p := TubeWeight.one d)
        ((R hd).continuousOn_one_w (Ps hd)) continuous_K.measurable (hr0 hd) x).targetMeasure =
      ((R hd).coverPieces (Ps hd) K_nonneg one_pos (hεb hd) (p := TubeWeight.one d)
        ((R hd).continuousOn_one_w (Ps hd)) continuous_K.measurable (hr0 hd) x).measure univ •
        Measure.dirac 0 := by
  have hx' : x.2.1 ⊆ (Ps hd x.1).e.support ∧ x.2.1.Nonempty := by
    unfold ResolutionCover.tiedCoverPieces at hx
    rw [Finset.mem_sigma] at hx
    have h2 := hx.2
    unfold ProductMonomialChartVar.tiedPieces at h2
    rw [Finset.mem_sigma] at h2
    exact ((Ps hd x.1).mem_strataTied.1 h2.1).1
  obtain ⟨β, I, σ⟩ := x
  simp only at hx'
  obtain ⟨hIs, hne'⟩ := hx'
  have hI : I = {β} := by
    rw [Ps_e_support] at hIs
    rcases Finset.subset_singleton_iff.1 hIs with h | h
    · exact absurd h hne'.ne_empty
    · exact h
  subst hI
  have hpiece : (R hd).coverPieces (Ps hd) K_nonneg one_pos (hεb hd) (p := TubeWeight.one d)
      ((R hd).continuousOn_one_w (Ps hd)) continuous_K.measurable (hr0 hd) ⟨β, ⟨{β}, σ⟩⟩ =
      ((Ps hd β).facePiece K_nonneg one_pos (hεb hd β) ((R hd).continuousOn_one_w (Ps hd) β)
        continuous_K.measurable {β} hIs hne' (hr0 hd β) σ).comp ((R hd).chart β).Φ
        ((R hd).chart β).measurable_Φ := by
    unfold ResolutionCover.coverPieces ProductMonomialChartVar.chartPieces
    rw [dif_pos (⟨hIs, hne'⟩ : ({β} : Finset (Fin d)) ⊆ (Ps hd β).e.support ∧
      ({β} : Finset (Fin d)).Nonempty)]
  rw [hpiece, LeadingFacePiece.comp_targetMeasure, facePiece_targetMeasure,
    Measure.map_map ((R hd).chart β).measurable_Φ
      ((Ps hd β).continuous_facePoint 1 {β} hne' σ).measurable,
    show ((R hd).chart β).Φ ∘ (Ps hd β).facePoint 1 {β} hne' σ =
      fun q => ((R hd).chart β).Φ ((Ps hd β).facePoint 1 {β} hne' σ q) from rfl,
    Measure.map_congr (ae_Φ_facePoint_eq_zero hd β hIs hne' σ), Measure.map_const]
  rfl

/-- ★★★ **The leading measure of the Gaussian cube is `π^{d/2} δ₀`.** -/
theorem leadingMeasure_eq :
    leadingMeasure hd = ENNReal.ofReal (Real.pi ^ (d / 2 : ℝ)) • Measure.dirac 0 := by
  have hsum : leadingMeasure hd = (∑ x ∈ (R hd).tiedCoverPieces (Ps hd) (hne hd),
      ((R hd).coverPieces (Ps hd) K_nonneg one_pos (hεb hd) (p := TubeWeight.one d)
        ((R hd).continuousOn_one_w (Ps hd)) continuous_K.measurable (hr0 hd) x).measure univ) •
      Measure.dirac (0 : Fin d → ℝ) := by
    unfold leadingMeasure ResolutionCover.leadingMeasure leadingMeasureOf
    rw [Finset.sum_smul]
    exact Finset.sum_congr rfl fun x hx => coverPieces_targetMeasure_eq hd hx
  have hmass : leadingMeasure hd univ = ENNReal.ofReal (Real.pi ^ (d / 2 : ℝ)) := by
    have h1 := (R hd).aeDisjointCoeff_eq_integral (Ps hd) K_nonneg one_pos (hεb hd)
      (p := TubeWeight.one d) ((R hd).continuousOn_one_w (Ps hd)) continuous_K.measurable (hne hd)
      (hr0 hd) (F := fun _ => (1 : ℝ)) (hFcR hd continuous_const) measurable_const
    have h2 : coeff hd (F := fun _ => (1 : ℝ)) (p := TubeWeight.one d) continuous_const
        continuous_const = (R hd).aeDisjointCoeff (Ps hd) K_nonneg one_pos (hεb hd)
          ((R hd).continuousOn_one_w (Ps hd)) (hFcR hd continuous_const) measurable_const
          continuous_K.measurable (hne hd) := rfl
    rw [coeff_eq_pi_rpow hd] at h2
    rw [← h2, integral_const, smul_eq_mul, mul_one, measureReal_def] at h1
    unfold leadingMeasure
    rw [h1, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  rw [hsum] at hmass ⊢
  rw [Measure.smul_apply, Measure.dirac_apply_of_mem (mem_univ _), smul_eq_mul, mul_one] at hmass
  rw [hmass]

include hd in
/-- ★★★ **The Gaussian cube has the leading measure `π^{d/2} δ₀` at the pair `(d/2, 0)`.** -/
theorem hasLeadingMeasure_cube :
    HasLeadingMeasure (cube d) K (d / 2) 0
      (ENNReal.ofReal (Real.pi ^ (d / 2 : ℝ)) • Measure.dirac 0) := by
  have h := (R hd).hasLeadingMeasure_of_aeDisjoint (Ps hd) K_nonneg one_pos (hεb hd)
    continuous_K.measurable (hne hd) (hr0 hd) (aeDisjointImages hd)
  rw [iUnion_image_eq, partitionLam'_eq, partitionDeg'_eq] at h
  rw [← leadingMeasure_eq hd]
  exact h

include hd in
/-- **The classical Laplace statement from the general machine**: for every bounded continuous
`a`, `∫_{[−1,1]^d} a(x) e^{−t|x|²} dx / t^{−d/2} → π^{d/2} a(0)`. -/
theorem tendsto_cube_laplace (a : (Fin d → ℝ) →ᵇ ℝ) :
    Tendsto (fun t : ℝ => (∫ x in cube d, a x * Real.exp (-t * K x)) / t ^ (-(d / 2 : ℝ))) atTop
      (𝓝 (Real.pi ^ (d / 2 : ℝ) * a 0)) := by
  have h := (hasLeadingMeasure_cube hd).tendsto a
  rw [integral_smul_measure, integral_dirac,
    ENNReal.toReal_ofReal (Real.rpow_nonneg Real.pi_pos.le _), smul_eq_mul] at h
  refine h.congr' (Eventually.of_forall fun t => ?_)
  simp [globalLaplace, powLogScale]

end BlowUpCube

end Grammar
