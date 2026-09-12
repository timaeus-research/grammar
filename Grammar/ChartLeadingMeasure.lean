/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SourceFaceMeasure
import Grammar.AEDisjointSourceAssembly

/-!
# The leading measure of a certified cover: strata integrals for the original integral (CCXCIII)

Unit 2c/5 of the global programme (consult #89). The tied face pieces of CCXCII are summed over
the strata of a chart and over the tied charts of a cover with a.e.-disjoint images:

* chart level: `chartLeadingMeasure P λ₀ k₀ = Σ_{I tied at (λ₀,k₀)} Σ_σ (facePoint σ)_* ν_{I,σ}` on
  the chart domain, and `P.sourceCoeff … λ₀ k₀ = ∫ G d(chartLeadingMeasure)` for every source
  amplitude `G` measurable and continuous on the domain (`sourceCoeff_eq_integral`);
* cover level: `leadingMeasure R Ps = Σ_{i tied} Σ_{I,σ} (Φ_i ∘ facePoint σ)_* ν_{i,I,σ}` on the
  parameter space, and ★★ `aeDisjointCoeff_eq_integral :
  aeDisjointCoeff Ps … F = ∫ F d(leadingMeasure)`: the library's explicit leading coefficient
  of the ORIGINAL integral `∫_{⋃ image_i} F p e^{−NK}`
  is the integral of the observable against a finite measure on the parameter space built from
  the face measures of the tied chart–stratum pairs (the chart-level shadows of the paper's strata
  `S_I`), the prior `p` included in the face densities;
* ★★★ `hasLeadingMeasure_of_aeDisjoint`: for the trivial tube weight the cover has the leading
  measure `leadingMeasure` at the extremal pair `(partitionLam', partitionDeg')` in the sense of
  CCXC — hence canonical (`HasLeadingMeasure.unique`) and with the equivalence and positivity
  consequences of CCXC for every bounded continuous test;
  `hasLeadingTerm_targetIntegral_of_aeDisjoint` is the prior-weighted leading term
  `∫_{⋃ image_i} F p e^{−NK} ~ (∫ F dσ_p) N^{−λ*} (log N)^{k*}`.

Hypotheses (as in CCLXXVIII): a.e.-disjoint chart images and supplied one-chart variable-unit
product packages with nonnegative weight factors. Nothing is claimed about individual strata: the
pieces are indexed by chart–stratum–orthant triples and only their SUM is canonical.
-/

open MeasureTheory Set Filter Topology BoundedContinuousFunction

namespace Grammar

/-! ### Integrability against a face measure from a bound on the region -/

namespace FaceWeightData

variable {t r : ℕ} (D : FaceWeightData t r)

/-- A measurable function bounded on the region is integrable against the face measure. -/
theorem integrable_of_bounded_on_region {g : (Fin t → ℝ) × (Fin r → ℝ) → ℝ} (hg : Measurable g)
    {Mg : ℝ} (hgM : ∀ q ∈ D.region, |g q| ≤ Mg) : Integrable g D.measure := by
  refine (integrable_const Mg).mono' hg.aestronglyMeasurable ?_
  rw [ae_iff]
  refine measure_mono_null ?_ D.measure_compl_region
  intro q hq hqr
  exact hq (by rw [Real.norm_eq_abs]; exact hgM q hqr)

end FaceWeightData

/-! ### Composition of a face piece with a measurable map -/

namespace LeadingFacePiece

variable {d : ℕ}

/-- Push a face piece forward along a measurable map of the parameter space. -/
def comp (a : LeadingFacePiece d) (T : (Fin d → ℝ) → (Fin d → ℝ)) (hT : Measurable T) :
    LeadingFacePiece d where
  α := a.α
  measure := a.measure
  toTarget := T ∘ a.toTarget
  measurable_toTarget := hT.comp a.measurable_toTarget

theorem comp_targetMeasure (a : LeadingFacePiece d) (T : (Fin d → ℝ) → (Fin d → ℝ))
    (hT : Measurable T) : (a.comp T hT).targetMeasure = a.targetMeasure.map T := by
  unfold targetMeasure comp
  rw [Measure.map_map hT a.measurable_toTarget]

theorem integrable_comp_iff (a : LeadingFacePiece d) (T : (Fin d → ℝ) → (Fin d → ℝ))
    (hT : Measurable T) {f : (Fin d → ℝ) → ℝ} (hf : Measurable f) :
    Integrable f (a.comp T hT).targetMeasure ↔ Integrable (f ∘ T) a.targetMeasure := by
  rw [comp_targetMeasure]
  exact integrable_map_measure hf.aestronglyMeasurable hT.aemeasurable

/-- The zero piece (index padding). -/
def zero (d : ℕ) : LeadingFacePiece d where
  α := Unit
  measure := 0
  toTarget := fun _ => 0
  measurable_toTarget := measurable_const

end LeadingFacePiece

/-! ### The chart-level leading measure -/

namespace ProductMonomialChartVar

open ResolutionCover (ofChart)

variable {d : ℕ} {C : ResolutionChart d} {K : (Fin d → ℝ) → ℝ}
  (P : ProductMonomialChartVar (ofChart C) () K) (hK0 : ∀ x, 0 ≤ K x) {ε : ℝ} (hε : 0 < ε)
  (hεb : ε ≤ P.b) {p : TubeWeight d} (hpc : ContinuousOn (fun y => p.w (C.φ y)) P.W)
  (hK : Measurable K) (hr0 : ∀ x, 0 ≤ P.r x)

/-- The index type of the chart-level pieces: a stratum and an orthant. -/
abbrev PieceIdx (d : ℕ) := Σ I : Finset (Fin d), (Fin (I.card - 1 + 1) → Bool)

include hK0 hε hεb hpc hK hr0 in
/-- **The chart-level pieces**: the face piece of each admissible stratum–orthant pair, the zero
piece elsewhere. -/
noncomputable def chartPieces : PieceIdx d → LeadingFacePiece d := fun x =>
  open scoped Classical in
  if h : x.1 ⊆ P.e.support ∧ x.1.Nonempty then
    P.facePiece hK0 hε hεb hpc hK x.1 h.1 h.2 hr0 x.2
  else LeadingFacePiece.zero d

open scoped Classical in
/-- **The tied strata** at a nominated pair. -/
noncomputable def strataTied (lam₀ : ℝ) (k₀ : ℕ) : Finset (Finset (Fin d)) :=
  (P.e.support.powerset.filter fun I => I.Nonempty).filter fun I =>
    ∃ hne : I.Nonempty, P.pieceLam I hne = lam₀ ∧ P.pieceMult I hne - 1 = k₀

/-- **The tied pieces**: every orthant of every tied stratum. -/
noncomputable def tiedPieces (lam₀ : ℝ) (k₀ : ℕ) : Finset (PieceIdx d) :=
  (P.strataTied lam₀ k₀).sigma fun _ => Finset.univ

theorem mem_strataTied {lam₀ : ℝ} {k₀ : ℕ} {I : Finset (Fin d)} :
    I ∈ P.strataTied lam₀ k₀ ↔ (I ⊆ P.e.support ∧ I.Nonempty) ∧
      ∃ hne : I.Nonempty, P.pieceLam I hne = lam₀ ∧ P.pieceMult I hne - 1 = k₀ := by
  unfold strataTied
  simp only [Finset.mem_filter, Finset.mem_powerset]

include hK0 hε hεb hpc hK hr0 in
/-- **The chart-level leading measure** at a nominated pair (chart coordinates). -/
noncomputable def chartLeadingMeasure (lam₀ : ℝ) (k₀ : ℕ) : Measure (Fin d → ℝ) :=
  leadingMeasureOf (P.chartPieces hK0 hε hεb hpc hK hr0) (P.tiedPieces lam₀ k₀)

instance (lam₀ : ℝ) (k₀ : ℕ) :
    IsFiniteMeasure (P.chartLeadingMeasure hK0 hε hεb hpc hK hr0 lam₀ k₀) := by
  unfold chartLeadingMeasure; infer_instance

include hK0 hε hεb hpc hK hr0 in
/-- A measurable amplitude continuous on the chart domain is integrable against every face piece.
-/
theorem integrable_facePiece {G : (Fin d → ℝ) → ℝ} (hGm : Measurable G)
    (hGc : ContinuousOn G C.dom) (I : Finset (Fin d)) (hI : I ⊆ P.e.support) (hne : I.Nonempty)
    (σ : Fin (I.card - 1 + 1) → Bool) :
    Integrable G (P.facePiece hK0 hε hεb hpc hK I hI hne hr0 σ).targetMeasure := by
  unfold LeadingFacePiece.targetMeasure
  rw [integrable_map_measure hGm.aestronglyMeasurable
    (P.facePiece hK0 hε hεb hpc hK I hI hne hr0 σ).measurable_toTarget.aemeasurable]
  obtain ⟨Mg, hMg⟩ := C.dom_compact.exists_bound_of_continuousOn hGc
  refine (P.faceData hK0 hε hεb hpc hK I hI hne hr0 σ).integrable_of_bounded_on_region
    (hGm.comp (P.continuous_facePoint ε I hne σ).measurable) (Mg := Mg) fun q hq => ?_
  rw [← Real.norm_eq_abs]
  exact hMg _ (P.mapsTo_facePoint hε hεb (p := p) I hI hne σ
    ⟨hq.1, unitBox_subset_closedCube _ hq.2⟩)

include hK0 hε hεb hpc hK hr0 in
theorem integrable_chartPieces {G : (Fin d → ℝ) → ℝ} (hGm : Measurable G)
    (hGc : ContinuousOn G C.dom) {lam₀ : ℝ} {k₀ : ℕ} {x : PieceIdx d}
    (hx : x ∈ P.tiedPieces lam₀ k₀) :
    Integrable G (P.chartPieces hK0 hε hεb hpc hK hr0 x).targetMeasure := by
  unfold tiedPieces at hx
  rw [Finset.mem_sigma] at hx
  obtain ⟨⟨hIs, hne⟩, -⟩ := (P.mem_strataTied).1 hx.1
  unfold chartPieces
  rw [dif_pos ⟨hIs, hne⟩]
  exact P.integrable_facePiece hK0 hε hεb hpc hK hr0 hGm hGc x.1 hIs hne x.2

include hK0 hε hεb hpc hK hr0 in
/-- ★★ **The source coefficient of a chart is the integral of the source amplitude against the
chart-level leading measure**: `Σ_{tied strata} Σ_σ ∫ G∘facePoint dν = ∫ G dσ_chart`. -/
theorem sourceCoeff_eq_integral {G : (Fin d → ℝ) → ℝ} (hGm : Measurable G)
    (hGc : ContinuousOn G C.dom) (lam₀ : ℝ) (k₀ : ℕ) :
    P.sourceCoeff hK0 hε hεb hpc hGm hGc hK lam₀ k₀ =
      ∫ y, G y ∂P.chartLeadingMeasure hK0 hε hεb hpc hK hr0 lam₀ k₀ := by
  classical
  unfold chartLeadingMeasure
  rw [integral_leadingMeasureOf _ _ fun x hx =>
    P.integrable_chartPieces hK0 hε hεb hpc hK hr0 hGm hGc hx]
  unfold tiedPieces
  rw [Finset.sum_sigma]
  unfold sourceCoeff strataTied
  conv_rhs => rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun I hI => ?_
  rw [Finset.mem_filter, Finset.mem_powerset] at hI
  obtain ⟨hIs, hne⟩ := hI
  rw [P.sourceAtlasPieceCoeff_eq hK0 hε hεb hpc hK I hIs hne hGm hGc hr0 lam₀ k₀]
  have hcond : (∃ hne' : I.Nonempty, P.pieceLam I hne' = lam₀ ∧ P.pieceMult I hne' - 1 = k₀) ↔
      (P.pieceLam I hne = lam₀ ∧ P.pieceMult I hne - 1 = k₀) :=
    ⟨fun ⟨_, h⟩ => h, fun h => ⟨hne, h⟩⟩
  by_cases htied : P.pieceLam I hne = lam₀ ∧ P.pieceMult I hne - 1 = k₀
  · rw [if_pos htied, if_pos (hcond.2 htied)]
    refine Finset.sum_congr rfl fun σ _ => ?_
    unfold chartPieces
    rw [dif_pos ⟨hIs, hne⟩]
    rfl
  · rw [if_neg htied, if_neg (fun h => htied (hcond.1 h))]

end ProductMonomialChartVar

/-! ### The cover-level leading measure -/

namespace ResolutionCover

variable {d : ℕ} {ι : Type*} [Fintype ι] (R : ResolutionCover d ι) {F K : (Fin d → ℝ) → ℝ}
  {p : TubeWeight d} (Ps : ∀ i, ProductMonomialChartVar (ofChart (R.chart i)) () K)
  (hK0 : ∀ x, 0 ≤ K x) {ε : ℝ} (hε : 0 < ε) (hεb : ∀ i, ε ≤ (Ps i).b)
  (hpc : ∀ i, ContinuousOn (fun y => p.w ((R.chart i).φ y)) (Ps i).W)
  (hK : Measurable K) (hne : (R.activeCharts Ps).Nonempty) (hr0 : ∀ i x, 0 ≤ (Ps i).r x)

/-- The index type of the cover-level pieces: a chart, a stratum and an orthant. -/
abbrev CoverPieceIdx (d : ℕ) (ι : Type*) := Σ _ : ι, ProductMonomialChartVar.PieceIdx d

include hK0 hε hεb hpc hK hr0 in
/-- **The cover-level pieces**: the chart pieces pushed forward along the chart maps. -/
noncomputable def coverPieces : CoverPieceIdx d ι → LeadingFacePiece d := fun x =>
  ((Ps x.1).chartPieces hK0 hε (hεb x.1) (hpc x.1) hK (hr0 x.1) x.2).comp (R.chart x.1).Φ
    (R.chart x.1).measurable_Φ

/-- **The tied cover pieces**: the tied pieces of every tied chart at its own pair (which is the
partition pair). -/
noncomputable def tiedCoverPieces : Finset (CoverPieceIdx d ι) :=
  (R.tiedCharts' Ps hne).sigma fun i => (Ps i).tiedPieces (R.chartLam' Ps i) (R.chartDeg' Ps i)

include hK0 hε hεb hpc hK hne hr0 in
/-- ★ **The leading measure of the cover**: the sum over the tied chart–stratum–orthant pieces of
the face measures pushed to the parameter space. -/
noncomputable def leadingMeasure : Measure (Fin d → ℝ) :=
  leadingMeasureOf (R.coverPieces Ps hK0 hε hεb hpc hK hr0) (R.tiedCoverPieces Ps hne)

instance : IsFiniteMeasure (R.leadingMeasure Ps hK0 hε hεb hpc hK hne hr0) := by
  unfold leadingMeasure; infer_instance

variable (hFc : ∀ i, ContinuousOn (fun y => F ((R.chart i).φ y)) (Ps i).W) (hFm : Measurable F)

include hK0 hε hεb hpc hK hr0 hFc hFm in
theorem integrable_coverPieces {x : CoverPieceIdx d ι} (hx : x ∈ R.tiedCoverPieces Ps hne) :
    Integrable F (R.coverPieces Ps hK0 hε hεb hpc hK hr0 x).targetMeasure := by
  unfold tiedCoverPieces at hx
  rw [Finset.mem_sigma] at hx
  unfold coverPieces
  rw [LeadingFacePiece.integrable_comp_iff _ _ _ hFm]
  exact (Ps x.1).integrable_chartPieces hK0 hε (hεb x.1) (hpc x.1) hK (hr0 x.1)
    (hFm.comp (R.chart x.1).measurable_Φ)
    (continuousOn_pullback_Φ (R.chart x.1) (hFc x.1) (Ps x.1).dom_subset) hx.2

include hK0 hε hεb hpc hK hne hr0 hFc hFm in
/-- ★★ **The explicit leading coefficient of the original integral is the integral of the
observable against the leading measure.** -/
theorem aeDisjointCoeff_eq_integral :
    R.aeDisjointCoeff Ps hK0 hε hεb hpc hFc hFm hK hne =
      ∫ x, F x ∂(R.leadingMeasure Ps hK0 hε hεb hpc hK hne hr0) := by
  unfold leadingMeasure
  rw [integral_leadingMeasureOf _ _ fun x hx =>
    R.integrable_coverPieces Ps hK0 hε hεb hpc hK hne hr0 hFc hFm hx]
  unfold tiedCoverPieces
  rw [Finset.sum_sigma]
  unfold aeDisjointCoeff sourceDecompCoeff
  refine Finset.sum_congr rfl fun i hi => ?_
  have hact : (Ps i).IsActive := by
    unfold tiedCharts' at hi
    exact (R.mem_activeCharts Ps).1 (Finset.mem_filter.1 hi).1
  unfold sourceChartCoeff'
  rw [dif_pos hact, (Ps i).sourceCoeff_eq_integral hK0 hε (hεb i) (hpc i) hK (hr0 i) _ _
    (R.chartLam' Ps i) (R.chartDeg' Ps i)]
  unfold ProductMonomialChartVar.chartLeadingMeasure
  beta_reduce
  rw [integral_leadingMeasureOf (f := fun y => F ((R.chart i).Φ y)) _ _ fun x hx =>
    (Ps i).integrable_chartPieces hK0 hε (hεb i) (hpc i) hK (hr0 i)
      (hFm.comp (R.chart i).measurable_Φ)
      (continuousOn_pullback_Φ (R.chart i) (hFc i) (Ps i).dom_subset) hx]
  rfl

include hK0 hε hεb hpc hK hne hr0 hFc hFm in
/-- **The prior-weighted leading term of the original integral over the union of the chart
images**: `∫_{⋃ image_i} F p e^{−NK} ~ (∫ F dσ_p) N^{−λ*} (log N)^{k*}` (as a certificate; the
coefficient may vanish for a signed observable). -/
theorem hasLeadingTerm_targetIntegral_of_aeDisjoint (hdisj : R.AEDisjointImages)
    (hF : Integrable (fun x => F x * p.w x) (volume.restrict (⋃ i, R.image i))) :
    HasLeadingTerm (targetIntegral (⋃ i, R.image i) F K p)
      (∫ x, F x ∂(R.leadingMeasure Ps hK0 hε hεb hpc hK hne hr0)) (R.partitionLam' Ps hne)
      (R.partitionDeg' Ps hne) := by
  rw [← R.aeDisjointCoeff_eq_integral Ps hK0 hε hεb hpc hK hne hr0 hFc hFm]
  exact R.hasLeadingTerm_boltzmannIntegral_of_aeDisjoint Ps hK0 hε hεb hpc hFc hFm hK hne hdisj hF

end ResolutionCover

namespace ResolutionCover

variable {d : ℕ} {ι : Type*} [Fintype ι] (R : ResolutionCover d ι) {K : (Fin d → ℝ) → ℝ}
  (Ps : ∀ i, ProductMonomialChartVar (ofChart (R.chart i)) () K)
  (hK0 : ∀ x, 0 ≤ K x) {ε : ℝ} (hε : 0 < ε) (hεb : ∀ i, ε ≤ (Ps i).b)
  (hK : Measurable K) (hne : (R.activeCharts Ps).Nonempty) (hr0 : ∀ i x, 0 ≤ (Ps i).r x)

/-- The trivial tube weight is continuous on every chart neighbourhood. -/
theorem continuousOn_one_w (i : ι) :
    ContinuousOn (fun y => (TubeWeight.one d).w ((R.chart i).φ y)) (Ps i).W :=
  continuousOn_const

theorem volume_iUnion_image_ne_top : volume (⋃ i, R.image i) ≠ ⊤ :=
  ((measure_iUnion_fintype_le _ _).trans_lt (ENNReal.sum_lt_top.2 fun i _ =>
    (R.isCompact_image i).measure_lt_top)).ne

include hK0 hε hεb hK hne hr0 in
/-- ★★★ **The leading measure of a certified cover**: the union of the chart images of a cover
with a.e.-disjoint images and supplied product packages has the leading measure
`leadingMeasure` (trivial tube weight) at the extremal pair, for every bounded continuous test —
so the leading measure is canonical (`HasLeadingMeasure.unique`) and the original integral
`∫_{⋃ image_i} a e^{−tK} ~ (∫ a dσ) t^{−λ*} (log t)^{k*}` whenever `∫ a dσ ≠ 0`. -/
theorem hasLeadingMeasure_of_aeDisjoint (hdisj : R.AEDisjointImages) :
    HasLeadingMeasure (⋃ i, R.image i) K (R.partitionLam' Ps hne) (R.partitionDeg' Ps hne)
      (R.leadingMeasure Ps hK0 hε hεb (p := TubeWeight.one d) (R.continuousOn_one_w Ps) hK hne
        hr0) := by
  intro a
  have hFc : ∀ i, ContinuousOn (fun y => a ((R.chart i).φ y)) (Ps i).W := fun i =>
    a.continuous.comp_continuousOn (Ps i).monomial.analyticOnNhd.continuousOn
  have hF : Integrable (fun x => a x * (TubeWeight.one d).w x)
      (volume.restrict (⋃ i, R.image i)) := by
    refine (integrableOn_const (C := ‖a‖) (R.volume_iUnion_image_ne_top)).mono'
      (a.continuous.measurable.mul measurable_const).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    simp only [TubeWeight.one_w, mul_one]
    exact a.norm_coe_le_norm x
  have h := R.hasLeadingTerm_targetIntegral_of_aeDisjoint Ps hK0 hε hεb
    (R.continuousOn_one_w Ps) hK hne hr0 hFc a.continuous.measurable hdisj hF
  rwa [globalLaplace_eq_targetIntegral]

end ResolutionCover

end Grammar
