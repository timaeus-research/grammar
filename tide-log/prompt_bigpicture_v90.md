# Consult #90 — audit of the global leading-measure programme (CCXC–CCXCV) and next direction

You are Astra, advising the Lean 4 formalisation (repo `timaeus-research/grammar`, namespace `Grammar`, Mathlib v4.33.1, 596 modules, no sorry/axioms) of the grammar paper (Gerraty–Murfet). Consult #89 designed the "global leading measure" programme for the user's request ("a version of the main theorem that addresses the actual original integrals over W and makes use of strata integrals in the coefficients"). Units 1, 2a, 2b, 2c/5, 7 (partial) and 8 have landed. Below are the exact Lean statements and the new paper-mirror paragraph. Please (1) audit the statements for correctness and honest scope (in particular the prior's place in the density, the meaning of `HasLeadingMeasure` over bounded continuous tests versus the paper's analytic observables, and whether the mirror paragraph overclaims), (2) say whether any of the remaining items is worth doing: a `BoxFamily` (derived-certificate) wrapper; a general-prior `HasLeadingMeasure` (prior as test-function weight rather than inside the density); the ownership-partition route with a Laplace normal-density hypothesis; a bounded-open-region corollary of `exponent_of_compact`; anything else of genuine value — or whether the programme should close here, and (3) list precisely what remains a hypothesis. Keep the answer to the point.

## Lean statements (verbatim)
```lean
-- ==== Grammar/GlobalLaplaceMeasureBasic.lean
variable {d : ℕ}

variable {W : Set (Fin d → ℝ)} {K : (Fin d → ℝ) → ℝ} {lam : ℝ} {q : ℕ}

variable (a : LeadingFacePiece d)

variable {σ τ : Measure (Fin d → ℝ)}

noncomputable def globalLaplace (W : Set (Fin d → ℝ)) (K a : (Fin d → ℝ) → ℝ) (t : ℝ) : ℝ

theorem globalLaplace_eq_targetIntegral (W : Set (Fin d → ℝ)) (K a : (Fin d → ℝ) → ℝ) :
    globalLaplace W K a = targetIntegral W a K (TubeWeight.one d)

theorem targetIntegral_eq_globalLaplace (W : Set (Fin d → ℝ)) (F K : (Fin d → ℝ) → ℝ)
    (p : TubeWeight d) : targetIntegral W F K p = globalLaplace W K (fun x => F x * p.w x)

theorem globalLaplace_smul (W : Set (Fin d → ℝ)) (K a : (Fin d → ℝ) → ℝ) (c t : ℝ) :
    globalLaplace W K (fun x => c * a x) t = c * globalLaplace W K a t

theorem globalLaplace_nonneg (W : Set (Fin d → ℝ)) (K : (Fin d → ℝ) → ℝ) {a : (Fin d → ℝ) → ℝ}
    (ha : ∀ x, 0 ≤ a x) (t : ℝ) : 0 ≤ globalLaplace W K a t

theorem integrableOn_mul_exp_of_bounded {W : Set (Fin d → ℝ)} (hW : volume W ≠ ⊤)
    {K : (Fin d → ℝ) → ℝ} (hK : Measurable K) (hK0 : ∀ x, 0 ≤ K x) {a : (Fin d → ℝ) → ℝ}
    (ham : Measurable a) {M : ℝ} (haM : ∀ x, |a x| ≤ M) {t : ℝ} (ht : 0 ≤ t) :
    IntegrableOn (fun x => a x * Real.exp (-t * K x)) W

theorem globalLaplace_add {W : Set (Fin d → ℝ)} (hW : volume W ≠ ⊤) {K : (Fin d → ℝ) → ℝ}
    (hK : Measurable K) (hK0 : ∀ x, 0 ≤ K x) (a b : (Fin d → ℝ) →ᵇ ℝ) {t : ℝ} (ht : 0 ≤ t) :
    globalLaplace W K (a + b) t = globalLaplace W K a t + globalLaplace W K b t

theorem coeff_add_of_hasLeadingTerm (hW : volume W ≠ ⊤) (hK : Measurable K) (hK0 : ∀ x, 0 ≤ K x)
    {a b : (Fin d → ℝ) →ᵇ ℝ} {ca cb cab : ℝ} (ha : HasLeadingTerm (globalLaplace W K a) ca lam q)
    (hb : HasLeadingTerm (globalLaplace W K b) cb lam q)
    (hab : HasLeadingTerm (globalLaplace W K (a + b)) cab lam q) : cab = ca + cb

theorem coeff_smul_of_hasLeadingTerm {a : (Fin d → ℝ) → ℝ} {c ca cca : ℝ}
    (ha : HasLeadingTerm (globalLaplace W K a) ca lam q)
    (hca : HasLeadingTerm (globalLaplace W K (fun x => c * a x)) cca lam q) : cca = c * ca

theorem coeff_nonneg_of_hasLeadingTerm {a : (Fin d → ℝ) → ℝ} (ha0 : ∀ x, 0 ≤ a x) {c : ℝ}
    (h : HasLeadingTerm (globalLaplace W K a) c lam q) : 0 ≤ c

theorem coeff_mono_of_hasLeadingTerm (hW : volume W ≠ ⊤) (hK : Measurable K) (hK0 : ∀ x, 0 ≤ K x)
    {a b : (Fin d → ℝ) →ᵇ ℝ} (hab : ∀ x, a x ≤ b x) {ca cb : ℝ}
    (ha : HasLeadingTerm (globalLaplace W K a) ca lam q)
    (hb : HasLeadingTerm (globalLaplace W K b) cb lam q) : ca ≤ cb

structure LeadingFacePiece (d : ℕ)

noncomputable def targetMeasure : Measure (Fin d → ℝ) := a.measure.map a.toTarget

instance : IsFiniteMeasure a.targetMeasure := Measure.isFiniteMeasure_map _ _

theorem targetMeasure_apply {s : Set (Fin d → ℝ)} (hs : MeasurableSet s) :
    a.targetMeasure s = a.measure (a.toTarget ⁻¹' s)

theorem integral_targetMeasure {f : (Fin d → ℝ) → ℝ} (hf : AEStronglyMeasurable f a.targetMeasure) :
    ∫ x, f x ∂a.targetMeasure = ∫ y, f (a.toTarget y) ∂a.measure

theorem targetMeasure_compl_eq_zero {S : Set (Fin d → ℝ)} (hS : MeasurableSet S)
    (h : ∀ᵐ y ∂a.measure, a.toTarget y ∈ S) : a.targetMeasure Sᶜ = 0

noncomputable def leadingMeasureOf {ι : Type*} (pieces : ι → LeadingFacePiece d) (T : Finset ι) :
    Measure (Fin d → ℝ)

theorem integral_leadingMeasureOf {ι : Type*} (pieces : ι → LeadingFacePiece d) (T : Finset ι)
    {f : (Fin d → ℝ) → ℝ} (hf : ∀ a ∈ T, Integrable f (pieces a).targetMeasure) :
    ∫ x, f x ∂leadingMeasureOf pieces T =
      ∑ a ∈ T, ∫ y, f ((pieces a).toTarget y) ∂(pieces a).measure

theorem integral_leadingMeasureOf_bcf {ι : Type*} (pieces : ι → LeadingFacePiece d) (T : Finset ι)
    (f : (Fin d → ℝ) →ᵇ ℝ) :
    ∫ x, f x ∂leadingMeasureOf pieces T =
      ∑ a ∈ T, ∫ y, f ((pieces a).toTarget y) ∂(pieces a).measure

theorem leadingMeasureOf_compl_eq_zero {ι : Type*} (pieces : ι → LeadingFacePiece d) (T : Finset ι)
    {S : Set (Fin d → ℝ)} (hS : MeasurableSet S)
    (h : ∀ a ∈ T, ∀ᵐ y ∂(pieces a).measure, (pieces a).toTarget y ∈ S) :
    leadingMeasureOf pieces T Sᶜ = 0

def HasLeadingMeasure (W : Set (Fin d → ℝ)) (K : (Fin d → ℝ) → ℝ) (lam : ℝ) (q : ℕ)
    (σ : Measure (Fin d → ℝ)) : Prop

theorem tendsto (h : HasLeadingMeasure W K lam q σ) (a : (Fin d → ℝ) →ᵇ ℝ) :
    Tendsto (fun t => globalLaplace W K a t / powLogScale lam q t) atTop (𝓝 (∫ w, a w ∂σ))

theorem of_coeff (C : ((Fin d → ℝ) →ᵇ ℝ) → ℝ)
    (hC : ∀ a : (Fin d → ℝ) →ᵇ ℝ, HasLeadingTerm (globalLaplace W K a) (C a) lam q)
    (hσ : ∀ a : (Fin d → ℝ) →ᵇ ℝ, C a = ∫ w, a w ∂σ) : HasLeadingMeasure W K lam q σ

theorem isEquivalent (h : HasLeadingMeasure W K lam q σ) (a : (Fin d → ℝ) →ᵇ ℝ)
    (hc : ∫ w, a w ∂σ ≠ 0) :
    globalLaplace W K a ~[atTop] fun t => (∫ w, a w ∂σ) * powLogScale lam q t

theorem integral_pos_iff [IsFiniteMeasure σ] (a : (Fin d → ℝ) →ᵇ ℝ) (ha0 : ∀ x, 0 ≤ a x) :
    0 < ∫ w, a w ∂σ ↔ 0 < σ (Function.support a)

theorem isEquivalent_of_pos [IsFiniteMeasure σ] (h : HasLeadingMeasure W K lam q σ)
    (a : (Fin d → ℝ) →ᵇ ℝ) (ha0 : ∀ x, 0 ≤ a x) (hpos : 0 < σ (Function.support a)) :
    0 < ∫ w, a w ∂σ ∧
      globalLaplace W K a ~[atTop] fun t => (∫ w, a w ∂σ) * powLogScale lam q t

theorem unique [IsFiniteMeasure σ] [IsFiniteMeasure τ] (h₁ : HasLeadingMeasure W K lam q σ)
    (h₂ : HasLeadingMeasure W K lam q τ) : σ = τ

theorem hasLeadingTerm_one [IsFiniteMeasure σ] (h : HasLeadingMeasure W K lam q σ) :
    HasLeadingTerm (globalLaplace W K (1 : (Fin d → ℝ) →ᵇ ℝ)) (σ.real univ) lam q

theorem pair_unique [IsFiniteMeasure σ] [IsFiniteMeasure τ] {lam' : ℝ} {q' : ℕ}
    (h₁ : HasLeadingMeasure W K lam q σ) (h₂ : HasLeadingMeasure W K lam' q' τ) (hσ : σ ≠ 0)
    (hτ : τ ≠ 0) : lam = lam' ∧ q = q'

theorem eq_of_ne_zero [IsFiniteMeasure σ] [IsFiniteMeasure τ] {lam' : ℝ} {q' : ℕ}
    (h₁ : HasLeadingMeasure W K lam q σ) (h₂ : HasLeadingMeasure W K lam' q' τ) (hσ : σ ≠ 0)
    (hτ : τ ≠ 0) : lam = lam' ∧ q = q' ∧ σ = τ

theorem of_locality {A B : Set (Fin d → ℝ)} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : volume (A ∪ B) ≠ ⊤) (hK : Measurable K) (hK0 : ∀ x, 0 ≤ K x) {κ : ℝ} (hκ : 0 < κ)
    (hKA : ∀ᵐ x ∂(volume.restrict (A \ B)), κ ≤ K x)
    (hKB : ∀ᵐ x ∂(volume.restrict (B \ A)), κ ≤ K x) (h : HasLeadingMeasure A K lam q σ) :
    HasLeadingMeasure B K lam q σ

theorem integral_congr_of_eqOn {S : Set (Fin d → ℝ)} (hS : σ Sᶜ = 0)
    {a b : (Fin d → ℝ) → ℝ} (hab : EqOn a b S) : ∫ w, a w ∂σ = ∫ w, b w ∂σ

-- ==== Grammar/FacePieceMeasure.lean
variable {t r : ℕ} (D : FaceWeightData t r)

structure FaceWeightData (t r : ℕ)

def region : Set ((Fin t → ℝ) × (Fin r → ℝ)) := D.base ×ˢ unitBox r

theorem measurableSet_region : MeasurableSet D.region

noncomputable def weight (q : (Fin t → ℝ) × (Fin r → ℝ)) : ℝ

theorem weight_nonneg {q : (Fin t → ℝ) × (Fin r → ℝ)} (hq : q ∈ D.region) : 0 ≤ D.weight q

theorem M_nonneg (hne : D.region.Nonempty) : 0 ≤ D.M

theorem restrict_region_eq :
    (volume : Measure ((Fin t → ℝ) × (Fin r → ℝ))).restrict D.region =
      (volume.restrict D.base).prod (volume.restrict (unitBox r))

theorem aestronglyMeasurable_weight :
    AEStronglyMeasurable D.weight (volume.restrict D.region)

theorem integrable_prod_weight :
    Integrable (fun q : (Fin t → ℝ) × (Fin r → ℝ) => D.βw q.1 * residualWeight D.h D.k D.l q.2)
      (volume.restrict D.region)

theorem integrable_weight_mul {g : (Fin t → ℝ) × (Fin r → ℝ) → ℝ}
    (hg : AEStronglyMeasurable g (volume.restrict D.region)) {Mg : ℝ}
    (hgM : ∀ q ∈ D.region, |g q| ≤ Mg) :
    Integrable (fun q => D.weight q * g q) (volume.restrict D.region)

theorem integrable_weight : Integrable D.weight (volume.restrict D.region)

noncomputable def measure : Measure ((Fin t → ℝ) × (Fin r → ℝ))

theorem aemeasurable_toNNReal_weight :
    AEMeasurable (fun q => (D.weight q).toNNReal) (volume.restrict D.region)

theorem integrable_coe_toNNReal_weight :
    Integrable (fun q => ((D.weight q).toNNReal : ℝ)) (volume.restrict D.region)

theorem integral_measure {g : (Fin t → ℝ) × (Fin r → ℝ) → ℝ}
    (hg : AEStronglyMeasurable g (volume.restrict D.region)) {Mg : ℝ}
    (hgM : ∀ q ∈ D.region, |g q| ≤ Mg) :
    ∫ q, g q ∂D.measure = ∫ z in D.base, D.βw z *
      ∫ u in unitBox r, D.B z u * residualWeight D.h D.k D.l u * g (z, u)

theorem measure_compl_region : D.measure D.regionᶜ = 0

-- ==== Grammar/SourceFaceMeasure.lean
variable {d : ℕ} {C : ResolutionChart d} {K : (Fin d → ℝ) → ℝ}
  (P : ProductMonomialChartVar (ofChart C) () K) (hK0 : ∀ x, 0 ≤ K x) (ε : ℝ) (hε : 0 < ε)
  (hεb : ε ≤ P.b) {p : TubeWeight d} (hpc : ContinuousOn (fun y => p.w (C.φ y)) P.W)
  (hK : Measurable K) (I : Finset (Fin d)) (hI : I ⊆ P.e.support) (hne : I.Nonempty)

variable {ε}
include hK0 hε hεb hpc hK hI

variable {ε}

noncomputable def faceNormal (σ : Fin (I.card - 1 + 1) → Bool) (w : Fin (I.card - 1 + 1) → ℝ) :
    Fin (I.card - 1 + 1) → ℝ

noncomputable def facePoint (σ : Fin (I.card - 1 + 1) → Bool)
    (q : (Fin (d - (I.card - 1 + 1)) → ℝ) × (Fin (I.card - 1 + 1) → ℝ)) : Fin d → ℝ

theorem continuous_faceNormal (σ : Fin (I.card - 1 + 1) → Bool) :
    Continuous (P.faceNormal ε I hne σ)

theorem continuous_facePoint (σ : Fin (I.card - 1 + 1) → Bool) :
    Continuous (P.facePoint ε I hne σ)

theorem faceNormal_mem_closedBall (σ : Fin (I.card - 1 + 1) → Bool)
    {w : Fin (I.card - 1 + 1) → ℝ} (hw : w ∈ closedCube (I.card - 1 + 1)) :
    P.faceNormal ε I hne σ w ∈ Metric.closedBall (0 : Fin (I.card - 1 + 1) → ℝ) ε

theorem measurable_pieceWeight : Measurable P.pieceWeight

theorem pieceFacts :
    IsCompact (P.pieceDensity hε hεb (D

theorem mem_dom_of_mem_base {z : Fin (d - (I.card - 1 + 1)) → ℝ}
    (hz : z ∈ (P.pieceDensity hε hεb (D

noncomputable def faceAmp (σ : Fin (I.card - 1 + 1) → Bool) (z : Fin (d - (I.card - 1 + 1)) → ℝ)
    (w : Fin (I.card - 1 + 1) → ℝ) : ℝ

theorem faceAmp_nonneg (hlam : 0 < P.pieceLam I hne) (hk : ∀ a, 0 < normalHalfExp I hne P.e a)
    (σ : Fin (I.card - 1 + 1) → Bool) (z : Fin (d - (I.card - 1 + 1)) → ℝ)
    (w : Fin (I.card - 1 + 1) → ℝ) : 0 ≤ P.faceAmp ε (p := p) I hne σ z w

theorem mapsTo_facePoint (σ : Fin (I.card - 1 + 1) → Bool) :
    MapsTo (P.facePoint ε I hne σ)
      ((P.pieceDensity hε hεb (D

theorem continuousOn_faceAmp (σ : Fin (I.card - 1 + 1) → Bool) :
    ContinuousOn (Function.uncurry (P.faceAmp ε (p := p) I hne σ))
      ((P.pieceDensity hε hεb (D

theorem exists_bound_faceAmp (σ : Fin (I.card - 1 + 1) → Bool) :
    ∃ M : ℝ, ∀ q ∈ (P.pieceDensity hε hεb (D

theorem pieceLam_pos : 0 < P.pieceLam I hne

noncomputable def faceData (hr0 : ∀ x, 0 ≤ P.r x) (σ : Fin (I.card - 1 + 1) → Bool) :
    FaceWeightData (d - (I.card - 1 + 1)) (I.card - 1 + 1)

theorem faceData_B (hr0 : ∀ x, 0 ≤ P.r x) (σ : Fin (I.card - 1 + 1) → Bool) :
    (P.faceData hK0 hε hεb hpc hK I hI hne hr0 σ).B = P.faceAmp ε (p := p) I hne σ

theorem faceData_h (hr0 : ∀ x, 0 ≤ P.r x) (σ : Fin (I.card - 1 + 1) → Bool) :
    (P.faceData hK0 hε hεb hpc hK I hI hne hr0 σ).h = normalExp I hne P.h

theorem faceData_k (hr0 : ∀ x, 0 ≤ P.r x) (σ : Fin (I.card - 1 + 1) → Bool) :
    (P.faceData hK0 hε hεb hpc hK I hI hne hr0 σ).k = normalHalfExp I hne P.e

theorem faceData_l (hr0 : ∀ x, 0 ≤ P.r x) (σ : Fin (I.card - 1 + 1) → Bool) :
    (P.faceData hK0 hε hεb hpc hK I hI hne hr0 σ).l = P.pieceLam I hne

noncomputable def facePiece (hr0 : ∀ x, 0 ≤ P.r x) (σ : Fin (I.card - 1 + 1) → Bool) :
    LeadingFacePiece d

theorem sum_cell_coeff_eq {G : (Fin d → ℝ) → ℝ} (hGm : Measurable G)
    (hGc : ContinuousOn G C.dom) (hr0 : ∀ x, 0 ≤ P.r x) :
    ∑ σ, ((P.sourceAtlases hK0 hε hεb hpc hGm hGc hK I hI hne).cell σ).coeff =
      ∑ σ : Fin (I.card - 1 + 1) → Bool, ∫ q, G (P.facePoint ε I hne σ q)
        ∂(P.faceData hK0 hε hεb hpc hK I hI hne hr0 σ).measure

theorem sourceAtlasPieceCoeff_eq {G : (Fin d → ℝ) → ℝ} (hGm : Measurable G)
    (hGc : ContinuousOn G C.dom) (hr0 : ∀ x, 0 ≤ P.r x) (lam₀ : ℝ) (k₀ : ℕ) :
    ResolutionCover.sourceAtlasPieceCoeff
      (fun I hI hne => (P.sourceAtlases hK0 hε hεb hpc hGm hGc hK I hI hne).toLeading) lam₀ k₀ I =
      if P.pieceLam I hne = lam₀ ∧ P.pieceMult I hne - 1 = k₀ then
        ∑ σ : Fin (I.card - 1 + 1) → Bool, ∫ q, G (P.facePoint ε I hne σ q)
          ∂(P.faceData hK0 hε hεb hpc hK I hI hne hr0 σ).measure
      else 0

-- ==== Grammar/ChartLeadingMeasure.lean
variable {t r : ℕ} (D : FaceWeightData t r)

variable {d : ℕ}

variable {d : ℕ} {C : ResolutionChart d} {K : (Fin d → ℝ) → ℝ}
  (P : ProductMonomialChartVar (ofChart C) () K) (hK0 : ∀ x, 0 ≤ K x) {ε : ℝ} (hε : 0 < ε)
  (hεb : ε ≤ P.b) {p : TubeWeight d} (hpc : ContinuousOn (fun y => p.w (C.φ y)) P.W)
  (hK : Measurable K) (hr0 : ∀ x, 0 ≤ P.r x)

variable {d : ℕ} {ι : Type*} [Fintype ι] (R : ResolutionCover d ι) {F K : (Fin d → ℝ) → ℝ}
  {p : TubeWeight d} (Ps : ∀ i, ProductMonomialChartVar (ofChart (R.chart i)) () K)
  (hK0 : ∀ x, 0 ≤ K x) {ε : ℝ} (hε : 0 < ε) (hεb : ∀ i, ε ≤ (Ps i).b)
  (hpc : ∀ i, ContinuousOn (fun y => p.w ((R.chart i).φ y)) (Ps i).W)
  (hK : Measurable K) (hne : (R.activeCharts Ps).Nonempty) (hr0 : ∀ i x, 0 ≤ (Ps i).r x)

variable (hFc : ∀ i, ContinuousOn (fun y => F ((R.chart i).φ y)) (Ps i).W) (hFm : Measurable F)

variable {d : ℕ} {ι : Type*} [Fintype ι] (R : ResolutionCover d ι) {K : (Fin d → ℝ) → ℝ}
  (Ps : ∀ i, ProductMonomialChartVar (ofChart (R.chart i)) () K)
  (hK0 : ∀ x, 0 ≤ K x) {ε : ℝ} (hε : 0 < ε) (hεb : ∀ i, ε ≤ (Ps i).b)
  (hK : Measurable K) (hne : (R.activeCharts Ps).Nonempty) (hr0 : ∀ i x, 0 ≤ (Ps i).r x)

theorem integrable_of_bounded_on_region {g : (Fin t → ℝ) × (Fin r → ℝ) → ℝ} (hg : Measurable g)
    {Mg : ℝ} (hgM : ∀ q ∈ D.region, |g q| ≤ Mg) : Integrable g D.measure

def comp (a : LeadingFacePiece d) (T : (Fin d → ℝ) → (Fin d → ℝ)) (hT : Measurable T) :
    LeadingFacePiece d

theorem comp_targetMeasure (a : LeadingFacePiece d) (T : (Fin d → ℝ) → (Fin d → ℝ))
    (hT : Measurable T) : (a.comp T hT).targetMeasure = a.targetMeasure.map T

theorem integrable_comp_iff (a : LeadingFacePiece d) (T : (Fin d → ℝ) → (Fin d → ℝ))
    (hT : Measurable T) {f : (Fin d → ℝ) → ℝ} (hf : Measurable f) :
    Integrable f (a.comp T hT).targetMeasure ↔ Integrable (f ∘ T) a.targetMeasure

def zero (d : ℕ) : LeadingFacePiece d

abbrev PieceIdx (d : ℕ) := Σ I : Finset (Fin d), (Fin (I.card - 1 + 1) → Bool)

include hK0 hε hεb hpc hK hr0 in
/-- **The chart-level pieces**: the face piece of each admissible stratum–orthant pair, the zero
piece elsewhere. -/
noncomputable def chartPieces : PieceIdx d → LeadingFacePiece d

noncomputable def strataTied (lam₀ : ℝ) (k₀ : ℕ) : Finset (Finset (Fin d))

noncomputable def tiedPieces (lam₀ : ℝ) (k₀ : ℕ) : Finset (PieceIdx d)

theorem mem_strataTied {lam₀ : ℝ} {k₀ : ℕ} {I : Finset (Fin d)} :
    I ∈ P.strataTied lam₀ k₀ ↔ (I ⊆ P.e.support ∧ I.Nonempty) ∧
      ∃ hne : I.Nonempty, P.pieceLam I hne = lam₀ ∧ P.pieceMult I hne - 1 = k₀

noncomputable def chartLeadingMeasure (lam₀ : ℝ) (k₀ : ℕ) : Measure (Fin d → ℝ)

theorem integrable_facePiece {G : (Fin d → ℝ) → ℝ} (hGm : Measurable G)
    (hGc : ContinuousOn G C.dom) (I : Finset (Fin d)) (hI : I ⊆ P.e.support) (hne : I.Nonempty)
    (σ : Fin (I.card - 1 + 1) → Bool) :
    Integrable G (P.facePiece hK0 hε hεb hpc hK I hI hne hr0 σ).targetMeasure

theorem integrable_chartPieces {G : (Fin d → ℝ) → ℝ} (hGm : Measurable G)
    (hGc : ContinuousOn G C.dom) {lam₀ : ℝ} {k₀ : ℕ} {x : PieceIdx d}
    (hx : x ∈ P.tiedPieces lam₀ k₀) :
    Integrable G (P.chartPieces hK0 hε hεb hpc hK hr0 x).targetMeasure

theorem sourceCoeff_eq_integral {G : (Fin d → ℝ) → ℝ} (hGm : Measurable G)
    (hGc : ContinuousOn G C.dom) (lam₀ : ℝ) (k₀ : ℕ) :
    P.sourceCoeff hK0 hε hεb hpc hGm hGc hK lam₀ k₀ =
      ∫ y, G y ∂P.chartLeadingMeasure hK0 hε hεb hpc hK hr0 lam₀ k₀

abbrev CoverPieceIdx (d : ℕ) (ι : Type*) := Σ _ : ι, ProductMonomialChartVar.PieceIdx d

include hK0 hε hεb hpc hK hr0 in
/-- **The cover-level pieces**: the chart pieces pushed forward along the chart maps. -/
noncomputable def coverPieces : CoverPieceIdx d ι → LeadingFacePiece d

noncomputable def tiedCoverPieces : Finset (CoverPieceIdx d ι)

noncomputable def leadingMeasure : Measure (Fin d → ℝ)

theorem integrable_coverPieces {x : CoverPieceIdx d ι} (hx : x ∈ R.tiedCoverPieces Ps hne) :
    Integrable F (R.coverPieces Ps hK0 hε hεb hpc hK hr0 x).targetMeasure

theorem aeDisjointCoeff_eq_integral :
    R.aeDisjointCoeff Ps hK0 hε hεb hpc hFc hFm hK hne =
      ∫ x, F x ∂(R.leadingMeasure Ps hK0 hε hεb hpc hK hne hr0)

theorem hasLeadingTerm_targetIntegral_of_aeDisjoint (hdisj : R.AEDisjointImages)
    (hF : Integrable (fun x => F x * p.w x) (volume.restrict (⋃ i, R.image i))) :
    HasLeadingTerm (targetIntegral (⋃ i, R.image i) F K p)
      (∫ x, F x ∂(R.leadingMeasure Ps hK0 hε hεb hpc hK hne hr0)) (R.partitionLam' Ps hne)
      (R.partitionDeg' Ps hne)

theorem continuousOn_one_w (i : ι) :
    ContinuousOn (fun y => (TubeWeight.one d).w ((R.chart i).φ y)) (Ps i).W

theorem volume_iUnion_image_ne_top : volume (⋃ i, R.image i) ≠ ⊤

theorem hasLeadingMeasure_of_aeDisjoint (hdisj : R.AEDisjointImages) :
    HasLeadingMeasure (⋃ i, R.image i) K (R.partitionLam' Ps hne) (R.partitionDeg' Ps hne)
      (R.leadingMeasure Ps hK0 hε hεb (p := TubeWeight.one d) (R.continuousOn_one_w Ps) hK hne
        hr0)

-- ==== Grammar/GlobalCompactTheta.lean
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {R : Set X} (hR : MeasurableSet R)
  {F K : X → ℝ} (hF0 : ∀ x ∈ R, 0 ≤ F x) (hFint : IntegrableOn F R μ) (hK0 : ∀ x ∈ R, 0 ≤ K x)
  (hKm : Measurable K) {ι : Type*} (Ω : ι → Set X)
  (hΩm : ∀ i, MeasurableSet (Ω i)) (hΩR : ∀ i, Ω i ⊆ R) {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
  (hgap : ∀ᵐ x ∂μ, x ∈ R → x ∉ ⋃ i, Ω i → δ₀ ≤ K x) (lam : ι → ℝ) (m : ι → ℕ)
  (hI : ∀ i, (fun N : ℝ => ∫ x in Ω i, F x * Real.exp (-N * K x) ∂μ) =Θ[atTop]
    powLogScale (lam i) (m i - 1))

variable {d : ℕ}

theorem powLogScale_isBigO_regionIntegral_of_theta (i₀ : ι) :
    powLogScale (lam i₀) (m i₀ - 1) =O[atTop] regionIntegral μ R F K

theorem regionIntegral_isBigO_powLogScale_of_theta [Finite ι] {i₀ : ι}
    (hmin : ∀ i, lam i₀ ≤ lam i) (hmax : ∀ i, lam i = lam i₀ → m i ≤ m i₀) :
    regionIntegral μ R F K =O[atTop] powLogScale (lam i₀) (m i₀ - 1)

theorem isTheta_of_local_theta [Finite ι] [Nonempty ι] :
    ∃ i₀ : ι, (∀ i, lam i₀ ≤ lam i) ∧ (∀ i, lam i = lam i₀ → m i ≤ m i₀) ∧
      regionIntegral μ R F K =Θ[atTop] powLogScale (lam i₀) (m i₀ - 1)

theorem exists_local_theta {U W : Set (Fin d → ℝ)} (hU : IsOpen U) (hWU : W ⊆ U)
    {K : (Fin d → ℝ) → ℝ} (hK : AnalyticOnNhd ℝ K U) (hK0 : ∀ x ∈ U, 0 ≤ K x) (hKm : Measurable K)
    {F : (Fin d → ℝ) → ℝ} (hF : AnalyticOnNhd ℝ F U) (hFpos : ∀ x ∈ U, 0 < F x)
    {w : Fin d → ℝ} (hw : w ∈ W) (hKw : K w = 0) (hint : w ∈ interior W) (hnt : ¬ K =ᶠ[𝓝 w] 0) :
    ∃ (Rg : Set (Fin d → ℝ)) (l : ℝ) (q : ℕ), IsCompact Rg ∧ Rg ∈ 𝓝 w ∧ Rg ⊆ W ∧
      (∃ (N : Set (Fin d → ℝ)) (R : PartialResolution d K N), R.IsMonomial ∧
        ∃ (i : R.ι) (y₀ : Fin d → ℝ) (h : Fin d →₀ ℕ) (C : CentredChartData K (R.φ i) h y₀),
          y₀ ∈ R.dom i ∧ K (R.φ i y₀) = 0 ∧ l = C.lam ∧ q = C.mult) ∧
      regionIntegral volume Rg F K =Θ[atTop] powLogScale l (q - 1)

theorem exponent_of_compact {U W : Set (Fin d → ℝ)} (hU : IsOpen U) (hW : IsCompact W)
    (hWU : W ⊆ U) {K : (Fin d → ℝ) → ℝ} (hK : AnalyticOnNhd ℝ K U) (hK0 : ∀ x ∈ U, 0 ≤ K x)
    (hKm : Measurable K) {F : (Fin d → ℝ) → ℝ} (hF : AnalyticOnNhd ℝ F U)
    (hFpos : ∀ x ∈ U, 0 < F x) (hint : ∀ w ∈ W, K w = 0 → w ∈ interior W)
    (hnt : ∀ w ∈ W, K w = 0 → ¬ K =ᶠ[𝓝 w] 0) (hW0 : ∃ w ∈ W, K w = 0) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : Nonempty ι) (lam : ι → ℝ) (m : ι → ℕ) (i₀ : ι),
      (∀ p, ∃ w ∈ W, K w = 0 ∧ ∃ (N : Set (Fin d → ℝ)) (R : PartialResolution d K N),
        R.IsMonomial ∧ ∃ (i : R.ι) (y₀ : Fin d → ℝ) (h : Fin d →₀ ℕ)
          (C : CentredChartData K (R.φ i) h y₀),
          y₀ ∈ R.dom i ∧ K (R.φ i y₀) = 0 ∧ lam p = C.lam ∧ m p = C.mult) ∧
      (∀ p, lam i₀ ≤ lam p) ∧ (∀ p, lam p = lam i₀ → m p ≤ m i₀) ∧
      globalLaplace W K F =Θ[atTop] powLogScale (lam i₀) (m i₀ - 1)

-- ==== Grammar/BlowUpCubeLeadingMeasure.lean
variable {d : ℕ}

variable {K : (Fin d → ℝ) → ℝ} {N : Set (Fin d → ℝ)} (R : PartialResolution d K N)
  (Ps : ∀ i, ProductMonomialChartVar (ofChart ((ofPartialResolution R).chart i)) () K)
  (hK0 : ∀ x, 0 ≤ K x) {ε : ℝ} (hε : 0 < ε) (hεb : ∀ i, ε ≤ (Ps i).b) (hK : Measurable K)
  (hne : ((ofPartialResolution R).activeCharts Ps).Nonempty) (hr0 : ∀ i x, 0 ≤ (Ps i).r x)

variable (hd : 1 < d) [NeZero d]

theorem HasLeadingMeasure.of_ae_eq_set {A B : Set (Fin d → ℝ)} (hAB : A =ᵐ[volume] B)
    {K : (Fin d → ℝ) → ℝ} {lam : ℝ} {q : ℕ} {σ : Measure (Fin d → ℝ)}
    (h : HasLeadingMeasure A K lam q σ) : HasLeadingMeasure B K lam q σ

theorem iUnion_image_ofPartialResolution_ae_eq :
    (⋃ i, (ofPartialResolution R).image i) =ᵐ[volume] N

theorem hasLeadingMeasure_ofPartialResolution (hdisj : (ofPartialResolution R).AEDisjointImages) :
    HasLeadingMeasure N K ((ofPartialResolution R).partitionLam' Ps hne)
      ((ofPartialResolution R).partitionDeg' Ps hne)
      ((ofPartialResolution R).leadingMeasure Ps hK0 hε hεb (p := TubeWeight.one d)
        ((ofPartialResolution R).continuousOn_one_w Ps) hK hne hr0)

theorem hr0 : ∀ β x, 0 ≤ (Ps hd β).r x

noncomputable def leadingMeasure : Measure (Fin d → ℝ)

theorem φ_eq_zero (β : Fin d) {y : Fin d → ℝ} (hy : y β = 0) : φ β y = 0

theorem ae_Φ_facePoint_eq_zero (β : Fin d) (hIs : ({β} : Finset (Fin d)) ⊆ (Ps hd β).e.support)
    (hne : ({β} : Finset (Fin d)).Nonempty)
    (σ : Fin (({β} : Finset (Fin d)).card - 1 + 1) → Bool) :
    ∀ᵐ q ∂((Ps hd β).faceData K_nonneg one_pos (hεb hd β) ((R hd).continuousOn_one_w (Ps hd) β)
        continuous_K.measurable {β} hIs hne (hr0 hd β) σ).measure,
      ((R hd).chart β).Φ ((Ps hd β).facePoint 1 {β} hne σ q) = 0

theorem facePiece_targetMeasure (β : Fin d) (hIs : ({β} : Finset (Fin d)) ⊆ (Ps hd β).e.support)
    (hne : ({β} : Finset (Fin d)).Nonempty)
    (σ : Fin (({β} : Finset (Fin d)).card - 1 + 1) → Bool) :
    ((Ps hd β).facePiece K_nonneg one_pos (hεb hd β) ((R hd).continuousOn_one_w (Ps hd) β)
        continuous_K.measurable {β} hIs hne (hr0 hd β) σ).targetMeasure =
      ((Ps hd β).faceData K_nonneg one_pos (hεb hd β) ((R hd).continuousOn_one_w (Ps hd) β)
        continuous_K.measurable {β} hIs hne (hr0 hd β) σ).measure.map
        ((Ps hd β).facePoint 1 {β} hne σ)

theorem coverPieces_targetMeasure_eq {x : ResolutionCover.CoverPieceIdx d (Fin d)}
    (hx : x ∈ (R hd).tiedCoverPieces (Ps hd) (hne hd)) :
    ((R hd).coverPieces (Ps hd) K_nonneg one_pos (hεb hd) (p := TubeWeight.one d)
        ((R hd).continuousOn_one_w (Ps hd)) continuous_K.measurable (hr0 hd) x).targetMeasure =
      ((R hd).coverPieces (Ps hd) K_nonneg one_pos (hεb hd) (p := TubeWeight.one d)
        ((R hd).continuousOn_one_w (Ps hd)) continuous_K.measurable (hr0 hd) x).measure univ •
        Measure.dirac 0

theorem leadingMeasure_eq :
    leadingMeasure hd = ENNReal.ofReal (Real.pi ^ (d / 2 : ℝ)) • Measure.dirac 0

theorem hasLeadingMeasure_cube :
    HasLeadingMeasure (cube d) K (d / 2) 0
      (ENNReal.ofReal (Real.pi ^ (d / 2 : ℝ)) • Measure.dirac 0)

theorem tendsto_cube_laplace (a : (Fin d → ℝ) →ᵇ ℝ) :
    Tendsto (fun t : ℝ => (∫ x in cube d, a x * Real.exp (-t * K x)) / t ^ (-(d / 2 : ℝ))) atTop
      (𝓝 (Real.pi ^ (d / 2 : ℝ) * a 0))

```

## New mirror paragraph (grammar_lean.tex)

