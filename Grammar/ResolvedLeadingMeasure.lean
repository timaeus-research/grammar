/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.EmpiricalResolvedLeading
import Grammar.LeadingFaceMeasure

/-!
# The leading measures on the resolved space (polar-distribution plan, unit 19)

Consult #169 (`tide-log/gpt6_leading_v169.md`).  The library's face measures on `U`
(`faceMeasureU Y p J μ`, the pushforward of the face density `faceNorm' · ρf · residueWeight` along
the face map, and its tilted version `empFaceMeasureU Y p J ξ μ` with the fluctuation density of
the branch trace) were used through their restrictions to the OPEN stratum `X = U ∖ D_{m+1}` and
against test functions.  At the leading pair `(λ, m)` of a chart-leading transport the
complementary walls of every attaining face carry exponents `> λ`, so the face densities are
integrable against every BOUNDED observable (`integrable_faceDensity_mul_leading`), and the sums

  `leadingResidueMeasureU λ m   = Σ_p Σ_{J ∈ simpleFaces p λ m} faceMeasureU Y p J λ`
  `empiricalLeadingMeasureU ξ λ m = Γ(λ)/(m−1)! · Σ_p Σ_{J ∈ simpleFaces p λ m}
empFaceMeasureU Y p J ξ λ`

are FINITE measures on `U` (`isFiniteMeasure_leadingResidueMeasureU`,
`isFiniteMeasure_empiricalLeadingMeasureU`).  The leading term of the empirical partition function
is then the integral of the observable against the tilted leading measure for EVERY observable
(★★★ `hasLeadingTerm_empZ_eq_integral_leadingU`, no test hypothesis: the identification
`integral_pieceFaceLimit_eq_faceRef` of the piece face limits with the face integrals uses only the
boundedness of the observable on the compact face), and at the zero field the population partition
function has the leading term `residueConst λ m · ∫ F dρ` against the raw measure
(★★ `hasLeadingTerm_Z_eq_integral_leadingResidueMeasureU`).  The raw measure is the
`(m−1)!/Γ(λ)`-multiple of the population coefficient measure (Astra #169: keep the two
normalisations distinct).
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff Manifold
open Monomialize.VolumeScaling Monomialize.Transport Monomialize.Manifold
open Grammar.NormalCrossing Grammar.NormalCrossing.EvenChartBoxDepth

namespace Grammar

namespace SmoothEngine

namespace ResolvedData

variable {d : ℕ} (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)

/-! ### Unconditional integral formulas for the face measures on `U` -/

section Integrals

variable (p : (Ξ.X Y).PIdx) (J : Finset (Fin ((Ξ.X Y).da p)))

/-- Integrals against the face measure on `U` are density integrals on the face. -/
theorem integral_faceMeasureU (μ : ℝ) {G : Ξ.R.U → ℝ} (hG : Measurable G) :
    ∫ x, G x ∂(Ξ.faceMeasureU Y p J μ) =
      ∫ z, Ξ.faceDensity Y p J μ z * G (Ξ.faceMap Y p J z) ∂(Ξ.faceRef Y p J) := by
  unfold faceMeasureU
  rw [integral_map (Ξ.measurable_faceMap Y p J).aemeasurable hG.aestronglyMeasurable]
  have hmeas : Measurable fun z => (Ξ.faceDensity Y p J μ z).toNNReal :=
    (Ξ.measurable_faceDensity Y p J μ).real_toNNReal
  have hd : (fun z => ENNReal.ofReal (Ξ.faceDensity Y p J μ z)) =
      fun z => ((Ξ.faceDensity Y p J μ z).toNNReal : ENNReal) := rfl
  rw [hd, integral_withDensity_eq_integral_smul hmeas]
  refine integral_congr_ae ?_
  filter_upwards [Ξ.ae_faceRef_mem_box Y p J] with z hz
  simp only [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (Ξ.faceDensity_nonneg Y p J μ hz)]

/-- Integrals against the tilted face measure on `U`. -/
theorem integral_empFaceMeasureU (ξ : Ξ.RootField Y) {μ : ℝ} (hμ : 0 < μ) {G : Ξ.R.U → ℝ}
    (hG : Measurable G) :
    ∫ x, G x ∂(Ξ.empFaceMeasureU Y p J ξ μ) =
      ∫ z, Ξ.empFaceDensity Y p J ξ μ z * G (Ξ.faceMap Y p J z) ∂(Ξ.faceRef Y p J) := by
  unfold empFaceMeasureU
  rw [integral_map (Ξ.measurable_faceMap Y p J).aemeasurable hG.aestronglyMeasurable]
  have hmeas : Measurable fun z => (Ξ.empFaceDensity Y p J ξ μ z).toNNReal :=
    (Ξ.measurable_empFaceDensity Y p J ξ hμ).real_toNNReal
  have hd : (fun z => ENNReal.ofReal (Ξ.empFaceDensity Y p J ξ μ z)) =
      fun z => ((Ξ.empFaceDensity Y p J ξ μ z).toNNReal : ENNReal) := rfl
  rw [hd, integral_withDensity_eq_integral_smul hmeas]
  refine integral_congr_ae ?_
  filter_upwards [Ξ.ae_faceRef_mem_box Y p J] with z hz
  simp only [NNReal.smul_def, smul_eq_mul,
    Real.coe_toNNReal _ (Ξ.empFaceDensity_nonneg Y p J ξ hμ hz)]

/-- An observable smooth on `U` is bounded on the face of a piece. -/
theorem exists_bound_faceMap {G : Ξ.R.U → ℝ} (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) :
    ∃ C : ℝ, ∀ z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × ({i // ¬ inJ J i} → ℝ),
      z.2 ∈ box {i // ¬ inJ J i} (Y.T.a p.1) → |G (Ξ.faceMap Y p J z)| ≤ C := by
  have hcont : ContinuousOn (fun z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × ({i // ¬ inJ J i} → ℝ) =>
      G ((Y.φ p.1).symm ((Ξ.X Y).Tm p z.1 (glue J 0 z.2))))
      ((univ : Set (Base ((Ξ.X Y).act p.1) (Y.T.a p.1))) ×ˢ
        (Set.univ.pi fun _ : {i // ¬ inJ J i} => Icc (0 : ℝ) (Y.T.a p.1))) := by
    refine hG.continuous.comp_continuousOn ((Y.φ p.1).continuousOn_symm.comp
      (((Ξ.X Y).continuous_Tm p).comp
        (continuous_fst.prodMk ((continuous_glue_zero J).comp continuous_snd))).continuousOn
      fun z hz => ?_)
    exact Ξ.facePt_mem_target Y p z.1
      (glue_zero_mem_closedBox_of_mem_Icc (Y.T.a_pos p.1).le fun i _ => hz.2 i (mem_univ i))
  obtain ⟨C, hC⟩ := (isCompact_univ.prod
    (isCompact_univ_pi fun _ => isCompact_Icc)).exists_bound_of_continuousOn hcont
  refine ⟨C, fun z hz => ?_⟩
  rw [Ξ.faceMap_eq_divPt Y p J hz]
  have hz' : z ∈ (univ : Set (Base ((Ξ.X Y).act p.1) (Y.T.a p.1))) ×ˢ
      (Set.univ.pi fun _ : {i // ¬ inJ J i} => Icc (0 : ℝ) (Y.T.a p.1)) :=
    ⟨mem_univ _, fun i _ => Ioc_subset_Icc_self (hz i (mem_univ i))⟩
  simpa [divPt, facePt, Real.norm_eq_abs] using hC z hz'

end Integrals

/-! ### Integrability at the leading face -/

section Leading

variable (p : (Ξ.X Y).PIdx) {lam : ℝ} {m : ℕ}

/-- The face density of the leading face is integrable against every observable bounded on the
face: the complementary walls carry exponents `> λ`. -/
theorem integrable_faceDensity_mul_leading (hlead : BoxLeading ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) lam m)
    {G : Ξ.R.U → ℝ} (hGm : Measurable G) {C : ℝ}
    (hGC : ∀ z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) ×
      ({i // ¬ inJ (resSet ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) lam) i} → ℝ),
      z.2 ∈ box _ (Y.T.a p.1) → |G (Ξ.faceMap Y p _ z)| ≤ C) :
    Integrable (fun z => Ξ.faceDensity Y p (resSet ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) lam) lam z *
      G (Ξ.faceMap Y p _ z)) (Ξ.faceRef Y p _) := by
  set J := resSet ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) lam with hJ
  -- a uniform bound on the transport density on the closed face
  have hcont : ContinuousOn (fun z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × ({i // ¬ inJ J i} → ℝ) =>
      (Ξ.X Y).ρf p.1 ((Ξ.X Y).Tm p z.1 (glue J 0 z.2)))
      ((univ : Set (Base ((Ξ.X Y).act p.1) (Y.T.a p.1))) ×ˢ
        (Set.univ.pi fun _ : {i // ¬ inJ J i} => Icc (0 : ℝ) (Y.T.a p.1))) :=
    (((Ξ.X Y).contDiff_ρf p.1).continuous.comp (((Ξ.X Y).continuous_Tm p).comp
      (continuous_fst.prodMk ((continuous_glue_zero J).comp continuous_snd)))).continuousOn
  obtain ⟨M, hM⟩ := (isCompact_univ.prod
    (isCompact_univ_pi fun _ => isCompact_Icc)).exists_bound_of_continuousOn hcont
  have hM' : ∀ z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × ({i // ¬ inJ J i} → ℝ),
      z.2 ∈ box {i // ¬ inJ J i} (Y.T.a p.1) →
      |(Ξ.X Y).ρf p.1 ((Ξ.X Y).Tm p z.1 (glue J 0 z.2))| ≤ M := fun z hz => by
    have := hM z ⟨mem_univ _, fun i _ => Ioc_subset_Icc_self (hz i (mem_univ i))⟩
    simpa [Real.norm_eq_abs] using this
  have hN0 : 0 ≤ Ξ.faceNorm' Y p J := (Ξ.faceNorm'_pos Y p J).le
  have hM0 : 0 ≤ max M 0 := le_max_right _ _
  have hC0 : 0 ≤ max C 0 := le_max_right _ _
  -- the integrable majorant `faceNorm' · M · C · residueWeight`
  have hmaj : Integrable (fun z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × ({i // ¬ inJ J i} → ℝ) =>
      (Ξ.faceNorm' Y p J * max M 0 * max C 0) *
        residueWeight (fun i : {i // ¬ inJ J i} => (Ξ.X Y).hA p i) (fun i => (Ξ.X Y).kA p i)
          lam z.2) (Ξ.faceRef Y p J) := by
    unfold faceRef
    exact (integrable_const (μ := (Ξ.piecePresentation Y p).ν) _).mul_prod
      (integrableOn_residueWeight_compl (h := (Ξ.X Y).hA p) (k := (Ξ.X Y).kA p) (l := lam)
        ((Ξ.X Y).kA_pos p) hlead.1 (Y.T.a_pos p.1).le)
  refine hmaj.mono' ((Ξ.measurable_faceDensity Y p J lam).mul
    (hGm.comp (Ξ.measurable_faceMap Y p J))).aestronglyMeasurable ?_
  filter_upwards [Ξ.ae_faceRef_mem_box Y p J] with z hz
  rw [Real.norm_eq_abs, abs_mul]
  unfold faceDensity
  have hrw : 0 ≤ residueWeight (fun i : {i // ¬ inJ J i} => (Ξ.X Y).hA p i)
      (fun i => (Ξ.X Y).kA p i) lam z.2 := residueWeight_nonneg _ _ lam hz
  rw [abs_mul, abs_mul, abs_of_nonneg hN0, abs_of_nonneg hrw]
  calc Ξ.faceNorm' Y p J * |(Ξ.X Y).ρf p.1 ((Ξ.X Y).Tm p z.1 (glue J 0 z.2))| *
        residueWeight (fun i : {i // ¬ inJ J i} => (Ξ.X Y).hA p i) (fun i => (Ξ.X Y).kA p i)
          lam z.2 *
        |G (Ξ.faceMap Y p J z)|
      ≤ Ξ.faceNorm' Y p J * max M 0 *
        residueWeight (fun i : {i // ¬ inJ J i} => (Ξ.X Y).hA p i) (fun i => (Ξ.X Y).kA p i)
          lam z.2 *
        max C 0 := by
        gcongr
        · exact (hM' z hz).trans (le_max_left _ _)
        · exact (hGC z hz).trans (le_max_left _ _)
    _ = _ := by ring

/-- The tilted face density of the leading face is integrable against every bounded observable. -/
theorem integrable_empFaceDensity_mul_leading (ξ : Ξ.RootField Y) (hμ : 0 < lam)
    (hlead : BoxLeading ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) lam m) {G : Ξ.R.U → ℝ} (hGm : Measurable G)
    {C : ℝ}
    (hGC : ∀ z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) ×
      ({i // ¬ inJ (resSet ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) lam) i} → ℝ),
      z.2 ∈ box _ (Y.T.a p.1) → |G (Ξ.faceMap Y p _ z)| ≤ C) :
    Integrable (fun z => Ξ.empFaceDensity Y p (resSet ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) lam) ξ lam z *
      G (Ξ.faceMap Y p _ z)) (Ξ.faceRef Y p _) := by
  set J := resSet ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) lam with hJ
  obtain ⟨M, -, hM⟩ := ξ.exists_bound
  have hint := Ξ.integrable_faceDensity_mul_leading Y p hlead hGm hGC
  have h := hint.bdd_mul (c := fluctDensity lam M)
    ((continuous_fluctDensity hμ).comp (Ξ.continuous_faceTrace Y p J ξ)).aestronglyMeasurable
    (by
      filter_upwards [Ξ.ae_faceRef_mem_box Y p J] with z hz
      rw [Function.comp_apply, Real.norm_eq_abs, abs_of_pos (fluctDensity_pos hμ _)]
      exact fluctDensity_le_of_abs_le hμ (Ξ.faceTrace_abs_le Y p J ξ (hM p) hz))
  refine h.congr (Eventually.of_forall fun z => ?_)
  simp only [Function.comp_apply, empFaceDensity]
  ring

/-- ★ **Identification of the piece face limit without a test hypothesis**: for an attaining
piece, `∫_{Base} pieceFaceLimit dν_p = residueConst λ m · ∫ empFaceDensity · F ∘ faceMap
  d(faceRef)`. -/
theorem integral_pieceFaceLimit_eq_faceRef (ξ : Ξ.RootField Y) (hμ : 0 < lam)
    (hlead : BoxLeading ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) lam m)
    (hmc : multCount (ratioExp ((Ξ.X Y).hA p) ((Ξ.X Y).kA p)) lam = m) :
    ∫ s, Ξ.pieceFaceLimit Y p ξ lam m s ∂(Ξ.piecePresentation Y p).ν =
      residueConst lam m * ∫ z, Ξ.empFaceDensity Y p (resSet ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) lam) ξ
        lam z * Ξ.F (Ξ.faceMap Y p _ z) ∂(Ξ.faceRef Y p _) := by
  obtain ⟨C, hC⟩ := Ξ.exists_bound_faceMap Y p (resSet ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) lam)
    Ξ.F_smooth
  rw [← integral_const_mul]
  unfold faceRef
  rw [integral_prod _ ((Ξ.integrable_empFaceDensity_mul_leading Y p ξ hμ hlead
    Ξ.F_smooth.continuous.measurable hC).const_mul (residueConst lam m))]
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  simp only [pieceFaceLimit, boxFaceLimit, if_pos hmc, faceFunctional]
  rw [← integral_const_mul]
  set J := resSet ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) lam with hJ
  refine setIntegral_congr_fun (measurableSet_box _) fun w hw => ?_
  have hface := Ξ.faceDensity_mul_eq Y p J Ξ.F_smooth lam (z := (s, w)) hw
  have hamp : (Ξ.ampObs Y p Ξ.F_smooth).amp s (glue J 0 w) =
    (Ξ.amp Y p).amp s (glue J 0 w) := rfl
  rw [hamp] at hface
  unfold empFaceDensity
  rw [show Ξ.faceDensity Y p J lam (s, w) * fluctDensity lam (Ξ.faceTrace Y p J ξ (s, w)) *
      Ξ.F (Ξ.faceMap Y p J (s, w)) =
      fluctDensity lam (Ξ.faceTrace Y p J ξ (s, w)) *
        (Ξ.faceDensity Y p J lam (s, w) * Ξ.F (Ξ.faceMap Y p J (s, w))) by ring, hface,
    Ξ.faceNorm'_eq_inv_prod Y p J]
  unfold faceTrace fluctDensity residueConst
  dsimp only
  rw [hmc]
  have hΓ : Real.Gamma lam ≠ 0 := (Real.Gamma_pos_of_pos hμ).ne'
  have hfact : ((m - 1).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have hprod : (∏ i ∈ J, (2 * ((Ξ.X Y).kA p i : ℝ))) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ => by
      have := Nat.cast_pos (α := ℝ) |>.2 ((Ξ.X Y).kA_pos p i)
      positivity
  field_simp

end Leading

/-! ### The leading measures on `U` -/

section Assembly

variable {lam : ℝ} {m : ℕ}

/-- ★★ **The raw leading measure** on `U` at `(λ, m)`: the sum over the pieces and their simple
faces of size `m` of the face measures. -/
noncomputable def leadingResidueMeasureU (lam : ℝ) (m : ℕ) : Measure Ξ.R.U :=
  ∑ p : (Ξ.X Y).PIdx, ∑ J ∈ Ξ.simpleFaces Y p lam m, Ξ.faceMeasureU Y p J lam

/-- ★★ **The tilted leading measure** on `U` at `(λ, m)` for the root field `ξ`, with the
coefficient normalisation `Γ(λ)/(m−1)!`. -/
noncomputable def empiricalLeadingMeasureU (ξ : Ξ.RootField Y) (lam : ℝ) (m : ℕ) :
    Measure Ξ.R.U :=
  ENNReal.ofReal (residueConst lam m) •
    ∑ p : (Ξ.X Y).PIdx, ∑ J ∈ Ξ.simpleFaces Y p lam m, Ξ.empFaceMeasureU Y p J ξ lam

/-- Every simple face of size `m` of a chart-leading piece is the resonant set. -/
theorem eq_resSet_of_mem_simpleFaces (p : (Ξ.X Y).PIdx)
    (hlead : BoxLeading ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) lam m) {J : Finset (Fin ((Ξ.X Y).da p))}
    (hJ : J ∈ Ξ.simpleFaces Y p lam m) :
    J = resSet ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) lam ∧
      multCount (ratioExp ((Ξ.X Y).hA p) ((Ξ.X Y).kA p)) lam = m := by
  rcases lt_or_eq_of_le hlead.2 with hlt | heq
  · rw [Ξ.simpleFaces_eq_empty Y p hlt] at hJ
    exact absurd hJ (Finset.notMem_empty _)
  · rw [Ξ.simpleFaces_eq_singleton Y p heq, Finset.mem_singleton] at hJ
    exact ⟨hJ, heq⟩

/-- Integrability of a bounded observable against a tilted face measure of a chart-leading
piece. -/
theorem integrable_empFaceMeasureU_of_bounded (ξ : Ξ.RootField Y) (hμ : 0 < lam)
    (p : (Ξ.X Y).PIdx) (hlead : BoxLeading ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) lam m)
    {J : Finset (Fin ((Ξ.X Y).da p))} (hJ : J ∈ Ξ.simpleFaces Y p lam m) {G : Ξ.R.U → ℝ}
    (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) :
    Integrable G (Ξ.empFaceMeasureU Y p J ξ lam) := by
  obtain ⟨rfl, -⟩ := Ξ.eq_resSet_of_mem_simpleFaces Y p hlead hJ
  obtain ⟨C, hC⟩ := Ξ.exists_bound_faceMap Y p (resSet ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) lam) hG
  unfold empFaceMeasureU
  rw [integrable_map_measure hG.continuous.measurable.aestronglyMeasurable
    (Ξ.measurable_faceMap Y p (resSet ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) lam)).aemeasurable]
  have hmeas : Measurable fun z => (Ξ.empFaceDensity Y p (resSet ((Ξ.X Y).hA p) ((Ξ.X Y).kA p)
    lam) ξ lam z).toNNReal :=
    (Ξ.measurable_empFaceDensity Y p (resSet ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) lam) ξ hμ).real_toNNReal
  have hd : (fun z => ENNReal.ofReal (Ξ.empFaceDensity Y p (resSet ((Ξ.X Y).hA p) ((Ξ.X Y).kA
    p) lam) ξ lam z)) =
      fun z => ((Ξ.empFaceDensity Y p (resSet ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) lam) ξ lam
        z).toNNReal : ENNReal) := rfl
  rw [hd, integrable_withDensity_iff_integrable_smul hmeas]
  refine (Ξ.integrable_empFaceDensity_mul_leading Y p ξ hμ hlead hG.continuous.measurable
    hC).congr ?_
  filter_upwards [Ξ.ae_faceRef_mem_box Y p (resSet ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) lam)] with z hz
  simp only [Function.comp_apply, NNReal.smul_def, smul_eq_mul,
    Real.coe_toNNReal _ (Ξ.empFaceDensity_nonneg Y p (resSet ((Ξ.X Y).hA p) ((Ξ.X Y).kA p)
      lam) ξ hμ hz)]

theorem integrable_faceMeasureU_of_bounded (hμ : 0 < lam) (p : (Ξ.X Y).PIdx)
    (hlead : BoxLeading ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) lam m) {J : Finset (Fin ((Ξ.X Y).da p))}
    (hJ : J ∈ Ξ.simpleFaces Y p lam m) {G : Ξ.R.U → ℝ}
    (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) :
    Integrable G (Ξ.faceMeasureU Y p J lam) := by
  have := Ξ.integrable_empFaceMeasureU_of_bounded Y (RootField.zero Ξ Y) hμ p hlead hJ hG
  rwa [Ξ.empFaceMeasureU_zero Y p J hμ] at this

/-- ★ Integrals of smooth observables against the tilted leading measure. -/
theorem integral_empiricalLeadingMeasureU (ξ : Ξ.RootField Y) (hμ : 0 < lam)
    (hlead : Ξ.ChartLeading Y lam m) {G : Ξ.R.U → ℝ}
    (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) :
    ∫ x, G x ∂(Ξ.empiricalLeadingMeasureU Y ξ lam m) =
      residueConst lam m * ∑ p : (Ξ.X Y).PIdx, ∑ J ∈ Ξ.simpleFaces Y p lam m,
        ∫ z, Ξ.empFaceDensity Y p J ξ lam z * G (Ξ.faceMap Y p J z) ∂(Ξ.faceRef Y p J) := by
  unfold empiricalLeadingMeasureU
  rw [integral_smul_measure, ENNReal.toReal_ofReal (residueConst_pos hμ m).le, smul_eq_mul,
    integral_finsetSum_measure fun p _ => integrable_finsetSum_measure.2 fun J hJ =>
      Ξ.integrable_empFaceMeasureU_of_bounded Y ξ hμ p (hlead p) hJ hG]
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [integral_finsetSum_measure fun J hJ =>
    Ξ.integrable_empFaceMeasureU_of_bounded Y ξ hμ p (hlead p) hJ hG]
  exact Finset.sum_congr rfl fun J _ =>
    Ξ.integral_empFaceMeasureU Y p J ξ hμ hG.continuous.measurable

/-- At the zero field the tilted leading measure is the coefficient-normalised raw measure. -/
theorem empiricalLeadingMeasureU_zero (hμ : 0 < lam) (m : ℕ) :
    Ξ.empiricalLeadingMeasureU Y (RootField.zero Ξ Y) lam m =
      ENNReal.ofReal (residueConst lam m) • Ξ.leadingResidueMeasureU Y lam m := by
  unfold empiricalLeadingMeasureU leadingResidueMeasureU
  refine congrArg (fun ν : Measure Ξ.R.U => ENNReal.ofReal (residueConst lam m) • ν)
    (Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun J _ => ?_)
  exact Ξ.empFaceMeasureU_zero Y p J hμ

/-- ★★★ **The empirical leading theorem for every observable**: at a chart-leading pair and for
a bounded root field, `N^λ (log N)^{−(m−1)} Z^{emp}_N[F; ξ] → ∫_U F dν̂^λ_m(ξ)` against the tilted
leading measure on `U` — no test hypothesis on `F`. -/
theorem hasLeadingTerm_empZ_eq_integral_leadingU (ξ : Ξ.RootField Y) (hμ : 0 < lam)
    (hm : 1 ≤ m) (hlead : Ξ.ChartLeading Y lam m) {M : ℝ} (hM : ∀ P, |ξ.ψ P| ≤ M) :
    HasLeadingTerm (Ξ.empZ Y ξ) (∫ x, Ξ.F x ∂(Ξ.empiricalLeadingMeasureU Y ξ lam m)) lam
      (m - 1) := by
  have hsum : ∀ p : (Ξ.X Y).PIdx, residueConst lam m * ∑ J ∈ Ξ.simpleFaces Y p lam m,
      ∫ z, Ξ.empFaceDensity Y p J ξ lam z * Ξ.F (Ξ.faceMap Y p J z) ∂(Ξ.faceRef Y p J) =
      ∫ s, Ξ.pieceFaceLimit Y p ξ lam m s ∂(Ξ.piecePresentation Y p).ν := by
    intro p
    rcases lt_or_eq_of_le (hlead p).2 with hlt | heq
    · rw [Ξ.simpleFaces_eq_empty Y p hlt, Finset.sum_empty, mul_zero]
      symm
      refine integral_eq_zero_of_ae (Eventually.of_forall fun s => ?_)
      simp only [pieceFaceLimit, boxFaceLimit, if_neg hlt.ne, Pi.zero_apply]
    · rw [Ξ.simpleFaces_eq_singleton Y p heq, Finset.sum_singleton,
        Ξ.integral_pieceFaceLimit_eq_faceRef Y p ξ hμ (hlead p) heq]
  have htot : ∫ x, Ξ.F x ∂(Ξ.empiricalLeadingMeasureU Y ξ lam m) =
      ∑ p : (Ξ.X Y).PIdx, ∫ s, Ξ.pieceFaceLimit Y p ξ lam m s ∂(Ξ.piecePresentation Y p).ν := by
    rw [Ξ.integral_empiricalLeadingMeasureU Y ξ hμ hlead Ξ.F_smooth, Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => hsum p
  rw [htot]
  exact Ξ.hasLeadingTerm_empZ Y ξ hm hlead hM

/-- ★★ **The population leading theorem for every observable**: at a chart-leading pair,
`N^λ (log N)^{−(m−1)} Z_N[F] → residueConst λ m · ∫_U F dρ^λ_m` against the raw leading
measure. -/
theorem hasLeadingTerm_Z_eq_integral_leadingResidueMeasureU (hμ : 0 < lam) (hm : 1 ≤ m)
    (hlead : Ξ.ChartLeading Y lam m) :
    HasLeadingTerm Ξ.Z (residueConst lam m * ∫ x, Ξ.F x ∂(Ξ.leadingResidueMeasureU Y lam m)) lam
      (m - 1) := by
  have h := Ξ.hasLeadingTerm_empZ_eq_integral_leadingU Y (RootField.zero Ξ Y) hμ hm hlead
    (M := 0) fun P => by simp [RootField.zero]
  rw [Ξ.empiricalLeadingMeasureU_zero Y hμ m, integral_smul_measure,
    ENNReal.toReal_ofReal (residueConst_pos hμ m).le, smul_eq_mul] at h
  refine h.congr' (Eventually.of_forall fun N => ?_)
  unfold empZ Z empIntegrand
  refine integral_congr_ae (Eventually.of_forall fun P => ?_)
  change Real.exp (-N * Ξ.phaseU P + Real.sqrt N * Real.sqrt (Ξ.phaseU P) * 0) * Ξ.F P = _
  rw [mul_zero, add_zero, mul_comm]
  rfl

/-- ★ The tilted leading measure is finite at a chart-leading pair. -/
theorem isFiniteMeasure_empiricalLeadingMeasureU (ξ : Ξ.RootField Y) (hμ : 0 < lam)
    (hlead : Ξ.ChartLeading Y lam m) :
    IsFiniteMeasure (Ξ.empiricalLeadingMeasureU Y ξ lam m) := by
  refine ⟨?_⟩
  unfold empiricalLeadingMeasureU
  rw [Measure.smul_apply, Measure.finsetSum_apply]
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.sum_lt_top.2 fun p _ => ?_)
  rw [Measure.finsetSum_apply]
  refine ENNReal.sum_lt_top.2 fun J hJ => ?_
  have hint := Ξ.integrable_empFaceMeasureU_of_bounded Y ξ hμ p (hlead p) hJ
    (G := fun _ => (1 : ℝ)) contMDiff_const
  exact ((integrable_const_iff.1 hint).resolve_left one_ne_zero).measure_univ_lt_top

theorem isFiniteMeasure_leadingResidueMeasureU (hμ : 0 < lam) (hlead : Ξ.ChartLeading Y lam m) :
    IsFiniteMeasure (Ξ.leadingResidueMeasureU Y lam m) := by
  refine ⟨?_⟩
  unfold leadingResidueMeasureU
  rw [Measure.finsetSum_apply]
  refine ENNReal.sum_lt_top.2 fun p _ => ?_
  rw [Measure.finsetSum_apply]
  refine ENNReal.sum_lt_top.2 fun J hJ => ?_
  have hint := Ξ.integrable_faceMeasureU_of_bounded Y hμ p (hlead p) hJ (G := fun _ => (1 : ℝ))
    contMDiff_const
  exact ((integrable_const_iff.1 hint).resolve_left one_ne_zero).measure_univ_lt_top

end Assembly

end ResolvedData

end SmoothEngine

end Grammar
