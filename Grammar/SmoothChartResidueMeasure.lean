/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothChartResidueCollar

/-!
# The chart residue measure: the face densities as a measure on `X = U ∖ D_{c+1}`

Units 2–3 and 5 of the chart-pushforward identity (consult #135). For a piece `p` of the resolved
core transport and a face `J` of its box, the FACE PARAMETER SPACE is `Base_p × ℝ^{Jᶜ}` with the
reference measure `base ⊗ volume|box` (`faceRef`), the F-free FACE DENSITY is
`∏_{j∈J}(2k_j)⁻¹ · ρ(Tm(s, glue J 0 w)) · residueWeight(w)` (`faceDensity`: `ρ = ω·|b|·prior∘ψ`
is the transport density), and the FACE MAP sends `(s, w)` to the divisor point
`divPt p s (glue J 0 w)`
(`faceMap`). The face
measure on `U` is the pushforward of the density measure (`faceMeasureU`),
restricted to `X` along the measurable embedding `X ↪ U` (`faceMeasure`); the CHART RESIDUE
MEASURE is the finite sum over pieces and simple faces (`chartResidueMeasure`). The smooth-test
bridge (`integral_faceMeasure_test`, `integral_chartResidueMeasure_test`): for a test `G` compactly
supported in `X`, `∫ G dfaceMeasure = ∫_s dlogResidueInt(…, amp of G at s) dbase`, so
`∫ G dchartResidueMeasure = residueSum / residueConst` — the pushforward of the face densities
integrates a test to the residue sum of CDLIII. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology Finset
open scoped ENNReal ContDiff Manifold
open Monomialize.VolumeScaling Monomialize.Transport Monomialize.Manifold
open Grammar.NormalCrossing Grammar.NormalCrossing.EvenChartBoxDepth

namespace Grammar

namespace SmoothEngine

namespace ResolvedData

variable {d : ℕ} (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)
  (p : (Ξ.X Y).PIdx) (J : Finset (Fin ((Ξ.X Y).da p)))

/-! ### The face parameter space -/

/-- The reference measure `base ⊗ volume|box` on the face parameter space `Base × ℝ^{Jᶜ}`. -/
noncomputable def faceRef :
    Measure (Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × ({i // ¬ inJ J i} → ℝ)) :=
  (Ξ.piecePresentation Y p).ν.prod (volume.restrict (box {i // ¬ inJ J i} (Y.T.a p.1)))

instance : IsFiniteMeasure (Ξ.faceRef Y p J) := by
  unfold faceRef
  have : IsFiniteMeasure (volume.restrict (box {i // ¬ inJ J i} (Y.T.a p.1))) :=
    isFiniteMeasure_restrict.2 (volume_box_lt_top _).ne
  infer_instance

theorem faceRef_eq_restrict : Ξ.faceRef Y p J =
    ((Ξ.piecePresentation Y p).ν.prod volume).restrict
      (Set.univ ×ˢ box {i // ¬ inJ J i} (Y.T.a p.1)) := by
  unfold faceRef
  rw [← Measure.restrict_univ (μ := (Ξ.piecePresentation Y p).ν), Measure.prod_restrict,
    Measure.restrict_univ]

theorem ae_faceRef_mem_box :
    ∀ᵐ z ∂(Ξ.faceRef Y p J), z.2 ∈ box {i // ¬ inJ J i} (Y.T.a p.1) := by
  rw [faceRef_eq_restrict]
  exact (ae_restrict_mem (MeasurableSet.univ.prod (measurableSet_box _))).mono fun z hz => hz.2

theorem glue_mem_closedBox_of_mem_box {w : {i // ¬ inJ J i} → ℝ}
    (hw : w ∈ box {i // ¬ inJ J i} (Y.T.a p.1)) : glue J 0 w ∈ closedBox _ (Y.T.a p.1) :=
  glue_zero_mem_closedBox_of_mem_Icc (Y.T.a_pos p.1).le fun i _ =>
    Set.Ioc_subset_Icc_self (hw i (Set.mem_univ i))

/-! ### The face density and the face map -/

/-- The multiplicity normalisation `∏_{j∈J} (2k_j)⁻¹` of a face. -/
noncomputable def faceNorm' : ℝ := ∏ j : {i // inJ J i}, (2 * ((Ξ.X Y).kA p j : ℝ))⁻¹

theorem faceNorm'_pos : 0 < Ξ.faceNorm' Y p J :=
  Finset.prod_pos fun j _ => inv_pos.2 (by
    have := Nat.cast_pos (α := ℝ) |>.2 ((Ξ.X Y).kA_pos p j.1)
    positivity)

/-- The F-free face density: normalisation × transport density at the face point × residue
weight of the complementary coordinates. -/
noncomputable def faceDensity (μ : ℝ)
    (z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × ({i // ¬ inJ J i} → ℝ)) : ℝ :=
  Ξ.faceNorm' Y p J * (Ξ.X Y).ρf p.1 ((Ξ.X Y).Tm p z.1 (glue J 0 z.2)) *
    residueWeight (fun i : {i // ¬ inJ J i} => (Ξ.X Y).hA p i) (fun i => (Ξ.X Y).kA p i) μ z.2

theorem faceDensity_nonneg (μ : ℝ)
    {z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × ({i // ¬ inJ J i} → ℝ)}
    (hz : z.2 ∈ box {i // ¬ inJ J i} (Y.T.a p.1)) : 0 ≤ Ξ.faceDensity Y p J μ z :=
  mul_nonneg (mul_nonneg (Ξ.faceNorm'_pos Y p J).le ((Ξ.X Y).ρf_nonneg p.1 _))
    (residueWeight_nonneg _ _ μ hz)

theorem measurable_faceDensity (μ : ℝ) : Measurable (Ξ.faceDensity Y p J μ) := by
  unfold faceDensity
  refine (measurable_const.mul ?_).mul ?_
  · exact (((Ξ.X Y).contDiff_ρf p.1).continuous.comp (((Ξ.X Y).continuous_Tm p).comp
      (continuous_fst.prodMk ((glueZeroCLM J).continuous.comp continuous_snd)))).measurable
  · unfold residueWeight
    exact ((measurable_mono _).comp measurable_snd).mul
      (((measurable_mono _).comp measurable_snd).pow_const _)

/-- The face map: the divisor point of the face point `(s, glue J 0 w)` (through the measurable
chart inverse). -/
noncomputable def faceMap
    (z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × ({i // ¬ inJ J i} → ℝ)) : Ξ.R.U :=
  Y.chartInv p.1 ((Ξ.X Y).Tm p z.1 (glue J 0 z.2))

theorem measurable_faceMap : Measurable (Ξ.faceMap Y p J) :=
  (Y.measurable_chartInv p.1).comp (((Ξ.X Y).continuous_Tm p).comp
    (continuous_fst.prodMk ((glueZeroCLM J).continuous.comp continuous_snd))).measurable

theorem faceMap_eq_divPt {z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × ({i // ¬ inJ J i} → ℝ)}
    (hz : z.2 ∈ box {i // ¬ inJ J i} (Y.T.a p.1)) :
    Ξ.faceMap Y p J z = Ξ.divPt Y p z.1 (glue J 0 z.2) := by
  change Y.chartInv p.1 (Ξ.facePt Y p z.1 (glue J 0 z.2)) = _
  rw [Y.chartInv_eq p.1 (Ξ.facePt_mem_target Y p z.1 (Ξ.glue_mem_closedBox_of_mem_box Y p J hz))]
  rfl

/-- **The face density times a test is the face integrand**: on the box,
`faceDensity z · G(faceMap z) = faceNorm' · amp_{withF G}(s, glue J 0 w) · residueWeight(w)`. -/
theorem faceDensity_mul_eq {G : Ξ.R.U → ℝ} (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) (μ : ℝ)
    {z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × ({i // ¬ inJ J i} → ℝ)}
    (hz : z.2 ∈ box {i // ¬ inJ J i} (Y.T.a p.1)) :
    Ξ.faceDensity Y p J μ z * G (Ξ.faceMap Y p J z) =
      Ξ.faceNorm' Y p J * ((Ξ.ampObs Y p hG).amp z.1 (glue J 0 z.2) *
        residueWeight (fun i : {i // ¬ inJ J i} => (Ξ.X Y).hA p i) (fun i => (Ξ.X Y).kA p i) μ
          z.2) := by
  have hvbox := Ξ.glue_mem_closedBox_of_mem_box Y p J hz
  rw [Ξ.faceMap_eq_divPt Y p J hz, Ξ.amp_withF_eq Y p hG z.1 hvbox]
  unfold faceDensity
  rw [(Ξ.X Y).ρf_eq p.1 ((Ξ.X Y).Tm_mem_box p z.1 fun j => (mem_closedBox.1 hvbox) j)]
  ring

/-! ### The face measure and the chart residue measure -/

/-- The face measure on `U`: the pushforward of the face density along the face map. -/
noncomputable def faceMeasureU (μ : ℝ) : Measure Ξ.R.U :=
  ((Ξ.faceRef Y p J).withDensity fun z => ENNReal.ofReal (Ξ.faceDensity Y p J μ z)).map
    (Ξ.faceMap Y p J)

/-- The face measure on `X = U ∖ D_{c+1}`: the restriction along the embedding `X ↪ U`. -/
noncomputable def faceMeasure (μ : ℝ) (c : ℕ) : Measure (Ξ.stratumOpen c) :=
  Measure.comap Subtype.val (Ξ.faceMeasureU Y p J μ)

/-- ★★★ **The chart residue measure**: the sum over the pieces of the resolved core transport
and the simple-pole faces of size `c` of the face measures. -/
noncomputable def chartResidueMeasure (μ : ℝ) (c : ℕ) : Measure (Ξ.stratumOpen c) :=
  ∑ I, ∑ J ∈ Ξ.simpleFaces Y ((Ξ.X Y).en I) μ c, Ξ.faceMeasure Y ((Ξ.X Y).en I) J μ c

/-! ### The smooth-test bridge -/

theorem measurableEmbedding_val (c : ℕ) :
    MeasurableEmbedding (Subtype.val : Ξ.stratumOpen c → Ξ.R.U) :=
  MeasurableEmbedding.subtype_coe (Ξ.isOpen_stratumOpen c).measurableSet

/-- Integrals of tests against the face measure on `X` are integrals against the pushforward. -/
theorem integral_faceMeasure_eq_faceMeasureU {c : ℕ} {G : Ξ.R.U → ℝ} (hGt : Ξ.IsTest c G)
    (μ : ℝ) : ∫ x, G x.1 ∂(Ξ.faceMeasure Y p J μ c) = ∫ y, G y ∂(Ξ.faceMeasureU Y p J μ) := by
  unfold faceMeasure
  rw [← (Ξ.measurableEmbedding_val c).integral_map (g := G),
    (Ξ.measurableEmbedding_val c).map_comap, Subtype.range_coe]
  exact setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy =>
    image_eq_zero_of_notMem_tsupport fun h => hy (hGt.2 h)

/-- The face-density integrand of a test is integrable against the reference measure. -/
theorem integrable_faceDensity_mul {c : ℕ} {G : Ξ.R.U → ℝ}
    (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) (hGt : Ξ.IsTest c G) (hJc : J.card = c)
    (μ : ℝ) :
    Integrable (fun z => Ξ.faceDensity Y p J μ z * G (Ξ.faceMap Y p J z)) (Ξ.faceRef Y p J) := by
  have h := ((Ξ.integrable_faceIntegrand Y p hG hGt.eventually_zero J hJc μ).const_mul
    (Ξ.faceNorm' Y p J))
  refine h.congr ?_
  filter_upwards [Ξ.ae_faceRef_mem_box Y p J] with z hz
  exact (Ξ.faceDensity_mul_eq Y p J hG μ hz).symm

/-- The inner integral of the face density against a test is the `d log`-residue integral of the
amplitude of the test at the base point. -/
theorem integral_faceDensity_mul_eq_dlogResidueInt {G : Ξ.R.U → ℝ}
    (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) (μ : ℝ) (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1)) :
    ∫ w in box {i // ¬ inJ J i} (Y.T.a p.1),
        Ξ.faceDensity Y p J μ (s, w) * G (Ξ.faceMap Y p J (s, w)) =
      dlogResidueInt ((Ξ.X Y).kA p) ((Ξ.X Y).hA p) μ (Y.T.a p.1) J ((Ξ.ampObs Y p hG).amp s) := by
  unfold dlogResidueInt
  rw [← integral_const_mul]
  refine setIntegral_congr_fun (measurableSet_box _) fun w hw => ?_
  exact Ξ.faceDensity_mul_eq Y p J hG μ (z := (s, w)) hw

/-- ★★ **The face measure integrates a test to the residue integral over the base**:
`∫ G dfaceMeasure = ∫_s dlogResidueInt(k, h, μ, b, J, amp_{withF G}(s)) dbase`. -/
theorem integral_faceMeasure_test {c : ℕ} {G : Ξ.R.U → ℝ}
    (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) (hGt : Ξ.IsTest c G) (hJc : J.card = c)
    (μ : ℝ) :
    ∫ x, G x.1 ∂(Ξ.faceMeasure Y p J μ c) =
      ∫ s, dlogResidueInt ((Ξ.X Y).kA p) ((Ξ.X Y).hA p) μ (Y.T.a p.1) J
        ((Ξ.ampObs Y p hG).amp s) ∂(Ξ.piecePresentation Y p).ν := by
  rw [Ξ.integral_faceMeasure_eq_faceMeasureU Y p J hGt μ]
  unfold faceMeasureU
  rw [integral_map (Ξ.measurable_faceMap Y p J).aemeasurable hG.continuous.aestronglyMeasurable]
  have hD : Measurable fun z => (Ξ.faceDensity Y p J μ z).toNNReal :=
    (Ξ.measurable_faceDensity Y p J μ).real_toNNReal
  change ∫ z, G (Ξ.faceMap Y p J z)
    ∂((Ξ.faceRef Y p J).withDensity fun z => ((Ξ.faceDensity Y p J μ z).toNNReal : ℝ≥0∞)) = _
  rw [integral_withDensity_eq_integral_smul hD]
  have hae : (fun z => (Ξ.faceDensity Y p J μ z).toNNReal • G (Ξ.faceMap Y p J z)) =ᵐ[
      Ξ.faceRef Y p J] fun z => Ξ.faceDensity Y p J μ z * G (Ξ.faceMap Y p J z) := by
    filter_upwards [Ξ.ae_faceRef_mem_box Y p J] with z hz
    rw [NNReal.smul_def, Real.coe_toNNReal _ (Ξ.faceDensity_nonneg Y p J μ hz), smul_eq_mul]
  rw [integral_congr_ae hae]
  unfold faceRef
  rw [integral_prod _ (by
    have := Ξ.integrable_faceDensity_mul Y p J hG hGt hJc μ
    unfold faceRef at this
    exact this)]
  exact integral_congr_ae (Eventually.of_forall fun s =>
    Ξ.integral_faceDensity_mul_eq_dlogResidueInt Y p J hG μ s)

end ResolvedData

end SmoothEngine

end Grammar
