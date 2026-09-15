/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothChartResidueMeasure

/-!
# The chart residue measure is the weighted residue measure

Units 4 and 6 of the chart-pushforward identity (consult #135). Tests are integrable against the
face measures (`integrable_faceMeasure_test`), the face measures are finite on compact subsets of
`X` (`faceMeasure_lt_top_of_isCompact`: a cutoff equal to `1` on the compact dominates the
indicator, and the face-density integrand of a test is integrable by the collar), so the chart
residue measure is finite on compacts, locally finite, and REGULAR on the σ-compact metrisable
`X`. Its smooth-test integrals are the residue sums of CDLIII
(`integral_chartResidueMeasure_test`), hence `residueConst · ∫ G dchart = 𝒯^U_{μ,c−1}[G]`
(`residueConst_mul_integral_chartResidueMeasure`). Uniqueness of the stratum measure by smooth
tests (CDLVI) then gives the ★★★ identities
`ν^μ_c = Γ(μ)/(c−1)! · chartResidueMeasure` (`stratumMeasure_eq_smul_chartResidueMeasure`) and
`chartResidueMeasure = ℛ^μ_c` (`chartResidueMeasure_eq_residueMeasure`): the intrinsically defined
weighted residue measure IS the finite sum of the pushforwards of the multiplicity-normalised
simple-face densities `∏_{j∈J}(2k_j)⁻¹ · ρ · ∏_{i∉J} w_i^{h_i}(∏_{i∉J} w_i^{2k_i})^{−μ}` in any
resolved chart transport — Definition B made a theorem. Zero `sorry`/`axiom`.
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

/-! ### Integrability of tests -/

/-- Tests are integrable against the face measure on `X`. -/
theorem integrable_faceMeasure_test {c : ℕ} {G : Ξ.R.U → ℝ}
    (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) (hGt : Ξ.IsTest c G) (hJc : J.card = c)
    (μ : ℝ) : Integrable (fun x : Ξ.stratumOpen c => G x.1) (Ξ.faceMeasure Y p J μ c) := by
  have hemb := Ξ.measurableEmbedding_val c
  unfold faceMeasure
  have key : Integrable G ((Ξ.faceMeasureU Y p J μ).restrict (Ξ.stratumOpen c)) := by
    refine (integrableOn_iff_integrable_of_support_subset
      ((subset_tsupport G).trans hGt.2)).2 ?_
    unfold faceMeasureU
    rw [integrable_map_measure hG.continuous.aestronglyMeasurable
      (Ξ.measurable_faceMap Y p J).aemeasurable]
    have hD : Measurable fun z => (Ξ.faceDensity Y p J μ z).toNNReal :=
      (Ξ.measurable_faceDensity Y p J μ).real_toNNReal
    change Integrable (G ∘ Ξ.faceMap Y p J)
      ((Ξ.faceRef Y p J).withDensity fun z => ((Ξ.faceDensity Y p J μ z).toNNReal : ℝ≥0∞))
    rw [integrable_withDensity_iff_integrable_smul hD]
    refine (Ξ.integrable_faceDensity_mul Y p J hG hGt hJc μ).congr ?_
    filter_upwards [Ξ.ae_faceRef_mem_box Y p J] with z hz
    simp only [Function.comp_apply, NNReal.smul_def, smul_eq_mul,
      Real.coe_toNNReal _ (Ξ.faceDensity_nonneg Y p J μ hz)]
  have key' : Integrable G (Measure.map (Subtype.val : Ξ.stratumOpen c → Ξ.R.U)
      (Measure.comap (Subtype.val : Ξ.stratumOpen c → Ξ.R.U) (Ξ.faceMeasureU Y p J μ))) := by
    rw [hemb.map_comap, Subtype.range_coe]
    exact key
  exact hemb.integrable_map_iff.1 key'

/-! ### Finiteness on compacts -/

/-- ★★ **Face measures are finite on compact subsets of `X`**: a cutoff equal to `1` on the compact
dominates the indicator, and the face-density integrand of the cutoff is integrable. -/
theorem faceMeasure_lt_top_of_isCompact {c : ℕ} (hJc : J.card = c) (μ : ℝ)
    {C : Set (Ξ.stratumOpen c)} (hC : IsCompact C) : Ξ.faceMeasure Y p J μ c C < ⊤ := by
  have hCU : IsCompact (Subtype.val '' C) := hC.image continuous_subtype_val
  have hCX : Subtype.val '' C ⊆ Ξ.stratumOpen c := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  obtain ⟨χ, hχ, hχt, hχ1, hχ01⟩ := Ξ.exists_cutoff c hCU hCX
  have hemb := Ξ.measurableEmbedding_val c
  unfold faceMeasure
  rw [hemb.comap_apply]
  unfold faceMeasureU
  rw [Measure.map_apply (Ξ.measurable_faceMap Y p J) hCU.isClosed.measurableSet,
    withDensity_apply _ ((Ξ.measurable_faceMap Y p J) hCU.isClosed.measurableSet)]
  have hint := Ξ.integrable_faceDensity_mul Y p J hχ hχt hJc μ
  have hnn : 0 ≤ᵐ[Ξ.faceRef Y p J] fun z => Ξ.faceDensity Y p J μ z * χ (Ξ.faceMap Y p J z) := by
    filter_upwards [Ξ.ae_faceRef_mem_box Y p J] with z hz
    exact mul_nonneg (Ξ.faceDensity_nonneg Y p J μ hz) (hχ01 _).1
  calc ∫⁻ z in Ξ.faceMap Y p J ⁻¹' (Subtype.val '' C), ENNReal.ofReal (Ξ.faceDensity Y p J μ z)
        ∂(Ξ.faceRef Y p J)
      ≤ ∫⁻ z, ENNReal.ofReal (Ξ.faceDensity Y p J μ z * χ (Ξ.faceMap Y p J z))
        ∂(Ξ.faceRef Y p J) := by
        rw [← lintegral_indicator ((Ξ.measurable_faceMap Y p J) hCU.isClosed.measurableSet)]
        refine lintegral_mono_ae ?_
        filter_upwards [Ξ.ae_faceRef_mem_box Y p J] with z hz
        by_cases hzC : z ∈ Ξ.faceMap Y p J ⁻¹' (Subtype.val '' C)
        · rw [indicator_of_mem hzC, hχ1 _ hzC, mul_one]
        · rw [indicator_of_notMem hzC]
          exact bot_le
    _ = ENNReal.ofReal (∫ z, Ξ.faceDensity Y p J μ z * χ (Ξ.faceMap Y p J z) ∂(Ξ.faceRef Y p J)) :=
        (ofReal_integral_eq_lintegral_ofReal hint hnn).symm
    _ < ⊤ := ENNReal.ofReal_lt_top

/-- The chart residue measure is finite on compact subsets of `X`. -/
theorem chartResidueMeasure_lt_top_of_isCompact (μ : ℝ) (c : ℕ) {C : Set (Ξ.stratumOpen c)}
    (hC : IsCompact C) : Ξ.chartResidueMeasure Y μ c C < ⊤ := by
  unfold chartResidueMeasure
  rw [Measure.finsetSum_apply]
  refine ENNReal.sum_lt_top.2 fun I _ => ?_
  rw [Measure.finsetSum_apply]
  refine ENNReal.sum_lt_top.2 fun J hJ => ?_
  exact Ξ.faceMeasure_lt_top_of_isCompact Y _ J (Finset.mem_filter.1 hJ).2.1 μ hC

instance (μ : ℝ) (c : ℕ) : IsFiniteMeasureOnCompacts (Ξ.chartResidueMeasure Y μ c) :=
  ⟨fun _ hC => Ξ.chartResidueMeasure_lt_top_of_isCompact Y μ c hC⟩

/-- ★★ The chart residue measure is a regular Borel measure on `X`. -/
instance (μ : ℝ) (c : ℕ) : (Ξ.chartResidueMeasure Y μ c).Regular :=
  Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _

/-! ### The identity -/

/-- ★★★ **The chart residue measure integrates a test to the residue sum** of CDLIII:
`∫ G dchartResidueMeasure = Σ_I ∫_s pieceResidueSum_I(s) dbase_I`. -/
theorem integral_chartResidueMeasure_test {c : ℕ} {G : Ξ.R.U → ℝ}
    (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) (hGt : Ξ.IsTest c G) (μ : ℝ) :
    ∫ x, G x.1 ∂(Ξ.chartResidueMeasure Y μ c) =
      ∑ I, ∫ s, (Ξ.withF G hG).pieceResidueSum Y I s μ c ∂((Ξ.decomp Y).chart I).ν := by
  unfold chartResidueMeasure
  rw [integral_finsetSum_measure fun I _ => integrable_finsetSum_measure.2 fun J hJ =>
    Ξ.integrable_faceMeasure_test Y _ J hG hGt (Finset.mem_filter.1 hJ).2.1 μ]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [integral_finsetSum_measure fun J hJ =>
    Ξ.integrable_faceMeasure_test Y _ J hG hGt (Finset.mem_filter.1 hJ).2.1 μ]
  have hJ : ∀ J ∈ Ξ.simpleFaces Y ((Ξ.X Y).en I) μ c,
      ∫ x, G x.1 ∂(Ξ.faceMeasure Y ((Ξ.X Y).en I) J μ c) =
        ∫ s, dlogResidueInt ((Ξ.X Y).kA ((Ξ.X Y).en I)) ((Ξ.X Y).hA ((Ξ.X Y).en I)) μ
          (Y.T.a ((Ξ.X Y).en I).1) J ((Ξ.ampObs Y ((Ξ.X Y).en I) hG).amp s)
          ∂(Ξ.piecePresentation Y ((Ξ.X Y).en I)).ν := fun J hJ =>
    Ξ.integral_faceMeasure_test Y _ J hG hGt (Finset.mem_filter.1 hJ).2.1 μ
  rw [Finset.sum_congr rfl hJ, ← integral_finsetSum]
  · rfl
  · intro J hJ
    have h := (Ξ.integrable_faceDensity_mul Y _ J hG hGt (Finset.mem_filter.1 hJ).2.1 μ)
    unfold faceRef at h
    have h' := h.integral_prod_left
    refine h'.congr (Eventually.of_forall fun s => ?_)
    exact Ξ.integral_faceDensity_mul_eq_dlogResidueInt Y _ J hG μ s

/-- ★★★ **The chart residue measure against a test is the coefficient functional** up to the
residue constant: `Γ(μ)/(c−1)! · ∫ G dchartResidueMeasure = 𝒯^U_{μ,c−1}[G]`. -/
theorem residueConst_mul_integral_chartResidueMeasure {μ : ℝ} {c : ℕ} (hc : 1 ≤ c)
    (hzero : Ξ.ZeroOrder μ c) {G : Ξ.R.U → ℝ} (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G)
    (hGt : Ξ.IsTest c G) :
    residueConst μ c * ∫ x, G x.1 ∂(Ξ.chartResidueMeasure Y μ c) = Ξ.T Y μ c G hG := by
  rw [Ξ.integral_chartResidueMeasure_test Y hG hGt μ]
  unfold T
  rw [(Ξ.withF G hG).coeff_eq_residueSum Y hc hzero hGt.eventually_zero]
  rfl

/-- ★★★ **The stratum measure is the normalised chart residue measure**:
`ν^μ_c = Γ(μ)/(c−1)! · chartResidueMeasure`. -/
theorem stratumMeasure_eq_smul_chartResidueMeasure {μ : ℝ} (hμ : 0 < μ) {c : ℕ} (hc : 1 ≤ c)
    (hzero : Ξ.ZeroOrder μ c) :
    Ξ.stratumMeasure Y hc hzero =
      ENNReal.ofReal (residueConst μ c) • Ξ.chartResidueMeasure Y μ c := by
  have hreg : (ENNReal.ofReal (residueConst μ c) • Ξ.chartResidueMeasure Y μ c).Regular :=
    Measure.Regular.smul ENNReal.ofReal_ne_top
  symm
  refine Ξ.eq_stratumMeasure_of_tests Y hc hzero _ fun G hG hGt => ?_
  rw [integral_smul_measure, ENNReal.toReal_ofReal (residueConst_pos hμ c).le, smul_eq_mul]
  exact Ξ.residueConst_mul_integral_chartResidueMeasure Y hc hzero hG hGt

/-- ★★★ **THE CHART RESIDUE MEASURE IS THE WEIGHTED RESIDUE MEASURE**: on `X = U ∖ D_{c+1}`,
`ℛ^μ_c` is exactly the finite sum over the pieces of the resolved chart transport and their
simple-pole faces of the pushforwards of the multiplicity-normalised face densities. -/
theorem chartResidueMeasure_eq_residueMeasure {μ : ℝ} (hμ : 0 < μ) {c : ℕ} (hc : 1 ≤ c)
    (hzero : Ξ.ZeroOrder μ c) :
    Ξ.chartResidueMeasure Y μ c = Ξ.residueMeasure Y hc hzero := by
  unfold residueMeasure
  rw [Ξ.stratumMeasure_eq_smul_chartResidueMeasure Y hμ hc hzero, smul_smul,
    ← ENNReal.ofReal_mul (div_nonneg (Nat.cast_nonneg _) (Real.Gamma_pos_of_pos hμ).le)]
  have h1 : ((c - 1).factorial : ℝ) / Real.Gamma μ * residueConst μ c = 1 := by
    unfold residueConst
    have hΓ := (Real.Gamma_pos_of_pos hμ).ne'
    have hfac : ((c - 1).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_pos _).ne'
    field_simp
  rw [h1, ENNReal.ofReal_one, one_smul]

/-- The chart residue measure is carried by the exact stratum (inherited from `ℛ`). -/
theorem chartResidueMeasure_compl_exactStratum {μ : ℝ} (hμ : 0 < μ) {c : ℕ} (hc : 1 ≤ c)
    (hzero : Ξ.ZeroOrder μ c) :
    Ξ.chartResidueMeasure Y μ c (Subtype.val ⁻¹' Ξ.exactStratum μ c)ᶜ = 0 := by
  rw [Ξ.chartResidueMeasure_eq_residueMeasure Y hμ hc hzero]
  exact Ξ.residueMeasure_compl_exactStratum Y hc hzero

/-- The chart residue measure does not depend on the transport (inherited from `ν`). -/
theorem chartResidueMeasure_eq_of_transports (Y' : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)
    {μ : ℝ} (hμ : 0 < μ) {c : ℕ} (hc : 1 ≤ c) (hzero : Ξ.ZeroOrder μ c) :
    Ξ.chartResidueMeasure Y μ c = Ξ.chartResidueMeasure Y' μ c := by
  rw [Ξ.chartResidueMeasure_eq_residueMeasure Y hμ hc hzero,
    Ξ.chartResidueMeasure_eq_residueMeasure Y' hμ hc hzero]
  unfold residueMeasure
  rw [Ξ.stratumMeasure_eq_of_transports Y Y' hc hzero]

end ResolvedData

end SmoothEngine

end Grammar
