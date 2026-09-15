/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothChartResidueIdentity
import Grammar.FluctuationLipschitz

/-!
# The empirical stratum measure

The population stratum measure `ν^μ_c` (zero order) is, on `X = U ∖ D_{c+1}`, the sum over the
pieces of a resolved chart transport and their simple-pole faces of the pushforwards of the face
densities (`SmoothChartResidueIdentity`). With the empirical phase
`e^{−N K∘π + √N √(K∘π) ψ}` the radial Gamma factor `Γ(μ)` of every face is replaced by the
fluctuation function `S_μ(ψ̂)` of the **branch trace** `ψ̂` of the root field
`ψ = √n (K − K_n)/√K` on the normal side of the face carried by the piece. This module defines the
resulting **empirical stratum measure**

`ν^μ_c(ξ) = Γ(μ)/(c−1)! · Σ_{pieces, simple faces} (faceDensity · S_μ(trace ξ)/Γ(μ))_*`

for a `RootField` `ξ` (a function on `U` with a continuous branch representative on the closed box
of every piece) and proves its basic properties: it is the population measure at the zero field
(`empiricalStratumMeasure_zero`), it depends on the field only through its branch traces on the
faces (`empiricalChartMeasure_congr`), it is dominated by a constant multiple of the population
measure, hence finite on compact subsets of `X` and regular (instances), and its test integrals
are locally Lipschitz in the sup norm of the trace
(`abs_integral_empiricalStratumMeasure_sub_le`). The asymptotic theorem identifying it as the
leading empirical coefficient is a later unit. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology Finset
open scoped ENNReal ContDiff Manifold
open Monomialize.VolumeScaling Monomialize.Transport Monomialize.Manifold
open Grammar.NormalCrossing Grammar.NormalCrossing.EvenChartBoxDepth

namespace Grammar

namespace SmoothEngine

namespace ResolvedData

variable {d : ℕ} (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)

/-! ### Root fields -/

/-- A **root field**: a function `ψ` on `U` (the pull-back of Watanabe's `√n(K − K_n)/√K`)
together with, for every piece, a continuous branch representative on `Base × ℝ^{da}` agreeing
with `ψ ∘ divPt` on the open box. Only the representatives' values on the closed boxes enter the
empirical stratum measure. -/
structure RootField where
  /-- the field on `U` -/
  ψ : Ξ.R.U → ℝ
  /-- the branch representative of the piece -/
  loc : ∀ p : (Ξ.X Y).PIdx,
    Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × (Fin ((Ξ.X Y).da p) → ℝ) → ℝ
  loc_cont : ∀ p, Continuous (loc p)
  loc_eq : ∀ (p : (Ξ.X Y).PIdx)
    (z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × (Fin ((Ξ.X Y).da p) → ℝ)),
    z.2 ∈ SmoothEngine.box (Fin ((Ξ.X Y).da p)) (Y.T.a p.1) → loc p z = ψ (Ξ.divPt Y p z.1 z.2)

namespace RootField

/-- The zero field. -/
def zero : Ξ.RootField Y where
  ψ _ := 0
  loc _ _ := 0
  loc_cont _ := continuous_const
  loc_eq _ _ _ := rfl

variable {Ξ Y} (ξ : Ξ.RootField Y)

/-- A root field is bounded on the closed boxes of all pieces. -/
theorem exists_bound : ∃ M : ℝ, 0 ≤ M ∧ ∀ (p : (Ξ.X Y).PIdx)
    (z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × (Fin ((Ξ.X Y).da p) → ℝ)),
    z.2 ∈ closedBox ((Ξ.X Y).da p) (Y.T.a p.1) → |ξ.loc p z| ≤ M := by
  have h : ∀ p : (Ξ.X Y).PIdx, ∃ M : ℝ, ∀ z ∈ (univ : Set (Base ((Ξ.X Y).act p.1) (Y.T.a p.1))) ×ˢ
      closedBox ((Ξ.X Y).da p) (Y.T.a p.1), ‖ξ.loc p z‖ ≤ M := fun p =>
    (isCompact_univ.prod (isCompact_closedBox _)).exists_bound_of_continuousOn
      (ξ.loc_cont p).continuousOn
  choose M hM using h
  refine ⟨∑ p, |M p|, Finset.sum_nonneg fun _ _ => abs_nonneg _, fun p z hz => ?_⟩
  calc |ξ.loc p z| ≤ M p := by
        have := hM p z ⟨mem_univ _, hz⟩
        simpa [Real.norm_eq_abs] using this
    _ ≤ |M p| := le_abs_self _
    _ ≤ ∑ q, |M q| :=
        Finset.single_le_sum (f := fun q => |M q|) (fun _ _ => abs_nonneg _) (Finset.mem_univ p)

end RootField

/-! ### The empirical face measures -/

section Face

variable (p : (Ξ.X Y).PIdx) (J : Finset (Fin ((Ξ.X Y).da p))) (ξ : Ξ.RootField Y)

/-- The branch trace of the field at the face point `(s, glue J 0 w)`. -/
noncomputable def faceTrace
    (z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × ({i // ¬ inJ J i} → ℝ)) : ℝ :=
  ξ.loc p (z.1, glue J 0 z.2)

theorem continuous_faceTrace : Continuous (Ξ.faceTrace Y p J ξ) :=
  (ξ.loc_cont p).comp (continuous_fst.prodMk ((glueZeroCLM J).continuous.comp continuous_snd))

/-- The empirical face density: the face density times the fluctuation density of the trace. -/
noncomputable def empFaceDensity (μ : ℝ)
    (z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × ({i // ¬ inJ J i} → ℝ)) : ℝ :=
  Ξ.faceDensity Y p J μ z * fluctDensity μ (Ξ.faceTrace Y p J ξ z)

theorem empFaceDensity_nonneg {μ : ℝ} (hμ : 0 < μ)
    {z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × ({i // ¬ inJ J i} → ℝ)}
    (hz : z.2 ∈ box {i // ¬ inJ J i} (Y.T.a p.1)) : 0 ≤ Ξ.empFaceDensity Y p J ξ μ z :=
  mul_nonneg (Ξ.faceDensity_nonneg Y p J μ hz) (fluctDensity_pos hμ _).le

theorem measurable_empFaceDensity {μ : ℝ} (hμ : 0 < μ) :
    Measurable (Ξ.empFaceDensity Y p J ξ μ) :=
  (Ξ.measurable_faceDensity Y p J μ).mul
    ((continuous_fluctDensity hμ).comp (Ξ.continuous_faceTrace Y p J ξ)).measurable

/-- The empirical face measure on `U`: the pushforward of the empirical face density along the
face map. -/
noncomputable def empFaceMeasureU (μ : ℝ) : Measure Ξ.R.U :=
  ((Ξ.faceRef Y p J).withDensity fun z => ENNReal.ofReal (Ξ.empFaceDensity Y p J ξ μ z)).map
    (Ξ.faceMap Y p J)

/-- The empirical face measure on `X = U ∖ D_{c+1}`. -/
noncomputable def empFaceMeasure (μ : ℝ) (c : ℕ) : Measure (Ξ.stratumOpen c) :=
  Measure.comap Subtype.val (Ξ.empFaceMeasureU Y p J ξ μ)

/-- At the zero field the empirical face measure is the face measure. -/
theorem empFaceMeasureU_zero {μ : ℝ} (hμ : 0 < μ) :
    Ξ.empFaceMeasureU Y p J (RootField.zero Ξ Y) μ = Ξ.faceMeasureU Y p J μ := by
  unfold empFaceMeasureU faceMeasureU
  congr 1
  refine withDensity_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [empFaceDensity, faceTrace, RootField.zero, fluctDensity_zero hμ, mul_one]

/-- The empirical face measure depends on the field only through its branch trace on the face. -/
theorem empFaceMeasureU_congr {ξ' : Ξ.RootField Y} (μ : ℝ)
    (h : ∀ z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × ({i // ¬ inJ J i} → ℝ),
      z.2 ∈ box {i // ¬ inJ J i} (Y.T.a p.1) → Ξ.faceTrace Y p J ξ z = Ξ.faceTrace Y p J ξ' z) :
    Ξ.empFaceMeasureU Y p J ξ μ = Ξ.empFaceMeasureU Y p J ξ' μ := by
  unfold empFaceMeasureU
  congr 1
  refine withDensity_congr_ae ?_
  filter_upwards [Ξ.ae_faceRef_mem_box Y p J] with z hz
  simp only [empFaceDensity, h z hz]

/-- **Domination**: with `|trace| ≤ M` on the face, the empirical face measure is at most
`fluctDensity μ M` times the face measure. -/
theorem empFaceMeasureU_le {μ : ℝ} (hμ : 0 < μ) {M : ℝ}
    (hM : ∀ z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × ({i // ¬ inJ J i} → ℝ),
      z.2 ∈ box {i // ¬ inJ J i} (Y.T.a p.1) → |Ξ.faceTrace Y p J ξ z| ≤ M) :
    Ξ.empFaceMeasureU Y p J ξ μ ≤ ENNReal.ofReal (fluctDensity μ M) • Ξ.faceMeasureU Y p J μ := by
  unfold empFaceMeasureU faceMeasureU
  rw [← Measure.map_smul, ← withDensity_smul _ (Ξ.measurable_faceDensity Y p J μ).ennreal_ofReal]
  refine Measure.map_mono (withDensity_mono ?_) (Ξ.measurable_faceMap Y p J)
  filter_upwards [Ξ.ae_faceRef_mem_box Y p J] with z hz
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [empFaceDensity, ENNReal.ofReal_mul (Ξ.faceDensity_nonneg Y p J μ hz), mul_comm]
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal (fluctDensity_le_of_abs_le hμ (hM z hz))) le_rfl

theorem empFaceMeasure_le {μ : ℝ} (hμ : 0 < μ) (c : ℕ) {M : ℝ}
    (hM : ∀ z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × ({i // ¬ inJ J i} → ℝ),
      z.2 ∈ box {i // ¬ inJ J i} (Y.T.a p.1) → |Ξ.faceTrace Y p J ξ z| ≤ M) :
    Ξ.empFaceMeasure Y p J ξ μ c ≤
      ENNReal.ofReal (fluctDensity μ M) • Ξ.faceMeasure Y p J μ c := by
  refine Measure.le_iff'.2 fun s => ?_
  unfold empFaceMeasure faceMeasure
  rw [Measure.smul_apply, (Ξ.measurableEmbedding_val c).comap_apply,
    (Ξ.measurableEmbedding_val c).comap_apply, ← Measure.smul_apply]
  exact Ξ.empFaceMeasureU_le Y p J ξ hμ hM _

/-- Trace bounds on a face follow from bounds of the representative on the closed box. -/
theorem faceTrace_abs_le {M : ℝ}
    (hM : ∀ z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × (Fin ((Ξ.X Y).da p) → ℝ),
      z.2 ∈ closedBox ((Ξ.X Y).da p) (Y.T.a p.1) → |ξ.loc p z| ≤ M)
    {z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × ({i // ¬ inJ J i} → ℝ)}
    (hz : z.2 ∈ box {i // ¬ inJ J i} (Y.T.a p.1)) : |Ξ.faceTrace Y p J ξ z| ≤ M :=
  hM (z.1, glue J 0 z.2) (Ξ.glue_mem_closedBox_of_mem_box Y p J hz)

theorem empFaceMeasure_lt_top_of_isCompact {μ : ℝ} (hμ : 0 < μ) {c : ℕ} (hJc : J.card = c)
    {C : Set (Ξ.stratumOpen c)} (hC : IsCompact C) : Ξ.empFaceMeasure Y p J ξ μ c C < ⊤ := by
  obtain ⟨M, -, hM⟩ := ξ.exists_bound
  refine lt_of_le_of_lt (Ξ.empFaceMeasure_le Y p J ξ hμ c
    (fun z hz => Ξ.faceTrace_abs_le Y p J ξ (hM p) hz) C) ?_
  rw [Measure.smul_apply, smul_eq_mul]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (Ξ.faceMeasure_lt_top_of_isCompact Y p J hJc μ hC)

/-! #### Test integrals against a pushed-forward density -/

/-- Integrals of a continuous function supported in `X` against the restriction to `X` of the
pushforward of a nonnegative density along the face map. -/
theorem integral_comap_map_withDensity {c : ℕ}
    {D : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × ({i // ¬ inJ J i} → ℝ) → ℝ} (hD : Measurable D)
    (hD0 : ∀ᵐ z ∂(Ξ.faceRef Y p J), 0 ≤ D z) {G : Ξ.R.U → ℝ} (hGc : Continuous G)
    (hGt : tsupport G ⊆ Ξ.stratumOpen c) :
    ∫ x, G x.1 ∂(Measure.comap (Subtype.val : Ξ.stratumOpen c → Ξ.R.U)
      (((Ξ.faceRef Y p J).withDensity fun z => ENNReal.ofReal (D z)).map (Ξ.faceMap Y p J))) =
      ∫ z, D z * G (Ξ.faceMap Y p J z) ∂(Ξ.faceRef Y p J) := by
  have hemb := Ξ.measurableEmbedding_val c
  rw [← hemb.integral_map (g := G), hemb.map_comap, Subtype.range_coe,
    setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy =>
      image_eq_zero_of_notMem_tsupport fun h => hy (hGt h),
    integral_map (Ξ.measurable_faceMap Y p J).aemeasurable hGc.aestronglyMeasurable]
  have hD' : Measurable fun z => (D z).toNNReal := hD.real_toNNReal
  change ∫ z, G (Ξ.faceMap Y p J z)
    ∂((Ξ.faceRef Y p J).withDensity fun z => ((D z).toNNReal : ℝ≥0∞)) = _
  rw [integral_withDensity_eq_integral_smul hD']
  refine integral_congr_ae ?_
  filter_upwards [hD0] with z hz
  rw [NNReal.smul_def, Real.coe_toNNReal _ hz, smul_eq_mul]

theorem integral_empFaceMeasure_eq {μ : ℝ} (hμ : 0 < μ) {c : ℕ} {G : Ξ.R.U → ℝ}
    (hGc : Continuous G) (hGt : tsupport G ⊆ Ξ.stratumOpen c) :
    ∫ x, G x.1 ∂(Ξ.empFaceMeasure Y p J ξ μ c) =
      ∫ z, Ξ.empFaceDensity Y p J ξ μ z * G (Ξ.faceMap Y p J z) ∂(Ξ.faceRef Y p J) :=
  Ξ.integral_comap_map_withDensity Y p J (Ξ.measurable_empFaceDensity Y p J ξ hμ)
    ((Ξ.ae_faceRef_mem_box Y p J).mono fun _ hz => Ξ.empFaceDensity_nonneg Y p J ξ hμ hz) hGc hGt

theorem integral_faceMeasure_eq {c : ℕ} (μ : ℝ) {G : Ξ.R.U → ℝ} (hGc : Continuous G)
    (hGt : tsupport G ⊆ Ξ.stratumOpen c) :
    ∫ x, G x.1 ∂(Ξ.faceMeasure Y p J μ c) =
      ∫ z, Ξ.faceDensity Y p J μ z * G (Ξ.faceMap Y p J z) ∂(Ξ.faceRef Y p J) :=
  Ξ.integral_comap_map_withDensity Y p J (Ξ.measurable_faceDensity Y p J μ)
    ((Ξ.ae_faceRef_mem_box Y p J).mono fun _ hz => Ξ.faceDensity_nonneg Y p J μ hz) hGc hGt

/-- **Lipschitz dependence of a face integral on the trace**: with traces bounded by `M` and
`δ`-close on the face, the test integrals differ by at most `fluctLip μ M · δ · ∫ |G| dface`. -/
theorem abs_integral_empFaceMeasure_sub_le {μ : ℝ} (hμ : 0 < μ) {c : ℕ} (hJc : J.card = c)
    {G : Ξ.R.U → ℝ} (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) (hGt : Ξ.IsTest c G)
    {ξ' : Ξ.RootField Y} {M δ : ℝ}
    (hM : ∀ z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × ({i // ¬ inJ J i} → ℝ),
      z.2 ∈ box {i // ¬ inJ J i} (Y.T.a p.1) → |Ξ.faceTrace Y p J ξ z| ≤ M)
    (hM' : ∀ z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × ({i // ¬ inJ J i} → ℝ),
      z.2 ∈ box {i // ¬ inJ J i} (Y.T.a p.1) → |Ξ.faceTrace Y p J ξ' z| ≤ M)
    (hδ : ∀ z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × ({i // ¬ inJ J i} → ℝ),
      z.2 ∈ box {i // ¬ inJ J i} (Y.T.a p.1) →
        |Ξ.faceTrace Y p J ξ z - Ξ.faceTrace Y p J ξ' z| ≤ δ) :
    |(∫ x, G x.1 ∂(Ξ.empFaceMeasure Y p J ξ μ c)) - ∫ x, G x.1 ∂(Ξ.empFaceMeasure Y p J ξ' μ c)| ≤
      fluctLip μ M * δ * ∫ x, |G x.1| ∂(Ξ.faceMeasure Y p J μ c) := by
  have hGts : tsupport G ⊆ Ξ.stratumOpen c := hGt.2
  have habs : tsupport (fun x => |G x|) ⊆ Ξ.stratumOpen c := by
    have hsupp : Function.support (fun x => |G x|) = Function.support G := by
      ext x
      simp [Function.mem_support]
    unfold tsupport
    rw [hsupp]
    exact hGts
  rw [Ξ.integral_empFaceMeasure_eq Y p J ξ hμ hG.continuous hGts,
    Ξ.integral_empFaceMeasure_eq Y p J ξ' hμ hG.continuous hGts,
    Ξ.integral_faceMeasure_eq Y p J μ hG.continuous.abs habs]
  have hint := Ξ.integrable_faceDensity_mul Y p J hG hGt hJc μ
  have hbdd : ∀ (η : Ξ.RootField Y), (∀ z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) ×
      ({i // ¬ inJ J i} → ℝ), z.2 ∈ box {i // ¬ inJ J i} (Y.T.a p.1) →
        |Ξ.faceTrace Y p J η z| ≤ M) →
      Integrable (fun z => Ξ.empFaceDensity Y p J η μ z * G (Ξ.faceMap Y p J z))
        (Ξ.faceRef Y p J) := by
    intro η hη
    have h := hint.bdd_mul (c := fluctDensity μ M)
      ((continuous_fluctDensity hμ).comp (Ξ.continuous_faceTrace Y p J η)).aestronglyMeasurable
      (by
        filter_upwards [Ξ.ae_faceRef_mem_box Y p J] with z hz
        rw [Function.comp_apply, Real.norm_eq_abs, abs_of_pos (fluctDensity_pos hμ _)]
        exact fluctDensity_le_of_abs_le hμ (hη z hz))
    refine h.congr (Eventually.of_forall fun z => ?_)
    simp only [Function.comp_apply, empFaceDensity]
    ring
  rw [← integral_sub (hbdd ξ hM) (hbdd ξ' hM')]
  rw [← integral_const_mul]
  have hRint : Integrable (fun z => fluctLip μ M * δ *
      (Ξ.faceDensity Y p J μ z * |G (Ξ.faceMap Y p J z)|)) (Ξ.faceRef Y p J) := by
    refine (hint.abs.const_mul (fluctLip μ M * δ)).congr ?_
    filter_upwards [Ξ.ae_faceRef_mem_box Y p J] with z hz
    rw [abs_mul, abs_of_nonneg (Ξ.faceDensity_nonneg Y p J μ hz)]
  refine (abs_integral_le_integral_abs).trans (integral_mono_ae ?_ hRint ?_)
  · exact (hbdd ξ hM).sub (hbdd ξ' hM') |>.abs
  filter_upwards [Ξ.ae_faceRef_mem_box Y p J] with z hz
  have hD0 := Ξ.faceDensity_nonneg Y p J μ hz
  calc |Ξ.empFaceDensity Y p J ξ μ z * G (Ξ.faceMap Y p J z) -
        Ξ.empFaceDensity Y p J ξ' μ z * G (Ξ.faceMap Y p J z)|
      = Ξ.faceDensity Y p J μ z * |G (Ξ.faceMap Y p J z)| *
          |fluctDensity μ (Ξ.faceTrace Y p J ξ z) - fluctDensity μ (Ξ.faceTrace Y p J ξ' z)| := by
        unfold empFaceDensity
        rw [show Ξ.faceDensity Y p J μ z * fluctDensity μ (Ξ.faceTrace Y p J ξ z) *
              G (Ξ.faceMap Y p J z) -
            Ξ.faceDensity Y p J μ z * fluctDensity μ (Ξ.faceTrace Y p J ξ' z) *
              G (Ξ.faceMap Y p J z) =
            Ξ.faceDensity Y p J μ z * G (Ξ.faceMap Y p J z) *
              (fluctDensity μ (Ξ.faceTrace Y p J ξ z) -
                fluctDensity μ (Ξ.faceTrace Y p J ξ' z)) by ring,
          abs_mul, abs_mul, abs_of_nonneg hD0]
    _ ≤ Ξ.faceDensity Y p J μ z * |G (Ξ.faceMap Y p J z)| * (fluctLip μ M * δ) := by
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hD0 (abs_nonneg _))
        exact (abs_fluctDensity_sub_le hμ (hM z hz) (hM' z hz)).trans
          (mul_le_mul_of_nonneg_left (hδ z hz)
            (div_nonneg (fluctuation_pos 1 _ M one_pos (by linarith)).le
              (Real.Gamma_pos_of_pos hμ).le))
    _ = fluctLip μ M * δ * (Ξ.faceDensity Y p J μ z * |G (Ξ.faceMap Y p J z)|) := by ring

end Face

/-! ### The empirical chart and stratum measures -/

variable (ξ : Ξ.RootField Y)

/-- The empirical chart measure: the sum over the pieces and simple-pole faces of the empirical
face measures. -/
noncomputable def empiricalChartMeasure (μ : ℝ) (c : ℕ) : Measure (Ξ.stratumOpen c) :=
  ∑ I, ∑ J ∈ Ξ.simpleFaces Y ((Ξ.X Y).en I) μ c, Ξ.empFaceMeasure Y ((Ξ.X Y).en I) J ξ μ c

/-- **The empirical stratum measure** `ν^μ_c(ξ) = Γ(μ)/(c−1)! · empiricalChartMeasure`, equal to
the population stratum measure at the zero field. -/
noncomputable def empiricalStratumMeasure (μ : ℝ) (c : ℕ) : Measure (Ξ.stratumOpen c) :=
  ENNReal.ofReal (residueConst μ c) • Ξ.empiricalChartMeasure Y ξ μ c

theorem empiricalChartMeasure_zero {μ : ℝ} (hμ : 0 < μ) (c : ℕ) :
    Ξ.empiricalChartMeasure Y (RootField.zero Ξ Y) μ c = Ξ.chartResidueMeasure Y μ c := by
  unfold empiricalChartMeasure chartResidueMeasure empFaceMeasure faceMeasure
  simp only [Ξ.empFaceMeasureU_zero Y _ _ hμ]

/-- ★★ **At the zero field the empirical stratum measure is the population stratum measure.** -/
theorem empiricalStratumMeasure_zero {μ : ℝ} (hμ : 0 < μ) {c : ℕ} (hc : 1 ≤ c)
    (hzero : Ξ.ZeroOrder μ c) :
    Ξ.empiricalStratumMeasure Y (RootField.zero Ξ Y) μ c = Ξ.stratumMeasure Y hc hzero := by
  rw [empiricalStratumMeasure, Ξ.empiricalChartMeasure_zero Y hμ c,
    Ξ.stratumMeasure_eq_smul_chartResidueMeasure Y hμ hc hzero]

/-- **Locality**: the empirical measures depend on the field only through the branch
representatives on the closed boxes. -/
theorem empiricalChartMeasure_congr {ξ' : Ξ.RootField Y} (μ : ℝ) (c : ℕ)
    (h : ∀ (p : (Ξ.X Y).PIdx) (z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × (Fin ((Ξ.X Y).da p) → ℝ)),
      z.2 ∈ closedBox ((Ξ.X Y).da p) (Y.T.a p.1) → ξ.loc p z = ξ'.loc p z) :
    Ξ.empiricalChartMeasure Y ξ μ c = Ξ.empiricalChartMeasure Y ξ' μ c := by
  unfold empiricalChartMeasure empFaceMeasure
  refine Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun J _ => ?_
  rw [Ξ.empFaceMeasureU_congr Y _ J ξ μ fun z hz =>
    h _ (z.1, glue J 0 z.2) (Ξ.glue_mem_closedBox_of_mem_box Y _ J hz)]

/-- **Domination by the population measure**: `ν^μ_c(ξ) ≤ fluctDensity μ M · ν^μ_c` when the
representatives are bounded by `M`. -/
theorem empiricalChartMeasure_le {μ : ℝ} (hμ : 0 < μ) (c : ℕ) {M : ℝ}
    (hM : ∀ (p : (Ξ.X Y).PIdx) (z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × (Fin ((Ξ.X Y).da p) → ℝ)),
      z.2 ∈ closedBox ((Ξ.X Y).da p) (Y.T.a p.1) → |ξ.loc p z| ≤ M) :
    Ξ.empiricalChartMeasure Y ξ μ c ≤
      ENNReal.ofReal (fluctDensity μ M) • Ξ.chartResidueMeasure Y μ c := by
  unfold empiricalChartMeasure chartResidueMeasure
  rw [Finset.smul_sum]
  refine Finset.sum_le_sum fun I _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_le_sum fun J _ => ?_
  exact Ξ.empFaceMeasure_le Y _ J ξ hμ c fun z hz => Ξ.faceTrace_abs_le Y _ J ξ (hM _) hz

theorem empiricalChartMeasure_lt_top_of_isCompact {μ : ℝ} (hμ : 0 < μ) (c : ℕ)
    {C : Set (Ξ.stratumOpen c)} (hC : IsCompact C) : Ξ.empiricalChartMeasure Y ξ μ c C < ⊤ := by
  unfold empiricalChartMeasure
  rw [Measure.finsetSum_apply]
  refine ENNReal.sum_lt_top.2 fun I _ => ?_
  rw [Measure.finsetSum_apply]
  refine ENNReal.sum_lt_top.2 fun J hJ => ?_
  exact Ξ.empFaceMeasure_lt_top_of_isCompact Y _ J ξ hμ (Finset.mem_filter.1 hJ).2.1 hC

theorem isFiniteMeasureOnCompacts_empiricalStratumMeasure {μ : ℝ} (hμ : 0 < μ) (c : ℕ) :
    IsFiniteMeasureOnCompacts (Ξ.empiricalStratumMeasure Y ξ μ c) := by
  refine ⟨fun _ hC => ?_⟩
  unfold empiricalStratumMeasure
  rw [Measure.smul_apply, smul_eq_mul]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (Ξ.empiricalChartMeasure_lt_top_of_isCompact Y ξ hμ c hC)

/-- The empirical stratum measure is a regular Borel measure on `X`. -/
theorem regular_empiricalStratumMeasure {μ : ℝ} (hμ : 0 < μ) (c : ℕ) :
    (Ξ.empiricalStratumMeasure Y ξ μ c).Regular :=
  have := Ξ.isFiniteMeasureOnCompacts_empiricalStratumMeasure Y ξ hμ c
  Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _

/-- Tests are integrable against the empirical chart measure. -/
theorem integrable_empFaceMeasure_test {μ : ℝ} (hμ : 0 < μ) {c : ℕ} (p : (Ξ.X Y).PIdx)
    {J : Finset (Fin ((Ξ.X Y).da p))} (hJc : J.card = c) {G : Ξ.R.U → ℝ}
    (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) (hGt : Ξ.IsTest c G) :
    Integrable (fun x => G x.1) (Ξ.empFaceMeasure Y p J ξ μ c) := by
  obtain ⟨M, -, hM⟩ := ξ.exists_bound
  exact Integrable.of_measure_le_smul ENNReal.ofReal_ne_top
    (Ξ.empFaceMeasure_le Y p J ξ hμ c fun z hz => Ξ.faceTrace_abs_le Y p J ξ (hM p) hz)
    (Ξ.integrable_faceMeasure_test Y p J hG hGt hJc μ)

/-- ★★ **Lipschitz dependence of the empirical stratum measure on the field**: for tests `G` and
fields with representatives bounded by `M` and uniformly `δ`-close on the closed boxes,
`|∫ G dν(ξ) − ∫ G dν(ξ')| ≤ fluctLip μ M · δ · ∫ |G| dν`. -/
theorem abs_integral_empiricalStratumMeasure_sub_le {μ : ℝ} (hμ : 0 < μ) {c : ℕ} (hc : 1 ≤ c)
    (hzero : Ξ.ZeroOrder μ c) {G : Ξ.R.U → ℝ} (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G)
    (hGt : Ξ.IsTest c G) {ξ' : Ξ.RootField Y} {M δ : ℝ}
    (hM : ∀ (p : (Ξ.X Y).PIdx) (z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × (Fin ((Ξ.X Y).da p) → ℝ)),
      z.2 ∈ closedBox ((Ξ.X Y).da p) (Y.T.a p.1) → |ξ.loc p z| ≤ M)
    (hM' : ∀ (p : (Ξ.X Y).PIdx) (z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × (Fin ((Ξ.X Y).da p) → ℝ)),
      z.2 ∈ closedBox ((Ξ.X Y).da p) (Y.T.a p.1) → |ξ'.loc p z| ≤ M)
    (hδ : ∀ (p : (Ξ.X Y).PIdx) (z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × (Fin ((Ξ.X Y).da p) → ℝ)),
      z.2 ∈ closedBox ((Ξ.X Y).da p) (Y.T.a p.1) → |ξ.loc p z - ξ'.loc p z| ≤ δ) :
    |(∫ x, G x.1 ∂(Ξ.empiricalStratumMeasure Y ξ μ c)) -
        ∫ x, G x.1 ∂(Ξ.empiricalStratumMeasure Y ξ' μ c)| ≤
      fluctLip μ M * δ * ∫ x, |G x.1| ∂(Ξ.stratumMeasure Y hc hzero) := by
  rw [Ξ.stratumMeasure_eq_smul_chartResidueMeasure Y hμ hc hzero]
  unfold empiricalStratumMeasure empiricalChartMeasure chartResidueMeasure
  simp only [integral_smul_measure, ENNReal.toReal_ofReal (residueConst_pos hμ c).le, smul_eq_mul]
  have hIf : ∀ (η : Ξ.RootField Y) (I : Fin (Fintype.card (Ξ.X Y).PIdx)),
      ∀ J ∈ Ξ.simpleFaces Y ((Ξ.X Y).en I) μ c,
        Integrable (fun x => G x.1) (Ξ.empFaceMeasure Y ((Ξ.X Y).en I) J η μ c) :=
    fun η I J hJ => Ξ.integrable_empFaceMeasure_test Y η hμ _ (Finset.mem_filter.1 hJ).2.1 hG hGt
  have hIa : ∀ (I : Fin (Fintype.card (Ξ.X Y).PIdx)), ∀ J ∈ Ξ.simpleFaces Y ((Ξ.X Y).en I) μ c,
      Integrable (fun x => |G x.1|) (Ξ.faceMeasure Y ((Ξ.X Y).en I) J μ c) :=
    fun I J hJ => (Ξ.integrable_faceMeasure_test Y _ J hG hGt (Finset.mem_filter.1 hJ).2.1 μ).abs
  rw [integral_finsetSum_measure (fun I _ => integrable_finsetSum_measure.2 (hIf ξ I)),
    integral_finsetSum_measure (fun I _ => integrable_finsetSum_measure.2 (hIf ξ' I)),
    integral_finsetSum_measure (fun I _ => integrable_finsetSum_measure.2 (hIa I))]
  simp only [integral_finsetSum_measure (hIf ξ _), integral_finsetSum_measure (hIf ξ' _),
    integral_finsetSum_measure (hIa _)]
  rw [← mul_sub, abs_mul, abs_of_pos (residueConst_pos hμ c), ← Finset.sum_sub_distrib,
    mul_left_comm, Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (residueConst_pos hμ c).le
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun I _ => ?_)
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun J hJ => ?_)
  exact Ξ.abs_integral_empFaceMeasure_sub_le Y _ J ξ hμ (Finset.mem_filter.1 hJ).2.1 hG hGt
    (fun z hz => Ξ.faceTrace_abs_le Y _ J ξ (hM _) hz)
    (fun z hz => Ξ.faceTrace_abs_le Y _ J ξ' (hM' _) hz)
    (fun z hz => hδ _ (z.1, glue J 0 z.2) (Ξ.glue_mem_closedBox_of_mem_box Y _ J hz))

end ResolvedData

end SmoothEngine

end Grammar
