/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.ResolvedExtremalLocalisation

/-!
# The global leading measure and the extremal stratum measure (polar-distribution plan, unit 21)

Consult #169 (`tide-log/gpt6_leading_v169.md`).  The extremal stratum measure `ν^{λ*}_{m*}` of the
library lives on the open stratum `X = U ∖ D_{m*+1}` and is characterised by its integrals of the
smooth TEST functions (compactly supported in `X`); the raw leading measure `ρ^{λ*}_{m*}` of unit 19
lives on all of `U` and represents the coefficient functional on EVERY smooth observable (unit 20).
On the tests the two representations agree, so by the uniqueness theorem
`eq_stratumMeasure_of_tests` (regularity of the restriction of a finite measure to an open subset
of the σ-compact metrisable manifold `U`):

  `ν^{λ*}_{m*} = Γ(λ*)/(m*−1)! · ρ^{λ*}_{m*}|_X`  (★★★ `extremalStratumMeasure_eq_leadingResidue`)

Pushing forward along `X ↪ U` gives the GLOBAL extremal stratum measure
`globalExtremalStratumMeasure = Γ(λ*)/(m*−1)! · ρ|_X` on `U`
(★★★ `globalExtremalStratumMeasure_eq_restrict`), and it is the full multiple
`Γ(λ*)/(m*−1)! · ρ` exactly when the raw measure gives the deep fibre `D_{m*+1} ∩ Z₀` measure zero
(★★ `globalExtremalStratumMeasure_eq_iff`).  The deep fibre IS null: a face of `m` walls maps a
point into the deep fibre only when a complementary chart coordinate vanishes, since the intrinsic
depth is the number of vanishing chart coordinates (`depth_divPt_eq`), and the coordinate
hyperplanes are null for the face reference measure (★★ `leadingResidueMeasureU_deepZeroFibre`).
Hence ★★★ `globalExtremalStratumMeasure_eq`: `ν^{λ*}_{m*} = Γ(λ*)/(m*−1)! · ρ^{λ*}_{m*}` on all of
`U`, the coefficient functional at the extremal pair is the global stratum measure for EVERY smooth
observable (`coeff_withF_eq_integral_globalExtremalStratumMeasure`), and the extremal stratum
measure is FINITE with total mass `Γ(λ*)/(m*−1)! · ρ(U)` (`extremalStratumMeasure_univ`,
`isFiniteMeasure_extremalStratumMeasure`).
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff Manifold
open Monomialize.VolumeScaling Monomialize.Transport Monomialize.Manifold
open Grammar.NormalCrossing Grammar.NormalCrossing.EvenChartBoxDepth

namespace Grammar

namespace SmoothEngine

namespace ResolvedData

variable {d : ℕ} (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)

/-! ### The raw leading measure on the open stratum -/

theorem measurableSet_stratumOpen (m : ℕ) : MeasurableSet (Ξ.stratumOpen m) :=
  (Ξ.isOpen_stratumOpen m).measurableSet

theorem measurableSet_deepZeroFibre (m : ℕ) : MeasurableSet (Ξ.deepZeroFibre m) :=
  (Ξ.isCompact_deepZeroFibre m).isClosed.measurableSet

/-- The raw leading measure restricted to the open stratum `X = U ∖ D_{m+1}`. -/
noncomputable def leadingResidueMeasureX (lam : ℝ) (m : ℕ) : Measure (Ξ.stratumOpen m) :=
  (Ξ.leadingResidueMeasureU Y lam m).comap Subtype.val

theorem integral_leadingResidueMeasureX (lam : ℝ) (m : ℕ) (G : Ξ.R.U → ℝ) :
    ∫ x, G x.1 ∂(Ξ.leadingResidueMeasureX Y lam m) =
      ∫ x in Ξ.stratumOpen m, G x ∂(Ξ.leadingResidueMeasureU Y lam m) :=
  integral_subtype_comap (Ξ.measurableSet_stratumOpen m) G

theorem leadingResidueMeasureX_apply (lam : ℝ) (m : ℕ) (s : Set (Ξ.stratumOpen m)) :
    Ξ.leadingResidueMeasureX Y lam m s = Ξ.leadingResidueMeasureU Y lam m (Subtype.val '' s) :=
  (MeasurableEmbedding.subtype_coe (Ξ.measurableSet_stratumOpen m)).comap_apply _ _

/-- The raw leading measure is regular at a chart-leading pair (finite on the σ-compact
metrisable manifold `U`). -/
theorem regular_leadingResidueMeasureU {lam : ℝ} {m : ℕ} (hμ : 0 < lam)
    (hlead : Ξ.ChartLeading Y lam m) : (Ξ.leadingResidueMeasureU Y lam m).Regular :=
  haveI := Ξ.isFiniteMeasure_leadingResidueMeasureU Y hμ hlead
  Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _

theorem regular_leadingResidueMeasureX {lam : ℝ} {m : ℕ} (hμ : 0 < lam)
    (hlead : Ξ.ChartLeading Y lam m) : (Ξ.leadingResidueMeasureX Y lam m).Regular :=
  haveI := Ξ.regular_leadingResidueMeasureU Y hμ hlead
  Measure.Regular.comap' _ (Ξ.isOpen_stratumOpen m).isOpenEmbedding_subtypeVal

/-! ### The deep fibre is null for the raw leading measure -/

/-- The coordinate hyperplanes of the complementary walls are null for the face reference
measure. -/
theorem faceRef_exists_eq_zero_null (p : (Ξ.X Y).PIdx) (J : Finset (Fin ((Ξ.X Y).da p))) :
    Ξ.faceRef Y p J {z | ∃ i, z.2 i = 0} = 0 := by
  have ht : (volume : Measure ({i // ¬ inJ J i} → ℝ)) {w | ∃ i, w i = 0} = 0 := by
    have : {w : {i // ¬ inJ J i} → ℝ | ∃ i, w i = 0} = ⋃ i, {w | w i = 0} := by ext w; simp
    rw [this]
    exact measure_iUnion_null fun i => by rw [volume_pi]; exact Measure.pi_hyperplane _ i 0
  unfold faceRef
  rw [show {z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × ({i // ¬ inJ J i} → ℝ) | ∃ i, z.2 i = 0} =
      univ ×ˢ {w | ∃ i, w i = 0} by ext z; simp, Measure.prod_prod,
    Measure.restrict_apply' (measurableSet_box _), measure_mono_null inter_subset_left ht,
    mul_zero]

/-- A point of the face box mapped into the deep fibre `D_{m+1} ∩ Z₀` by a face of `m` walls has a
vanishing complementary coordinate: the intrinsic depth is the number of vanishing chart
coordinates (`depth_divPt_eq`). -/
theorem exists_eq_zero_of_faceMap_mem_deepZeroFibre (p : (Ξ.X Y).PIdx) {m : ℕ}
    {J : Finset (Fin ((Ξ.X Y).da p))} (hJ : J.card = m)
    {z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × ({i // ¬ inJ J i} → ℝ)}
    (hz : z.2 ∈ box {i // ¬ inJ J i} (Y.T.a p.1)) (hmem : Ξ.faceMap Y p J z ∈ Ξ.deepZeroFibre m) :
    ∃ i, z.2 i = 0 := by
  by_contra hne
  simp only [not_exists] at hne
  have hdepth : m + 1 ≤ depth Ξ.R Ξ.hK0 (Ξ.faceMap Y p J z) := hmem.2
  rw [Ξ.faceMap_eq_divPt Y p J hz, Ξ.depth_divPt_eq Y p z.1
    (Ξ.glue_mem_closedBox_of_mem_box Y p J hz) (J := J) ?_, hJ] at hdepth
  · omega
  · intro i
    by_cases hi : i ∈ J
    · simp [glue_apply_of_mem J _ _ hi, hi]
    · simp [glue_apply_of_not_mem J _ _ hi, hi, hne ⟨i, hi⟩]

/-- ★ **A face measure of `m` walls gives the deep fibre `D_{m+1} ∩ Z₀` measure zero.** -/
theorem faceMeasureU_deepZeroFibre (p : (Ξ.X Y).PIdx) {m : ℕ}
    {J : Finset (Fin ((Ξ.X Y).da p))} (hJ : J.card = m) (μ : ℝ) :
    Ξ.faceMeasureU Y p J μ (Ξ.deepZeroFibre m) = 0 := by
  unfold faceMeasureU
  rw [Measure.map_apply (Ξ.measurable_faceMap Y p J) (Ξ.measurableSet_deepZeroFibre m)]
  refine withDensity_absolutelyContinuous _ _ (measure_mono_null (t := {z | z.2 ∉ box
    {i // ¬ inJ J i} (Y.T.a p.1)} ∪ {z | ∃ i, z.2 i = 0}) ?_
    (measure_union_null (ae_iff.1 (Ξ.ae_faceRef_mem_box Y p J))
      (Ξ.faceRef_exists_eq_zero_null Y p J)))
  intro z hz
  by_cases hzb : z.2 ∈ box {i // ¬ inJ J i} (Y.T.a p.1)
  · exact Or.inr (Ξ.exists_eq_zero_of_faceMap_mem_deepZeroFibre Y p hJ hzb hz)
  · exact Or.inl hzb

/-- ★★ **Deep-fibre nullity**: the raw leading measure `ρ^λ_m` gives `D_{m+1} ∩ Z₀` measure zero. -/
theorem leadingResidueMeasureU_deepZeroFibre (lam : ℝ) (m : ℕ) :
    Ξ.leadingResidueMeasureU Y lam m (Ξ.deepZeroFibre m) = 0 := by
  unfold leadingResidueMeasureU
  rw [Measure.finsetSum_apply]
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [Measure.finsetSum_apply]
  refine Finset.sum_eq_zero fun J hJ => ?_
  exact Ξ.faceMeasureU_deepZeroFibre Y p (Finset.mem_filter.1 hJ).2.1 lam

/-- The raw leading measure is carried by the open stratum `X = U ∖ D_{m+1}`. -/
theorem leadingResidueMeasureU_restrict_stratumOpen (lam : ℝ) (m : ℕ) :
    (Ξ.leadingResidueMeasureU Y lam m).restrict (Ξ.stratumOpen m) =
      Ξ.leadingResidueMeasureU Y lam m :=
  Measure.restrict_eq_self_of_ae_mem
    (compl_mem_ae_iff.2 (Ξ.leadingResidueMeasureU_deepZeroFibre Y lam m))

/-! ### The extremal stratum measure is the raw leading measure on the stratum -/

/-- ★★★ **The extremal stratum measure is the raw leading measure on the open stratum**:
`ν^{λ*}_{m*} = Γ(λ*)/(m*−1)! · ρ^{λ*}_{m*}|_X`. -/
theorem extremalStratumMeasure_eq_leadingResidue {lam : ℝ} {m : ℕ} (h : Ξ.IsExtremalData lam m)
    (hc : Ξ.ExtremalCertificate Y) (hμ : 0 < lam) (hm : 1 ≤ m) :
    Ξ.extremalStratumMeasure Y h hm =
      ENNReal.ofReal (residueConst lam m) • Ξ.leadingResidueMeasureX Y lam m := by
  symm
  have := Ξ.regular_leadingResidueMeasureX Y hμ (Ξ.chartLeading_of_extremalData Y h hc)
  have : (ENNReal.ofReal (residueConst lam m) • Ξ.leadingResidueMeasureX Y lam m).Regular :=
    Measure.Regular.smul ENNReal.ofReal_ne_top
  unfold extremalStratumMeasure
  refine Ξ.eq_stratumMeasure_of_tests Y hm _ _ fun G hG hGt => ?_
  rw [integral_smul_measure, ENNReal.toReal_ofReal (residueConst_pos hμ m).le, smul_eq_mul,
    Ξ.integral_leadingResidueMeasureX, setIntegral_eq_integral_of_forall_compl_eq_zero
      fun x hx => image_eq_zero_of_notMem_tsupport fun hx' => hx (hGt.2 hx')]
  exact (Ξ.coeff_withF_eq_integral_leadingResidueMeasureU Y h hc hμ hm hG).symm

/-- The total mass of the extremal stratum measure is `Γ(λ*)/(m*−1)! · ρ^{λ*}_{m*}(U)`. -/
theorem extremalStratumMeasure_univ {lam : ℝ} {m : ℕ} (h : Ξ.IsExtremalData lam m)
    (hc : Ξ.ExtremalCertificate Y) (hμ : 0 < lam) (hm : 1 ≤ m) :
    Ξ.extremalStratumMeasure Y h hm univ =
      ENNReal.ofReal (residueConst lam m) * Ξ.leadingResidueMeasureU Y lam m univ := by
  rw [Ξ.extremalStratumMeasure_eq_leadingResidue Y h hc hμ hm, Measure.smul_apply, smul_eq_mul,
    Ξ.leadingResidueMeasureX_apply, image_univ, Subtype.range_coe, ← Measure.restrict_apply_univ,
    Ξ.leadingResidueMeasureU_restrict_stratumOpen]

/-- ★ The extremal stratum measure is finite under the certificate. -/
theorem isFiniteMeasure_extremalStratumMeasure {lam : ℝ} {m : ℕ} (h : Ξ.IsExtremalData lam m)
    (hc : Ξ.ExtremalCertificate Y) (hμ : 0 < lam) (hm : 1 ≤ m) :
    IsFiniteMeasure (Ξ.extremalStratumMeasure Y h hm) := by
  have := Ξ.isFiniteMeasure_leadingResidueMeasureU Y hμ (Ξ.chartLeading_of_extremalData Y h hc)
  refine ⟨?_⟩
  rw [Ξ.extremalStratumMeasure_univ Y h hc hμ hm]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

/-! ### The global extremal stratum measure on `U` -/

/-- ★★★ **The global extremal stratum measure** on `U`: the pushforward of `ν^{λ*}_{m*}` along
`X ↪ U`. -/
noncomputable def globalExtremalStratumMeasure {lam : ℝ} {m : ℕ} (h : Ξ.IsExtremalData lam m)
    (hm : 1 ≤ m) : Measure Ξ.R.U :=
  (Ξ.extremalStratumMeasure Y h hm).map Subtype.val

/-- ★★★ **The global extremal stratum measure is the raw leading measure restricted to the open
stratum**: `Γ(λ*)/(m*−1)! · ρ^{λ*}_{m*}|_{U ∖ D_{m*+1}}`. -/
theorem globalExtremalStratumMeasure_eq_restrict {lam : ℝ} {m : ℕ} (h : Ξ.IsExtremalData lam m)
    (hc : Ξ.ExtremalCertificate Y) (hμ : 0 < lam) (hm : 1 ≤ m) :
    Ξ.globalExtremalStratumMeasure Y h hm = ENNReal.ofReal (residueConst lam m) •
      (Ξ.leadingResidueMeasureU Y lam m).restrict (Ξ.stratumOpen m) := by
  unfold globalExtremalStratumMeasure
  rw [Ξ.extremalStratumMeasure_eq_leadingResidue Y h hc hμ hm, Measure.map_smul,
    leadingResidueMeasureX, map_comap_subtype_coe (Ξ.measurableSet_stratumOpen m)]

/-- ★★ **The raw leading measure is the global extremal stratum measure exactly when the deep
fibre is null**: `ν^{λ*}_{m*} = Γ(λ*)/(m*−1)! · ρ^{λ*}_{m*}` on `U` iff
`ρ^{λ*}_{m*}(D_{m*+1} ∩ Z₀) = 0`. -/
theorem globalExtremalStratumMeasure_eq_iff {lam : ℝ} {m : ℕ} (h : Ξ.IsExtremalData lam m)
    (hc : Ξ.ExtremalCertificate Y) (hμ : 0 < lam) (hm : 1 ≤ m) :
    Ξ.globalExtremalStratumMeasure Y h hm =
        ENNReal.ofReal (residueConst lam m) • Ξ.leadingResidueMeasureU Y lam m ↔
      Ξ.leadingResidueMeasureU Y lam m (Ξ.deepZeroFibre m) = 0 := by
  rw [Ξ.globalExtremalStratumMeasure_eq_restrict Y h hc hμ hm]
  constructor
  · intro heq
    have hc0 : ENNReal.ofReal (residueConst lam m) ≠ 0 :=
      (ENNReal.ofReal_pos.2 (residueConst_pos hμ m)).ne'
    have := congrArg (fun ν : Measure Ξ.R.U => ν (Ξ.deepZeroFibre m)) heq
    simp only [Measure.smul_apply, smul_eq_mul,
      Measure.restrict_apply (Ξ.measurableSet_deepZeroFibre m)] at this
    rw [stratumOpen, inter_compl_self, measure_empty, mul_zero, eq_comm, mul_eq_zero] at this
    exact this.resolve_left hc0
  · intro hnull
    rw [Measure.restrict_eq_self_of_ae_mem]
    exact compl_mem_ae_iff.2 hnull

/-- ★★★ **The global extremal stratum measure is the residue-constant multiple of the raw leading
measure on all of `U`**: `ν^{λ*}_{m*} = Γ(λ*)/(m*−1)! · ρ^{λ*}_{m*}` (the deep fibre is null). -/
theorem globalExtremalStratumMeasure_eq {lam : ℝ} {m : ℕ} (h : Ξ.IsExtremalData lam m)
    (hc : Ξ.ExtremalCertificate Y) (hμ : 0 < lam) (hm : 1 ≤ m) :
    Ξ.globalExtremalStratumMeasure Y h hm =
      ENNReal.ofReal (residueConst lam m) • Ξ.leadingResidueMeasureU Y lam m :=
  (Ξ.globalExtremalStratumMeasure_eq_iff Y h hc hμ hm).2
    (Ξ.leadingResidueMeasureU_deepZeroFibre Y lam m)

/-- ★★★ **The coefficient functional at the extremal pair is the global extremal stratum measure
for EVERY smooth observable** (no test hypothesis). -/
theorem coeff_withF_eq_integral_globalExtremalStratumMeasure {lam : ℝ} {m : ℕ}
    (h : Ξ.IsExtremalData lam m) (hc : Ξ.ExtremalCertificate Y) (hμ : 0 < lam) (hm : 1 ≤ m)
    {G : Ξ.R.U → ℝ} (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) :
    (Ξ.withF G hG).coeff Y lam (m - 1) =
      ∫ x, G x ∂(Ξ.globalExtremalStratumMeasure Y h hm) := by
  rw [Ξ.globalExtremalStratumMeasure_eq Y h hc hμ hm, integral_smul_measure,
    ENNReal.toReal_ofReal (residueConst_pos hμ m).le, smul_eq_mul]
  exact Ξ.coeff_withF_eq_integral_leadingResidueMeasureU Y h hc hμ hm hG

/-- The global extremal stratum measure integrates every smooth observable vanishing off the open
stratum to the coefficient functional. -/
theorem integral_globalExtremalStratumMeasure {lam : ℝ} {m : ℕ} (h : Ξ.IsExtremalData lam m)
    (hm : 1 ≤ m) (G : Ξ.R.U → ℝ) :
    ∫ x, G x ∂(Ξ.globalExtremalStratumMeasure Y h hm) =
      ∫ x, G x.1 ∂(Ξ.extremalStratumMeasure Y h hm) :=
  (MeasurableEmbedding.subtype_coe (Ξ.measurableSet_stratumOpen m)).integral_map _

end ResolvedData

end SmoothEngine

end Grammar
