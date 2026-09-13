/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.ChartBoxCertificate
import Grammar.CoordinateBoxInputs
import Grammar.HolomorphicOriginalFaceSeries
import Grammar.CollarDeltaSelection

/-!
# Analytic inputs of the chart-box producer (consult #111, unit F)

The adapters of CCCXXV and the holomorphic bridge of CCCXXXI, for the chart collar (CCCLXXI–II):
the chart cores are indexed through the ambient index sets `amb I` (`toNonemptyIdx`), so the
ORIGINAL-variable face series `OriginalFaceSeries a ϕ φ (toNonemptyIdx I)` of CCCXXV and the face
series `HolomorphicBoxExtension.faceSeries` of a holomorphic packet apply verbatim; what changes is
the rescaling: the unit-corrected widthsC `λ_{I,i}(s)` are bounded by
`L_i = (δ/c)^{1/(2k_i |A|)} / b_I` (`abs_widthsC_le`, from `q_I ≤ (δ/c)^{1/|A|}`), and the smallness
condition becomes `2 (δ/c)^{1/(2k_i |A|)} < ρ`. Hence `toChartFaceSeries`,
★★ `hasCoordFreeExpansion_chart_of_face`, the level selection `exists_delta_chart`, and
★★★ `hasCoordFreeExpansion_chart_of_holomorphicBoxExtension`: for a chart with active set `A`,
orders `(k, h)`, positive tangential unit `u ≥ c` and a holomorphic packet for the analytic prior
factor `ϕ` and the observable `φ` near `[0,a]^d`, the weighted integral
`∫_{[0,a]^d} φ · ∏|y_i|^{h_i} ϕ · e^{−n u ∏_{A} y^{2k}}` has the coordinate-free expansion, with
log degree `|A| − 1` (`commonD_chart`). Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Grammar

namespace ChartCollar

open NormalisedBox WaterFilling CoordModel CoeffFamily

variable {d : ℕ} (A : Finset (Fin d)) (k h : Fin d → ℕ) (hkA : ∀ i ∈ A, 0 < k i)
  (hk0 : ∀ i, i ∉ A → k i = 0) (u : (Fin d → ℝ) → ℝ) (a δ : ℝ) (hδ : 0 < δ) (hu_cont : Continuous u)
  (ϕ φ : (Fin d → ℝ) → ℝ)
  (hu_tan : ∀ w w' : Fin d → ℝ, (∀ j, j ∉ A → w j = w' j) → u w = u w')
  (c : ℝ) (hc : 0 < c) (hu_lb : ∀ w ∈ piBox d (Icc 0 a), c ≤ u w) (ha : 0 < a)

/-! ### The closed faces and the widthsC -/

include ha in
/-- A collar base point lies on the closed face `X_{amb I}`. -/
theorem mem_faceSet_of_KIC (I : Idx A) (s : KI A k h hkA u a δ I) :
    s.1.1 ∈ WaterFilling.faceSet a (amb A I) := by
  refine ⟨?_, fun i hi => stratum_coord_zero A k h hkA s.1 hi⟩
  rw [piBox, mem_univ_pi]
  intro j
  by_cases hj : j ∈ amb A I
  · rw [stratum_coord_zero A k h hkA s.1 hj]
    exact ⟨le_rfl, ha.le⟩
  · exact ⟨(s.2 ⟨j, hj⟩).1, (s.2 ⟨j, hj⟩).2.1⟩

include ha in
/-- The restriction of a collar base point to the closed face. -/
def toFaceC (I : Idx A) (s : KI A k h hkA u a δ I) : ↥(WaterFilling.faceSet a (amb A I)) :=
  ⟨s.1.1, mem_faceSet_of_KIC A k h hkA u a δ ha I s⟩

include ha in
theorem continuous_toFaceC (I : Idx A) : Continuous (toFaceC A k h hkA u a δ ha I) :=
  (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

/-- The water-filling widthsC in box coordinates. -/
noncomputable def widthsC (I : Idx A) (s : KI A k h hkA u a δ I) (i : Fin (nI A I + 1)) : ℝ :=
  lamT k u (amb A I) δ (eI A k h hkA u a δ I s) (σI A I i)

/-- The uniform bound `L_i = (δ/c)^{1/(2k_i |A|)} / b_I` on the widthsC. -/
noncomputable def widthBoundC (I : Idx A) (i : Fin (nI A I + 1)) : ℝ :=
  (δ / c) ^ ((A.card : ℝ)⁻¹ * ((2 * k (σI A I i).1 : ℕ) : ℝ)⁻¹) / side k (amb A I) δ

include hk0 hδ hu_cont hc hu_lb ha in
theorem continuous_widthsC (I : Idx A) (i : Fin (nI A I + 1)) :
    Continuous fun s => widthsC A k h hkA u a δ I s i :=
  (continuous_apply _).comp ((continuousOn_lamT A k u (amb A I) a δ hu_cont hkA hk0
    (amb_nonempty A I) hδ hc hu_lb ha.le).comp_continuous (continuous_eI A k h hkA u a δ I)
    fun s => s.2)

include hk0 hδ hc hu_lb ha in
theorem widthsC_pos (I : Idx A) (s : KI A k h hkA u a δ I) (i : Fin (nI A I + 1)) :
    0 < widthsC A k h hkA u a δ I s i :=
  lamT_pos_of_mem_baseSet A k u (amb A I) a δ hkA hk0 (amb_nonempty A I) hδ hc hu_lb ha.le s.2 _

include hδ hc in
theorem widthBoundC_pos (I : Idx A) (i : Fin (nI A I + 1)) : 0 < widthBoundC A k δ c I i :=
  div_pos (Real.rpow_pos_of_pos (div_pos hδ hc) _) (side_pos k (amb A I) δ hδ)

include hk0 hδ hc hu_lb ha in
/-- `λ_{I,i}(s) ≤ L_i` on the collar base. -/
theorem abs_widthsC_le (I : Idx A) (s : KI A k h hkA u a δ I) (i : Fin (nI A I + 1)) :
    |widthsC A k h hkA u a δ I s i| ≤ widthBoundC A k δ c I i := by
  rw [abs_of_pos (widthsC_pos A k h hkA hk0 u a δ hδ c hc hu_lb ha I s i), widthsC, widthBoundC,
    lamT]
  refine div_le_div_of_nonneg_right ?_ (side_pos k (amb A I) δ hδ).le
  rw [ell, Real.rpow_mul (div_pos hδ hc).le]
  exact Real.rpow_le_rpow
    (q_pos_of_mem_baseSet A k u (amb A I) a δ hkA hk0 (amb_nonempty A I) hδ hc hu_lb ha.le s.2).le
    (q_le_rpow A k u (amb A I) a δ hkA hk0 (amb_nonempty A I) (amb_subset A I) hδ hc hu_lb ha.le
      s.2) (by positivity)

include hδ in
/-- The rescaled radius: `L_i · 2 b_I = 2 (δ/c)^{1/(2k_i |A|)}`. -/
theorem widthBoundC_mul (I : Idx A) (i : Fin (nI A I + 1)) :
    widthBoundC A k δ c I i * (2 * side k (amb A I) δ) =
      2 * (δ / c) ^ ((A.card : ℝ)⁻¹ * ((2 * k (σI A I i).1 : ℕ) : ℝ)⁻¹) := by
  have hs := (side_pos k (amb A I) δ hδ).ne'
  rw [widthBoundC]
  field_simp

/-- The core parametrisation in original normal coordinates: `Φ(s, v) = Ψ_I(s, λ(s)·v)`. -/
theorem Φ_eq_originalNormalMapC (I : Idx A) (s : KI A k h hkA u a δ I) (v : Fin (nI A I + 1) → ℝ) :
    Φ (amb A I) (σI A I) (eI A k h hkA u a δ I) (lamT k u (amb A I) δ) (s, v) =
      originalNormalMap (toNonemptyIdx A I) s.1.1 fun i => widthsC A k h hkA u a δ I s i * v i := by
  funext j
  rw [Φ_apply, originalNormalMap]
  by_cases hj : j ∈ amb A I
  · have hj' : j ∈ (toNonemptyIdx A I).1 := hj
    rw [dif_pos hj, dif_pos hj', stratum_coord_zero A k h hkA s.1 hj, zero_add]
    unfold widthsC
    change lamT k u (amb A I) δ (eI A k h hkA u a δ I s) ⟨j, hj⟩ * v ((σI A I).symm ⟨j, hj⟩) =
      lamT k u (amb A I) δ (eI A k h hkA u a δ I s) (σI A I ((σI A I).symm ⟨j, hj'⟩)) *
        v ((σI A I).symm ⟨j, hj'⟩)
    rw [Equiv.apply_symm_apply]
  · have hj' : j ∉ (toNonemptyIdx A I).1 := hj
    rw [dif_neg hj, dif_neg hj']
    rfl

variable {ϕ φ}

include hk0 hδ hc hu_lb ha in
/-- The rescaled displacement lies in the original normal ball. -/
theorem norm_widthsC_mul_lt (I : Idx A) {ρ : ℝ} (hρ : 0 < ρ)
    (hsmall : ∀ i : Fin (nI A I + 1),
      2 * (δ / c) ^ ((A.card : ℝ)⁻¹ * ((2 * k (σI A I i).1 : ℕ) : ℝ)⁻¹) < ρ)
    (s : KI A k h hkA u a δ I) {v : Fin (nI A I + 1) → ℝ} (hv : ‖v‖ < 2 * side k (amb A I) δ) :
    ‖fun i => widthsC A k h hkA u a δ I s i * v i‖ < ρ := by
  rw [pi_norm_lt_iff hρ]
  intro i
  rw [Real.norm_eq_abs, abs_mul]
  have hvi : |v i| < 2 * side k (amb A I) δ := by
    have := (pi_norm_lt_iff (by linarith [side_pos k (amb A I) δ hδ])).1 hv i
    rwa [Real.norm_eq_abs] at this
  calc |widthsC A k h hkA u a δ I s i| * |v i|
      ≤ widthBoundC A k δ c I i * (2 * side k (amb A I) δ) :=
        mul_le_mul (abs_widthsC_le A k h hkA hk0 u a δ hδ c hc hu_lb ha I s i) hvi.le (abs_nonneg _)
          (widthBoundC_pos A k δ hδ c hc I i).le
    _ = 2 * (δ / c) ^ ((A.card : ℝ)⁻¹ * ((2 * k (σI A I i).1 : ℕ) : ℝ)⁻¹) :=
        widthBoundC_mul A k δ hδ c I i
    _ < ρ := hsmall i

include hk0 hδ hu_cont hc hu_lb ha in
/-- ★ **The original-face adapter for the chart**: restriction to the collar base and rescaling by
the unit-corrected widthsC turn original-variable face series into the chart face series. -/
noncomputable def toChartFaceSeries {I : Idx A}
    (O : OriginalFaceSeries a ϕ φ (toNonemptyIdx A I))
    (hsmall : ∀ i : Fin (nI A I + 1),
      2 * (δ / c) ^ ((A.card : ℝ)⁻¹ * ((2 * k (σI A I i).1 : ℕ) : ℝ)⁻¹) < O.ρ) :
    FaceSeries A k h hkA u a δ ϕ φ I where
  Fϕ := (O.Fϕ.precomp (toFaceC A k h hkA u a δ ha I)
    (continuous_toFaceC A k h hkA u a δ ha I)).rescale (widthsC A k h hkA u a δ I)
    (continuous_widthsC A k h hkA hk0 u a δ hδ hu_cont c hc hu_lb ha I)
    (widthBoundC A k δ c I) (abs_widthsC_le A k h hkA hk0 u a δ hδ c hc hu_lb ha I)
    (fun i => (widthBoundC_pos A k δ hδ c hc I i).le) (by linarith [side_pos k (amb A I) δ hδ])
    fun i => by
      rw [widthBoundC_mul A k δ hδ c I i]
      exact (hsmall i).le
  Fφ := (O.Fφ.precomp (toFaceC A k h hkA u a δ ha I)
    (continuous_toFaceC A k h hkA u a δ ha I)).rescale (widthsC A k h hkA u a δ I)
    (continuous_widthsC A k h hkA hk0 u a δ hδ hu_cont c hc hu_lb ha I)
    (widthBoundC A k δ c I) (abs_widthsC_le A k h hkA hk0 u a δ hδ c hc hu_lb ha I)
    (fun i => (widthBoundC_pos A k δ hδ c hc I i).le) (by linarith [side_pos k (amb A I) δ hδ])
    fun i => by
      rw [widthBoundC_mul A k δ hδ c I i]
      exact (hsmall i).le
  hϕ_eq := fun s v hv => by
    have hv' : ‖v‖ < 2 * side k (amb A I) δ := by
      refine lt_of_le_of_lt ((pi_norm_le_iff_of_nonneg (side_pos k (amb A I) δ hδ).le).2
        fun i => ?_) (by linarith [side_pos k (amb A I) δ hδ])
      have := hv i (mem_univ _)
      rw [mem_Ioc] at this
      rw [Real.norm_eq_abs]
      exact abs_le.2 ⟨by linarith, this.2⟩
    exact (congrArg ϕ (Φ_eq_originalNormalMapC A k h hkA u a δ I s v)).trans
      ((O.hϕ_eq (toFaceC A k h hkA u a δ ha I s) _
        (norm_widthsC_mul_lt A k h hkA hk0 u a δ hδ c hc hu_lb ha I O.hρ hsmall s hv')).trans
        (evalF_rescale (widthsC A k h hkA u a δ I s)
          (O.Fϕ.f (toFaceC A k h hkA u a δ ha I s)) v).symm)
  hφ_eq := fun s v hv =>
    (congrArg φ (Φ_eq_originalNormalMapC A k h hkA u a δ I s v)).trans
      ((O.hφ_eq (toFaceC A k h hkA u a δ ha I s) _
        (norm_widthsC_mul_lt A k h hkA hk0 u a δ hδ c hc hu_lb ha I O.hρ hsmall s hv)).trans
        (evalF_rescale (widthsC A k h hkA u a δ I s)
          (O.Fφ.f (toFaceC A k h hkA u a δ ha I s)) v).symm)

/-! ### The log degree of the chart collar -/

/-- The deepest stratum `I = univ` has ambient index set `A`. -/
theorem amb_univ (hA : A.Nonempty) : amb A ⟨Finset.univ, Finset.univ_nonempty_iff.2 ⟨⟨hA.choose,
    hA.choose_spec⟩⟩⟩ = A := by
  ext j
  rw [amb, ChartModel.mem_amb]
  constructor
  · rintro ⟨hj, -⟩
    exact hj
  · intro hj
    exact ⟨hj, Finset.mem_univ _⟩

/-- The maximal normal dimension minus one over the chart collar is `|A| − 1`. -/
theorem commonD_chart (hA : A.Nonempty) :
    commonD (fun i : Fin (numCores A) => nI A (coreIdx A i)) = A.card - 1 := by
  apply le_antisymm
  · refine Finset.sup_le fun i _ => ?_
    exact Nat.sub_le_sub_right (Finset.card_le_card (amb_subset A (coreIdx A i))) 1
  · unfold commonD
    have hne : (Finset.univ : Finset ↥A).Nonempty :=
      Finset.univ_nonempty_iff.2 ⟨⟨hA.choose, hA.choose_spec⟩⟩
    have h := Finset.le_sup (f := fun i : Fin (numCores A) => nI A (coreIdx A i))
      (Finset.mem_univ ((coreIdx A).symm ⟨Finset.univ, hne⟩))
    simp only [Equiv.apply_symm_apply] at h
    refine le_trans (le_of_eq ?_) h
    change A.card - 1 = (amb A ⟨Finset.univ, hne⟩).card - 1
    rw [amb_univ A hA]

/-! ### The expansion from original-variable face series and from holomorphic packets -/

variable (hδa : ∀ i ∈ A, (δ / c) ^ ((A.card : ℝ)⁻¹) < a ^ (2 * k i))
  (hϕm : Measurable ϕ) (hϕ0 : ∀ w, 0 ≤ ϕ w) (hφm : Measurable φ)
  (hφint : Integrable φ ((volume.restrict (piBox d (Icc 0 a))).withDensity
    fun w => ENNReal.ofReal (wgt h w * ϕ w)))

include hk0 hδ hu_cont hu_tan hc hu_lb ha hδa hϕm hϕ0 hφm hφint in
/-- ★★ **The chart-box expansion from original-variable face series**, with the log degree
`|A| − 1`. -/
theorem hasCoordFreeExpansion_chart_of_face (hA : A.Nonempty)
    (O : ∀ I : Idx A, OriginalFaceSeries a ϕ φ (toNonemptyIdx A I))
    (hsmall : ∀ (I : Idx A) (i : Fin (nI A I + 1)),
      2 * (δ / c) ^ ((A.card : ℝ)⁻¹ * ((2 * k (σI A I i).1 : ℕ) : ℝ)⁻¹) < (O I).ρ) :
    (ChartModel.normalData d A k h hkA).HasCoordFreeExpansion
      (certificate A k h hkA hk0 u a δ hδ hu_cont ϕ φ hu_tan hc hu_lb ha hδa hϕm hϕ0 hφint
        (fun I => toChartFaceSeries A k h hkA hk0 u a δ hδ hu_cont c hc hu_lb ha (O I) (hsmall I))
        hA).stratumMeasure
      (coeffCertificate A k h hkA hk0 u a δ hδ hu_cont ϕ φ hu_tan hc hu_lb ha hδa hϕm hϕ0 hφint
        (fun I => toChartFaceSeries A k h hkA hk0 u a δ hδ hu_cont c hc hu_lb ha (O I) (hsmall I))
        hA).field
      (spectrumLe (commonQ (certificate A k h hkA hk0 u a δ hδ hu_cont ϕ φ hu_tan hc hu_lb ha hδa
        hϕm hϕ0 hφint (fun I => toChartFaceSeries A k h hkA hk0 u a δ hδ hu_cont c hc hu_lb
          ha (O I) (hsmall I)) hA).cores.k) (A.card - 1))
      (piBox d (Icc 0 a)) (ChartModel.phase d A k u) (fun w => wgt h w * ϕ w) φ := by
  have hexp := hasCoordFreeExpansion_chart A k h hkA hk0 u a δ hδ hu_cont ϕ φ hu_tan hc hu_lb ha
    hδa hϕm hϕ0 hφm hφint
    (fun I => toChartFaceSeries A k h hkA hk0 u a δ hδ hu_cont c hc hu_lb ha (O I) (hsmall I)) hA
  have hD : commonD (certificate A k h hkA hk0 u a δ hδ hu_cont ϕ φ hu_tan hc hu_lb ha hδa hϕm hϕ0
      hφint (fun I => toChartFaceSeries A k h hkA hk0 u a δ hδ hu_cont c hc hu_lb ha (O I)
        (hsmall I)) hA).n = A.card - 1 := commonD_chart A hA
  rwa [hD] at hexp

omit hδ hu_cont hu_tan hu_lb hδa hϕm hϕ0 hφm hφint in
include hkA hc ha in
/-- ★ **Small-level selection for the chart**: for every radius `ρ > 0` there is a level `δ > 0`
with `(δ/c)^{1/|A|} < a^{2k_i}` and `2 (δ/c)^{1/(2k_i |A|)} < ρ` for every `i ∈ A`. -/
theorem exists_delta_chart (hA : A.Nonempty) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ δ : ℝ, 0 < δ ∧ (∀ i ∈ A, (δ / c) ^ ((A.card : ℝ)⁻¹) < a ^ (2 * k i)) ∧
      ∀ i ∈ A, 2 * (δ / c) ^ ((A.card : ℝ)⁻¹ * ((2 * k i : ℕ) : ℝ)⁻¹) < ρ := by
  have hApos : (0 : ℝ) < (A.card : ℝ)⁻¹ := inv_pos.2 (by exact_mod_cast hA.card_pos)
  have h1 : ∀ᶠ ε : ℝ in 𝓝 0, ∀ i ∈ A, ε ^ ((A.card : ℝ)⁻¹) < a ^ (2 * k i) :=
    Filter.eventually_all_finset A |>.2 fun i _ =>
      (tendsto_rpow_const_zero hApos).eventually_lt_const (pow_pos ha _)
  have h2 : ∀ᶠ ε : ℝ in 𝓝 0, ∀ i ∈ A, ε ^ ((A.card : ℝ)⁻¹ * ((2 * k i : ℕ) : ℝ)⁻¹) < ρ / 2 :=
    Filter.eventually_all_finset A |>.2 fun i hi => by
      have hki : 0 < (A.card : ℝ)⁻¹ * ((2 * k i : ℕ) : ℝ)⁻¹ := by
        have := hkA i hi
        positivity
      exact (tendsto_rpow_const_zero hki).eventually_lt_const (by linarith)
  have h3 : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  obtain ⟨ε, hε, h1ε, h2ε⟩ :=
    (h3.and ((h1.and h2).filter_mono nhdsWithin_le_nhds)).exists
  refine ⟨c * ε, mul_pos hc hε, fun i hi => ?_, fun i hi => ?_⟩
  · rw [mul_div_cancel_left₀ _ hc.ne']
    exact h1ε i hi
  · rw [mul_div_cancel_left₀ _ hc.ne']
    linarith [h2ε i hi]

omit hδ hδa in
include hk0 hu_cont hu_tan hc hu_lb ha hϕm hϕ0 hφm hφint in
/-- ★★★ **The coordinate-free expansion of a chart box from a holomorphic packet**: for a chart
with active set `A`, orders `(k, h)`, positive tangential unit `u ≥ c` on `[0,a]^d`, and a
holomorphic box extension of the analytic prior factor `ϕ` and the observable `φ`, there is a
collar level `δ` for which `∫_{[0,a]^d} φ · ∏|y_i|^{h_i} ϕ · e^{−n u ∏_{i∈A} y_i^{2k_i}}` has the
coordinate-free expansion on the chart strata with log degree `|A| − 1`, with the certificates
built from the face series of the extension rescaled by the unit-corrected widthsC. -/
theorem hasCoordFreeExpansion_chart_of_holomorphicBoxExtension (hA : A.Nonempty)
    (P : HolomorphicBoxExtension a ϕ φ) :
    ∃ (δ : ℝ) (hδ : 0 < δ) (hδa : ∀ i ∈ A, (δ / c) ^ ((A.card : ℝ)⁻¹) < a ^ (2 * k i))
      (hsmall : ∀ (I : Idx A) (i : Fin (nI A I + 1)),
        2 * (δ / c) ^ ((A.card : ℝ)⁻¹ * ((2 * k (σI A I i).1 : ℕ) : ℝ)⁻¹) <
          (P.faceSeries a (toNonemptyIdx A I)).ρ),
      (ChartModel.normalData d A k h hkA).HasCoordFreeExpansion
        (certificate A k h hkA hk0 u a δ hδ hu_cont ϕ φ hu_tan hc hu_lb ha hδa hϕm hϕ0 hφint
          (fun I => toChartFaceSeries A k h hkA hk0 u a δ hδ
            hu_cont c hc hu_lb ha
            (P.faceSeries a (toNonemptyIdx A I)) (hsmall I)) hA).stratumMeasure
        (coeffCertificate A k h hkA hk0 u a δ hδ hu_cont ϕ φ hu_tan hc hu_lb ha hδa hϕm hϕ0 hφint
          (fun I => toChartFaceSeries A k h hkA hk0 u a δ hδ
            hu_cont c hc hu_lb ha
            (P.faceSeries a (toNonemptyIdx A I)) (hsmall I)) hA).field
        (spectrumLe (commonQ (certificate A k h hkA hk0 u a δ hδ hu_cont ϕ φ hu_tan hc hu_lb ha hδa
          hϕm hϕ0 hφint (fun I => toChartFaceSeries A k h hkA
            hk0 u a δ hδ hu_cont c hc hu_lb ha
            (P.faceSeries a (toNonemptyIdx A I)) (hsmall I)) hA).cores.k) (A.card - 1))
        (piBox d (Icc 0 a)) (ChartModel.phase d A k u) (fun w => wgt h w * ϕ w) φ := by
  obtain ⟨δ, hδ, hδa, hsm⟩ := exists_delta_chart A k hkA a c hc ha hA (P.radius_pos a)
  have hsmall : ∀ (I : Idx A) (i : Fin (nI A I + 1)),
      2 * (δ / c) ^ ((A.card : ℝ)⁻¹ * ((2 * k (σI A I i).1 : ℕ) : ℝ)⁻¹) <
        (P.faceSeries a (toNonemptyIdx A I)).ρ :=
    fun I i => hsm (σI A I i).1 (amb_subset A I (σI A I i).2)
  exact ⟨δ, hδ, hδa, hsmall, hasCoordFreeExpansion_chart_of_face A k h hkA hk0 u a δ hδ hu_cont
    hu_tan c hc hu_lb ha hδa hϕm hϕ0 hφm hφint hA (fun I => P.faceSeries a (toNonemptyIdx A I))
    hsmall⟩

end ChartCollar

end Grammar
