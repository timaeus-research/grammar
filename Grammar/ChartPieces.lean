/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.ChartBoxInputs
import Grammar.SignedBoxPackets
import Grammar.CoreTransport

/-!
# The orthant pieces of a chart on a symmetric box (consult #111, unit G)

A chart box `[−a,a]^d` with active set `A`, orders `(k, h)`, a positive tangential unit `u` and a
holomorphic signed-box packet `P` for the analytic prior factor `ϕ` and the observable `φ`
decomposes into its `2^d` orthant boxes `R_σ [0,a]^d` (phase G, CCCXXXVI). On the orthant `σ` the
reflected data `u ∘ R_σ`, `ϕ ∘ R_σ`, `φ ∘ R_σ` and the pulled-back packet `P.pullback σ` are inputs
of the chart-box producer (CCCLXXIII): the phase and the Jacobian weight are even
(`chartPhase_refl`, `wgt_refl`), the reflected unit is tangential and bounded below
(`unitR_tan`, `unitR_lb`). This module gives the PIECE certificate `pieceCert σ` on `[0,a]^d`, its
coefficient certificate and expansion, the push-forward identity of its localisation measure onto
the orthant box (`map_refl_pieceMeasure`), the integrability transfer, and a common collar level
for a finite set of selected orthants (`exists_delta_pieces`). The assembly of the pieces of a
domain-sector atlas on the sheet geometry is unit H. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Grammar

namespace ChartCollar

open NormalisedBox WaterFilling CoordModel CoeffFamily

variable {d : ℕ}

/-! ### Reflected data -/

/-- The reflected unit `u ∘ R_σ`. -/
def unitR (u : (Fin d → ℝ) → ℝ) (σ : CoordSign d) : (Fin d → ℝ) → ℝ := u ∘ refl σ

theorem unitR_tan {A : Finset (Fin d)} {u : (Fin d → ℝ) → ℝ}
    (hu_tan : ∀ w w' : Fin d → ℝ, (∀ j, j ∉ A → w j = w' j) → u w = u w') (σ : CoordSign d) :
    ∀ w w' : Fin d → ℝ, (∀ j, j ∉ A → w j = w' j) → unitR u σ w = unitR u σ w' :=
  fun _ _ hw => hu_tan _ _ fun j hj => by simp only [refl_apply, hw j hj]

theorem unitR_lb {u : (Fin d → ℝ) → ℝ} {a c : ℝ}
    (hu_lb : ∀ w ∈ piBox d (Icc (-a) a), c ≤ u w) (σ : CoordSign d) :
    ∀ w ∈ piBox d (Icc 0 a), c ≤ unitR u σ w :=
  fun _ hw => hu_lb _ (refl_mem_signedBox hw)

theorem continuous_unitR {u : (Fin d → ℝ) → ℝ} (hu_cont : Continuous u) (σ : CoordSign d) :
    Continuous (unitR u σ) :=
  hu_cont.comp (continuous_refl σ)

/-- The chart phase is even: `K(R_σ w) = (u ∘ R_σ)(w) · ∏_{A} w^{2k}`. -/
theorem chartPhase_refl (A : Finset (Fin d)) (k : Fin d → ℕ) (u : (Fin d → ℝ) → ℝ)
    (σ : CoordSign d) (w : Fin d → ℝ) :
    ChartModel.phase d A k u (refl σ w) = ChartModel.phase d A k (unitR u σ) w := by
  unfold ChartModel.phase ChartModel.monoPhase unitR
  simp only [Function.comp]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [refl_apply, mul_pow, pow_mul, sq_sgn, one_pow, one_mul]

/-- The Jacobian weight is even. -/
theorem wgt_refl (h : Fin d → ℕ) (σ : CoordSign d) (w : Fin d → ℝ) :
    wgt h (refl σ w) = wgt h w := by
  unfold wgt
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [refl_apply, abs_mul, abs_sgn, one_mul]

/-! ### The piece measure and its push-forward -/

/-- The localisation measure of the piece `σ`: the weighted reflected prior on `[0,a]^d`. -/
noncomputable def pieceMeasure (h : Fin d → ℕ) (a : ℝ) (ϕ : (Fin d → ℝ) → ℝ) (σ : CoordSign d) :
    Measure (Fin d → ℝ) :=
  (volume.restrict (piBox d (Icc 0 a))).withDensity fun w => ENNReal.ofReal (wgt h w * ϕ (refl σ w))

theorem refl_preimage_orthantBox (σ : CoordSign d) (a : ℝ) :
    refl σ ⁻¹' orthantBox σ a = piBox d (Icc 0 a) := by
  ext w
  simp only [orthantBox, mem_preimage, refl_refl]

/-- ★ **The piece measure pushed by the reflection is the weighted prior on the orthant box.** -/
theorem map_refl_pieceMeasure (h : Fin d → ℕ) (a : ℝ) (ϕ : (Fin d → ℝ) → ℝ) (σ : CoordSign d) :
    (pieceMeasure h a ϕ σ).map (refl σ) =
      (volume.restrict (orthantBox σ a)).withDensity fun w => ENNReal.ofReal (wgt h w * ϕ w) := by
  have h1 : (volume.restrict (piBox d (Icc 0 a))).map (reflEquiv σ) =
      volume.restrict (orthantBox σ a) := by
    rw [← refl_preimage_orthantBox σ a]
    change (volume.restrict ((reflEquiv σ) ⁻¹' orthantBox σ a)).map (reflEquiv σ) = _
    rw [← MeasurableEquiv.restrict_map, map_reflEquiv_volume]
  have h2 := withDensity_map_equiv (volume.restrict (piBox d (Icc 0 a))) (reflEquiv σ)
    fun w => ENNReal.ofReal (wgt h w * ϕ w)
  rw [h1] at h2
  rw [h2]
  change (pieceMeasure h a ϕ σ).map (refl σ) = ((volume.restrict (piBox d (Icc 0 a))).withDensity
    fun w => ENNReal.ofReal (wgt h (refl σ w) * ϕ (refl σ w))).map (refl σ)
  unfold pieceMeasure
  simp only [wgt_refl]

/-- The weighted prior on the orthant box is bounded by the weighted prior on the signed box. -/
theorem orthant_withDensity_le (h : Fin d → ℕ) (a : ℝ) (ϕ : (Fin d → ℝ) → ℝ) (σ : CoordSign d) :
    ((volume.restrict (orthantBox σ a)).withDensity fun w => ENNReal.ofReal (wgt h w * ϕ w)) ≤
      (volume.restrict (piBox d (Icc (-a) a))).withDensity
        fun w => ENNReal.ofReal (wgt h w * ϕ w) := by
  intro s
  rw [withDensity_apply', withDensity_apply']
  exact lintegral_mono' (Measure.restrict_mono subset_rfl
    (Measure.restrict_mono (orthantBox_subset σ a) le_rfl)) le_rfl

/-- Integrability of the observable transfers to the reflected piece. -/
theorem integrable_piece (h : Fin d → ℕ) (a : ℝ) (ϕ φ : (Fin d → ℝ) → ℝ) (hφm : Measurable φ)
    (hφint : Integrable φ ((volume.restrict (piBox d (Icc (-a) a))).withDensity
      fun w => ENNReal.ofReal (wgt h w * ϕ w))) (σ : CoordSign d) :
    Integrable (φ ∘ refl σ) (pieceMeasure h a ϕ σ) := by
  have h1 : Integrable φ ((pieceMeasure h a ϕ σ).map (refl σ)) := by
    rw [map_refl_pieceMeasure]
    exact hφint.mono_measure (orthant_withDensity_le h a ϕ σ)
  exact (integrable_map_measure hφm.aestronglyMeasurable (measurable_refl σ).aemeasurable).1 h1

/-! ### The piece certificate -/

variable (A : Finset (Fin d)) (k h : Fin d → ℕ) (hkA : ∀ i ∈ A, 0 < k i)
  (hk0 : ∀ i, i ∉ A → k i = 0) (u : (Fin d → ℝ) → ℝ) (a δ : ℝ) (hδ : 0 < δ) (hu_cont : Continuous u)
  (ϕ φ : (Fin d → ℝ) → ℝ)
  (hu_tan : ∀ w w' : Fin d → ℝ, (∀ j, j ∉ A → w j = w' j) → u w = u w')
  (c : ℝ) (hc : 0 < c) (hu_lb : ∀ w ∈ piBox d (Icc (-a) a), c ≤ u w) (ha : 0 < a)
  (hδa : ∀ i ∈ A, (δ / c) ^ ((A.card : ℝ)⁻¹) < a ^ (2 * k i))
  (hϕm : Measurable ϕ) (hϕ0 : ∀ w, 0 ≤ ϕ w) (hφm : Measurable φ)
  (hφint : Integrable φ ((volume.restrict (piBox d (Icc (-a) a))).withDensity
    fun w => ENNReal.ofReal (wgt h w * ϕ w)))
  (P : HolomorphicSignedBoxExtension a ϕ φ) (σ : CoordSign d)
  (hsmall : ∀ (I : Idx A) (i : Fin (nI A I + 1)),
    2 * (δ / c) ^ ((A.card : ℝ)⁻¹ * ((2 * k (σI A I i).1 : ℕ) : ℝ)⁻¹) <
      ((P.pullback σ).faceSeries a (toNonemptyIdx A I)).ρ)
  (hA : A.Nonempty)

include hk0 hδ hu_cont hu_tan hc hu_lb ha hδa hϕm hϕ0 hφm hφint hsmall hA in
/-- ★★ **The piece certificate of the orthant `σ`**: the chart-box certificate of the reflected
data on `[0,a]^d`. -/
noncomputable def pieceCert :
    ResolvedCertificate (ChartModel.geometry d A k h hkA) (ChartModel.normalData d A k h hkA)
      (piBox d (Icc 0 a)) (ChartModel.phase d A k (unitR u σ))
      (fun w => wgt h w * (ϕ ∘ refl σ) w) (φ ∘ refl σ) :=
  certificate A k h hkA hk0 (unitR u σ) a δ hδ (continuous_unitR hu_cont σ) (ϕ ∘ refl σ)
    (φ ∘ refl σ) (unitR_tan hu_tan σ) hc (unitR_lb hu_lb σ) ha hδa
    (hϕm.comp (measurable_refl σ)) (fun _ => hϕ0 _) (integrable_piece h a ϕ φ hφm hφint σ)
    (fun I => toChartFaceSeries A k h hkA hk0 (unitR u σ) a δ hδ (continuous_unitR hu_cont σ) c hc
      (unitR_lb hu_lb σ) ha ((P.pullback σ).faceSeries a (toNonemptyIdx A I)) (hsmall I)) hA

include hk0 hδ hu_cont hu_tan hc hu_lb ha hδa hϕm hϕ0 hφm hφint hsmall hA in
/-- The coefficient certificate of the piece. -/
noncomputable def pieceCoeff :
    (pieceCert A k h hkA hk0 u a δ hδ hu_cont ϕ φ hu_tan c hc hu_lb ha hδa hϕm hϕ0 hφm hφint P σ
      hsmall hA).CoefficientCertificate :=
  coeffCertificate A k h hkA hk0 (unitR u σ) a δ hδ (continuous_unitR hu_cont σ) (ϕ ∘ refl σ)
    (φ ∘ refl σ) (unitR_tan hu_tan σ) hc (unitR_lb hu_lb σ) ha hδa
    (hϕm.comp (measurable_refl σ)) (fun _ => hϕ0 _) (integrable_piece h a ϕ φ hφm hφint σ)
    (fun I => toChartFaceSeries A k h hkA hk0 (unitR u σ) a δ hδ (continuous_unitR hu_cont σ) c hc
      (unitR_lb hu_lb σ) ha ((P.pullback σ).faceSeries a (toNonemptyIdx A I)) (hsmall I)) hA

include hk0 hδ hu_cont hu_tan hc hu_lb ha hδa hϕm hϕ0 hφm hφint hsmall hA in
theorem pieceCert_L_μ :
    (pieceCert A k h hkA hk0 u a δ hδ hu_cont ϕ φ hu_tan c hc hu_lb ha hδa hϕm hϕ0 hφm hφint P σ
      hsmall hA).L.μ = pieceMeasure h a ϕ σ := rfl

include hk0 hδ hu_cont hu_tan hc hu_lb ha hδa hϕm hϕ0 hφm hφint hsmall hA in
/-- ★★ **The expansion of the piece**: log degree `|A| − 1`. -/
theorem piece_expansion :
    (ChartModel.normalData d A k h hkA).HasCoordFreeExpansion
      (pieceCert A k h hkA hk0 u a δ hδ hu_cont ϕ φ hu_tan c hc hu_lb ha hδa hϕm hϕ0 hφm hφint P
        σ hsmall hA).stratumMeasure
      (pieceCoeff A k h hkA hk0 u a δ hδ hu_cont ϕ φ hu_tan c hc hu_lb ha hδa hϕm hϕ0 hφm hφint P
        σ hsmall hA).field
      (spectrumLe (commonQ (pieceCert A k h hkA hk0 u a δ hδ hu_cont ϕ φ hu_tan c hc hu_lb ha hδa
        hϕm hϕ0 hφm hφint P σ hsmall hA).cores.k) (A.card - 1))
      (piBox d (Icc 0 a)) (ChartModel.phase d A k (unitR u σ))
      (fun w => wgt h w * (ϕ ∘ refl σ) w) (φ ∘ refl σ) :=
  hasCoordFreeExpansion_chart_of_face A k h hkA hk0 (unitR u σ) a δ hδ (continuous_unitR hu_cont σ)
    (unitR_tan hu_tan σ) c hc (unitR_lb hu_lb σ) ha hδa (hϕm.comp (measurable_refl σ))
    (fun _ => hϕ0 _) (hφm.comp (measurable_refl σ)) (integrable_piece h a ϕ φ hφm hφint σ) hA
    (fun I => (P.pullback σ).faceSeries a (toNonemptyIdx A I)) hsmall

/-! ### The cores lie in the box -/

omit hφm P σ hsmall hA in
include hk0 hδ hu_cont hu_tan hc ha hϕm hϕ0 in
/-- The core parametrisation of every stratum lands in the box, a.e. on the chart measure. -/
theorem stratumCore_Φ_mem_box (hu_lb' : ∀ w ∈ piBox d (Icc 0 a), c ≤ u w)
    (hδa' : ∀ i ∈ A, (δ / c) ^ ((A.card : ℝ)⁻¹) < a ^ (2 * k i))
    (hφint' : Integrable φ ((volume.restrict (piBox d (Icc 0 a))).withDensity
      fun w => ENNReal.ofReal (wgt h w * ϕ w)))
    (F : ∀ I : Idx A, FaceSeries A k h hkA u a δ ϕ φ I) (I : Idx A) :
    ∀ᵐ q ∂chartMeasure (baseMeasure (amb A I) (eI A k h hkA u a δ I)) (nI A I)
      (side k (amb A I) δ),
      (stratumCore A k h hkA hk0 u a δ hδ hu_cont ϕ φ hu_tan hc hu_lb' ha hδa' hϕm hϕ0 hφint' F
        I).Φ q ∈ piBox d (Icc 0 a) := by
  have := compactSpace_KI A k h hkA u a δ hδ hu_cont I
  have := isFiniteMeasure_baseMeasure (amb A I) (eI A k h hkA u a δ I)
    (continuous_eI A k h hkA u a δ I) (eI_injective A k h hkA u a δ I)
  filter_upwards [ae_snd_mem_box (baseMeasure (amb A I) (eI A k h hkA u a δ I)) (nI A I)
    (side k (amb A I) δ)]
  rintro ⟨s, v⟩ hv
  change Φ (amb A I) (σI A I) (eI A k h hkA u a δ I) (lamT k u (amb A I) δ) (s, v) ∈ _
  exact image_subset_box A k u (amb A I) a δ (eI A k h hkA u a δ I) (range_eI A k h hkA u a δ hδ I)
    hδ hkA hk0 (amb_nonempty A I) (amb_subset A I) hc hu_lb' ha hδa'
    (mem_image_Φ (amb A I) (σI A I) (eI A k h hkA u a δ I) (lamT k u (amb A I) δ)
      (toWData A k h hkA hk0 u a δ hδ hu_cont ϕ φ hc hu_lb' ha hδa' (F I)).hpos s hv)

/-! ### A common collar level for finitely many pieces -/

omit hδ hu_cont hu_tan hu_lb hδa hϕm hϕ0 hφm hφint P σ hsmall in
include hkA hc ha hA in
/-- ★ **A common level for a finite set of orthants**: one `δ` below all the packet radii. -/
theorem exists_delta_pieces (P : HolomorphicSignedBoxExtension a ϕ φ) (S : Finset (CoordSign d))
    (hS : S.Nonempty) :
    ∃ δ : ℝ, 0 < δ ∧ (∀ i ∈ A, (δ / c) ^ ((A.card : ℝ)⁻¹) < a ^ (2 * k i)) ∧
      ∀ σ ∈ S, ∀ (I : Idx A) (i : Fin (nI A I + 1)),
        2 * (δ / c) ^ ((A.card : ℝ)⁻¹ * ((2 * k (σI A I i).1 : ℕ) : ℝ)⁻¹) <
          ((P.pullback σ).faceSeries a (toNonemptyIdx A I)).ρ := by
  have hmin : 0 < S.inf' hS fun σ => (P.pullback σ).radius a := by
    rw [Finset.lt_inf'_iff]
    exact fun σ _ => (P.pullback σ).radius_pos a
  obtain ⟨δ, hδ, hδa, hsm⟩ := exists_delta_chart A k hkA a c hc ha hA hmin
  refine ⟨δ, hδ, hδa, fun σ hσ I i => ?_⟩
  change 2 * (δ / c) ^ ((A.card : ℝ)⁻¹ * ((2 * k (σI A I i).1 : ℕ) : ℝ)⁻¹) <
    (P.pullback σ).radius a
  exact (hsm (σI A I i).1 (amb_subset A I (σI A I i).2)).trans_le
    (Finset.inf'_le (fun σ => (P.pullback σ).radius a) hσ)

end ChartCollar

end Grammar
