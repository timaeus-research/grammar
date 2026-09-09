/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.SpatialIndependenceConverse

/-!
# Independence of energy and face location iff essential face constancy

The face-location law `ν^ξ = μ_P · J_λ(ξ)` and the weighted base face measure `μ_P` are mutually
absolutely continuous (`J_λ > 0`), so a `ν^ξ`-a.e. statement about the face phase transfers to the
box: for a.e. `u` in the box with `η(P_J u) w(u) ≠ 0`, `ξ(P_J u) = a` (`ae_box_of_ae_faceLocation`).
This is exactly what the disintegration formula needs, giving the missing direction of the
product form: `ξ = a` `ν^ξ`-a.e. ⇒ `Q̃^ξ = ρ_a ⊗ ν^ξ` (`spatialJointFaceLaw_prod_of_ae`).
Combined with the converse (LXXXVI) and the strict monotonicity of the tilted mean:

* `spatialJointFaceLaw_prod_iff_ae`: `Q̃^ξ = ρ_a ⊗ ν^ξ ↔ ξ = a` `ν^ξ`-a.e. (fixed `a`);
* `spatialJointFaceLaw_indep_iff`: energy and face location are independent under `Q̃^ξ` iff the
  face phase is `ν^ξ`-essentially constant.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

variable {n : ℕ} (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {l β : ℝ} (hl : 0 < l) (hβ : 0 < β)
  (hmin : ∀ i, l ≤ ratioExp h k i) {ξ η : (Fin (n + 1) → ℝ) → ℝ} (hξc : Continuous ξ)
  (hηc : Continuous η) (hηnn : ∀ v ∈ closedCube (n + 1), 0 ≤ η v)
  (hZ : 0 < spatialMass h k l β ξ η)

include hk hl hβ hmin hξc hηc hηnn hZ

/-- `ν^ξ ≪ μ_P`. -/
theorem faceLocationLimit_absolutelyContinuous :
    faceLocationLimit h k l β ξ η ≪ faceBaseMeasure h k l β ξ η := by
  rw [faceLocationLimit_eq_withDensity h k hk hl hβ hmin hξc hηc hηnn hZ]
  exact withDensity_absolutelyContinuous _ _

/-- `μ_P ≪ ν^ξ` (the density `J_λ(ξ(v))` is everywhere positive). -/
theorem faceBaseMeasure_absolutelyContinuous :
    faceBaseMeasure h k l β ξ η ≪ faceLocationLimit h k l β ξ η := by
  rw [faceLocationLimit_eq_withDensity h k hk hl hβ hmin hξc hηc hηnn hZ]
  have hJm : Measurable fun v => ENNReal.ofReal (fluctMoment β (ξ v) 0 l 0) :=
    ((continuous_fluctMoment_phase β hβ hl).comp hξc).measurable.ennreal_ofReal
  refine Measure.AbsolutelyContinuous.mk fun s hs h0 => ?_
  rw [withDensity_apply _ hs, lintegral_eq_zero_iff' hJm.aemeasurable] at h0
  have h1 := (ae_restrict_iff' hs).1 h0
  refine compl_mem_ae_iff.1 ?_
  filter_upwards [h1] with v hv hvs
  have := hv hvs
  simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at this
  exact absurd this (not_le.2 (fluctMoment_pos β (ξ v) l hβ hl))

/-- A `ν^ξ`-a.e. value of the face phase transfers to the box: for a.e. `u` in the box with
`η(P_J u) w(u) ≠ 0`, `ξ(P_J u) = a`. -/
theorem ae_box_of_ae_faceLocation {a : ℝ}
    (hae : ∀ᵐ v ∂(faceLocationLimit h k l β ξ η), ξ v = a) :
    ∀ᵐ u ∂(volume.restrict (unitBox (n + 1))),
      faceWeight h k l η u ≠ 0 → ξ (faceProj h k l u) = a := by
  have hae' : ∀ᵐ v ∂(faceBaseMeasure h k l β ξ η), ξ v = a :=
    (faceBaseMeasure_absolutelyContinuous h k hk hl hβ hmin hξc hηc hηnn hZ).ae_le hae
  unfold faceBaseMeasure at hae'
  rw [ae_map_iff (measurable_faceProj h k l).aemeasurable (p := fun v => ξ v = a)
    (hξc.measurable (measurableSet_singleton a))] at hae'
  have hwm : Measurable fun u => ENNReal.ofReal (faceWeight h k l η u / spatialMass h k l β ξ η) :=
    ((measurable_faceWeight h k l hηc).div_const _).ennreal_ofReal
  rw [ae_withDensity_iff' hwm.aemeasurable] at hae'
  filter_upwards [hae', ae_restrict_mem (measurableSet_unitBox _)] with u hu hmem hw
  refine hu ?_
  have hpos : 0 < faceWeight h k l η u :=
    lt_of_le_of_ne (faceWeight_nonneg h k l hηnn hmem) (Ne.symm hw)
  exact (ENNReal.ofReal_pos.2 (div_pos hpos hZ)).ne'

/-- **The a.e. product form**: if the face phase is `ν^ξ`-a.e. equal to `a`, then
`Q̃^ξ = ρ_a ⊗ ν^ξ`. -/
theorem spatialJointFaceLaw_prod_of_ae {a : ℝ}
    (hae : ∀ᵐ v ∂(faceLocationLimit h k l β ξ η), ξ v = a) :
    spatialJointFaceLaw h k l β ξ η = (phaseLaw β a l).prod (faceLocationLimit h k l β ξ η) := by
  have hbox := ae_box_of_ae_faceLocation h k hk hl hβ hmin hξc hηc hηnn hZ hae
  have : Fact (0 < β) := ⟨hβ⟩
  have : Fact (0 < l) := ⟨hl⟩
  have := faceLocationLimit_isProbabilityMeasure h k hk hl hβ hmin hξc hηc hηnn hZ
  have := spatialJointFaceLaw_isProbabilityMeasure h k hk hl hβ hmin hξc hηc hηnn hZ
  symm
  refine Measure.prod_eq fun s t hs ht => ?_
  rw [← ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _)
    (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)), ENNReal.toReal_mul,
    ← measureReal_def, ← measureReal_def, ← measureReal_def, ← integral_indicator_one (hs.prod ht),
    spatialJointFaceLaw_integral_disintegration h k hk hl hβ hmin hξc hηc hηnn hZ
      (measurable_one.indicator (hs.prod ht)) (C := 1) (fun z => by
        simp only [Set.indicator, Pi.one_apply]
        split_ifs <;> simp),
    faceLocationLimit_real_eq h k hk hl hβ hmin hξc hηc hηnn hZ ht, ← mul_div_assoc,
    ← integral_const_mul]
  congr 1
  refine setIntegral_congr_ae (measurableSet_unitBox _) ?_
  filter_upwards [(ae_restrict_iff' (measurableSet_unitBox _)).1 hbox] with u hu hmem
  by_cases hw : faceWeight h k l η u = 0
  · simp [hw]
  · simp only [Set.indicator_prod_one, hu hmem hw]
    rw [integral_mul_const, integral_indicator_one hs]
    ring

/-- For a `ν^ξ`-essentially constant face phase the limiting energy law is `ρ_a`. -/
theorem spatialEnergyLimit_eq_phaseLaw_of_ae {a : ℝ}
    (hae : ∀ᵐ v ∂(faceLocationLimit h k l β ξ η), ξ v = a) :
    spatialEnergyLimit h k l β ξ η = phaseLaw β a l := by
  have := faceLocationLimit_isProbabilityMeasure h k hk hl hβ hmin hξc hηc hηnn hZ
  rw [← spatialJointFaceLaw_fst, spatialJointFaceLaw_prod_of_ae h k hk hl hβ hmin hξc hηc hηnn
    hZ hae, Measure.map_fst_prod, measure_univ, one_smul]

/-- **Fixed-parameter product form iff**: `Q̃^ξ = ρ_a ⊗ ν^ξ` iff `ξ = a` `ν^ξ`-a.e. -/
theorem spatialJointFaceLaw_prod_iff_ae (a : ℝ) :
    spatialJointFaceLaw h k l β ξ η = (phaseLaw β a l).prod (faceLocationLimit h k l β ξ η) ↔
      ∀ᵐ v ∂(faceLocationLimit h k l β ξ η), ξ v = a := by
  refine ⟨fun hprod => ?_, spatialJointFaceLaw_prod_of_ae h k hk hl hβ hmin hξc hηc hηnn hZ⟩
  have := faceLocationLimit_isProbabilityMeasure h k hk hl hβ hmin hξc hηc hηnn hZ
  have hE : spatialEnergyLimit h k l β ξ η = phaseLaw β a l := by
    rw [← spatialJointFaceLaw_fst, hprod, Measure.map_fst_prod, measure_univ, one_smul]
  obtain ⟨a₀, ha₀⟩ := faceConstant_of_indep h k hk hl hβ hmin hξc hηc hηnn hZ
    (by rw [hE]; exact hprod)
  have hE₀ := spatialEnergyLimit_eq_phaseLaw_of_ae h k hk hl hβ hmin hξc hηc hηnn hZ ha₀
  have hmean : phaseLawMean β l a = phaseLawMean β l a₀ := by
    rw [← phaseLaw_mean β a l hβ hl, ← phaseLaw_mean β a₀ l hβ hl, ← hE, hE₀]
  have haa := (phaseLawMean_strictMono β l hβ hl).injective hmean
  filter_upwards [ha₀] with v hv
  rw [hv, haa]

/-- **Independence iff essential face constancy**: under the limiting joint law the energy and the
face location are independent iff the face phase is `ν^ξ`-a.e. constant. -/
theorem spatialJointFaceLaw_indep_iff :
    spatialJointFaceLaw h k l β ξ η =
        (spatialEnergyLimit h k l β ξ η).prod (faceLocationLimit h k l β ξ η) ↔
      ∃ a₀ : ℝ, ∀ᵐ v ∂(faceLocationLimit h k l β ξ η), ξ v = a₀ := by
  refine ⟨faceConstant_of_indep h k hk hl hβ hmin hξc hηc hηnn hZ, fun ⟨a₀, ha₀⟩ => ?_⟩
  rw [spatialEnergyLimit_eq_phaseLaw_of_ae h k hk hl hβ hmin hξc hηc hηnn hZ ha₀]
  exact spatialJointFaceLaw_prod_of_ae h k hk hl hβ hmin hξc hηc hηnn hZ ha₀

end Grammar
