/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.GlobalLaplaceMeasureBasic
import Grammar.SpatialEnergyLaw
import Grammar.PopulationPositivity

/-!
# The face measure of a weighted normal block (CCXCI)

The second unit of the global programme (consult #89): the finite measure on `base × unitBox`
whose integrals are the residual-face coefficient functionals of the library's leading cells.

A `FaceWeightData t r` consists of a compact tangential base with a nonnegative integrable weight
`β_w`, normal exponent data `(h, k)` with a pair value `l ≤ (h_a+1)/(2k_a)`, and a nonnegative
amplitude factor `B` continuous and bounded on `base × unitBox`. Its **face measure**
`ν = (β_w(z) B(z,u) residualWeight(u)) · vol|_{base × unitBox}` is finite
(`FaceWeightData.instIsFiniteMeasure`), and for every bounded measurable `g`
`∫ g dν = ∫_{base} β_w(z) ∫_{unitBox} B(z,u) residualWeight(u) g(z,u) du dz`
(`FaceWeightData.integral_measure`) — exactly the shape of the reflected cell coefficient
`reflected_coeff_eq` once `g` is the observable pulled back to the face and `B` collects the
Jacobian unit, the tangential monomial, the prior, the frozen phase unit `u^{−λ}` and the box
constants. The pieces of the strata coefficient (`LeadingFacePiece`) are these measures pushed to
the parameter space along the chart maps (next unit).
-/

open MeasureTheory Set Filter Topology

namespace Grammar

/-- **Face weight data**: a compact base with a nonnegative integrable weight, normal exponents with
a dominated pair value, and a nonnegative bounded continuous amplitude factor on `base × unitBox`.
-/
structure FaceWeightData (t r : ℕ) where
  /-- The tangential base. -/
  base : Set (Fin t → ℝ)
  base_compact : IsCompact base
  /-- The base weight. -/
  βw : (Fin t → ℝ) → ℝ
  βw_meas : Measurable βw
  βw_nonneg : ∀ z, 0 ≤ βw z
  βw_int : IntegrableOn βw base
  /-- The density exponents. -/
  h : Fin r → ℕ
  /-- The half phase exponents. -/
  k : Fin r → ℕ
  k_pos : ∀ a, 0 < k a
  /-- The pair value. -/
  l : ℝ
  l_le : ∀ a, l ≤ ratioExp h k a
  /-- The amplitude factor (Jacobian unit, tangential monomial, prior, frozen phase unit, box
  constants). -/
  B : (Fin t → ℝ) → (Fin r → ℝ) → ℝ
  B_cont : ContinuousOn (Function.uncurry B) (base ×ˢ unitBox r)
  B_nonneg : ∀ z u, 0 ≤ B z u
  /-- A bound for the amplitude factor on the region. -/
  M : ℝ
  B_le : ∀ z ∈ base, ∀ u ∈ unitBox r, B z u ≤ M

namespace FaceWeightData

variable {t r : ℕ} (D : FaceWeightData t r)

/-- The region `base × unitBox`. -/
def region : Set ((Fin t → ℝ) × (Fin r → ℝ)) := D.base ×ˢ unitBox r

theorem measurableSet_region : MeasurableSet D.region :=
  D.base_compact.isClosed.measurableSet.prod (measurableSet_unitBox r)

/-- The real density `β_w(z) B(z,u) residualWeight(u)`. -/
noncomputable def weight (q : (Fin t → ℝ) × (Fin r → ℝ)) : ℝ :=
  D.βw q.1 * B D q.1 q.2 * residualWeight D.h D.k D.l q.2

theorem weight_nonneg {q : (Fin t → ℝ) × (Fin r → ℝ)} (hq : q ∈ D.region) : 0 ≤ D.weight q :=
  mul_nonneg (mul_nonneg (D.βw_nonneg _) (D.B_nonneg _ _))
    (residualWeight_nonneg _ _ _ _ hq.2)

theorem M_nonneg (hne : D.region.Nonempty) : 0 ≤ D.M := by
  obtain ⟨q, hq⟩ := hne
  exact (D.B_nonneg q.1 q.2).trans (D.B_le q.1 hq.1 q.2 hq.2)

/-- The restricted volume of the region equals the product of the restricted volumes. -/
theorem restrict_region_eq :
    (volume : Measure ((Fin t → ℝ) × (Fin r → ℝ))).restrict D.region =
      (volume.restrict D.base).prod (volume.restrict (unitBox r)) := by
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  rfl

theorem aestronglyMeasurable_weight :
    AEStronglyMeasurable D.weight (volume.restrict D.region) := by
  refine AEStronglyMeasurable.mul (AEStronglyMeasurable.mul ?_ ?_) ?_
  · exact (D.βw_meas.comp measurable_fst).aestronglyMeasurable
  · exact D.B_cont.aestronglyMeasurable D.measurableSet_region
  · exact ((measurable_residualWeight D.h D.k D.l).comp measurable_snd).aestronglyMeasurable

/-- The product weight `β_w(z) residualWeight(u)` is integrable on the region. -/
theorem integrable_prod_weight :
    Integrable (fun q : (Fin t → ℝ) × (Fin r → ℝ) => D.βw q.1 * residualWeight D.h D.k D.l q.2)
      (volume.restrict D.region) := by
  rw [restrict_region_eq]
  exact D.βw_int.mul_prod (residualWeight_integrableOn D.h D.k D.k_pos D.l D.l_le)

/-- **The density times a bounded measurable function is integrable on the region.** -/
theorem integrable_weight_mul {g : (Fin t → ℝ) × (Fin r → ℝ) → ℝ}
    (hg : AEStronglyMeasurable g (volume.restrict D.region)) {Mg : ℝ}
    (hgM : ∀ q ∈ D.region, |g q| ≤ Mg) :
    Integrable (fun q => D.weight q * g q) (volume.restrict D.region) := by
  refine ((D.integrable_prod_weight.const_mul (D.M * Mg))).mono'
    (D.aestronglyMeasurable_weight.mul hg) ?_
  rw [ae_restrict_iff' D.measurableSet_region]
  refine Eventually.of_forall fun q hq => ?_
  have hβ := D.βw_nonneg q.1
  have hres := residualWeight_nonneg D.h D.k D.l q.2 hq.2
  have hB0 := D.B_nonneg q.1 q.2
  have hB := D.B_le q.1 hq.1 q.2 hq.2
  have hg0 := (abs_nonneg (g q)).trans (hgM q hq)
  have hgq := hgM q hq
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (D.weight_nonneg hq)]
  unfold weight
  have hβM : 0 ≤ D.βw q.1 * D.M := mul_nonneg hβ (hB0.trans hB)
  calc D.βw q.1 * D.B q.1 q.2 * residualWeight D.h D.k D.l q.2 * |g q|
      ≤ D.βw q.1 * D.M * residualWeight D.h D.k D.l q.2 * Mg :=
        mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hB hβ) le_rfl hres hβM) hgq
          (abs_nonneg _) (mul_nonneg hβM hres)
    _ = D.M * Mg * (D.βw q.1 * residualWeight D.h D.k D.l q.2) := by ring

theorem integrable_weight : Integrable D.weight (volume.restrict D.region) := by
  have := D.integrable_weight_mul (g := fun _ => (1 : ℝ)) aestronglyMeasurable_const
    (Mg := 1) (fun _ _ => by simp)
  simpa using this

/-- **The face measure** `(β_w B residualWeight) · vol|_{base × unitBox}`. -/
noncomputable def measure : Measure ((Fin t → ℝ) × (Fin r → ℝ)) :=
  (volume.restrict D.region).withDensity fun q => ((D.weight q).toNNReal : ENNReal)

theorem aemeasurable_toNNReal_weight :
    AEMeasurable (fun q => (D.weight q).toNNReal) (volume.restrict D.region) :=
  measurable_real_toNNReal.comp_aemeasurable D.aestronglyMeasurable_weight.aemeasurable

theorem integrable_coe_toNNReal_weight :
    Integrable (fun q => ((D.weight q).toNNReal : ℝ)) (volume.restrict D.region) := by
  refine D.integrable_weight.norm.mono'
    (NNReal.continuous_coe.measurable.comp_aemeasurable
      D.aemeasurable_toNNReal_weight).aestronglyMeasurable (Eventually.of_forall fun q => ?_)
  rw [Real.coe_toNNReal', Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (le_max_right _ _)]
  exact max_le (le_abs_self _) (abs_nonneg _)

instance : IsFiniteMeasure D.measure := by
  refine isFiniteMeasure_withDensity ?_
  rw [lintegral_coe_eq_integral _ D.integrable_coe_toNNReal_weight]
  exact ENNReal.ofReal_ne_top

/-- ★ **Integrals against the face measure are the iterated face integrals**: for `g` bounded and
measurable on the region, `∫ g dν = ∫_{base} β_w(z) ∫_{unitBox} B(z,u) residualWeight(u) g(z,u)`.
-/
theorem integral_measure {g : (Fin t → ℝ) × (Fin r → ℝ) → ℝ}
    (hg : AEStronglyMeasurable g (volume.restrict D.region)) {Mg : ℝ}
    (hgM : ∀ q ∈ D.region, |g q| ≤ Mg) :
    ∫ q, g q ∂D.measure = ∫ z in D.base, D.βw z *
      ∫ u in unitBox r, D.B z u * residualWeight D.h D.k D.l u * g (z, u) := by
  unfold measure
  rw [integral_withDensity_eq_integral_smul₀ D.aemeasurable_toNNReal_weight]
  have h1 : ∫ q, (D.weight q).toNNReal • g q ∂(volume.restrict D.region) =
      ∫ q, D.weight q * g q ∂(volume.restrict D.region) := by
    refine integral_congr_ae ?_
    rw [Filter.EventuallyEq, ae_restrict_iff' D.measurableSet_region]
    refine Eventually.of_forall fun q hq => ?_
    simp only [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (D.weight_nonneg hq)]
  rw [h1, restrict_region_eq,
    integral_prod _ (by rw [← restrict_region_eq]; exact D.integrable_weight_mul hg hgM)]
  refine setIntegral_congr_fun D.base_compact.isClosed.measurableSet fun z _ => ?_
  rw [← integral_const_mul]
  refine setIntegral_congr_fun (measurableSet_unitBox r) fun u _ => ?_
  unfold weight
  ring

/-- The face measure is concentrated on the region. -/
theorem measure_compl_region : D.measure D.regionᶜ = 0 := by
  unfold measure
  rw [withDensity_apply _ D.measurableSet_region.compl, Measure.restrict_restrict
    D.measurableSet_region.compl, compl_inter_self, Measure.restrict_empty, lintegral_zero_measure]

end FaceWeightData

end Grammar
