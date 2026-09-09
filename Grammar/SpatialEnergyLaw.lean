/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.SpatialPhaseLeading
import Grammar.PolynomialObservables

/-!
# The posterior energy law under a continuous phase (unit 356; Astra #44 units 2–3, energy part)

The limiting joint law of `(NK, u)` under the phase-`ξ` posterior is
`Q^ξ ∝ η(P_J u) w(u) · y^{λ-1} e^{-βy+βξ(P_J u)√y} dy du` on `(0,∞) × box`
(`spatialJointLaw`); its energy marginal `spatialEnergyLimit` is the evidence-weighted mixture of
the tilted laws `ρ_{ξ(P_J u)}` with weights `η(P_J u) w(u) J_λ(ξ(P_J u))`.  Its Laplace transform
is computed by Fubini (`spatialEnergyLimit_laplace`), and it matches the limit of the weighted
Laplace transform of Headline LXXII, so **the posterior law of `NK` under a fixed continuous phase
converges weakly to the face mixture** (`spatialEnergyLaw_tendsto`): only the restriction of the
phase to the dominant face enters, through the phase-dependent tilt and the evidence weight.
-/

namespace Grammar

open MeasureTheory Filter Topology Set

/-! ### The face weight -/

/-- The face weight `η(P_J u) w(u)`. -/
noncomputable def faceWeight {d : ℕ} (h k : Fin (d + 1) → ℕ) (l : ℝ)
    (η : (Fin (d + 1) → ℝ) → ℝ) (u : Fin (d + 1) → ℝ) : ℝ :=
  η (faceProj h k l u) * residualWeight h k l u

theorem measurable_residualWeight {d : ℕ} (h k : Fin d → ℕ) (l : ℝ) :
    Measurable (residualWeight h k l) := by
  unfold residualWeight
  refine Finset.measurable_prod _ fun i _ => ?_
  split_ifs
  · exact measurable_const
  · exact (measurable_pi_apply i).pow_const _

theorem measurable_faceWeight {d : ℕ} (h k : Fin (d + 1) → ℕ) (l : ℝ)
    {η : (Fin (d + 1) → ℝ) → ℝ} (hηc : Continuous η) : Measurable (faceWeight h k l η) :=
  (hηc.measurable.comp (measurable_faceProj h k l)).mul (measurable_residualWeight h k l)

theorem faceWeight_nonneg {d : ℕ} (h k : Fin (d + 1) → ℕ) (l : ℝ)
    {η : (Fin (d + 1) → ℝ) → ℝ} (hηnn : ∀ v ∈ closedCube (d + 1), 0 ≤ η v)
    {u : Fin (d + 1) → ℝ} (hu : u ∈ unitBox (d + 1)) : 0 ≤ faceWeight h k l η u :=
  mul_nonneg (hηnn _ (faceProj_mem_closedCube h k l (unitBox_subset_closedCube _ hu)))
    (residualWeight_nonneg h k l u hu)

theorem integrableOn_faceWeight {d : ℕ} (h k : Fin (d + 1) → ℕ) (hk : ∀ i, 0 < k i) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) {η : (Fin (d + 1) → ℝ) → ℝ} (hηc : Continuous η) :
    IntegrableOn (faceWeight h k l η) (unitBox (d + 1)) := by
  obtain ⟨C, hC⟩ := (isCompact_closedCube (d + 1)).exists_bound_of_continuousOn
    hηc.continuousOn
  refine Integrable.bdd_mul (c := C) (residualWeight_integrableOn h k hk l hmin)
    (hηc.measurable.comp (measurable_faceProj h k l)).aestronglyMeasurable ?_
  rw [ae_restrict_iff' (measurableSet_unitBox _)]
  exact Eventually.of_forall fun u hu =>
    hC _ (faceProj_mem_closedCube h k l (unitBox_subset_closedCube _ hu))

/-- The face functional in terms of the face weight. -/
theorem spatialFace_eq_faceWeight {d : ℕ} (h k : Fin (d + 1) → ℕ) (l β : ℝ)
    (ξ η : (Fin (d + 1) → ℝ) → ℝ) :
    spatialFace h k l β ξ η =
      1 / (((multCount (ratioExp h k) l - 1).factorial : ℝ) *
        ∏ i, if ratioExp h k i = l then (k i : ℝ) else 1) *
      (∫ u in unitBox (d + 1),
        faceWeight h k l η u * phaseMoment β (2 * l) (ξ (faceProj h k l u))) /
      2 ^ (multCount (ratioExp h k) l - 1) := by
  unfold spatialFace faceWeight
  congr 2
  refine setIntegral_congr_fun (measurableSet_unitBox _) fun u _ => ?_
  ring

/-! ### The joint law and its energy marginal -/

/-- The mass `Z_ξ = ∫ η(P_J u) w(u) J_λ(ξ(P_J u)) du`. -/
noncomputable def spatialMass {d : ℕ} (h k : Fin (d + 1) → ℕ) (l β : ℝ)
    (ξ η : (Fin (d + 1) → ℝ) → ℝ) : ℝ :=
  ∫ u in unitBox (d + 1), faceWeight h k l η u * fluctMoment β (ξ (faceProj h k l u)) 0 l 0

/-- The joint density `η(P_J u) w(u) y^{λ-1} e^{-βy+βξ(P_J u)√y}/Z_ξ` on `(0,∞) × box`. -/
noncomputable def spatialJointDensity {d : ℕ} (h k : Fin (d + 1) → ℕ) (l β : ℝ)
    (ξ η : (Fin (d + 1) → ℝ) → ℝ) (z : ℝ × (Fin (d + 1) → ℝ)) : ℝ :=
  faceWeight h k l η z.2 * phaseLawKernel β (ξ (faceProj h k l z.2)) l z.1 /
    spatialMass h k l β ξ η

/-- The product reference measure on `(0,∞) × box`. -/
noncomputable def energyBoxMeasure (d : ℕ) : Measure (ℝ × (Fin (d + 1) → ℝ)) :=
  (volume.restrict (Ioi 0)).prod (volume.restrict (unitBox (d + 1)))

/-- **The limiting joint law of `(NK, u)` under a continuous phase.** -/
noncomputable def spatialJointLaw {d : ℕ} (h k : Fin (d + 1) → ℕ) (l β : ℝ)
    (ξ η : (Fin (d + 1) → ℝ) → ℝ) : Measure (ℝ × (Fin (d + 1) → ℝ)) :=
  (energyBoxMeasure d).withDensity fun z => ENNReal.ofReal (spatialJointDensity h k l β ξ η z)

/-- **The limiting energy law under a continuous phase**: the marginal of the joint law. -/
noncomputable def spatialEnergyLimit {d : ℕ} (h k : Fin (d + 1) → ℕ) (l β : ℝ)
    (ξ η : (Fin (d + 1) → ℝ) → ℝ) : Measure ℝ :=
  (spatialJointLaw h k l β ξ η).map Prod.fst

theorem phaseLawKernel_le_of_abs_le {β l c C y : ℝ} (hβ : 0 ≤ β) (hc : |c| ≤ C) (hy : 0 ≤ y) :
    phaseLawKernel β c l y ≤ phaseLawKernel β C l y := by
  unfold phaseLawKernel phaseKernel
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_)
    (pow_nonneg (Real.sqrt_nonneg _) _)) (Real.rpow_nonneg hy _)
  have := le_abs_self c
  have hs : 0 ≤ β * Real.sqrt y := mul_nonneg hβ (Real.sqrt_nonneg _)
  nlinarith [mul_le_mul_of_nonneg_left (this.trans hc) hs]

theorem measurable_spatialJointDensity {n : ℕ} (h k : Fin (n + 1) → ℕ) (l β : ℝ)
    {ξ η : (Fin (n + 1) → ℝ) → ℝ} (hξc : Continuous ξ) (hηc : Continuous η) :
    Measurable (spatialJointDensity h k l β ξ η) := by
  unfold spatialJointDensity phaseLawKernel
  have h1 : Measurable fun z : ℝ × (Fin (n + 1) → ℝ) => faceWeight h k l η z.2 :=
    (measurable_faceWeight h k l hηc).comp measurable_snd
  have h2 : Measurable fun z : ℝ × (Fin (n + 1) → ℝ) => z.1 ^ (l - 1) :=
    measurable_fst.pow_const _
  have hξfp : Continuous fun z : ℝ × (Fin (n + 1) → ℝ) => ξ (faceProj h k l z.2) :=
    hξc.comp ((continuous_faceProj h k l).comp continuous_snd)
  have h3 : Continuous fun z : ℝ × (Fin (n + 1) → ℝ) =>
      phaseKernel β (ξ (faceProj h k l z.2)) 0 z.1 := by
    unfold phaseKernel
    exact ((Real.continuous_sqrt.comp continuous_fst).pow 0).mul (Real.continuous_exp.comp
      (((continuous_const.mul continuous_fst).neg).add
        ((continuous_const.mul (Real.continuous_sqrt.comp continuous_fst)).mul hξfp)))
  exact ((h1.mul (h2.mul h3.measurable))).div_const _

/-- Integrability of `e^{-t y}` against the joint density on `(0,∞) × box`. -/
theorem integrable_spatialJointDensity_exp {n : ℕ} (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    {l β : ℝ} (hl : 0 < l) (hβ : 0 < β) (hmin : ∀ i, l ≤ ratioExp h k i)
    {ξ η : (Fin (n + 1) → ℝ) → ℝ} (hξc : Continuous ξ) (hηc : Continuous η) {t : ℝ}
    (ht : 0 ≤ t) :
    Integrable (fun z : ℝ × (Fin (n + 1) → ℝ) =>
      Real.exp (-(t * z.1)) * spatialJointDensity h k l β ξ η z) (energyBoxMeasure n) := by
  obtain ⟨Cξ, hCξ⟩ := (isCompact_closedCube (n + 1)).exists_bound_of_continuousOn
    hξc.continuousOn
  obtain ⟨Cη, hCη⟩ := (isCompact_closedCube (n + 1)).exists_bound_of_continuousOn
    hηc.continuousOn
  have hK : Integrable (fun y => phaseLawKernel β Cξ l y) (volume.restrict (Ioi 0)) :=
    integrableOn_phaseLawKernel β Cξ l hβ hl
  have hw : Integrable (residualWeight h k l) (volume.restrict (unitBox (n + 1))) :=
    residualWeight_integrableOn h k hk l hmin
  have hbound := (hK.mul_prod hw).const_mul (Cη / |spatialMass h k l β ξ η|)
  refine hbound.mono' ?_ ?_
  · exact ((Real.continuous_exp.comp (continuous_const.mul continuous_fst).neg).measurable.mul
      (measurable_spatialJointDensity h k l β hξc hηc)).aestronglyMeasurable
  · try unfold energyBoxMeasure
    rw [Measure.prod_restrict, ae_restrict_iff' (measurableSet_Ioi.prod (measurableSet_unitBox _))]
    refine Eventually.of_forall fun z hz => ?_
    obtain ⟨hy, hu⟩ := hz
    have hy0 : 0 < z.1 := hy
    have hfp := faceProj_mem_closedCube h k l (unitBox_subset_closedCube _ hu)
    have hw0 := residualWeight_nonneg h k l z.2 hu
    have hK0 := phaseLawKernel_nonneg β (ξ (faceProj h k l z.2)) l hy0.le
    have hKle := phaseLawKernel_le_of_abs_le (l := l) hβ.le
      ((Real.norm_eq_abs _).symm.trans_le (hCξ _ hfp)) hy0.le
    have hηle : |η (faceProj h k l z.2)| ≤ Cη := (Real.norm_eq_abs _).symm.trans_le (hCη _ hfp)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), spatialJointDensity, abs_div,
      faceWeight, abs_mul, abs_mul, abs_of_nonneg hw0, abs_of_nonneg hK0]
    have hexp : Real.exp (-(t * z.1)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    have hZ0 : 0 ≤ |spatialMass h k l β ξ η| := abs_nonneg _
    have hCη0 : 0 ≤ Cη := (abs_nonneg _).trans hηle
    have hXY : |η (faceProj h k l z.2)| * residualWeight h k l z.2 *
        phaseLawKernel β (ξ (faceProj h k l z.2)) l z.1 ≤
        Cη * residualWeight h k l z.2 * phaseLawKernel β Cξ l z.1 :=
      mul_le_mul (mul_le_mul_of_nonneg_right hηle hw0) hKle hK0 (mul_nonneg hCη0 hw0)
    calc Real.exp (-(t * z.1)) * (|η (faceProj h k l z.2)| * residualWeight h k l z.2 *
          phaseLawKernel β (ξ (faceProj h k l z.2)) l z.1 / |spatialMass h k l β ξ η|)
        ≤ 1 * (Cη * residualWeight h k l z.2 * phaseLawKernel β Cξ l z.1 /
          |spatialMass h k l β ξ η|) :=
          mul_le_mul hexp (div_le_div_of_nonneg_right hXY hZ0)
            (div_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) hw0) hK0) hZ0) zero_le_one
      _ = Cη / |spatialMass h k l β ξ η| *
          (phaseLawKernel β Cξ l z.1 * residualWeight h k l z.2) := by ring

/-- **Fubini for the joint density**:
`∫ e^{-t y} dQ^ξ = ∫ η(P_J u) w(u) r^{-λ} J_λ(ξ(P_J u)/√r) du / Z_ξ`. -/
theorem integral_spatialJointDensity_exp {n : ℕ} (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    {l β : ℝ} (hl : 0 < l) (hβ : 0 < β) (hmin : ∀ i, l ≤ ratioExp h k i)
    {ξ η : (Fin (n + 1) → ℝ) → ℝ} (hξc : Continuous ξ) (hηc : Continuous η) {t : ℝ}
    (ht : 0 ≤ t) :
    ∫ z, Real.exp (-(t * z.1)) * spatialJointDensity h k l β ξ η z ∂(energyBoxMeasure n) =
      (∫ u in unitBox (n + 1), faceWeight h k l η u * (((β + t) / β) ^ (-l) *
        fluctMoment β (ξ (faceProj h k l u) / Real.sqrt ((β + t) / β)) 0 l 0)) /
        spatialMass h k l β ξ η := by
  try unfold energyBoxMeasure
  rw [integral_prod_symm _ (integrable_spatialJointDensity_exp h k hk hl hβ hmin hξc hηc ht),
    ← integral_div]
  refine setIntegral_congr_fun (measurableSet_unitBox _) fun u _ => ?_
  simp only [spatialJointDensity]
  rw [← integral_phaseLawKernel_exp β (ξ (faceProj h k l u)) l hβ ht, mul_div_right_comm,
    ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
  ring

/-- The normalisation `∫ dQ^ξ = 1` in integral form. -/
theorem integral_spatialJointDensity {n : ℕ} (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    {l β : ℝ} (hl : 0 < l) (hβ : 0 < β) (hmin : ∀ i, l ≤ ratioExp h k i)
    {ξ η : (Fin (n + 1) → ℝ) → ℝ} (hξc : Continuous ξ) (hηc : Continuous η)
    (hZ : 0 < spatialMass h k l β ξ η) :
    ∫ z, spatialJointDensity h k l β ξ η z ∂(energyBoxMeasure n) = 1 := by
  have := integral_spatialJointDensity_exp h k hk hl hβ hmin hξc hηc (le_refl 0)
  simp only [zero_mul, neg_zero, Real.exp_zero, one_mul, add_zero, div_self hβ.ne',
    Real.one_rpow, Real.sqrt_one, div_one] at this
  rw [this]
  exact div_self hZ.ne'

theorem spatialJointLaw_isProbabilityMeasure {n : ℕ} (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    {l β : ℝ} (hl : 0 < l) (hβ : 0 < β) (hmin : ∀ i, l ≤ ratioExp h k i)
    {ξ η : (Fin (n + 1) → ℝ) → ℝ} (hξc : Continuous ξ) (hηc : Continuous η)
    (hηnn : ∀ v ∈ closedCube (n + 1), 0 ≤ η v) (hZ : 0 < spatialMass h k l β ξ η) :
    IsProbabilityMeasure (spatialJointLaw h k l β ξ η) := by
  constructor
  unfold spatialJointLaw
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal,
    integral_spatialJointDensity h k hk hl hβ hmin hξc hηc hZ, ENNReal.ofReal_one]
  · have := integrable_spatialJointDensity_exp h k hk hl hβ hmin hξc hηc (le_refl 0)
    simpa using this
  · rw [Filter.EventuallyLE]
    try unfold energyBoxMeasure
    rw [Measure.prod_restrict, ae_restrict_iff' (measurableSet_Ioi.prod (measurableSet_unitBox _))]
    refine Eventually.of_forall fun z hz => ?_
    obtain ⟨hy, hu⟩ := hz
    have hy0 : 0 < z.1 := hy
    exact div_nonneg (mul_nonneg (faceWeight_nonneg h k l hηnn hu)
      (phaseLawKernel_nonneg β _ l hy0.le)) hZ.le

theorem spatialEnergyLimit_isProbabilityMeasure {n : ℕ} (h k : Fin (n + 1) → ℕ)
    (hk : ∀ i, 0 < k i) {l β : ℝ} (hl : 0 < l) (hβ : 0 < β) (hmin : ∀ i, l ≤ ratioExp h k i)
    {ξ η : (Fin (n + 1) → ℝ) → ℝ} (hξc : Continuous ξ) (hηc : Continuous η)
    (hηnn : ∀ v ∈ closedCube (n + 1), 0 ≤ η v) (hZ : 0 < spatialMass h k l β ξ η) :
    IsProbabilityMeasure (spatialEnergyLimit h k l β ξ η) :=
  have := spatialJointLaw_isProbabilityMeasure h k hk hl hβ hmin hξc hηc hηnn hZ
  Measure.isProbabilityMeasure_map measurable_fst.aemeasurable

/-- The energy marginal is carried by `[0,∞)`. -/
theorem spatialEnergyLimit_Iio {n : ℕ} (h k : Fin (n + 1) → ℕ) (l β : ℝ)
    (ξ η : (Fin (n + 1) → ℝ) → ℝ) : spatialEnergyLimit h k l β ξ η (Iio 0) = 0 := by
  unfold spatialEnergyLimit spatialJointLaw
  rw [Measure.map_apply measurable_fst measurableSet_Iio,
    withDensity_apply _ (measurable_fst measurableSet_Iio)]
  refine setLIntegral_measure_zero _ _ ?_
  try unfold energyBoxMeasure
  rw [Measure.prod_restrict, Measure.restrict_apply (measurable_fst measurableSet_Iio)]
  have : Prod.fst ⁻¹' Iio (0 : ℝ) ∩ Ioi (0 : ℝ) ×ˢ unitBox (n + 1) = ∅ :=
    Set.eq_empty_of_forall_notMem fun z hz =>
      absurd (lt_trans (show z.1 < 0 from hz.1) (show 0 < z.1 from hz.2.1)) (lt_irrefl _)
  rw [this, measure_empty]

/-- **Laplace transform of the limiting energy law**:
`∫ e^{-ty} dρ^ξ = ∫ η(P_J u) w(u) r^{-λ} J_λ(ξ(P_J u)/√r) du / Z_ξ`. -/
theorem spatialEnergyLimit_laplace {n : ℕ} (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    {l β : ℝ} (hl : 0 < l) (hβ : 0 < β) (hmin : ∀ i, l ≤ ratioExp h k i)
    {ξ η : (Fin (n + 1) → ℝ) → ℝ} (hξc : Continuous ξ) (hηc : Continuous η)
    (hηnn : ∀ v ∈ closedCube (n + 1), 0 ≤ η v) (hZ : 0 < spatialMass h k l β ξ η) {t : ℝ}
    (ht : 0 ≤ t) :
    ∫ y, Real.exp (-(t * y)) ∂(spatialEnergyLimit h k l β ξ η) =
      (∫ u in unitBox (n + 1), faceWeight h k l η u * (((β + t) / β) ^ (-l) *
        fluctMoment β (ξ (faceProj h k l u) / Real.sqrt ((β + t) / β)) 0 l 0)) /
        spatialMass h k l β ξ η := by
  unfold spatialEnergyLimit spatialJointLaw
  rw [integral_map measurable_fst.aemeasurable
    (by fun_prop : Continuous fun y : ℝ => Real.exp (-(t * y))).measurable.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul
      (measurable_spatialJointDensity h k l β hξc hηc).ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top),
    ← integral_spatialJointDensity_exp h k hk hl hβ hmin hξc hηc ht]
  refine integral_congr_ae ?_
  rw [Filter.EventuallyEq]
  try unfold energyBoxMeasure
  rw [Measure.prod_restrict, ae_restrict_iff' (measurableSet_Ioi.prod (measurableSet_unitBox _))]
  refine Eventually.of_forall fun z hz => ?_
  obtain ⟨hy, hu⟩ := hz
  have hy0 : 0 < z.1 := hy
  simp only [smul_eq_mul]
  have hd : 0 ≤ spatialJointDensity h k l β ξ η z :=
    div_nonneg (mul_nonneg (faceWeight_nonneg h k l hηnn hu)
      (phaseLawKernel_nonneg β _ l hy0.le)) hZ.le
  rw [ENNReal.toReal_ofReal hd, mul_comm]

/-! ### Weak convergence -/

/-- The Laplace transform of the finite-`N` energy law under the phase `ξ` is the unweighted
`spatialLaplace`. -/
theorem phaseEnergyLaw_laplace_spatial (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N : ℝ)
    {ξ η : (Fin (n + 1) → ℝ) → ℝ} (hξm : Measurable ξ) (hηc : Continuous η)
    (hηnn : ∀ u ∈ unitBox (n + 1), 0 ≤ η u) (hZ : 0 < origPhaseIntegral n h k β N 1 ξ η)
    (t : ℝ) :
    ∫ y, Real.exp (-(t * y)) ∂(phaseEnergyLaw n h k β N ξ η) =
      spatialLaplace n h k β N ξ η (fun _ => 1) t := by
  rw [phaseEnergyLaw_integral n h k β N hξm hηc hηnn hZ
    (by fun_prop : Continuous fun y : ℝ => Real.exp (-(t * y))).measurable]
  unfold spatialLaplace origPhaseIntegral phaseIntegrand
  congr 1
  refine setIntegral_congr_fun (measurableSet_unitBox _) fun u _ => ?_
  dsimp only
  rw [one_mul, mul_assoc t N]
  ring

/-- The positivity of `Z_ξ` from the positivity of the face functional. -/
theorem spatialMass_pos_of_face {d : ℕ} (h k : Fin (d + 1) → ℕ) (hk : ∀ i, 0 < k i) (l β : ℝ)
    (ξ η : (Fin (d + 1) → ℝ) → ℝ) (hF : 0 < spatialFace h k l β ξ η) :
    0 < spatialMass h k l β ξ η := by
  rw [spatialFace_eq_faceWeight] at hF
  have hc : 0 < 1 / (((multCount (ratioExp h k) l - 1).factorial : ℝ) *
      ∏ i, if ratioExp h k i = l then (k i : ℝ) else 1) := by
    refine one_div_pos.2 (mul_pos (by positivity) (Finset.prod_pos fun i _ => ?_))
    split_ifs
    · exact_mod_cast hk i
    · exact one_pos
  have hI : 0 < ∫ u in unitBox (d + 1),
      faceWeight h k l η u * phaseMoment β (2 * l) (ξ (faceProj h k l u)) := by
    by_contra hneg
    push Not at hneg
    have : spatialFace h k l β ξ η ≤ 0 := by
      rw [spatialFace_eq_faceWeight]
      exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hc.le hneg)
        (by positivity)
    rw [spatialFace_eq_faceWeight] at this
    linarith
  unfold spatialMass
  have : (fun u => faceWeight h k l η u * fluctMoment β (ξ (faceProj h k l u)) 0 l 0) =
      fun u => 2 * (faceWeight h k l η u * phaseMoment β (2 * l) (ξ (faceProj h k l u))) := by
    funext u
    rw [fluctMoment_eq_two_mul_phaseMoment]
    ring
  rw [this, integral_const_mul]
  exact mul_pos two_pos hI

/-- Probability of the finite-`N` energy law for a continuous phase (bounded on the closed cube). -/
theorem phaseEnergyLaw_isProbabilityMeasure_of_continuous (n : ℕ) (h k : Fin (n + 1) → ℕ)
    {β : ℝ} (N : ℝ) (hβ : 0 ≤ β) {ξ η : (Fin (n + 1) → ℝ) → ℝ} (hξc : Continuous ξ)
    (hηc : Continuous η) (hηnn : ∀ u ∈ unitBox (n + 1), 0 ≤ η u)
    (hZ : 0 < origPhaseIntegral n h k β N 1 ξ η) :
    IsProbabilityMeasure (phaseEnergyLaw n h k β N ξ η) := by
  obtain ⟨C, hC⟩ := (isCompact_closedCube (n + 1)).exists_bound_of_continuousOn hξc.continuousOn
  exact phaseEnergyLaw_isProbabilityMeasure n h k N hβ hξc.measurable hηc hηnn (a := 0) (ε := C)
    (fun u hu => by
      rw [sub_zero, ← Real.norm_eq_abs]
      exact hC u (unitBox_subset_closedCube _ hu)) hZ

/-- **Weak convergence of the posterior law of `NK` under a fixed continuous phase** to the
evidence-weighted face mixture `ρ^ξ`, along `N_m → ∞` with positive chart integrals. -/
theorem spatialEnergyLaw_tendsto (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {β : ℝ}
    (hβ : 0 < β) {η : (Fin (n + 1) → ℝ) → ℝ} (hηc : Continuous η)
    (hηnn : ∀ v ∈ closedCube (n + 1), 0 ≤ η v) {l : ℝ} (hmin : ∀ i, l ≤ ratioExp h k i)
    (hatt : ∃ i, ratioExp h k i = l) {ξ : (Fin (n + 1) → ℝ) → ℝ} (hξc : Continuous ξ)
    (hF : 0 < spatialFace h k l β ξ η) (Nseq : ℕ → ℝ) (hN1 : ∀ m, 1 < Nseq m)
    (hN : Tendsto Nseq atTop atTop) (hZ : ∀ m, 0 < origPhaseIntegral n h k β (Nseq m) 1 ξ η) :
    Tendsto (β := ProbabilityMeasure ℝ) (fun m => ⟨phaseEnergyLaw n h k β (Nseq m) ξ η,
        phaseEnergyLaw_isProbabilityMeasure_of_continuous n h k (Nseq m) hβ.le hξc hηc
          (fun u hu => hηnn u (unitBox_subset_closedCube _ hu)) (hZ m)⟩) atTop
      (𝓝 ⟨spatialEnergyLimit h k l β ξ η, spatialEnergyLimit_isProbabilityMeasure h k hk
        (ratioExp_min_pos h k hk hatt) hβ hmin hξc hηc hηnn
        (spatialMass_pos_of_face h k hk l β ξ η hF)⟩) := by
  have hl0 : 0 < l := ratioExp_min_pos h k hk hatt
  have hZξ := spatialMass_pos_of_face h k hk l β ξ η hF
  have hηnn' : ∀ u ∈ unitBox (n + 1), 0 ≤ η u := fun u hu =>
    hηnn u (unitBox_subset_closedCube _ hu)
  refine tendsto_of_laplace _ _ (fun m => phaseEnergyLaw_Iio n h k β (by linarith [hN1 m]) ξ η)
    (spatialEnergyLimit_Iio h k l β ξ η) fun t ht => ?_
  change Tendsto (fun m => ∫ y, Real.exp (-(t * y)) ∂(phaseEnergyLaw n h k β (Nseq m) ξ η))
    atTop (𝓝 (∫ y, Real.exp (-(t * y)) ∂(spatialEnergyLimit h k l β ξ η)))
  have e : ∀ m, ∫ y, Real.exp (-(t * y)) ∂(phaseEnergyLaw n h k β (Nseq m) ξ η) =
      spatialLaplace n h k β (Nseq m) ξ η (fun _ => 1) t := fun m =>
    phaseEnergyLaw_laplace_spatial n h k β (Nseq m) hξc.measurable hηc hηnn' (hZ m) t
  simp only [e]
  rw [spatialEnergyLimit_laplace h k hk hl0 hβ hmin hξc hηc hηnn hZξ ht]
  have := (spatialLaplace_tendsto n h k hk l β hl0 hβ hmin hatt ξ η (fun _ => 1) hξc hηc
    continuous_const ht hF.ne').comp hN
  convert this using 2
  all_goals try rfl
  -- identify the limits
  try simp only [one_mul]
  rw [spatialFace_temperature h k l hβ ht, spatialFace_eq_faceWeight, spatialFace_eq_faceWeight]
  have hc : (1 / (((multCount (ratioExp h k) l - 1).factorial : ℝ) *
      ∏ i, if ratioExp h k i = l then (k i : ℝ) else 1)) ≠ 0 := by
    refine one_div_ne_zero (mul_ne_zero (by positivity) (Finset.prod_ne_zero_iff.2 fun i _ => ?_))
    split_ifs
    · exact_mod_cast (hk i).ne'
    · exact one_ne_zero
  have h2 : (2 : ℝ) ^ (multCount (ratioExp h k) l - 1) ≠ 0 := pow_ne_zero _ two_ne_zero
  have hP : (∏ i, if ratioExp h k i = l then (k i : ℝ) else 1) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
    split_ifs
    · exact_mod_cast (hk i).ne'
    · exact one_ne_zero
  have hI : 0 < ∫ u in unitBox (n + 1),
      faceWeight h k l η u * phaseMoment β (2 * l) (ξ (faceProj h k l u)) := by
    have := spatialMass_pos_of_face h k hk l β ξ η hF
    unfold spatialMass at this
    rw [show (fun u => faceWeight h k l η u * fluctMoment β (ξ (faceProj h k l u)) 0 l 0) =
        fun u => 2 * (faceWeight h k l η u * phaseMoment β (2 * l) (ξ (faceProj h k l u))) from
        funext fun u => by rw [fluctMoment_eq_two_mul_phaseMoment]; ring,
      integral_const_mul] at this
    linarith
  have hA : ∫ u in unitBox (n + 1), faceWeight h k l η u * (((β + t) / β) ^ (-l) *
      fluctMoment β (ξ (faceProj h k l u) / Real.sqrt ((β + t) / β)) 0 l 0) =
      ((β + t) / β) ^ (-l) * 2 * ∫ u in unitBox (n + 1), faceWeight h k l η u *
        phaseMoment β (2 * l) (ξ (faceProj h k l u) / Real.sqrt ((β + t) / β)) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun (measurableSet_unitBox _) fun u _ => ?_
    rw [fluctMoment_eq_two_mul_phaseMoment]
    ring
  have hZ' : spatialMass h k l β ξ η = 2 * ∫ u in unitBox (n + 1),
      faceWeight h k l η u * phaseMoment β (2 * l) (ξ (faceProj h k l u)) := by
    unfold spatialMass
    rw [← integral_const_mul]
    refine setIntegral_congr_fun (measurableSet_unitBox _) fun u _ => ?_
    rw [fluctMoment_eq_two_mul_phaseMoment]
    ring
  rw [hA, hZ']
  field_simp

end Grammar
