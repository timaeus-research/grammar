/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.SpatialIndependence

/-!
# Independence forces a face-constant phase (unit 375; Astra #46 unit 3, converse)

Let `μ_P = (P_J)_#(η(P_Ju) w(u)/Z_ξ du)` be the weighted box measure pushed to the face
(`faceBaseMeasure`), so that the face-location law is `ν^ξ = μ_P · J_λ(ξ)`
(`faceLocationLimit_eq_withDensity`).  Under the limiting joint law the energy has the
`v`-conditional mean `μ(ξ(v)) = J_{λ+1}(ξ(v))/J_λ(ξ(v))` (`lintegral_energy_indicator`).  If energy
and face location are **independent**, `Q̃^ξ = ρ̄ ⊗ ν^ξ`, then the conditional mean equals the
overall mean `ν^ξ`-a.e., and since `a ↦ μ(a)` is strictly increasing the face phase is almost
surely constant: `∃ a₀, ξ = a₀` `ν^ξ`-a.e. (`faceConstant_of_indep`).  Together with Headline LXXXV
this characterises independence of energy and location under the limiting joint law.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

variable {d : ℕ}

/-! ### The weighted face measure -/

/-- `μ_P = (P_J)_#(η(P_J u) w(u)/Z_ξ du)`. -/
noncomputable def faceBaseMeasure (h k : Fin (d + 1) → ℕ) (l β : ℝ) (ξ η : (Fin (d + 1) → ℝ) → ℝ) :
    Measure (Fin (d + 1) → ℝ) :=
  ((volume.restrict (unitBox (d + 1))).withDensity fun u =>
    ENNReal.ofReal (faceWeight h k l η u / spatialMass h k l β ξ η)).map (faceProj h k l)

theorem lintegral_faceBaseMeasure (h k : Fin (d + 1) → ℕ) (l β : ℝ) {ξ η : (Fin (d + 1) → ℝ) → ℝ}
    (hηc : Continuous η) {g : (Fin (d + 1) → ℝ) → ENNReal} (hg : Measurable g) :
    ∫⁻ v, g v ∂(faceBaseMeasure h k l β ξ η) =
      ∫⁻ u in unitBox (d + 1),
        ENNReal.ofReal (faceWeight h k l η u / spatialMass h k l β ξ η) * g (faceProj h k l u) := by
  unfold faceBaseMeasure
  have hg' : Measurable fun u => g (faceProj h k l u) := hg.comp (measurable_faceProj h k l)
  rw [lintegral_map hg (measurable_faceProj h k l), lintegral_withDensity_eq_lintegral_mul _
    ((measurable_faceWeight h k l hηc).div_const _).ennreal_ofReal hg']
  rfl

theorem faceBaseMeasure_isFiniteMeasure {n : ℕ} (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    {l β : ℝ} (hmin : ∀ i, l ≤ ratioExp h k i) {ξ η : (Fin (n + 1) → ℝ) → ℝ} (hηc : Continuous η)
    (hηnn : ∀ v ∈ closedCube (n + 1), 0 ≤ η v) (hZ : 0 < spatialMass h k l β ξ η) :
    IsFiniteMeasure (faceBaseMeasure h k l β ξ η) := by
  have hint : Integrable (fun u => faceWeight h k l η u / spatialMass h k l β ξ η)
      (volume.restrict (unitBox (n + 1))) :=
    (integrableOn_faceWeight h k hk hmin hηc).div_const _
  have hfin : ∫⁻ u in unitBox (n + 1),
      ENNReal.ofReal (faceWeight h k l η u / spatialMass h k l β ξ η) ≠ ⊤ := by
    rw [← ofReal_integral_eq_lintegral_ofReal hint (by
      rw [Filter.EventuallyLE, ae_restrict_iff' (measurableSet_unitBox _)]
      exact Eventually.of_forall fun u hu => div_nonneg (faceWeight_nonneg h k l hηnn hu) hZ.le)]
    exact ENNReal.ofReal_ne_top
  have := isFiniteMeasure_withDensity hfin
  exact Measure.isFiniteMeasure_map _ _

/-- The face-location law is `μ_P` with density `J_λ(ξ(v))`. -/
theorem faceLocationLimit_eq_withDensity {n : ℕ} (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    {l β : ℝ} (hl : 0 < l) (hβ : 0 < β) (hmin : ∀ i, l ≤ ratioExp h k i)
    {ξ η : (Fin (n + 1) → ℝ) → ℝ} (hξc : Continuous ξ) (hηc : Continuous η)
    (hηnn : ∀ v ∈ closedCube (n + 1), 0 ≤ η v) (hZ : 0 < spatialMass h k l β ξ η) :
    faceLocationLimit h k l β ξ η =
      (faceBaseMeasure h k l β ξ η).withDensity
        fun v => ENNReal.ofReal (fluctMoment β (ξ v) 0 l 0) := by
  have hJm : Measurable fun v => ENNReal.ofReal (fluctMoment β (ξ v) 0 l 0) :=
    ((continuous_fluctMoment_phase β hβ hl).comp hξc).measurable.ennreal_ofReal
  have hprob := faceLocationLimit_isProbabilityMeasure h k hk hl hβ hmin hξc hηc hηnn hZ
  obtain ⟨C, hC⟩ := (isCompact_closedCube (n + 1)).exists_bound_of_continuousOn
    ((continuous_fluctMoment_phase β hβ hl).comp hξc).continuousOn
  ext A hA
  rw [withDensity_apply _ hA, ← lintegral_indicator hA, lintegral_faceBaseMeasure h k l β hηc
    (hJm.indicator hA), ← ENNReal.ofReal_toReal (measure_ne_top _ A), ← measureReal_def,
    faceLocationLimit_real_eq h k hk hl hβ hmin hξc hηc hηnn hZ hA, div_eq_mul_one_div,
    ← integral_mul_const, ofReal_integral_eq_lintegral_ofReal]
  · refine setLIntegral_congr_fun (measurableSet_unitBox _) fun u hu => ?_
    have hw0 := faceWeight_nonneg h k l hηnn hu
    by_cases hmem : faceProj h k l u ∈ A
    · simp only [Set.indicator_of_mem hmem, Pi.one_apply]
      rw [← ENNReal.ofReal_mul (div_nonneg hw0 hZ.le)]
      congr 1
      ring
    · simp only [Set.indicator_of_notMem hmem]
      simp
  · have hi1 : Integrable
        (fun u => fluctMoment β (ξ (faceProj h k l u)) 0 l 0 * faceWeight h k l η u)
        (volume.restrict (unitBox (n + 1))) := by
      refine Integrable.bdd_mul (c := |C|) (integrableOn_faceWeight h k hk hmin hηc)
        (((continuous_fluctMoment_phase β hβ hl).comp hξc).measurable.comp
          (measurable_faceProj h k l)).aestronglyMeasurable ?_
      rw [ae_restrict_iff' (measurableSet_unitBox _)]
      refine Eventually.of_forall fun u hu => ?_
      have := hC _ (faceProj_mem_closedCube h k l (unitBox_subset_closedCube _ hu))
      rw [Real.norm_eq_abs] at this ⊢
      exact this.trans (le_abs_self C)
    have hi2 : Integrable (fun u => A.indicator 1 (faceProj h k l u) *
        (fluctMoment β (ξ (faceProj h k l u)) 0 l 0 * faceWeight h k l η u))
        (volume.restrict (unitBox (n + 1))) :=
      Integrable.bdd_mul (c := 1) hi1
        ((measurable_one.indicator hA).comp (measurable_faceProj h k l)).aestronglyMeasurable
        (Eventually.of_forall fun u => by
          by_cases hx : faceProj h k l u ∈ A <;> simp [hx])
    refine (hi2.mul_const (1 / spatialMass h k l β ξ η)).congr (Eventually.of_forall fun u => ?_)
    simp only
    ring
  · rw [Filter.EventuallyLE, ae_restrict_iff' (measurableSet_unitBox _)]
    refine Eventually.of_forall fun u hu => ?_
    have hw0 := faceWeight_nonneg h k l hηnn hu
    have hJ0 := (fluctMoment_pos β (ξ (faceProj h k l u)) l hβ hl).le
    have hI0 : (0 : ℝ) ≤ A.indicator 1 (faceProj h k l u) :=
      Set.indicator_nonneg (fun _ _ => zero_le_one) _
    positivity

/-! ### The conditional mean of the energy -/

/-- `y · phaseLawKernel(a, λ, y) = phaseLawKernel(a, λ+1, y)` for `y > 0`. -/
theorem phaseLawKernel_mul_self (β a l : ℝ) {y : ℝ} (hy : 0 < y) :
    phaseLawKernel β a l y * y = phaseLawKernel β a (l + 1) y := by
  unfold phaseLawKernel
  rw [show l + 1 - 1 = (l - 1) + 1 by ring, Real.rpow_add_one hy.ne']
  ring

/-- **The conditional energy mean under the limiting joint law**:
`∫ y 1_A(v) dQ̃^ξ = ∫_A J_{λ+1}(ξ(v)) dμ_P`. -/
theorem lintegral_energy_indicator {n : ℕ} (h k : Fin (n + 1) → ℕ) {l β : ℝ}
    (hl : 0 < l) (hβ : 0 < β)
    {ξ η : (Fin (n + 1) → ℝ) → ℝ} (hξc : Continuous ξ) (hηc : Continuous η)
    (hηnn : ∀ v ∈ closedCube (n + 1), 0 ≤ η v) (hZ : 0 < spatialMass h k l β ξ η)
    {A : Set (Fin (n + 1) → ℝ)} (hA : MeasurableSet A) :
    ∫⁻ z, ENNReal.ofReal z.1 * A.indicator 1 z.2 ∂(spatialJointFaceLaw h k l β ξ η) =
      ∫⁻ v, A.indicator 1 v * ENNReal.ofReal (fluctMoment β (ξ v) 0 (l + 1) 0)
        ∂(faceBaseMeasure h k l β ξ η) := by
  have hfm : Measurable fun z : ℝ × (Fin (n + 1) → ℝ) => ENNReal.ofReal z.1 * A.indicator 1 z.2 :=
    measurable_fst.ennreal_ofReal.mul ((measurable_one.indicator hA).comp measurable_snd)
  have hJm : Measurable fun v => ENNReal.ofReal (fluctMoment β (ξ v) 0 (l + 1) 0) :=
    ((continuous_fluctMoment_phase β hβ (by linarith)).comp hξc).measurable.ennreal_ofReal
  have hfm' : Measurable fun z : ℝ × (Fin (n + 1) → ℝ) =>
      ENNReal.ofReal z.1 * A.indicator 1 (faceProj h k l z.2) :=
    hfm.comp (measurable_facePair h k l)
  have hg : Measurable fun v =>
      A.indicator 1 v * ENNReal.ofReal (fluctMoment β (ξ v) 0 (l + 1) 0) :=
    (measurable_one.indicator hA).mul hJm
  unfold spatialJointFaceLaw spatialJointLaw
  rw [lintegral_map hfm (measurable_facePair h k l)]
  dsimp only
  rw [lintegral_withDensity_eq_lintegral_mul _
    (measurable_spatialJointDensity h k l β hξc hηc).ennreal_ofReal hfm',
    lintegral_faceBaseMeasure h k l β hηc hg]
  change ∫⁻ z, ENNReal.ofReal (spatialJointDensity h k l β ξ η z) *
    (ENNReal.ofReal z.1 * A.indicator 1 (faceProj h k l z.2)) ∂(energyBoxMeasure n) = _
  have hfm2 : Measurable fun z : ℝ × (Fin (n + 1) → ℝ) =>
      ENNReal.ofReal (spatialJointDensity h k l β ξ η z) *
        (ENNReal.ofReal z.1 * A.indicator 1 (faceProj h k l z.2)) :=
    (measurable_spatialJointDensity h k l β hξc hηc).ennreal_ofReal.mul hfm'
  try unfold energyBoxMeasure
  rw [lintegral_prod_symm _ hfm2.aemeasurable]
  refine setLIntegral_congr_fun (measurableSet_unitBox _) fun u hu => ?_
  have hw0 : 0 ≤ faceWeight h k l η u / spatialMass h k l β ξ η :=
    div_nonneg (faceWeight_nonneg h k l hηnn hu) hZ.le
  set a := ξ (faceProj h k l u) with ha
  have hK : Measurable fun y : ℝ => ENNReal.ofReal (phaseLawKernel β a l y * y) :=
    ((measurable_phaseLawKernel β a l).mul measurable_id).ennreal_ofReal
  have hinner : ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (phaseLawKernel β a l y * y) =
      ENNReal.ofReal (fluctMoment β a 0 (l + 1) 0) := by
    rw [← integral_phaseLawKernel β a (l + 1), ← ofReal_integral_eq_lintegral_ofReal]
    · congr 1
      exact setIntegral_congr_fun measurableSet_Ioi fun y hy => phaseLawKernel_mul_self β a l hy
    · exact (integrableOn_phaseLawKernel β a (l + 1) hβ (by linarith)).congr_fun
        (fun y hy => (phaseLawKernel_mul_self β a l hy).symm) measurableSet_Ioi
    · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioi]
      exact Eventually.of_forall fun y hy =>
        mul_nonneg (phaseLawKernel_nonneg β a l (le_of_lt hy)) (le_of_lt hy)
  calc ∫⁻ y in Ioi (0 : ℝ), (ENNReal.ofReal (spatialJointDensity h k l β ξ η (y, u)) *
        (ENNReal.ofReal y * A.indicator 1 (faceProj h k l u)))
      = ∫⁻ y in Ioi (0 : ℝ), (ENNReal.ofReal (faceWeight h k l η u / spatialMass h k l β ξ η) *
          A.indicator 1 (faceProj h k l u)) * ENNReal.ofReal (phaseLawKernel β a l y * y) := by
        refine setLIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
        have hy0 : 0 < y := hy
        simp only [spatialJointDensity]
        rw [show faceWeight h k l η u * phaseLawKernel β a l y / spatialMass h k l β ξ η =
          (faceWeight h k l η u / spatialMass h k l β ξ η) * phaseLawKernel β a l y by ring,
          ENNReal.ofReal_mul hw0, ENNReal.ofReal_mul (phaseLawKernel_nonneg β a l hy0.le)]
        ring
    _ = (ENNReal.ofReal (faceWeight h k l η u / spatialMass h k l β ξ η) *
          A.indicator 1 (faceProj h k l u)) * ENNReal.ofReal (fluctMoment β a 0 (l + 1) 0) := by
        rw [lintegral_const_mul _ hK, hinner]
    _ = _ := by ring

/-! ### The converse -/

/-- **Independence forces a face-constant phase**: if `Q̃^ξ = ρ̄ ⊗ ν^ξ` (energy and face location
independent under the limiting joint law), then there is `a₀` with `ξ = a₀` `ν^ξ`-a.e. -/
theorem faceConstant_of_indep {n : ℕ} (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {l β : ℝ}
    (hl : 0 < l) (hβ : 0 < β) (hmin : ∀ i, l ≤ ratioExp h k i)
    {ξ η : (Fin (n + 1) → ℝ) → ℝ} (hξc : Continuous ξ) (hηc : Continuous η)
    (hηnn : ∀ v ∈ closedCube (n + 1), 0 ≤ η v) (hZ : 0 < spatialMass h k l β ξ η)
    (hind : spatialJointFaceLaw h k l β ξ η =
      (spatialEnergyLimit h k l β ξ η).prod (faceLocationLimit h k l β ξ η)) :
    ∃ a₀ : ℝ, ∀ᵐ v ∂(faceLocationLimit h k l β ξ η), ξ v = a₀ := by
  have hfin := faceBaseMeasure_isFiniteMeasure h k hk hmin hηc hηnn hZ
  have hprob := faceLocationLimit_isProbabilityMeasure h k hk hl hβ hmin hξc hηc hηnn hZ
  have hν := faceLocationLimit_eq_withDensity h k hk hl hβ hmin hξc hηc hηnn hZ
  set μP := faceBaseMeasure h k l β ξ η with hμP
  have hJ1m : Measurable fun v => ENNReal.ofReal (fluctMoment β (ξ v) 0 (l + 1) 0) :=
    ((continuous_fluctMoment_phase β hβ (by linarith)).comp hξc).measurable.ennreal_ofReal
  have hJm : Measurable fun v => ENNReal.ofReal (fluctMoment β (ξ v) 0 l 0) :=
    ((continuous_fluctMoment_phase β hβ hl).comp hξc).measurable.ennreal_ofReal
  set mbar : ENNReal := ∫⁻ y, ENNReal.ofReal y ∂(spatialEnergyLimit h k l β ξ η) with hmbar
  -- the two expressions for `∫ y 1_A(v) dQ̃`
  have hE : ∀ A : Set (Fin (n + 1) → ℝ), MeasurableSet A →
      ∫⁻ v in A, ENNReal.ofReal (fluctMoment β (ξ v) 0 (l + 1) 0) ∂μP =
        mbar * ∫⁻ v in A, ENNReal.ofReal (fluctMoment β (ξ v) 0 l 0) ∂μP := by
    intro A hA
    have h1 := lintegral_energy_indicator h k hl hβ hξc hηc hηnn hZ hA
    rw [hind, lintegral_prod_mul ENNReal.measurable_ofReal.aemeasurable
      (measurable_one.indicator hA).aemeasurable, lintegral_indicator_one hA, hν,
      withDensity_apply _ hA, ← hμP] at h1
    calc ∫⁻ v in A, ENNReal.ofReal (fluctMoment β (ξ v) 0 (l + 1) 0) ∂μP
        = ∫⁻ v, A.indicator 1 v * ENNReal.ofReal (fluctMoment β (ξ v) 0 (l + 1) 0) ∂μP := by
          rw [← lintegral_indicator hA]
          refine lintegral_congr fun v => ?_
          by_cases hv : v ∈ A <;> simp [hv]
      _ = _ := h1.symm
  -- `mbar` is finite
  obtain ⟨C, hC⟩ := (isCompact_closedCube (n + 1)).exists_bound_of_continuousOn
    ((continuous_fluctMoment_phase β hβ (by linarith : 0 < l + 1)).comp hξc).continuousOn
  have hcube : ∀ᵐ v ∂μP, v ∈ closedCube (n + 1) := by
    rw [hμP]
    unfold faceBaseMeasure
    refine (ae_map_iff (measurable_faceProj h k l).aemeasurable
      (p := fun v => v ∈ closedCube (n + 1))
      (by simpa using (isCompact_closedCube (n + 1)).isClosed.measurableSet)).2 ?_
    refine (withDensity_absolutelyContinuous _ _).ae_le ?_
    exact (ae_restrict_iff' (measurableSet_unitBox _)).2 (Eventually.of_forall fun u hu =>
      faceProj_mem_closedCube h k l (unitBox_subset_closedCube _ hu))
  have hmbar_fin : mbar ≠ ⊤ := by
    have h1 := hE univ MeasurableSet.univ
    have h2 : ∫⁻ v, ENNReal.ofReal (fluctMoment β (ξ v) 0 l 0) ∂μP = 1 := by
      have := measure_univ (μ := faceLocationLimit h k l β ξ η)
      rwa [hν, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at this
    try simp only [Measure.restrict_univ] at h1
    rw [h2, mul_one] at h1
    rw [← h1]
    refine ne_top_of_le_ne_top (b := ENNReal.ofReal |C| * μP univ)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)) ?_
    rw [← lintegral_one, ← lintegral_const_mul _ measurable_const]
    refine lintegral_mono_ae (hcube.mono fun v hv => ?_)
    have hle := hC _ hv
    simp only [Function.comp_apply, Real.norm_eq_abs] at hle
    rw [mul_one]
    exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hle.trans (le_abs_self C)))
  -- the conditional mean is a.e. constant
  have hae : (fun v => ENNReal.ofReal (fluctMoment β (ξ v) 0 (l + 1) 0)) =ᵐ[μP]
      fun v => mbar * ENNReal.ofReal (fluctMoment β (ξ v) 0 l 0) :=
    ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite₀ hJ1m.aemeasurable
      (measurable_const.mul hJm).aemeasurable fun A hA _ => by
        rw [hE A hA, lintegral_const_mul _ hJm]
  have hmean : ∀ᵐ v ∂μP, phaseLawMean β l (ξ v) = mbar.toReal := by
    filter_upwards [hae] with v hv
    have hJ0 := fluctMoment_pos β (ξ v) l hβ hl
    have hJ1 := (fluctMoment_pos β (ξ v) (l + 1) hβ (by linarith)).le
    have := congrArg ENNReal.toReal hv
    rw [ENNReal.toReal_ofReal hJ1, ENNReal.toReal_mul, ENNReal.toReal_ofReal hJ0.le] at this
    unfold phaseLawMean
    rw [this]
    field_simp
  -- `μP ≠ 0`, so the a.e. set is nonempty
  have hμP0 : μP ≠ 0 := by
    intro h0
    have hac : faceLocationLimit h k l β ξ η ≪ μP := by
      rw [hν]
      exact withDensity_absolutelyContinuous _ _
    have : faceLocationLimit h k l β ξ η univ = 0 := hac (by rw [h0]; rfl)
    rw [measure_univ] at this
    exact one_ne_zero this
  have : (ae μP).NeBot := ae_neBot.2 hμP0
  obtain ⟨v₀, hv₀⟩ := hmean.exists
  refine ⟨ξ v₀, ?_⟩
  have hac : faceLocationLimit h k l β ξ η ≪ μP := by
    rw [hν]
    exact withDensity_absolutelyContinuous _ _
  refine hac.ae_eq ?_
  filter_upwards [hmean] with v hv
  exact (phaseLawMean_strictMono β l hβ hl).injective (hv.trans hv₀.symm)

end Grammar
