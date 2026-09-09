/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.SpatialEnergyLaw

/-!
# Posterior concentration on the dominant face (unit 357; Astra #44 unit 3, location part)

Under a fixed continuous phase `ξ`, the posterior law of the chart coordinate `u` converges weakly
to the face-location law `ν^ξ = (P_J)_# (η(P_J u) w(u) J_λ(ξ(P_J u)) du / Z_ξ)`
(`phasePosterior_tendsto_faceLocation`): the limit is carried by the dominant face
`{u : u_i = 0 for i ∈ J}` (`faceLocationLimit_faceSet_compl`), with density on the face selected by
the evidence weight `J_λ(ξ(v))`.  The proof is the `t = 0` case of the weighted Laplace limit of
Headline LXXII, together with Fubini for the joint density.
-/

namespace Grammar

open MeasureTheory Filter Topology Set

/-! ### Fubini for bounded observables of the location -/

/-- Fubini for `φ(u)` against the joint density, `φ` measurable and bounded on the box:
`∫ φ(u) dQ^ξ = ∫ η(P_J u) w(u) φ(u) J_λ(ξ(P_J u)) du / Z_ξ`. -/
theorem integral_spatialJointDensity_mul {n : ℕ} (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    {l β : ℝ} (hl : 0 < l) (hβ : 0 < β) (hmin : ∀ i, l ≤ ratioExp h k i)
    {ξ η : (Fin (n + 1) → ℝ) → ℝ} (hξc : Continuous ξ) (hηc : Continuous η)
    {φ : (Fin (n + 1) → ℝ) → ℝ} (hφm : Measurable φ) {C : ℝ}
    (hφ : ∀ u ∈ unitBox (n + 1), |φ u| ≤ C) :
    ∫ z, φ z.2 * spatialJointDensity h k l β ξ η z ∂(energyBoxMeasure n) =
      (∫ u in unitBox (n + 1),
        faceWeight h k l η u * φ u * fluctMoment β (ξ (faceProj h k l u)) 0 l 0) /
        spatialMass h k l β ξ η := by
  -- integrability via the domination used for the Laplace transform
  have hint : Integrable (fun z : ℝ × (Fin (n + 1) → ℝ) =>
      φ z.2 * spatialJointDensity h k l β ξ η z) (energyBoxMeasure n) := by
    have h0 := integrable_spatialJointDensity_exp h k hk hl hβ hmin hξc hηc (le_refl 0)
    simp only [zero_mul, neg_zero, Real.exp_zero, one_mul] at h0
    refine Integrable.bdd_mul (c := C) h0 (hφm.comp measurable_snd).aestronglyMeasurable ?_
    try unfold energyBoxMeasure
    rw [Measure.prod_restrict, ae_restrict_iff' (measurableSet_Ioi.prod (measurableSet_unitBox _))]
    exact Eventually.of_forall fun z hz => (Real.norm_eq_abs _).trans_le (hφ _ hz.2)
  try unfold energyBoxMeasure
  rw [integral_prod_symm _ hint, ← integral_div]
  refine setIntegral_congr_fun (measurableSet_unitBox _) fun u _ => ?_
  simp only [spatialJointDensity]
  rw [← integral_phaseLawKernel β (ξ (faceProj h k l u)) l, mul_div_right_comm,
    ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
  ring

/-! ### The face-location law -/

/-- The dominant face `{u : u_i = 0 for all i ∈ J}`. -/
def faceSet {d : ℕ} (h k : Fin d → ℕ) (l : ℝ) : Set (Fin d → ℝ) :=
  {u | ∀ i, ratioExp h k i = l → u i = 0}

theorem faceProj_mem_faceSet {d : ℕ} (h k : Fin d → ℕ) (l : ℝ) (u : Fin d → ℝ) :
    faceProj h k l u ∈ faceSet h k l := fun i hi => by
  simp [faceProj, hi]

theorem isClosed_faceSet {d : ℕ} (h k : Fin d → ℕ) (l : ℝ) : IsClosed (faceSet h k l) := by
  have : faceSet h k l = ⋂ i, {u : Fin d → ℝ | ratioExp h k i = l → u i = 0} := by
    ext u
    simp [faceSet]
  rw [this]
  refine isClosed_iInter fun i => ?_
  by_cases hi : ratioExp h k i = l
  · simp only [hi, true_implies]
    exact isClosed_eq (continuous_apply i) continuous_const
  · simp only [hi, false_implies, ofPred_true]
    exact isClosed_univ

/-- **The limiting face-location law** `ν^ξ = (P_J)_# Q^ξ`. -/
noncomputable def faceLocationLimit {d : ℕ} (h k : Fin (d + 1) → ℕ) (l β : ℝ)
    (ξ η : (Fin (d + 1) → ℝ) → ℝ) : Measure (Fin (d + 1) → ℝ) :=
  (spatialJointLaw h k l β ξ η).map fun z => faceProj h k l z.2

theorem faceLocationLimit_isProbabilityMeasure {n : ℕ} (h k : Fin (n + 1) → ℕ)
    (hk : ∀ i, 0 < k i) {l β : ℝ} (hl : 0 < l) (hβ : 0 < β) (hmin : ∀ i, l ≤ ratioExp h k i)
    {ξ η : (Fin (n + 1) → ℝ) → ℝ} (hξc : Continuous ξ) (hηc : Continuous η)
    (hηnn : ∀ v ∈ closedCube (n + 1), 0 ≤ η v) (hZ : 0 < spatialMass h k l β ξ η) :
    IsProbabilityMeasure (faceLocationLimit h k l β ξ η) :=
  have := spatialJointLaw_isProbabilityMeasure h k hk hl hβ hmin hξc hηc hηnn hZ
  Measure.isProbabilityMeasure_map ((measurable_faceProj h k l).comp measurable_snd).aemeasurable

/-- **Concentration on the dominant face**: the limiting location law charges only the face. -/
theorem faceLocationLimit_faceSet_compl {n : ℕ} (h k : Fin (n + 1) → ℕ) (l β : ℝ)
    (ξ η : (Fin (n + 1) → ℝ) → ℝ) : faceLocationLimit h k l β ξ η (faceSet h k l)ᶜ = 0 := by
  unfold faceLocationLimit
  have hm : Measurable fun z : ℝ × (Fin (n + 1) → ℝ) => faceProj h k l z.2 :=
    (measurable_faceProj h k l).comp measurable_snd
  rw [Measure.map_apply hm (isClosed_faceSet h k l).measurableSet.compl]
  have : (fun z : ℝ × (Fin (n + 1) → ℝ) => faceProj h k l z.2) ⁻¹' (faceSet h k l)ᶜ = ∅ :=
    Set.eq_empty_of_forall_notMem fun z hz => hz (faceProj_mem_faceSet h k l z.2)
  rw [this, measure_empty]

/-- Integrals against the face-location law. -/
theorem faceLocationLimit_integral {n : ℕ} (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    {l β : ℝ} (hl : 0 < l) (hβ : 0 < β) (hmin : ∀ i, l ≤ ratioExp h k i)
    {ξ η : (Fin (n + 1) → ℝ) → ℝ} (hξc : Continuous ξ) (hηc : Continuous η)
    (hηnn : ∀ v ∈ closedCube (n + 1), 0 ≤ η v) (hZ : 0 < spatialMass h k l β ξ η)
    {g : (Fin (n + 1) → ℝ) → ℝ} (hgc : Continuous g) :
    ∫ u, g u ∂(faceLocationLimit h k l β ξ η) =
      (∫ u in unitBox (n + 1), faceWeight h k l η u * g (faceProj h k l u) *
        fluctMoment β (ξ (faceProj h k l u)) 0 l 0) / spatialMass h k l β ξ η := by
  obtain ⟨C, hC⟩ := (isCompact_closedCube (n + 1)).exists_bound_of_continuousOn hgc.continuousOn
  unfold faceLocationLimit spatialJointLaw
  have hm : Measurable fun z : ℝ × (Fin (n + 1) → ℝ) => faceProj h k l z.2 :=
    (measurable_faceProj h k l).comp measurable_snd
  rw [integral_map hm.aemeasurable hgc.measurable.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul
      (measurable_spatialJointDensity h k l β hξc hηc).ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top),
    ← integral_spatialJointDensity_mul h k hk hl hβ hmin hξc hηc
      (φ := fun u => g (faceProj h k l u)) (hgc.measurable.comp (measurable_faceProj h k l))
      (C := C) (fun u hu => (Real.norm_eq_abs _).symm.trans_le
        (hC _ (faceProj_mem_closedCube h k l (unitBox_subset_closedCube _ hu))))]
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

/-! ### Weak convergence of the posterior location -/

theorem phasePosterior_isProbabilityMeasure_of_continuous (n : ℕ) (h k : Fin (n + 1) → ℕ)
    {β : ℝ} (N : ℝ) (hβ : 0 ≤ β) {ξ η : (Fin (n + 1) → ℝ) → ℝ} (hξc : Continuous ξ)
    (hηc : Continuous η) (hηnn : ∀ u ∈ unitBox (n + 1), 0 ≤ η u)
    (hZ : 0 < origPhaseIntegral n h k β N 1 ξ η) :
    IsProbabilityMeasure (phasePosterior n h k β N ξ η) := by
  obtain ⟨C, hC⟩ := (isCompact_closedCube (n + 1)).exists_bound_of_continuousOn hξc.continuousOn
  exact phasePosterior_isProbabilityMeasure n h k N hβ hξc.measurable hηc hηnn (a := 0) (ε := C)
    (fun u hu => by
      rw [sub_zero, ← Real.norm_eq_abs]
      exact hC u (unitBox_subset_closedCube _ hu)) hZ

/-- The posterior expectation of `g(u)` is the `t = 0` weighted Laplace transform. -/
theorem phasePosterior_integral_eq_spatialLaplace (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N : ℝ)
    {ξ η : (Fin (n + 1) → ℝ) → ℝ} (hξm : Measurable ξ) (hηc : Continuous η)
    (hηnn : ∀ u ∈ unitBox (n + 1), 0 ≤ η u) (hZ : 0 < origPhaseIntegral n h k β N 1 ξ η)
    (g : (Fin (n + 1) → ℝ) → ℝ) :
    ∫ u, g u ∂(phasePosterior n h k β N ξ η) = spatialLaplace n h k β N ξ η g 0 := by
  rw [phasePosterior_integral n h k β N hξm hηc hηnn hZ g]
  unfold spatialLaplace origPhaseIntegral phaseIntegrand
  congr 1
  refine setIntegral_congr_fun (measurableSet_unitBox _) fun u _ => ?_
  dsimp only
  simp only [zero_mul, neg_zero, Real.exp_zero, one_mul]
  ring

/-- **Posterior concentration on the dominant face**: under a fixed continuous phase the posterior
law of the chart coordinate converges weakly to the face-location law `ν^ξ`. -/
theorem phasePosterior_tendsto_faceLocation (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    {β : ℝ} (hβ : 0 < β) {η : (Fin (n + 1) → ℝ) → ℝ} (hηc : Continuous η)
    (hηnn : ∀ v ∈ closedCube (n + 1), 0 ≤ η v) {l : ℝ} (hmin : ∀ i, l ≤ ratioExp h k i)
    (hatt : ∃ i, ratioExp h k i = l) {ξ : (Fin (n + 1) → ℝ) → ℝ} (hξc : Continuous ξ)
    (hF : 0 < spatialFace h k l β ξ η) (Nseq : ℕ → ℝ) (hN : Tendsto Nseq atTop atTop)
    (hZ : ∀ m, 0 < origPhaseIntegral n h k β (Nseq m) 1 ξ η) :
    Tendsto (β := ProbabilityMeasure (Fin (n + 1) → ℝ))
      (fun m => ⟨phasePosterior n h k β (Nseq m) ξ η,
        phasePosterior_isProbabilityMeasure_of_continuous n h k (Nseq m) hβ.le hξc hηc
          (fun u hu => hηnn u (unitBox_subset_closedCube _ hu)) (hZ m)⟩) atTop
      (𝓝 ⟨faceLocationLimit h k l β ξ η, faceLocationLimit_isProbabilityMeasure h k hk
        (ratioExp_min_pos h k hk hatt) hβ hmin hξc hηc hηnn
        (spatialMass_pos_of_face h k hk l β ξ η hF)⟩) := by
  have hl0 : 0 < l := ratioExp_min_pos h k hk hatt
  have hZξ := spatialMass_pos_of_face h k hk l β ξ η hF
  have hηnn' : ∀ u ∈ unitBox (n + 1), 0 ≤ η u := fun u hu =>
    hηnn u (unitBox_subset_closedCube _ hu)
  refine ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.2 fun g => ?_
  change Tendsto (fun m => ∫ u, g u ∂(phasePosterior n h k β (Nseq m) ξ η)) atTop
    (𝓝 (∫ u, g u ∂(faceLocationLimit h k l β ξ η)))
  have e : ∀ m, ∫ u, g u ∂(phasePosterior n h k β (Nseq m) ξ η) =
      spatialLaplace n h k β (Nseq m) ξ η g 0 := fun m =>
    phasePosterior_integral_eq_spatialLaplace n h k β (Nseq m) hξc.measurable hηc hηnn' (hZ m) g
  simp only [e]
  rw [faceLocationLimit_integral h k hk hl0 hβ hmin hξc hηc hηnn hZξ g.continuous]
  have := (spatialLaplace_tendsto n h k hk l β hl0 hβ hmin hatt ξ η g hξc hηc g.continuous
    le_rfl hF.ne').comp hN
  convert this using 2
  all_goals try rfl
  -- identify the limits at `t = 0`
  simp only [add_zero, div_self hβ.ne', mul_one]
  rw [spatialFace_eq_faceWeight, spatialFace_eq_faceWeight]
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
  have hZ' : spatialMass h k l β ξ η = 2 * ∫ u in unitBox (n + 1),
      faceWeight h k l η u * phaseMoment β (2 * l) (ξ (faceProj h k l u)) := by
    unfold spatialMass
    rw [← integral_const_mul]
    refine setIntegral_congr_fun (measurableSet_unitBox _) fun u _ => ?_
    rw [fluctMoment_eq_two_mul_phaseMoment]
    ring
  have hA : ∫ u in unitBox (n + 1), faceWeight h k l η u * g (faceProj h k l u) *
      fluctMoment β (ξ (faceProj h k l u)) 0 l 0 = 2 * ∫ u in unitBox (n + 1),
      faceWeight h k l (fun u => g u * η u) u * phaseMoment β (2 * l) (ξ (faceProj h k l u)) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun (measurableSet_unitBox _) fun u _ => ?_
    unfold faceWeight
    rw [fluctMoment_eq_two_mul_phaseMoment]
    ring
  have hI : 0 < ∫ u in unitBox (n + 1),
      faceWeight h k l η u * phaseMoment β (2 * l) (ξ (faceProj h k l u)) := by
    have := hZξ
    rw [hZ'] at this
    linarith
  rw [hA, hZ']
  field_simp

end Grammar
