/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.SpatialNextLogDictionary

/-!
# Moving-phase joint weak convergence

If `N_m → ∞` and the phases `ξ_m` converge uniformly on the box to a continuous `ξ₀`
(`‖ξ_m − ξ₀‖_∞ ≤ ε_m → 0`), the joint law of `(N_m K, u)` under `Q_{N_m}^{ξ_m}` converges weakly to
the limiting joint law `Q̃^{ξ₀}` (`movingPhaseJointLaw_tendsto`).  For every bounded continuous
test `g` on `ℝ × ℝ^d` the moving-phase expectation differs from the fixed-phase one by
`E_{Q_N^{ξ_m}}[g(NK,u)] − E_{Q_N^{ξ₀}}[g(NK,u)] → 0` (the perturbation theorem with the
observable `u ↦ g(N_m K(u), u)`, uniformly bounded by `‖g‖`), and the fixed-phase joint law
converges by the joint convergence theorem.  A diagonal argument then gives the sequential
continuity of the limit map `ξ ↦ Q̃^ξ` for the sup norm on the box
(`spatialJointFaceLaw_tendsto_of_uniform`).  Together these form the deterministic core of the
random-field transfer: the joint posterior law is a continuously convergent function of the phase.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

open BoundedContinuousFunction

/-- Near a continuous phase the chart posterior is a probability measure. -/
theorem phasePosterior_isProbabilityMeasure_of_near (n : ℕ) (h k : Fin (n + 1) → ℕ) {β : ℝ}
    (N : ℝ) (hβ : 0 ≤ β) {ξ ξ₀ η : (Fin (n + 1) → ℝ) → ℝ} (hξm : Measurable ξ)
    (hξ₀c : Continuous ξ₀) (hηc : Continuous η) (hηnn : ∀ u ∈ unitBox (n + 1), 0 ≤ η u) {ε : ℝ}
    (hξ : ∀ u ∈ unitBox (n + 1), |ξ u - ξ₀ u| ≤ ε) (hZ : 0 < origPhaseIntegral n h k β N 1 ξ η) :
    IsProbabilityMeasure (phasePosterior n h k β N ξ η) := by
  have := phaseEnergyLaw_isProbabilityMeasure_of_near n h k N hβ hξm hξ₀c hηc hηnn hξ hZ
  refine ⟨?_⟩
  have h1 := this.measure_univ
  unfold phaseEnergyLaw at h1
  rwa [Measure.map_apply (measurable_energyMap n k N) MeasurableSet.univ, Set.preimage_univ] at h1

theorem phaseJointLaw_isProbabilityMeasure_of_near (n : ℕ) (h k : Fin (n + 1) → ℕ) {β : ℝ}
    (N : ℝ) (hβ : 0 ≤ β) {ξ ξ₀ η : (Fin (n + 1) → ℝ) → ℝ} (hξm : Measurable ξ)
    (hξ₀c : Continuous ξ₀) (hηc : Continuous η) (hηnn : ∀ u ∈ unitBox (n + 1), 0 ≤ η u) {ε : ℝ}
    (hξ : ∀ u ∈ unitBox (n + 1), |ξ u - ξ₀ u| ≤ ε) (hZ : 0 < origPhaseIntegral n h k β N 1 ξ η) :
    IsProbabilityMeasure (phaseJointLaw n h k β N ξ η) :=
  haveI := phasePosterior_isProbabilityMeasure_of_near n h k N hβ hξm hξ₀c hηc hηnn hξ hZ
  Measure.isProbabilityMeasure_map (measurable_energyPair n k N).aemeasurable

/-- Integrals against the finite-`N` joint law of `(NK, u)`. -/
theorem phaseJointLaw_integral (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N : ℝ)
    {ξ η : (Fin (n + 1) → ℝ) → ℝ} (hξm : Measurable ξ) (hηc : Continuous η)
    (hηnn : ∀ u ∈ unitBox (n + 1), 0 ≤ η u) (hZ : 0 < origPhaseIntegral n h k β N 1 ξ η)
    {g : ℝ × (Fin (n + 1) → ℝ) → ℝ} (hg : Measurable g) :
    ∫ z, g z ∂(phaseJointLaw n h k β N ξ η) =
      (∫ u in unitBox (n + 1),
        phaseIntegrand n h k β N ξ η u * g (N * ∏ i, u i ^ (2 * k i), u)) /
        origPhaseIntegral n h k β N 1 ξ η := by
  unfold phaseJointLaw
  rw [integral_map (measurable_energyPair n k N).aemeasurable hg.aestronglyMeasurable,
    phasePosterior_integral n h k β N hξm hηc hηnn hZ]

/-- **Moving-phase joint weak convergence.**  If `N_m → ∞` and `‖ξ_m − ξ₀‖_∞ ≤ ε_m → 0` on the box,
the joint law of `(N_m K, u)` under the `ξ_m`-posterior converges weakly to `Q̃^{ξ₀}`. -/
theorem movingPhaseJointLaw_tendsto (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    {β : ℝ} (hβ : 0 < β) {η : (Fin (n + 1) → ℝ) → ℝ} (hηc : Continuous η)
    (hηnn : ∀ v ∈ closedCube (n + 1), 0 ≤ η v) {l : ℝ} (hmin : ∀ i, l ≤ ratioExp h k i)
    (hatt : ∃ i, ratioExp h k i = l) (hW : 0 < ∫ u in unitBox (n + 1), faceWeight h k l η u)
    {ξ₀ : (Fin (n + 1) → ℝ) → ℝ} (hξ₀c : Continuous ξ₀) (Nseq : ℕ → ℝ) (hN1 : ∀ m, 1 < Nseq m)
    (hN : Tendsto Nseq atTop atTop) (ξ : ℕ → (Fin (n + 1) → ℝ) → ℝ) (hξm : ∀ m, Measurable (ξ m))
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hξ : ∀ m, ∀ u ∈ unitBox (n + 1), |ξ m u - ξ₀ u| ≤ ε m)
    (hZξ : ∀ m, 0 < origPhaseIntegral n h k β (Nseq m) 1 (ξ m) η)
    (hZ0 : ∀ m, 0 < origPhaseIntegral n h k β (Nseq m) 1 ξ₀ η) :
    Tendsto (β := ProbabilityMeasure (ℝ × (Fin (n + 1) → ℝ)))
      (fun m => ⟨phaseJointLaw n h k β (Nseq m) (ξ m) η,
        phaseJointLaw_isProbabilityMeasure_of_near n h k (Nseq m) hβ.le (hξm m) hξ₀c hηc
          (fun u hu => hηnn u (unitBox_subset_closedCube _ hu)) (hξ m) (hZξ m)⟩) atTop
      (𝓝 ⟨spatialJointFaceLaw h k l β ξ₀ η, spatialJointFaceLaw_isProbabilityMeasure h k hk
        (ratioExp_min_pos h k hk hatt) hβ hmin hξ₀c hηc hηnn (spatialMass_pos_of_face h k hk l β
          ξ₀ η (spatialFace_pos_of_faceWeight h k hk (ratioExp_min_pos h k hk hatt) hβ hmin hξ₀c
            hηc hηnn hW))⟩) := by
  have hl0 : 0 < l := ratioExp_min_pos h k hk hatt
  have hF := spatialFace_pos_of_faceWeight h k hk hl0 hβ hmin hξ₀c hηc hηnn hW
  have hηnn' : ∀ u ∈ unitBox (n + 1), 0 ≤ η u := fun u hu =>
    hηnn u (unitBox_subset_closedCube _ hu)
  have hconst := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1
    (spatialJointLaw_tendsto n h k hk hβ hηc hηnn hmin hatt hξ₀c hF Nseq hN1 hN hZ0)
  refine ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.2 fun f => ?_
  change Tendsto (fun m => ∫ z, f z ∂(phaseJointLaw n h k β (Nseq m) (ξ m) η)) atTop
    (𝓝 (∫ z, f z ∂(spatialJointFaceLaw h k l β ξ₀ η)))
  have hf := hconst f
  change Tendsto (fun m => ∫ z, f z ∂(phaseJointLaw n h k β (Nseq m) ξ₀ η)) atTop
    (𝓝 (∫ z, f z ∂(spatialJointFaceLaw h k l β ξ₀ η))) at hf
  have hpert := spatialPhase_perturbation_tendsto n h k hk hβ hηc hηnn hmin hatt hW hξ₀c Nseq hN
    ξ hξm ε hε hξ (fun m u => f (Nseq m * ∏ i, u i ^ (2 * k i), u))
    (fun m => f.continuous.measurable.comp (measurable_energyPair n k (Nseq m))) (norm_nonneg f)
    (fun m u _ => by rw [← Real.norm_eq_abs]; exact f.norm_coe_le_norm _)
  have := hpert.add hf
  rw [zero_add] at this
  refine this.congr' (Eventually.of_forall fun m => ?_)
  dsimp only
  rw [phaseJointLaw_integral n h k β (Nseq m) (hξm m) hηc hηnn' (hZξ m) f.continuous.measurable,
    phaseJointLaw_integral n h k β (Nseq m) hξ₀c.measurable hηc hηnn' (hZ0 m)
      f.continuous.measurable, sub_add_cancel]

/-! ### Sequential continuity of the limit map `ξ ↦ Q̃^ξ` -/

/-- For a continuous phase with positive face weight the chart normaliser is eventually positive. -/
theorem origPhaseIntegral_eventually_pos (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    {β : ℝ} (hβ : 0 < β) {η : (Fin (n + 1) → ℝ) → ℝ} (hηc : Continuous η)
    (hηnn : ∀ v ∈ closedCube (n + 1), 0 ≤ η v) {l : ℝ} (hmin : ∀ i, l ≤ ratioExp h k i)
    (hatt : ∃ i, ratioExp h k i = l) (hW : 0 < ∫ u in unitBox (n + 1), faceWeight h k l η u)
    {ξ : (Fin (n + 1) → ℝ) → ℝ} (hξc : Continuous ξ) :
    ∀ᶠ N in atTop, 0 < origPhaseIntegral n h k β N 1 ξ η := by
  have hl0 : 0 < l := ratioExp_min_pos h k hk hatt
  have hF := spatialFace_pos_of_faceWeight h k hk hl0 hβ hmin hξc hηc hηnn hW
  have hT := spatialPhase_tendsto n h k hk l β hl0 hβ hmin hatt ξ η hξc hηc
  filter_upwards [hT.eventually (lt_mem_nhds hF), eventually_gt_atTop (1 : ℝ)] with N hN hN1
  have hden : 0 < N ^ (-l) * Real.log N ^ (multCount (ratioExp h k) l - 1) :=
    mul_pos (Real.rpow_pos_of_pos (by linarith) _) (pow_pos (Real.log_pos hN1) _)
  exact (div_pos_iff_of_pos_right hden).1 hN

/-- **Continuity of the limiting joint law in the phase.**  If continuous phases `ξ_m` converge
uniformly on the box to `ξ₀`, then `Q̃^{ξ_m} → Q̃^{ξ₀}` weakly.  Proof: a diagonal argument through
`movingPhaseJointLaw_tendsto`, choosing `N_m` so large that `Q_{N_m}^{ξ_m}` is within `1/(m+1)` of
`Q̃^{ξ_m}` in a metric for the weak topology. -/
theorem spatialJointFaceLaw_tendsto_of_uniform (n : ℕ) (h k : Fin (n + 1) → ℕ)
    (hk : ∀ i, 0 < k i) {β : ℝ} (hβ : 0 < β) {η : (Fin (n + 1) → ℝ) → ℝ} (hηc : Continuous η)
    (hηnn : ∀ v ∈ closedCube (n + 1), 0 ≤ η v) {l : ℝ} (hmin : ∀ i, l ≤ ratioExp h k i)
    (hatt : ∃ i, ratioExp h k i = l) (hW : 0 < ∫ u in unitBox (n + 1), faceWeight h k l η u)
    {ξ₀ : (Fin (n + 1) → ℝ) → ℝ} (hξ₀c : Continuous ξ₀) (ξ : ℕ → (Fin (n + 1) → ℝ) → ℝ)
    (hξc : ∀ m, Continuous (ξ m)) (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hξ : ∀ m, ∀ u ∈ unitBox (n + 1), |ξ m u - ξ₀ u| ≤ ε m) :
    Tendsto (β := ProbabilityMeasure (ℝ × (Fin (n + 1) → ℝ)))
      (fun m => ⟨spatialJointFaceLaw h k l β (ξ m) η, spatialJointFaceLaw_isProbabilityMeasure h k
        hk (ratioExp_min_pos h k hk hatt) hβ hmin (hξc m) hηc hηnn (spatialMass_pos_of_face h k hk
          l β (ξ m) η (spatialFace_pos_of_faceWeight h k hk (ratioExp_min_pos h k hk hatt) hβ hmin
            (hξc m) hηc hηnn hW))⟩) atTop
      (𝓝 ⟨spatialJointFaceLaw h k l β ξ₀ η, spatialJointFaceLaw_isProbabilityMeasure h k hk
        (ratioExp_min_pos h k hk hatt) hβ hmin hξ₀c hηc hηnn (spatialMass_pos_of_face h k hk l β
          ξ₀ η (spatialFace_pos_of_faceWeight h k hk (ratioExp_min_pos h k hk hatt) hβ hmin hξ₀c
            hηc hηnn hW))⟩) := by
  have hl0 : 0 < l := ratioExp_min_pos h k hk hatt
  have hηnn' : ∀ u ∈ unitBox (n + 1), 0 ≤ η u := fun u hu =>
    hηnn u (unitBox_subset_closedCube _ hu)
  letI : MetricSpace (ProbabilityMeasure (ℝ × (Fin (n + 1) → ℝ))) :=
    TopologicalSpace.metrizableSpaceMetric _
  -- thresholds beyond which both normalisers are positive
  have hev : ∀ m, ∃ N₀ : ℝ, ∀ N ≥ N₀, 0 < origPhaseIntegral n h k β N 1 (ξ m) η ∧
      0 < origPhaseIntegral n h k β N 1 ξ₀ η := fun m =>
    eventually_atTop.1 ((origPhaseIntegral_eventually_pos n h k hk hβ hηc hηnn hmin hatt hW
      (hξc m)).and (origPhaseIntegral_eventually_pos n h k hk hβ hηc hηnn hmin hatt hW hξ₀c))
  choose N₀ hN₀ using hev
  obtain ⟨Nm, hNm⟩ : ∃ Nm : ℕ → ℕ → ℝ, ∀ m j : ℕ, Nm m j = max (N₀ m) 1 + 1 + (j : ℝ) :=
    ⟨fun m j => max (N₀ m) 1 + 1 + (j : ℝ), fun _ _ => rfl⟩
  have hNm1 : ∀ (m j : ℕ), 1 < Nm m j := fun m j => by
    rw [hNm]; have := le_max_right (N₀ m) 1; have : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith
  have hNm0 : ∀ (m j : ℕ), N₀ m ≤ Nm m j := fun m j => by
    rw [hNm]; have := le_max_left (N₀ m) 1; have : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith
  have hNmj : ∀ (m j : ℕ), (j : ℝ) ≤ Nm m j := fun m j => by
    rw [hNm]; have := le_max_right (N₀ m) 1; linarith
  have hZξ : ∀ (m j : ℕ), 0 < origPhaseIntegral n h k β (Nm m j) 1 (ξ m) η := fun m j =>
    (hN₀ m _ (hNm0 m j)).1
  have hZ0 : ∀ (m j : ℕ), 0 < origPhaseIntegral n h k β (Nm m j) 1 ξ₀ η := fun m j =>
    (hN₀ m _ (hNm0 m j)).2
  -- fixed-phase convergence for each `m`, then pick `j` so the distance is below `1/(m+1)`
  have hfix : ∀ m, ∃ J : ℕ, ∀ j ≥ J,
      @dist (ProbabilityMeasure (ℝ × (Fin (n + 1) → ℝ))) _
        ⟨phaseJointLaw n h k β (Nm m j) (ξ m) η, phaseJointLaw_isProbabilityMeasure n h k
          (Nm m j) hβ.le (hξc m) hηc hηnn' (hZξ m j)⟩
        ⟨spatialJointFaceLaw h k l β (ξ m) η, spatialJointFaceLaw_isProbabilityMeasure h k
          hk hl0 hβ hmin (hξc m) hηc hηnn (spatialMass_pos_of_face h k hk l β (ξ m) η
            (spatialFace_pos_of_faceWeight h k hk hl0 hβ hmin (hξc m) hηc hηnn hW))⟩ <
        1 / ((m : ℝ) + 1) := fun m => by
    have hN : Tendsto (Nm m) atTop atTop :=
      tendsto_atTop_mono (hNmj m) tendsto_natCast_atTop_atTop
    have := spatialJointLaw_tendsto n h k hk hβ hηc hηnn hmin hatt (hξc m)
      (spatialFace_pos_of_faceWeight h k hk hl0 hβ hmin (hξc m) hηc hηnn hW) (Nm m) (hNm1 m) hN
      (hZξ m)
    exact Metric.tendsto_atTop.1 this _ (by positivity)
  choose J hJ using hfix
  -- the moving-phase theorem along `N_m = Nm m (J m + m)`
  have hN : Tendsto (fun m => Nm m (J m + m)) atTop atTop := by
    refine tendsto_atTop_mono (fun m => ?_) tendsto_natCast_atTop_atTop
    calc (m : ℝ) ≤ ((J m + m : ℕ) : ℝ) := by
          push_cast; linarith [(Nat.cast_nonneg (J m) : (0 : ℝ) ≤ J m)]
      _ ≤ Nm m (J m + m) := hNmj m _
  have hmov := movingPhaseJointLaw_tendsto n h k hk hβ hηc hηnn hmin hatt hW hξ₀c
    (fun m => Nm m (J m + m)) (fun m => hNm1 m _) hN ξ (fun m => (hξc m).measurable) ε hε hξ
    (fun m => hZξ m _) (fun m => hZ0 m _)
  have hmov' := tendsto_iff_dist_tendsto_zero.1 hmov
  refine tendsto_iff_dist_tendsto_zero.2 ?_
  refine squeeze_zero (fun _ => dist_nonneg) (fun m => ?_)
    ((tendsto_one_div_add_atTop_nhds_zero_nat.add hmov').trans (by rw [zero_add]))
  exact (dist_triangle_left _ _ _).trans (add_le_add (hJ m _ (Nat.le_add_right _ _)).le le_rfl)

end Grammar
