/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.SpatialJointMoving

/-!
# The compact phase space and fixed-`N` phase continuity

Phases live in `C(K, ℝ)` for the compact cube `K = [0,1]^d` (`PhaseDomain`), a Polish space under
the sup norm.  A phase `p` is extended to all of `ℝ^d` by coordinatewise clamping (`extPhase`),
which is continuous, agrees with `p` on the cube, and is `1`-Lipschitz for the sup norm
(`abs_extPhase_sub_le`).

Main results.
* `origPhaseIntegral_pos`: the chart normaliser is positive for **every** `N` and every continuous
  phase when the face weight is positive (the amplitude is positive on an open subset of the box).
* `continuous_phaseJointLaw_integral`, `continuous_phaseJointLawP`: at fixed `N`, the joint law
  `Q_N(ext p)` of `(NK, u)` is a continuous function of the phase `p ∈ C(K, ℝ)` (dominated
  convergence with the constant-phase envelope `F_{‖p₀‖+1}`).
* `phaseObservable`, `limitObservable`: the finite observable vectors
  `p ↦ (∫ g_i dQ_N(ext p))_i` and `p ↦ (∫ g_i dQ̃(ext p))_i`; the former is continuous, hence
  measurable, and converges to the latter along every `N_{κ_j} → ∞`, `x_j → p`
  (`phaseObservable_tendsto_seq`), the arbitrary-index sequential form of continuous convergence.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

open BoundedContinuousFunction

/-! ### The compact phase domain and clamping -/

/-- The compact phase domain `K = [0,1]^d` as a type. -/
abbrev PhaseDomain (n : ℕ) : Type := ↥(closedCube (n + 1))

instance (n : ℕ) : CompactSpace (PhaseDomain n) :=
  isCompact_iff_compactSpace.1 (isCompact_closedCube (n + 1))

/-- The extension of a phase on the cube to `ℝ^d` by clamping. -/
def extPhase {n : ℕ} (p : C(PhaseDomain n, ℝ)) : (Fin (n + 1) → ℝ) → ℝ :=
  fun x => p (clampCube (n + 1) x)

theorem continuous_extPhase {n : ℕ} (p : C(PhaseDomain n, ℝ)) : Continuous (extPhase p) :=
  p.continuous.comp (continuous_clampCube (n + 1))

theorem extPhase_apply_of_mem {n : ℕ} (p : C(PhaseDomain n, ℝ)) {x : Fin (n + 1) → ℝ}
    (hx : x ∈ closedCube (n + 1)) : extPhase p x = p ⟨x, hx⟩ := by
  unfold extPhase
  congr 1
  exact Subtype.ext (clampCube_of_mem hx)

/-- The extension is `1`-Lipschitz for the sup norm: `|ext p (x) − ext q (x)| ≤ ‖p − q‖`. -/
theorem abs_extPhase_sub_le {n : ℕ} (p q : C(PhaseDomain n, ℝ)) (x : Fin (n + 1) → ℝ) :
    |extPhase p x - extPhase q x| ≤ ‖p - q‖ := by
  have := ContinuousMap.norm_coe_le_norm (p - q) (clampCube (n + 1) x)
  simpa [extPhase, Real.norm_eq_abs] using this

theorem abs_extPhase_le {n : ℕ} (p : C(PhaseDomain n, ℝ)) (x : Fin (n + 1) → ℝ) :
    |extPhase p x| ≤ ‖p‖ := by
  have := ContinuousMap.norm_coe_le_norm p (clampCube (n + 1) x)
  simpa [extPhase, Real.norm_eq_abs] using this

/-! ### Unconditional positivity of the chart normaliser -/

theorem continuous_phaseIntegrand_fun (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N : ℝ)
    {ξ η : (Fin (n + 1) → ℝ) → ℝ} (hξc : Continuous ξ) (hηc : Continuous η) :
    Continuous (phaseIntegrand n h k β N ξ η) := by
  unfold phaseIntegrand
  fun_prop

/-- **Positivity of the chart normaliser** for every `N` and every continuous phase, when the
face weight is positive: `η` is then positive at a point of the cube, hence on an open subset of
the open box, where the integrand is strictly positive. -/
theorem origPhaseIntegral_pos (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N : ℝ)
    {η : (Fin (n + 1) → ℝ) → ℝ} (hηc : Continuous η) (hηnn : ∀ v ∈ closedCube (n + 1), 0 ≤ η v)
    {l : ℝ} (hW : 0 < ∫ u in unitBox (n + 1), faceWeight h k l η u)
    {ξ : (Fin (n + 1) → ℝ) → ℝ} (hξc : Continuous ξ) :
    0 < origPhaseIntegral n h k β N 1 ξ η := by
  have hηnn' : ∀ u ∈ unitBox (n + 1), 0 ≤ η u := fun u hu =>
    hηnn u (unitBox_subset_closedCube _ hu)
  obtain ⟨v₀, hv₀, hpos⟩ : ∃ v₀ ∈ closedCube (n + 1), 0 < η v₀ := by
    by_contra hcon
    push Not at hcon
    have hzero : ∀ u ∈ unitBox (n + 1), faceWeight h k l η u = 0 := fun u hu => by
      have hv := faceProj_mem_closedCube h k l (unitBox_subset_closedCube _ hu)
      unfold faceWeight
      rw [le_antisymm (hcon _ hv) (hηnn _ hv), zero_mul]
    rw [setIntegral_congr_fun (measurableSet_unitBox _) hzero, integral_zero] at hW
    exact lt_irrefl _ hW
  have hU : IsOpen {x : Fin (n + 1) → ℝ | 0 < η x} := isOpen_lt continuous_const hηc
  have hO : IsOpen (Set.pi univ fun _ : Fin (n + 1) => Ioo (0 : ℝ) 1) :=
    isOpen_set_pi finite_univ fun _ _ => isOpen_Ioo
  have hcl : v₀ ∈ closure (Set.pi univ fun _ : Fin (n + 1) => Ioo (0 : ℝ) 1) := by
    rw [closure_pi_set]
    intro i _
    simp only [closure_Ioo (zero_ne_one' ℝ)]
    exact hv₀ i (mem_univ _)
  obtain ⟨x, hxU, hxO⟩ := mem_closure_iff.1 hcl _ hU hpos
  rw [origPhaseIntegral_eq_integral_phaseIntegrand,
    setIntegral_pos_iff_support_of_nonneg_ae ((ae_restrict_iff' (measurableSet_unitBox _)).2
      (Eventually.of_forall fun u hu => phaseIntegrand_nonneg n h k β N hηnn' hu))
      (integrableOn_unitBox_of_continuous _ (continuous_phaseIntegrand_fun n h k β N hξc hηc))]
  refine lt_of_lt_of_le (IsOpen.measure_pos volume (hU.inter hO) ⟨x, hxU, hxO⟩) (measure_mono ?_)
  rintro y ⟨hyU, hyO⟩
  have hy : ∀ i, 0 < y i ∧ y i < 1 := fun i => hyO i (mem_univ _)
  refine ⟨?_, fun i _ => ⟨(hy i).1, (hy i).2.le⟩⟩
  change phaseIntegrand n h k β N ξ η y ≠ 0
  unfold phaseIntegrand
  exact (mul_pos (mul_pos hyU (Finset.prod_pos fun i _ => pow_pos (hy i).1 _))
    (Real.exp_pos _)).ne'

/-! ### Fixed-`N` continuity in the phase -/

/-- Chart integrals of a bounded observable against the phase integrand depend continuously on
the phase `p ∈ C(K, ℝ)` (dominated convergence on the box with the envelope `F_{‖p₀‖+1}`). -/
theorem continuous_phaseIntegrand_integral (n : ℕ) (h k : Fin (n + 1) → ℕ) {β : ℝ} (N : ℝ)
    (hβ : 0 ≤ β) {η : (Fin (n + 1) → ℝ) → ℝ} (hηc : Continuous η)
    (hηnn : ∀ u ∈ unitBox (n + 1), 0 ≤ η u) {G : (Fin (n + 1) → ℝ) → ℝ} (hGm : Measurable G)
    {C : ℝ} (hG : ∀ u ∈ unitBox (n + 1), |G u| ≤ C) :
    Continuous fun p : C(PhaseDomain n, ℝ) =>
      ∫ u in unitBox (n + 1), phaseIntegrand n h k β N (extPhase p) η u * G u := by
  refine continuous_iff_continuousAt.2 fun p₀ => ?_
  refine continuousAt_of_dominated (bound := fun u =>
      constPhaseIntegrand n h k β N η (‖p₀‖ + 1) u * C) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun p => ((measurable_phaseIntegrand n h k β N
      (continuous_extPhase p).measurable hηc.measurable).mul hGm).aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds p₀ one_pos] with p hp
    rw [Metric.mem_ball, dist_eq_norm] at hp
    have hpn : ‖p‖ ≤ ‖p₀‖ + 1 := by have := norm_sub_norm_le p p₀; linarith
    refine (ae_restrict_iff' (measurableSet_unitBox _)).2 (Eventually.of_forall fun u hu => ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (phaseIntegrand_nonneg n h k β N hηnn hu)]
    refine mul_le_mul ?_ (hG u hu) (abs_nonneg _) (constPhaseIntegrand_nonneg n h k β N hηnn _ hu)
    rw [← phaseIntegrand_const]
    exact phaseIntegrand_mono n h k N hβ hηnn hu
      ((le_abs_self _).trans ((abs_extPhase_le p u).trans hpn))
  · exact (integrableOn_unitBox_of_continuous _
      (continuous_constPhaseIntegrand n h k β N hηc _)).mul_const C
  · refine Eventually.of_forall fun u => Continuous.continuousAt ?_
    unfold phaseIntegrand extPhase
    fun_prop

/-- Integrals of bounded continuous tests against the fixed-`N` joint law are continuous in the
phase. -/
theorem continuous_phaseJointLaw_integral (n : ℕ) (h k : Fin (n + 1) → ℕ) {β : ℝ} (N : ℝ)
    (hβ : 0 ≤ β) {η : (Fin (n + 1) → ℝ) → ℝ} (hηc : Continuous η)
    (hηnn : ∀ v ∈ closedCube (n + 1), 0 ≤ η v) {l : ℝ}
    (hW : 0 < ∫ u in unitBox (n + 1), faceWeight h k l η u)
    (g : (ℝ × (Fin (n + 1) → ℝ)) →ᵇ ℝ) :
    Continuous fun p : C(PhaseDomain n, ℝ) =>
      ∫ z, g z ∂(phaseJointLaw n h k β N (extPhase p) η) := by
  have hηnn' : ∀ u ∈ unitBox (n + 1), 0 ≤ η u := fun u hu =>
    hηnn u (unitBox_subset_closedCube _ hu)
  have heq : ∀ p : C(PhaseDomain n, ℝ), ∫ z, g z ∂(phaseJointLaw n h k β N (extPhase p) η) =
      (∫ u in unitBox (n + 1), phaseIntegrand n h k β N (extPhase p) η u *
        g (N * ∏ i, u i ^ (2 * k i), u)) / origPhaseIntegral n h k β N 1 (extPhase p) η :=
    fun p => phaseJointLaw_integral n h k β N (continuous_extPhase p).measurable hηc hηnn'
      (origPhaseIntegral_pos n h k β N hηc hηnn hW (continuous_extPhase p)) g.continuous.measurable
  simp_rw [heq, origPhaseIntegral_eq_integral_phaseIntegrand]
  refine Continuous.div ?_ ?_ fun p => ?_
  · exact continuous_phaseIntegrand_integral n h k N hβ hηc hηnn'
      (g.continuous.measurable.comp (measurable_energyPair n k N))
      (fun u _ => by rw [← Real.norm_eq_abs]; exact g.norm_coe_le_norm _)
  · have := continuous_phaseIntegrand_integral n h k N hβ hηc hηnn' (G := fun _ => (1 : ℝ))
      measurable_const (C := 1) (fun u _ => by simp)
    simpa only [mul_one] using this
  · rw [← origPhaseIntegral_eq_integral_phaseIntegrand]
    exact (origPhaseIntegral_pos n h k β N hηc hηnn hW (continuous_extPhase p)).ne'

/-- The fixed-`N` joint law of `(NK, u)` as a probability-measure-valued function of the phase. -/
noncomputable def phaseJointLawP (n : ℕ) (h k : Fin (n + 1) → ℕ) {β : ℝ} (N : ℝ)
    (hβ : 0 ≤ β) {η : (Fin (n + 1) → ℝ) → ℝ} (hηc : Continuous η)
    (hηnn : ∀ v ∈ closedCube (n + 1), 0 ≤ η v) {l : ℝ}
    (hW : 0 < ∫ u in unitBox (n + 1), faceWeight h k l η u) (p : C(PhaseDomain n, ℝ)) :
    ProbabilityMeasure (ℝ × (Fin (n + 1) → ℝ)) :=
  ⟨phaseJointLaw n h k β N (extPhase p) η, phaseJointLaw_isProbabilityMeasure n h k N hβ
    (continuous_extPhase p) hηc (fun u hu => hηnn u (unitBox_subset_closedCube _ hu))
    (origPhaseIntegral_pos n h k β N hηc hηnn hW (continuous_extPhase p))⟩

/-- **Fixed-`N` continuity of the joint law in the phase**, in `ProbabilityMeasure (ℝ × ℝ^d)`. -/
theorem continuous_phaseJointLawP (n : ℕ) (h k : Fin (n + 1) → ℕ) {β : ℝ} (N : ℝ)
    (hβ : 0 ≤ β) {η : (Fin (n + 1) → ℝ) → ℝ} (hηc : Continuous η)
    (hηnn : ∀ v ∈ closedCube (n + 1), 0 ≤ η v) {l : ℝ}
    (hW : 0 < ∫ u in unitBox (n + 1), faceWeight h k l η u) :
    Continuous (phaseJointLawP n h k N hβ hηc hηnn hW) := by
  refine continuous_iff_continuousAt.2 fun p₀ => ?_
  refine ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.2 fun g => ?_
  exact (continuous_phaseJointLaw_integral n h k N hβ hηc hηnn hW g).continuousAt

/-! ### Finite observable vectors -/

/-- The finite-`N` observable vector `p ↦ (∫ g_i dQ_N(ext p))_i`. -/
noncomputable def phaseObservable (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N : ℝ)
    (η : (Fin (n + 1) → ℝ) → ℝ) {r : ℕ} (g : Fin r → (ℝ × (Fin (n + 1) → ℝ)) →ᵇ ℝ)
    (p : C(PhaseDomain n, ℝ)) : Fin r → ℝ :=
  fun i => ∫ z, g i z ∂(phaseJointLaw n h k β N (extPhase p) η)

/-- The limiting observable vector `p ↦ (∫ g_i dQ̃(ext p))_i`. -/
noncomputable def limitObservable {n : ℕ} (h k : Fin (n + 1) → ℕ) (l β : ℝ)
    (η : (Fin (n + 1) → ℝ) → ℝ) {r : ℕ} (g : Fin r → (ℝ × (Fin (n + 1) → ℝ)) →ᵇ ℝ)
    (p : C(PhaseDomain n, ℝ)) : Fin r → ℝ :=
  fun i => ∫ z, g i z ∂(spatialJointFaceLaw h k l β (extPhase p) η)

theorem continuous_phaseObservable (n : ℕ) (h k : Fin (n + 1) → ℕ) {β : ℝ} (N : ℝ)
    (hβ : 0 ≤ β) {η : (Fin (n + 1) → ℝ) → ℝ} (hηc : Continuous η)
    (hηnn : ∀ v ∈ closedCube (n + 1), 0 ≤ η v) {l : ℝ}
    (hW : 0 < ∫ u in unitBox (n + 1), faceWeight h k l η u) {r : ℕ}
    (g : Fin r → (ℝ × (Fin (n + 1) → ℝ)) →ᵇ ℝ) :
    Continuous (phaseObservable n h k β N η g) :=
  continuous_pi fun i => continuous_phaseJointLaw_integral n h k N hβ hηc hηnn hW (g i)

theorem measurable_phaseObservable (n : ℕ) (h k : Fin (n + 1) → ℕ) {β : ℝ} (N : ℝ)
    (hβ : 0 ≤ β) {η : (Fin (n + 1) → ℝ) → ℝ} (hηc : Continuous η)
    (hηnn : ∀ v ∈ closedCube (n + 1), 0 ≤ η v) {l : ℝ}
    (hW : 0 < ∫ u in unitBox (n + 1), faceWeight h k l η u) {r : ℕ}
    (g : Fin r → (ℝ × (Fin (n + 1) → ℝ)) →ᵇ ℝ) :
    Measurable (phaseObservable n h k β N η g) :=
  (continuous_phaseObservable n h k N hβ hηc hηnn hW g).measurable

/-- **Arbitrary-index sequential continuous convergence** of the observable vectors: along any
`N_{κ_j} → ∞` and `x_j → p` in `C(K, ℝ)`, `T_{κ_j}(x_j) → T(p)`. -/
theorem phaseObservable_tendsto_seq (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    {β : ℝ} (hβ : 0 < β) {η : (Fin (n + 1) → ℝ) → ℝ} (hηc : Continuous η)
    (hηnn : ∀ v ∈ closedCube (n + 1), 0 ≤ η v) {l : ℝ} (hmin : ∀ i, l ≤ ratioExp h k i)
    (hatt : ∃ i, ratioExp h k i = l) (hW : 0 < ∫ u in unitBox (n + 1), faceWeight h k l η u)
    (Nseq : ℕ → ℝ) (hN1 : ∀ m, 1 < Nseq m) (hN : Tendsto Nseq atTop atTop) {r : ℕ}
    (g : Fin r → (ℝ × (Fin (n + 1) → ℝ)) →ᵇ ℝ) (κ : ℕ → ℕ) (hκ : Tendsto κ atTop atTop)
    (x : ℕ → C(PhaseDomain n, ℝ)) (p : C(PhaseDomain n, ℝ)) (hx : Tendsto x atTop (𝓝 p)) :
    Tendsto (fun j => phaseObservable n h k β (Nseq (κ j)) η g (x j)) atTop
      (𝓝 (limitObservable h k l β η g p)) := by
  refine tendsto_pi_nhds.2 fun i => ?_
  have hε : Tendsto (fun j => ‖x j - p‖) atTop (𝓝 0) :=
    (tendsto_iff_norm_sub_tendsto_zero.1 hx)
  have := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1
    (movingPhaseJointLaw_tendsto n h k hk hβ hηc hηnn hmin hatt hW (continuous_extPhase p)
      (fun j => Nseq (κ j)) (fun j => hN1 _) (hN.comp hκ) (fun j => extPhase (x j))
      (fun j => (continuous_extPhase (x j)).measurable) (fun j => ‖x j - p‖) hε
      (fun j u _ => abs_extPhase_sub_le (x j) p u)
      (fun j => origPhaseIntegral_pos n h k β _ hηc hηnn hW (continuous_extPhase (x j)))
      (fun j => origPhaseIntegral_pos n h k β _ hηc hηnn hW (continuous_extPhase p))) (g i)
  exact this

end Grammar
