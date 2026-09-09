/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.SpatialMoments
import Grammar.PhaseStability

/-!
# Moving continuous phases (unit 359; Astra #44 unit 5)

The tilt bound of Headline LXVIII holds around any continuous base phase `ξ₀`: for measurable `ξ`
with `|ξ − ξ₀| ≤ ε` on the box and `|g| ≤ G`,
`|E_ξ[g] − E_{ξ₀}[g]| ≤ 2G (𝒵_N[ξ₀+ε] − 𝒵_N[ξ₀])/𝒵_N[ξ₀−ε]` (`phase_observable_bound_base`).  The
face functional is continuous under constant shifts of the phase
(`spatialFace_shift_continuousAt`, dominated convergence) and positive under a positive face
weight (`spatialFace_pos_of_faceWeight`), so for `‖ξ_m − ξ₀‖_∞ ≤ ε_m → 0` the bounded posterior
expectations under `ξ_m` and `ξ₀` merge (`spatialPhase_perturbation_tendsto`) and **the posterior
law of `NK` under the moving phases converges weakly to the spatial limit `ρ^{ξ₀}`**
(`movingPhaseEnergyLaw_tendsto`): the deterministic input for random spatial phase fields.
-/

namespace Grammar

open MeasureTheory Filter Topology Set

/-! ### The tilt bound around a spatial base phase -/

theorem phaseIntegrand_eq_mul_base (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N : ℝ)
    (ξ ξ₀ η : (Fin (n + 1) → ℝ) → ℝ) (u : Fin (n + 1) → ℝ) :
    phaseIntegrand n h k β N ξ η u = phaseIntegrand n h k β N ξ₀ η u *
      Real.exp (β * (Real.sqrt N * ∏ i, u i ^ k i) * (ξ u - ξ₀ u)) := by
  unfold phaseIntegrand
  rw [mul_assoc (η u * ∏ i, u i ^ h i), ← Real.exp_add]
  congr 2
  ring

theorem abs_phaseIntegrand_sub_le_base (n : ℕ) (h k : Fin (n + 1) → ℕ) {β : ℝ} (N : ℝ)
    (hβ : 0 ≤ β) {ξ ξ₀ η : (Fin (n + 1) → ℝ) → ℝ} (hηnn : ∀ u ∈ unitBox (n + 1), 0 ≤ η u) {ε : ℝ}
    {u : Fin (n + 1) → ℝ} (hu : u ∈ unitBox (n + 1)) (hξ : |ξ u - ξ₀ u| ≤ ε) :
    |phaseIntegrand n h k β N ξ η u - phaseIntegrand n h k β N ξ₀ η u| ≤
      phaseIntegrand n h k β N (fun u => ξ₀ u + ε) η u - phaseIntegrand n h k β N ξ₀ η u := by
  have hu' : ∀ i, 0 < u i ∧ u i ≤ 1 := fun i => Set.mem_univ_pi.1 hu i
  have hP : 0 ≤ ∏ i, u i ^ k i := Finset.prod_nonneg fun i _ => pow_nonneg (hu' i).1.le _
  have hc : 0 ≤ β * (Real.sqrt N * ∏ i, u i ^ k i) := by positivity
  have hF : 0 ≤ phaseIntegrand n h k β N ξ₀ η u := phaseIntegrand_nonneg n h k β N hηnn hu
  rw [phaseIntegrand_eq_mul_base n h k β N ξ ξ₀ η u,
    phaseIntegrand_eq_mul_base n h k β N (fun u => ξ₀ u + ε) ξ₀ η u]
  simp only [add_sub_cancel_left]
  rw [← mul_sub_one, ← mul_sub_one, abs_mul, abs_of_nonneg hF]
  refine mul_le_mul_of_nonneg_left ((abs_exp_sub_one_le_exp_abs_sub_one _).trans ?_) hF
  rw [abs_mul, abs_of_nonneg hc]
  exact sub_le_sub_right (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hξ hc)) 1

theorem integrableOn_phaseIntegrand_of_bound (n : ℕ) (h k : Fin (n + 1) → ℕ) {β : ℝ} (N : ℝ)
    (hβ : 0 ≤ β) {ξ η : (Fin (n + 1) → ℝ) → ℝ} (hξm : Measurable ξ) (hηc : Continuous η)
    (hηnn : ∀ u ∈ unitBox (n + 1), 0 ≤ η u) {C : ℝ} (hξ : ∀ u ∈ unitBox (n + 1), |ξ u| ≤ C) :
    IntegrableOn (phaseIntegrand n h k β N ξ η) (unitBox (n + 1)) :=
  integrableOn_phaseIntegrand n h k N hβ hξm hηc hηnn (a := 0) (ε := C)
    fun u hu => by rw [sub_zero]; exact hξ u hu

/-- **Tilt bound around a continuous base phase**: for `|ξ − ξ₀| ≤ ε` on the box and `|g| ≤ G`,
`|E_ξ[g] − E_{ξ₀}[g]| ≤ 2G (𝒵_N[ξ₀+ε] − 𝒵_N[ξ₀])/𝒵_N[ξ₀−ε]`. -/
theorem phase_observable_bound_base (n : ℕ) (h k : Fin (n + 1) → ℕ) {β : ℝ} (N : ℝ) (hβ : 0 ≤ β)
    {ξ ξ₀ η : (Fin (n + 1) → ℝ) → ℝ} (hξm : Measurable ξ) (hξ₀c : Continuous ξ₀)
    (hηc : Continuous η) (hηnn : ∀ u ∈ unitBox (n + 1), 0 ≤ η u) {ε : ℝ} (hε : 0 ≤ ε)
    (hξ : ∀ u ∈ unitBox (n + 1), |ξ u - ξ₀ u| ≤ ε) {g : (Fin (n + 1) → ℝ) → ℝ}
    (hgm : Measurable g) {G : ℝ} (hG0 : 0 ≤ G) (hG : ∀ u ∈ unitBox (n + 1), |g u| ≤ G)
    (hZ : 0 < origPhaseIntegral n h k β N 1 (fun u => ξ₀ u - ε) η) :
    |(∫ u in unitBox (n + 1), phaseIntegrand n h k β N ξ η u * g u) /
        origPhaseIntegral n h k β N 1 ξ η -
      (∫ u in unitBox (n + 1), phaseIntegrand n h k β N ξ₀ η u * g u) /
        origPhaseIntegral n h k β N 1 ξ₀ η| ≤
      2 * G * (origPhaseIntegral n h k β N 1 (fun u => ξ₀ u + ε) η -
        origPhaseIntegral n h k β N 1 ξ₀ η) /
        origPhaseIntegral n h k β N 1 (fun u => ξ₀ u - ε) η := by
  have hbox := measurableSet_unitBox (n + 1)
  obtain ⟨C, hC⟩ := (isCompact_closedCube (n + 1)).exists_bound_of_continuousOn hξ₀c.continuousOn
  have hC' : ∀ u ∈ unitBox (n + 1), |ξ₀ u| ≤ C := fun u hu =>
    (Real.norm_eq_abs _).symm.trans_le (hC u (unitBox_subset_closedCube _ hu))
  -- integrability of the four integrands
  have iξ : IntegrableOn (phaseIntegrand n h k β N ξ η) (unitBox (n + 1)) :=
    integrableOn_phaseIntegrand_of_bound n h k N hβ hξm hηc hηnn (C := C + ε) fun u hu => by
      have := abs_sub_abs_le_abs_sub (ξ u) (ξ₀ u)
      linarith [hξ u hu, hC' u hu]
  have i0 : IntegrableOn (phaseIntegrand n h k β N ξ₀ η) (unitBox (n + 1)) :=
    integrableOn_phaseIntegrand_of_bound n h k N hβ hξ₀c.measurable hηc hηnn hC'
  have ip : IntegrableOn (phaseIntegrand n h k β N (fun u => ξ₀ u + ε) η) (unitBox (n + 1)) :=
    integrableOn_phaseIntegrand_of_bound n h k N hβ (hξ₀c.measurable.add_const ε) hηc hηnn
      (C := C + ε) fun u hu => by
        have := abs_add_le (ξ₀ u) ε
        rw [abs_of_nonneg hε] at this
        linarith [hC' u hu]
  have im : IntegrableOn (phaseIntegrand n h k β N (fun u => ξ₀ u - ε) η) (unitBox (n + 1)) :=
    integrableOn_phaseIntegrand_of_bound n h k N hβ (hξ₀c.measurable.sub_const ε) hηc hηnn
      (C := C + ε) fun u hu => by
        have := abs_sub (ξ₀ u) ε
        rw [abs_of_nonneg hε] at this
        linarith [hC' u hu]
  have hgbd : ∀ (F : (Fin (n + 1) → ℝ) → ℝ), IntegrableOn F (unitBox (n + 1)) →
      IntegrableOn (fun u => F u * g u) (unitBox (n + 1)) := fun F hF => by
    have := Integrable.bdd_mul (c := G) hF hgm.aestronglyMeasurable (by
      rw [ae_restrict_iff' hbox]
      exact Eventually.of_forall fun u hu => by rw [Real.norm_eq_abs]; exact hG u hu)
    exact this.congr (Eventually.of_forall fun u => mul_comm _ _)
  -- masses
  have hmξ : origPhaseIntegral n h k β N 1 (fun u => ξ₀ u - ε) η ≤
      origPhaseIntegral n h k β N 1 ξ η :=
    setIntegral_mono_on im iξ hbox fun u hu =>
      phaseIntegrand_mono n h k N hβ (ξ := fun u => ξ₀ u - ε) (ξ' := ξ) hηnn hu (by
        have := (abs_le.1 (hξ u hu)).1
        change ξ₀ u - ε ≤ ξ u
        linarith)
  have hm0 : origPhaseIntegral n h k β N 1 (fun u => ξ₀ u - ε) η ≤
      origPhaseIntegral n h k β N 1 ξ₀ η :=
    setIntegral_mono_on im i0 hbox fun u hu =>
      phaseIntegrand_mono n h k N hβ (ξ := fun u => ξ₀ u - ε) (ξ' := ξ₀) hηnn hu (by linarith)
  have hZξ : 0 < origPhaseIntegral n h k β N 1 ξ η := lt_of_lt_of_le hZ hmξ
  have hZ0 : 0 < origPhaseIntegral n h k β N 1 ξ₀ η := lt_of_lt_of_le hZ hm0
  set Zξ := origPhaseIntegral n h k β N 1 ξ η with hZξdef
  set Z0 := origPhaseIntegral n h k β N 1 ξ₀ η with hZ0def
  set Zp := origPhaseIntegral n h k β N 1 (fun u => ξ₀ u + ε) η with hZpdef
  set Zm := origPhaseIntegral n h k β N 1 (fun u => ξ₀ u - ε) η with hZmdef
  set Iξ := ∫ u in unitBox (n + 1), phaseIntegrand n h k β N ξ η u * g u with hIξ
  set I0 := ∫ u in unitBox (n + 1), phaseIntegrand n h k β N ξ₀ η u * g u with hI0
  -- the tilt discrepancy
  have iD : IntegrableOn (fun u => |phaseIntegrand n h k β N ξ η u -
      phaseIntegrand n h k β N ξ₀ η u|) (unitBox (n + 1)) := (iξ.sub i0).norm
  have hD : ∫ u in unitBox (n + 1), |phaseIntegrand n h k β N ξ η u -
      phaseIntegrand n h k β N ξ₀ η u| ≤ Zp - Z0 := by
    rw [hZpdef, hZ0def, origPhaseIntegral_eq_integral_phaseIntegrand,
      origPhaseIntegral_eq_integral_phaseIntegrand, ← integral_sub ip i0]
    exact setIntegral_mono_on iD (ip.sub i0) hbox fun u hu =>
      abs_phaseIntegrand_sub_le_base n h k N hβ hηnn hu (hξ u hu)
  have hD0 : 0 ≤ Zp - Z0 := le_trans (integral_nonneg fun _ => abs_nonneg _) hD
  have h1 : |Iξ - I0| ≤ G * (Zp - Z0) := by
    rw [hIξ, hI0, ← integral_sub (hgbd _ iξ) (hgbd _ i0), ← Real.norm_eq_abs]
    refine (norm_integral_le_integral_norm _).trans ?_
    refine le_trans (setIntegral_mono_on ((hgbd _ iξ).sub (hgbd _ i0)).norm (iD.const_mul G) hbox
      fun u hu => ?_) ?_
    · change ‖phaseIntegrand n h k β N ξ η u * g u - phaseIntegrand n h k β N ξ₀ η u * g u‖ ≤
        G * |phaseIntegrand n h k β N ξ η u - phaseIntegrand n h k β N ξ₀ η u|
      rw [← sub_mul, norm_mul, mul_comm, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hG u hu) (abs_nonneg _)
    · rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left hD hG0
  have h2 : |I0| ≤ G * Z0 := by
    rw [hI0, hZ0def, origPhaseIntegral_eq_integral_phaseIntegrand, ← Real.norm_eq_abs]
    refine (norm_integral_le_integral_norm _).trans ?_
    refine le_trans (setIntegral_mono_on (hgbd _ i0).norm (i0.const_mul G) hbox
      fun u hu => ?_) ?_
    · change ‖phaseIntegrand n h k β N ξ₀ η u * g u‖ ≤ G * phaseIntegrand n h k β N ξ₀ η u
      rw [norm_mul, mul_comm, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (phaseIntegrand_nonneg n h k β N hηnn hu)]
      exact mul_le_mul_of_nonneg_right (hG u hu) (phaseIntegrand_nonneg n h k β N hηnn hu)
    · rw [integral_const_mul]
  have h3 : |Zξ - Z0| ≤ Zp - Z0 := by
    rw [hZξdef, hZ0def, origPhaseIntegral_eq_integral_phaseIntegrand,
      origPhaseIntegral_eq_integral_phaseIntegrand, ← integral_sub iξ i0, ← Real.norm_eq_abs]
    exact (norm_integral_le_integral_norm _).trans hD
  have hnum : |Iξ * Z0 - Zξ * I0| ≤ 2 * G * (Zp - Z0) * Z0 := by
    have e : Iξ * Z0 - Zξ * I0 = (Iξ - I0) * Z0 - I0 * (Zξ - Z0) := by ring
    rw [e]
    calc |(Iξ - I0) * Z0 - I0 * (Zξ - Z0)| ≤ |(Iξ - I0) * Z0| + |I0 * (Zξ - Z0)| := abs_sub _ _
      _ = |Iξ - I0| * Z0 + |I0| * |Zξ - Z0| := by
          rw [abs_mul, abs_mul, abs_of_pos hZ0]
      _ ≤ G * (Zp - Z0) * Z0 + G * Z0 * (Zp - Z0) :=
          add_le_add (mul_le_mul_of_nonneg_right h1 hZ0.le)
            (mul_le_mul h2 h3 (abs_nonneg _) (by positivity))
      _ = 2 * G * (Zp - Z0) * Z0 := by ring
  rw [div_sub_div _ _ hZξ.ne' hZ0.ne', abs_div, abs_of_pos (mul_pos hZξ hZ0)]
  calc |Iξ * Z0 - Zξ * I0| / (Zξ * Z0) ≤ 2 * G * (Zp - Z0) * Z0 / (Zm * Z0) :=
        div_le_div₀ (by positivity) hnum (mul_pos hZ hZ0)
          (mul_le_mul_of_nonneg_right hmξ hZ0.le)
    _ = 2 * G * (Zp - Z0) / Zm := by
        rw [mul_div_mul_right _ _ hZ0.ne']

/-! ### Continuity and positivity of the face functional under constant shifts -/

/-- Positivity of the face functional from a positive face weight. -/
theorem spatialFace_pos_of_faceWeight {d : ℕ} (h k : Fin (d + 1) → ℕ) (hk : ∀ i, 0 < k i)
    {l β : ℝ} (hl : 0 < l) (hβ : 0 < β) (hmin : ∀ i, l ≤ ratioExp h k i)
    {ξ η : (Fin (d + 1) → ℝ) → ℝ} (hξc : Continuous ξ) (hηc : Continuous η)
    (hηnn : ∀ v ∈ closedCube (d + 1), 0 ≤ η v)
    (hW : 0 < ∫ u in unitBox (d + 1), faceWeight h k l η u) :
    0 < spatialFace h k l β ξ η := by
  obtain ⟨C, hC⟩ := (isCompact_closedCube (d + 1)).exists_bound_of_continuousOn hξc.continuousOn
  rw [spatialFace_eq_faceWeight]
  have hc : 0 < 1 / (((multCount (ratioExp h k) l - 1).factorial : ℝ) *
      ∏ i, if ratioExp h k i = l then (k i : ℝ) else 1) := by
    refine one_div_pos.2 (mul_pos (by positivity) (Finset.prod_pos fun i _ => ?_))
    split_ifs
    · exact_mod_cast hk i
    · exact one_pos
  have hM := phaseMoment_pos β (2 * l) (-C) hβ (by linarith)
  have hI : phaseMoment β (2 * l) (-C) * (∫ u in unitBox (d + 1), faceWeight h k l η u) ≤
      ∫ u in unitBox (d + 1),
        faceWeight h k l η u * phaseMoment β (2 * l) (ξ (faceProj h k l u)) := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on ((integrableOn_faceWeight h k hk hmin hηc).const_mul _) ?_
      (measurableSet_unitBox _) fun u hu => ?_
    · -- integrability of the face integrand: bounded moment times the face weight
      refine Integrable.bdd_mul (c := phaseMoment β (2 * l) C)
        (integrableOn_faceWeight h k hk hmin hηc)
        ((continuous_phaseMoment β (2 * l) hβ (by linarith)).measurable.comp
          (hξc.measurable.comp (measurable_faceProj h k l))).aestronglyMeasurable ?_ |>.congr
        (Eventually.of_forall fun u => mul_comm _ _)
      rw [ae_restrict_iff' (measurableSet_unitBox _)]
      refine Eventually.of_forall fun u hu => ?_
      have hfp := faceProj_mem_closedCube h k l (unitBox_subset_closedCube _ hu)
      have hb : ξ (faceProj h k l u) ≤ C :=
        (le_abs_self _).trans ((Real.norm_eq_abs _).symm.trans_le (hC _ hfp))
      change ‖phaseMoment β (2 * l) (ξ (faceProj h k l u))‖ ≤ phaseMoment β (2 * l) C
      rw [Real.norm_eq_abs, abs_of_pos (phaseMoment_pos β (2 * l) _ hβ (by linarith))]
      exact phaseMoment_le_of_le β (2 * l) _ C hβ (by linarith) hb
    · have hfp := faceProj_mem_closedCube h k l (unitBox_subset_closedCube _ hu)
      have hb : -C ≤ ξ (faceProj h k l u) := by
        have := (abs_le.1 ((Real.norm_eq_abs _).symm.trans_le (hC _ hfp))).1
        linarith
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (phaseMoment_le_of_le β (2 * l) _ _ hβ (by linarith) hb)
        (faceWeight_nonneg h k l hηnn hu)
  have : 0 < ∫ u in unitBox (d + 1),
      faceWeight h k l η u * phaseMoment β (2 * l) (ξ (faceProj h k l u)) :=
    lt_of_lt_of_le (mul_pos hM hW) hI
  positivity

/-- Continuity of the face functional under constant shifts of the phase. -/
theorem spatialFace_shift_continuousAt {d : ℕ} (h k : Fin (d + 1) → ℕ) (hk : ∀ i, 0 < k i)
    {l β : ℝ} (hl : 0 < l) (hβ : 0 < β) (hmin : ∀ i, l ≤ ratioExp h k i)
    {ξ η : (Fin (d + 1) → ℝ) → ℝ} (hξc : Continuous ξ) (hηc : Continuous η) :
    ContinuousAt (fun ε : ℝ => spatialFace h k l β (fun u => ξ u + ε) η) 0 := by
  obtain ⟨C, hC⟩ := (isCompact_closedCube (d + 1)).exists_bound_of_continuousOn hξc.continuousOn
  simp only [spatialFace_eq_faceWeight]
  refine (((continuousAt_of_dominated (F := fun ε u => faceWeight h k l η u *
      phaseMoment β (2 * l) (ξ (faceProj h k l u) + ε))
      (bound := fun u => |faceWeight h k l η u| * phaseMoment β (2 * l) (C + 1))
      ?_ ?_ ?_ ?_).const_mul _).div_const _)
  · exact Eventually.of_forall fun ε =>
      ((measurable_faceWeight h k l hηc).mul
        ((continuous_phaseMoment β (2 * l) hβ (by linarith)).measurable.comp
          ((hξc.measurable.comp (measurable_faceProj h k l)).add_const ε))).aestronglyMeasurable
  · refine Filter.eventually_of_mem (Metric.ball_mem_nhds (0 : ℝ) one_pos) fun ε hε => ?_
    rw [ae_restrict_iff' (measurableSet_unitBox _)]
    refine Eventually.of_forall fun u hu => ?_
    have hfp := faceProj_mem_closedCube h k l (unitBox_subset_closedCube _ hu)
    have hb : ξ (faceProj h k l u) + ε ≤ C + 1 := by
      have h1 := (le_abs_self _).trans ((Real.norm_eq_abs _).symm.trans_le (hC _ hfp))
      have h2 := (abs_lt.1 (by simpa [Real.dist_eq] using hε : |ε| < 1)).2
      linarith
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (phaseMoment_pos β (2 * l) _ hβ (by linarith))]
    exact mul_le_mul_of_nonneg_left (phaseMoment_le_of_le β (2 * l) _ _ hβ (by linarith) hb)
      (abs_nonneg _)
  · exact (integrableOn_faceWeight h k hk hmin hηc).norm.mul_const _
  · exact Eventually.of_forall fun u => (continuous_const.mul
      ((continuous_phaseMoment β (2 * l) hβ (by linarith)).comp
        (continuous_const.add continuous_id))).continuousAt

/-! ### Moving continuous phases -/

/-- **Bounded posterior expectations under moving phases merge with the base phase**: for
measurable phases with `|ξ_i − ξ₀| ≤ ε_i → 0` on the box and observables `|g_i| ≤ G`,
`E_{ξ_i}[g_i] − E_{ξ₀}[g_i] → 0` along `N_i → ∞`. -/
theorem spatialPhase_perturbation_tendsto (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    {β : ℝ} (hβ : 0 < β) {η : (Fin (n + 1) → ℝ) → ℝ} (hηc : Continuous η)
    (hηnn : ∀ v ∈ closedCube (n + 1), 0 ≤ η v) {l : ℝ} (hmin : ∀ i, l ≤ ratioExp h k i)
    (hatt : ∃ i, ratioExp h k i = l) (hW : 0 < ∫ u in unitBox (n + 1), faceWeight h k l η u)
    {ξ₀ : (Fin (n + 1) → ℝ) → ℝ} (hξ₀c : Continuous ξ₀) {ι : Type*} {F : Filter ι}
    (Nseq : ι → ℝ) (hN : Tendsto Nseq F atTop) (ξ : ι → (Fin (n + 1) → ℝ) → ℝ)
    (hξm : ∀ i, Measurable (ξ i)) (ε : ι → ℝ) (hε : Tendsto ε F (𝓝 0))
    (hξ : ∀ i, ∀ u ∈ unitBox (n + 1), |ξ i u - ξ₀ u| ≤ ε i) (g : ι → (Fin (n + 1) → ℝ) → ℝ)
    (hgm : ∀ i, Measurable (g i)) {G : ℝ} (hG0 : 0 ≤ G)
    (hG : ∀ i, ∀ u ∈ unitBox (n + 1), |g i u| ≤ G) :
    Tendsto (fun i =>
      (∫ u in unitBox (n + 1), phaseIntegrand n h k β (Nseq i) (ξ i) η u * g i u) /
        origPhaseIntegral n h k β (Nseq i) 1 (ξ i) η -
      (∫ u in unitBox (n + 1), phaseIntegrand n h k β (Nseq i) ξ₀ η u * g i u) /
        origPhaseIntegral n h k β (Nseq i) 1 ξ₀ η) F (𝓝 0) := by
  have hl0 : 0 < l := ratioExp_min_pos h k hk hatt
  have hηnn' : ∀ u ∈ unitBox (n + 1), 0 ≤ η u := fun u hu =>
    hηnn u (unitBox_subset_closedCube _ hu)
  -- positivity of all shifted face functionals
  have hFpos : ∀ c : ℝ, 0 < spatialFace h k l β (fun u => ξ₀ u + c) η := fun c =>
    spatialFace_pos_of_faceWeight h k hk hl0 hβ hmin (hξ₀c.add continuous_const) hηc hηnn hW
  have hFpos' : ∀ c : ℝ, 0 < spatialFace h k l β (fun u => ξ₀ u - c) η := fun c =>
    spatialFace_pos_of_faceWeight h k hk hl0 hβ hmin (hξ₀c.sub continuous_const) hηc hηnn hW
  -- the limiting bound is continuous in `ε` and vanishes at `ε = 0`
  have hcont : Tendsto (fun ε : ℝ => 2 * G *
      (spatialFace h k l β (fun u => ξ₀ u + ε) η - spatialFace h k l β ξ₀ η) /
      spatialFace h k l β (fun u => ξ₀ u - ε) η) (𝓝[>] 0) (𝓝 0) := by
    have hplus := spatialFace_shift_continuousAt h k hk hl0 hβ hmin hξ₀c hηc
    have hminus : ContinuousAt (fun ε : ℝ => spatialFace h k l β (fun u => ξ₀ u - ε) η) 0 := by
      have h0 : ContinuousAt (fun ε : ℝ => spatialFace h k l β (fun u => ξ₀ u + ε) η)
          (-(0 : ℝ)) := by simpa using hplus
      have := h0.comp (continuous_neg.continuousAt : ContinuousAt (fun x : ℝ => -x) 0)
      refine this.congr (Eventually.of_forall fun ε => ?_)
      simp [sub_eq_add_neg]
    have hc : ContinuousAt (fun ε : ℝ => 2 * G *
        (spatialFace h k l β (fun u => ξ₀ u + ε) η - spatialFace h k l β ξ₀ η) /
        spatialFace h k l β (fun u => ξ₀ u - ε) η) 0 :=
      (continuousAt_const.mul (hplus.sub continuousAt_const)).div hminus (by
        simpa using (hFpos' 0).ne')
    have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using this
  rw [Metric.tendsto_nhds]
  intro δ hδ
  obtain ⟨ε₀, hε₀L, hε₀⟩ := ((hcont.eventually (gt_mem_nhds (half_pos hδ))).and
    self_mem_nhdsWithin).exists
  have hε₀0 : 0 < ε₀ := hε₀
  -- the finite-`N` bound converges to the limiting bound (all phases continuous)
  have hbound : Tendsto (fun N => 2 * G * (origPhaseIntegral n h k β N 1 (fun u => ξ₀ u + ε₀) η -
      origPhaseIntegral n h k β N 1 ξ₀ η) / origPhaseIntegral n h k β N 1 (fun u => ξ₀ u - ε₀) η)
      atTop (𝓝 (2 * G * (spatialFace h k l β (fun u => ξ₀ u + ε₀) η - spatialFace h k l β ξ₀ η) /
        spatialFace h k l β (fun u => ξ₀ u - ε₀) η)) := by
    have hZp := spatialPhase_tendsto n h k hk l β hl0 hβ hmin hatt (fun u => ξ₀ u + ε₀) η
      (hξ₀c.add continuous_const) hηc
    have hZ0 := spatialPhase_tendsto n h k hk l β hl0 hβ hmin hatt ξ₀ η hξ₀c hηc
    have hZm := spatialPhase_tendsto n h k hk l β hl0 hβ hmin hatt (fun u => ξ₀ u - ε₀) η
      (hξ₀c.sub continuous_const) hηc
    have := (((hZp.sub hZ0).const_mul (2 * G)).div hZm (hFpos' _).ne')
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
    have hb : N ^ (-l) * Real.log N ^ (multCount (ratioExp h k) l - 1) ≠ 0 :=
      mul_ne_zero (Real.rpow_pos_of_pos (by linarith) _).ne'
        (pow_ne_zero _ (Real.log_pos hN).ne')
    simp only [Pi.div_apply]
    rw [← sub_div, ← mul_div_assoc, div_div_div_cancel_right₀ hb]
  have hZmN := spatialPhase_tendsto n h k hk l β hl0 hβ hmin hatt (fun u => ξ₀ u - ε₀) η
    (hξ₀c.sub continuous_const) hηc
  have hFm : 0 < spatialFace h k l β (fun u => ξ₀ u - ε₀) η := hFpos' ε₀
  filter_upwards [hε.eventually (gt_mem_nhds hε₀0), hN.eventually (eventually_gt_atTop (1 : ℝ)),
    hN.eventually (hZmN.eventually (lt_mem_nhds hFm)),
    hN.eventually (hbound.eventually (gt_mem_nhds (lt_of_lt_of_le hε₀L (half_le_self hδ.le))))]
    with i hεi hN1 hZmi hbi
  have hZm' : 0 < origPhaseIntegral n h k β (Nseq i) 1 (fun u => ξ₀ u - ε₀) η := by
    have hb : 0 < Nseq i ^ (-l) * Real.log (Nseq i) ^ (multCount (ratioExp h k) l - 1) :=
      mul_pos (Real.rpow_pos_of_pos (by linarith) _) (pow_pos (Real.log_pos hN1) _)
    exact (div_pos_iff_of_pos_right hb).1 hZmi
  rw [dist_zero_right, Real.norm_eq_abs]
  refine lt_of_le_of_lt (phase_observable_bound_base n h k (Nseq i) hβ.le (hξm i) hξ₀c hηc hηnn'
    hε₀0.le (fun u hu => (hξ i u hu).trans hεi.le) (hgm i) hG0 (hG i) hZm') hbi

/-- Probability of the finite-`N` energy law for a measurable phase near a continuous one. -/
theorem phaseEnergyLaw_isProbabilityMeasure_of_near (n : ℕ) (h k : Fin (n + 1) → ℕ) {β : ℝ}
    (N : ℝ) (hβ : 0 ≤ β) {ξ ξ₀ η : (Fin (n + 1) → ℝ) → ℝ} (hξm : Measurable ξ)
    (hξ₀c : Continuous ξ₀) (hηc : Continuous η) (hηnn : ∀ u ∈ unitBox (n + 1), 0 ≤ η u) {ε : ℝ}
    (hξ : ∀ u ∈ unitBox (n + 1), |ξ u - ξ₀ u| ≤ ε) (hZ : 0 < origPhaseIntegral n h k β N 1 ξ η) :
    IsProbabilityMeasure (phaseEnergyLaw n h k β N ξ η) := by
  obtain ⟨C, hC⟩ := (isCompact_closedCube (n + 1)).exists_bound_of_continuousOn hξ₀c.continuousOn
  exact phaseEnergyLaw_isProbabilityMeasure n h k N hβ hξm hηc hηnn (a := 0) (ε := C + ε)
    (fun u hu => by
      rw [sub_zero]
      have h1 := hξ u hu
      have h2 : |ξ₀ u| ≤ C :=
        (Real.norm_eq_abs _).symm.trans_le (hC u (unitBox_subset_closedCube _ hu))
      have := abs_sub_abs_le_abs_sub (ξ u) (ξ₀ u)
      linarith) hZ

/-- **Weak convergence of the posterior law of `NK` under moving continuous phases**: for
measurable phases `ξ_m` with `‖ξ_m − ξ₀‖_∞ ≤ ε_m → 0` on the box, the posterior law of `NK`
under `ξ_m` converges weakly to the spatial limit `ρ^{ξ₀}`. -/
theorem movingPhaseEnergyLaw_tendsto (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    {β : ℝ} (hβ : 0 < β) {η : (Fin (n + 1) → ℝ) → ℝ} (hηc : Continuous η)
    (hηnn : ∀ v ∈ closedCube (n + 1), 0 ≤ η v) {l : ℝ} (hmin : ∀ i, l ≤ ratioExp h k i)
    (hatt : ∃ i, ratioExp h k i = l) (hW : 0 < ∫ u in unitBox (n + 1), faceWeight h k l η u)
    {ξ₀ : (Fin (n + 1) → ℝ) → ℝ} (hξ₀c : Continuous ξ₀) (Nseq : ℕ → ℝ) (hN1 : ∀ m, 1 < Nseq m)
    (hN : Tendsto Nseq atTop atTop) (ξ : ℕ → (Fin (n + 1) → ℝ) → ℝ) (hξm : ∀ m, Measurable (ξ m))
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hξ : ∀ m, ∀ u ∈ unitBox (n + 1), |ξ m u - ξ₀ u| ≤ ε m)
    (hZξ : ∀ m, 0 < origPhaseIntegral n h k β (Nseq m) 1 (ξ m) η)
    (hZ0 : ∀ m, 0 < origPhaseIntegral n h k β (Nseq m) 1 ξ₀ η) :
    Tendsto (β := ProbabilityMeasure ℝ) (fun m => ⟨phaseEnergyLaw n h k β (Nseq m) (ξ m) η,
        phaseEnergyLaw_isProbabilityMeasure_of_near n h k (Nseq m) hβ.le (hξm m) hξ₀c hηc
          (fun u hu => hηnn u (unitBox_subset_closedCube _ hu)) (hξ m) (hZξ m)⟩) atTop
      (𝓝 ⟨spatialEnergyLimit h k l β ξ₀ η, spatialEnergyLimit_isProbabilityMeasure h k hk
        (ratioExp_min_pos h k hk hatt) hβ hmin hξ₀c hηc hηnn (spatialMass_pos_of_face h k hk l β
          ξ₀ η (spatialFace_pos_of_faceWeight h k hk (ratioExp_min_pos h k hk hatt) hβ hmin hξ₀c
            hηc hηnn hW))⟩) := by
  have hl0 : 0 < l := ratioExp_min_pos h k hk hatt
  have hF := spatialFace_pos_of_faceWeight h k hk hl0 hβ hmin hξ₀c hηc hηnn hW
  have hηnn' : ∀ u ∈ unitBox (n + 1), 0 ≤ η u := fun u hu =>
    hηnn u (unitBox_subset_closedCube _ hu)
  have hconst := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1
    (spatialEnergyLaw_tendsto n h k hk hβ hηc hηnn hmin hatt hξ₀c hF Nseq hN1 hN hZ0)
  refine ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.2 fun f => ?_
  change Tendsto (fun m => ∫ y, f y ∂(phaseEnergyLaw n h k β (Nseq m) (ξ m) η)) atTop
    (𝓝 (∫ y, f y ∂(spatialEnergyLimit h k l β ξ₀ η)))
  have hf := hconst f
  change Tendsto (fun m => ∫ y, f y ∂(phaseEnergyLaw n h k β (Nseq m) ξ₀ η)) atTop
    (𝓝 (∫ y, f y ∂(spatialEnergyLimit h k l β ξ₀ η))) at hf
  have hpert := spatialPhase_perturbation_tendsto n h k hk hβ hηc hηnn hmin hatt hW hξ₀c Nseq hN
    ξ hξm ε hε hξ (fun m u => f (Nseq m * ∏ i, u i ^ (2 * k i)))
    (fun m => f.continuous.measurable.comp (measurable_energyMap n k (Nseq m))) (norm_nonneg f)
    (fun m u _ => by rw [← Real.norm_eq_abs]; exact f.norm_coe_le_norm _)
  have := hpert.add hf
  rw [zero_add] at this
  refine this.congr' (Eventually.of_forall fun m => ?_)
  dsimp only
  rw [phaseEnergyLaw_integral n h k β (Nseq m) (hξm m) hηc hηnn' (hZξ m) f.continuous.measurable,
    phaseEnergyLaw_integral n h k β (Nseq m) hξ₀c.measurable hηc hηnn' (hZ0 m)
      f.continuous.measurable, sub_add_cancel]

end Grammar
