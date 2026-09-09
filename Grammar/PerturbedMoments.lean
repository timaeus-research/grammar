/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.PhaseStability
import Grammar.PhaseLawStructure

/-!
# Perturbed posterior energy moments (unit 352; Astra #43 unit 1)

For a phase `ξ` with `|ξ − a| ≤ δ` on the unit box and a nonnegative observable `h`, positivity
of the tilt gives the sandwich
`(𝒵_N(a−δ)/𝒵_N(a+δ)) E_{a−δ}[h] ≤ E_ξ[h] ≤ (𝒵_N(a+δ)/𝒵_N(a−δ)) E_{a+δ}[h]`
(`phase_nonneg_observable_sandwich`).  With `h = (NK)^r`, the constant-phase moment asymptotics
and continuity of `a ↦ A(a)` and `a ↦ J_{λ+r}(a)/J_λ(a)` give, for `|ξ_N − a| ≤ ε_N → 0`,
`E_{ξ_N}[(NK)^r] → J_{λ+r}(a)/J_λ(a) = ∫ y^r dρ_a` (`perturbed_energy_moment_tendsto`): fix
`δ`, let `N → ∞`, then `δ ↓ 0`.  In particular the perturbed posterior mean and variance of `NK`
converge to `μ(a)` and `v(a)`.  Posterior energy estimators survive vanishing spatial phase error.
-/

namespace Grammar

open MeasureTheory Filter Topology Set CoeffFamily

/-! ### The sandwich -/

theorem integrableOn_phaseIntegrand_mul (n : ℕ) (h k : Fin (n + 1) → ℕ) {β : ℝ} (N : ℝ)
    (hβ : 0 ≤ β) {ξ η : (Fin (n + 1) → ℝ) → ℝ} (hξm : Measurable ξ) (hηc : Continuous η)
    (hηnn : ∀ u ∈ unitBox (n + 1), 0 ≤ η u) {a δ : ℝ}
    (hξ : ∀ u ∈ unitBox (n + 1), |ξ u - a| ≤ δ) {g : (Fin (n + 1) → ℝ) → ℝ}
    (hgc : Continuous g) :
    IntegrableOn (fun u => phaseIntegrand n h k β N ξ η u * g u) (unitBox (n + 1)) := by
  obtain ⟨C, hC⟩ := (isCompact_closedCube (n + 1)).exists_bound_of_continuousOn hgc.continuousOn
  have hb : ∀ u ∈ unitBox (n + 1), ‖g u‖ ≤ C := fun u hu => hC u (unitBox_subset_closedCube _ hu)
  have hC0 : 0 ≤ C := by
    obtain ⟨u, hu⟩ : (unitBox (n + 1)).Nonempty :=
      ⟨fun _ => 1, Set.mem_univ_pi.2 fun _ => ⟨one_pos, le_rfl⟩⟩
    exact (norm_nonneg _).trans (hb u hu)
  have := Integrable.bdd_mul (c := C) (integrableOn_phaseIntegrand n h k N hβ hξm hηc hηnn hξ)
    hgc.measurable.aestronglyMeasurable (by
      rw [ae_restrict_iff' (measurableSet_unitBox _)]
      exact Eventually.of_forall hb)
  exact this.congr (Eventually.of_forall fun u => mul_comm _ _)

/-- **Positive-observable sandwich**: for `|ξ − a| ≤ δ` on the box and `h ≥ 0`,
`E_ξ[h] ≤ (𝒵_N(a+δ)/𝒵_N(a−δ)) E_{a+δ}[h]` and `E_ξ[h] ≥ (𝒵_N(a−δ)/𝒵_N(a+δ)) E_{a−δ}[h]`. -/
theorem phase_nonneg_observable_sandwich (n : ℕ) (h k : Fin (n + 1) → ℕ) {β : ℝ} (N : ℝ)
    (hβ : 0 ≤ β) {ξ η : (Fin (n + 1) → ℝ) → ℝ} (hξm : Measurable ξ) (hηc : Continuous η)
    (hηnn : ∀ u ∈ unitBox (n + 1), 0 ≤ η u) {a δ : ℝ}
    (hξ : ∀ u ∈ unitBox (n + 1), |ξ u - a| ≤ δ) {g : (Fin (n + 1) → ℝ) → ℝ} (hgc : Continuous g)
    (hg0 : ∀ u ∈ unitBox (n + 1), 0 ≤ g u)
    (hZ : 0 < origPhaseIntegral n h k β N 1 (fun _ => a - δ) η) :
    origPhaseIntegral n h k β N 1 (fun _ => a - δ) η /
        origPhaseIntegral n h k β N 1 (fun _ => a + δ) η *
      ((∫ u in unitBox (n + 1), constPhaseIntegrand n h k β N η (a - δ) u * g u) /
        origPhaseIntegral n h k β N 1 (fun _ => a - δ) η) ≤
      (∫ u in unitBox (n + 1), phaseIntegrand n h k β N ξ η u * g u) /
        origPhaseIntegral n h k β N 1 ξ η ∧
    (∫ u in unitBox (n + 1), phaseIntegrand n h k β N ξ η u * g u) /
        origPhaseIntegral n h k β N 1 ξ η ≤
      origPhaseIntegral n h k β N 1 (fun _ => a + δ) η /
        origPhaseIntegral n h k β N 1 (fun _ => a - δ) η *
      ((∫ u in unitBox (n + 1), constPhaseIntegrand n h k β N η (a + δ) u * g u) /
        origPhaseIntegral n h k β N 1 (fun _ => a + δ) η) := by
  have hbox := measurableSet_unitBox (n + 1)
  have hδ0 : 0 ≤ δ := by
    obtain ⟨u, hu⟩ : (unitBox (n + 1)).Nonempty :=
      ⟨fun _ => 1, Set.mem_univ_pi.2 fun _ => ⟨one_pos, le_rfl⟩⟩
    exact (abs_nonneg _).trans (hξ u hu)
  have iξ := integrableOn_phaseIntegrand n h k N hβ hξm hηc hηnn hξ
  have im : IntegrableOn (constPhaseIntegrand n h k β N η (a - δ)) (unitBox (n + 1)) :=
    integrableOn_unitBox_of_continuous _ (continuous_constPhaseIntegrand n h k β N hηc (a - δ))
  have ip : IntegrableOn (constPhaseIntegrand n h k β N η (a + δ)) (unitBox (n + 1)) :=
    integrableOn_unitBox_of_continuous _ (continuous_constPhaseIntegrand n h k β N hηc (a + δ))
  have iξg := integrableOn_phaseIntegrand_mul n h k N hβ hξm hηc hηnn hξ hgc
  have img : IntegrableOn (fun u => constPhaseIntegrand n h k β N η (a - δ) u * g u)
      (unitBox (n + 1)) :=
    integrableOn_phaseIntegrand_mul n h k N hβ measurable_const hηc hηnn
      (a := a - δ) (δ := 0) (fun u _ => by simp) hgc
  have ipg : IntegrableOn (fun u => constPhaseIntegrand n h k β N η (a + δ) u * g u)
      (unitBox (n + 1)) :=
    integrableOn_phaseIntegrand_mul n h k N hβ measurable_const hηc hηnn
      (a := a + δ) (δ := 0) (fun u _ => by simp) hgc
  -- masses (the chart integrals are definitionally the box integrals of the integrands)
  have hmξ : origPhaseIntegral n h k β N 1 (fun _ => a - δ) η ≤
      origPhaseIntegral n h k β N 1 ξ η :=
    setIntegral_mono_on im iξ hbox fun u hu =>
      phaseIntegrand_mono n h k N hβ (ξ := fun _ => a - δ) (ξ' := ξ) hηnn hu (by
        have := (abs_le.1 (hξ u hu)).1
        change a - δ ≤ ξ u
        linarith)
  have hξp : origPhaseIntegral n h k β N 1 ξ η ≤
      origPhaseIntegral n h k β N 1 (fun _ => a + δ) η :=
    setIntegral_mono_on iξ ip hbox fun u hu =>
      phaseIntegrand_mono n h k N hβ (ξ := ξ) (ξ' := fun _ => a + δ) hηnn hu (by
        have := (abs_le.1 (hξ u hu)).2
        change ξ u ≤ a + δ
        linarith)
  have hZξ : 0 < origPhaseIntegral n h k β N 1 ξ η := lt_of_lt_of_le hZ hmξ
  have hZp : 0 < origPhaseIntegral n h k β N 1 (fun _ => a + δ) η := lt_of_lt_of_le hZξ hξp
  -- weighted integrals
  have hIm : (∫ u in unitBox (n + 1), constPhaseIntegrand n h k β N η (a - δ) u * g u) ≤
      ∫ u in unitBox (n + 1), phaseIntegrand n h k β N ξ η u * g u :=
    setIntegral_mono_on img iξg hbox fun u hu => by
      refine mul_le_mul_of_nonneg_right ?_ (hg0 u hu)
      rw [← phaseIntegrand_const]
      exact phaseIntegrand_mono n h k N hβ hηnn hu (by linarith [(abs_le.1 (hξ u hu)).1])
  have hIp : (∫ u in unitBox (n + 1), phaseIntegrand n h k β N ξ η u * g u) ≤
      ∫ u in unitBox (n + 1), constPhaseIntegrand n h k β N η (a + δ) u * g u :=
    setIntegral_mono_on iξg ipg hbox fun u hu => by
      refine mul_le_mul_of_nonneg_right ?_ (hg0 u hu)
      rw [← phaseIntegrand_const]
      exact phaseIntegrand_mono n h k N hβ hηnn hu (by linarith [(abs_le.1 (hξ u hu)).2])
  have hIm0 : 0 ≤ ∫ u in unitBox (n + 1), constPhaseIntegrand n h k β N η (a - δ) u * g u :=
    setIntegral_nonneg hbox fun u hu =>
      mul_nonneg (constPhaseIntegrand_nonneg n h k β N hηnn _ hu) (hg0 u hu)
  have hIξ0 : 0 ≤ ∫ u in unitBox (n + 1), phaseIntegrand n h k β N ξ η u * g u :=
    setIntegral_nonneg hbox fun u hu =>
      mul_nonneg (phaseIntegrand_nonneg n h k β N hηnn hu) (hg0 u hu)
  constructor
  · rw [div_mul_div_comm, mul_comm (origPhaseIntegral n h k β N 1 (fun _ => a - δ) η),
      mul_div_mul_right _ _ hZ.ne']
    exact div_le_div₀ hIξ0 hIm hZξ hξp
  · rw [div_mul_div_comm, mul_comm (origPhaseIntegral n h k β N 1 (fun _ => a + δ) η),
      mul_div_mul_right _ _ hZp.ne']
    exact div_le_div₀ (hIm0.trans (hIm.trans hIp)) hIp hZ hmξ

/-! ### Perturbed moments -/

/-- Continuity of the limiting moment ratio `a ↦ J_{λ+r}(a)/J_λ(a)`. -/
theorem continuous_phaseLaw_momentRatio (β l : ℝ) (hβ : 0 < β) (hl : 0 < l) (r : ℕ) :
    Continuous fun a => fluctMoment β a 0 (l + r) 0 / fluctMoment β a 0 l 0 :=
  (continuous_iff_continuousAt.2 fun a =>
      (hasDerivAt_fluctMoment_phase hβ (by positivity : 0 < l + r) 0 a).continuousAt).div
    (continuous_iff_continuousAt.2 fun a => (hasDerivAt_fluctMoment_phase hβ hl 0 a).continuousAt)
    fun a => (fluctMoment_pos β a l hβ hl).ne'

/-- The constant-phase posterior moment in integrand form. -/
theorem constPhase_moment_integral_tendsto (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    {β : ℝ} (hβ : 0 < β) (b : ℝ) {cη : CoeffFamily (n + 1)} (hη : AbsSummable cη)
    {η : (Fin (n + 1) → ℝ) → ℝ} (hηc : Continuous η)
    (hev : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF cη u = η u) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (hA : familySpectralCoeff n h k β (constFamily b) cη l (multCount (ratioExp h k) l - 1) ≠ 0)
    (r : ℕ) :
    Tendsto (fun N => (∫ u in unitBox (n + 1),
        constPhaseIntegrand n h k β N η b u * (N * ∏ i, u i ^ (2 * k i)) ^ r) /
      origPhaseIntegral n h k β N 1 (fun _ => b) η) atTop
      (𝓝 (fluctMoment β b 0 (l + r) 0 / fluctMoment β b 0 l 0)) := by
  refine (constPhase_energy_moment_chart n h k hk hβ b hη hηc hev hmin hatt hA r).congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
  rw [← mul_div_assoc]
  congr 1
  rw [origPhaseIntegral_eq_integral_integrand, ← integral_const_mul]
  unfold constPhaseIntegrand
  refine setIntegral_congr_fun (measurableSet_unitBox _) fun u _ => ?_
  rw [mul_pow]
  ring

/-- **Perturbed posterior energy moments**: for `|ξ_N − a| ≤ ε_N → 0` on the box,
`E_{ξ_N}[(NK)^r] → J_{λ+r}(a)/J_λ(a) = ∫ y^r dρ_a`. -/
theorem perturbed_energy_moment_tendsto (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    {β : ℝ} (hβ : 0 < β) {cη : CoeffFamily (n + 1)} (hη : AbsSummable cη)
    {η : (Fin (n + 1) → ℝ) → ℝ} (hηc : Continuous η) (hηnn : ∀ u ∈ unitBox (n + 1), 0 ≤ η u)
    (hev : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF cη u = η u) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (hApos : ∀ b,
      0 < familySpectralCoeff n h k β (constFamily b) cη l (multCount (ratioExp h k) l - 1))
    (a : ℝ) {ι : Type*} {F : Filter ι} (Nseq : ι → ℝ) (hN : Tendsto Nseq F atTop)
    (ξ : ι → (Fin (n + 1) → ℝ) → ℝ) (hξm : ∀ i, Measurable (ξ i)) (ε : ι → ℝ)
    (hε : Tendsto ε F (𝓝 0)) (hξ : ∀ i, ∀ u ∈ unitBox (n + 1), |ξ i u - a| ≤ ε i) (r : ℕ) :
    Tendsto (fun i => (∫ u in unitBox (n + 1),
        phaseIntegrand n h k β (Nseq i) (ξ i) η u * (Nseq i * ∏ j, u j ^ (2 * k j)) ^ r) /
      origPhaseIntegral n h k β (Nseq i) 1 (ξ i) η) F
      (𝓝 (fluctMoment β a 0 (l + r) 0 / fluctMoment β a 0 l 0)) := by
  have hl0 : 0 < l := ratioExp_min_pos h k hk hatt
  -- notation for the limiting quantities
  set A : ℝ → ℝ := fun b =>
    familySpectralCoeff n h k β (constFamily b) cη l (multCount (ratioExp h k) l - 1) with hAdef
  set m : ℝ → ℝ := fun b => fluctMoment β b 0 (l + r) 0 / fluctMoment β b 0 l 0 with hmdef
  have hAc : Continuous A := continuous_constPhaseCoeff n h k hk hβ hη hl0 _
  have hmc : Continuous m := continuous_phaseLaw_momentRatio β l hβ hl0 r
  have hApos' : ∀ b, 0 < A b := hApos
  -- the two envelopes are continuous in `δ` and equal `m a` at `δ = 0`
  have hup : Tendsto (fun δ => A (a + δ) / A (a - δ) * m (a + δ)) (𝓝[>] 0) (𝓝 (m a)) := by
    have hc : Continuous fun δ => A (a + δ) / A (a - δ) * m (a + δ) :=
      ((hAc.comp (continuous_const.add continuous_id)).div
        (hAc.comp (continuous_const.sub continuous_id)) fun δ => (hApos' _).ne').mul
        (hmc.comp (continuous_const.add continuous_id))
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa [div_self (hApos' a).ne'] using this
  have hlow : Tendsto (fun δ => A (a - δ) / A (a + δ) * m (a - δ)) (𝓝[>] 0) (𝓝 (m a)) := by
    have hc : Continuous fun δ => A (a - δ) / A (a + δ) * m (a - δ) :=
      ((hAc.comp (continuous_const.sub continuous_id)).div
        (hAc.comp (continuous_const.add continuous_id)) fun δ => (hApos' _).ne').mul
        (hmc.comp (continuous_const.sub continuous_id))
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa [div_self (hApos' a).ne'] using this
  rw [Metric.tendsto_nhds]
  intro ε' hε'
  obtain ⟨δ, ⟨hδu, hδl⟩, hδ⟩ := (((hup.eventually (gt_mem_nhds (show m a < m a + ε' / 2 by
    linarith))).and (hlow.eventually (lt_mem_nhds (show m a - ε' / 2 < m a by linarith)))).and
    self_mem_nhdsWithin).exists
  have hδ0 : 0 < δ := hδ
  -- finite-`N` envelopes converge to the limiting envelopes
  have hZ : ∀ b, Tendsto (fun N => origPhaseIntegral n h k β N 1 (fun _ => b) η /
      (N ^ (-l) * Real.log N ^ (multCount (ratioExp h k) l - 1))) atTop (𝓝 (A b)) := fun b => by
    have := constPhase_tendsto n h k hk l β hl0 hβ hmin hatt b η hηc
    rwa [← (constPhase_leadingCoeff n h k hk hβ b hη hηc hev hmin hatt).2] at this
  have hratio : ∀ b c, Tendsto (fun N => origPhaseIntegral n h k β N 1 (fun _ => b) η /
      origPhaseIntegral n h k β N 1 (fun _ => c) η) atTop (𝓝 (A b / A c)) := fun b c => by
    refine ((hZ b).div (hZ c) (hApos' c).ne').congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
    have hb : N ^ (-l) * Real.log N ^ (multCount (ratioExp h k) l - 1) ≠ 0 :=
      mul_ne_zero (Real.rpow_pos_of_pos (by linarith) _).ne'
        (pow_ne_zero _ (Real.log_pos hN).ne')
    simp only [Pi.div_apply]
    rw [div_div_div_cancel_right₀ hb]
  have hup_N := (hratio (a + δ) (a - δ)).mul
    (constPhase_moment_integral_tendsto n h k hk hβ (a + δ) hη hηc hev hmin hatt
      (hApos' _).ne' r)
  have hlow_N := (hratio (a - δ) (a + δ)).mul
    (constPhase_moment_integral_tendsto n h k hk hβ (a - δ) hη hηc hev hmin hatt
      (hApos' _).ne' r)
  have hZm := (hZ (a - δ)).eventually (lt_mem_nhds (hApos' (a - δ)))
  filter_upwards [hε.eventually (gt_mem_nhds hδ0), hN.eventually (eventually_gt_atTop (1 : ℝ)),
    hN.eventually hZm, hN.eventually (hup_N.eventually (gt_mem_nhds (show
      A (a + δ) / A (a - δ) * m (a + δ) < m a + ε' by linarith))),
    hN.eventually (hlow_N.eventually (lt_mem_nhds (show
      m a - ε' < A (a - δ) / A (a + δ) * m (a - δ) by linarith)))] with i hεi hN1 hZmi hupi hlowi
  have hZm' : 0 < origPhaseIntegral n h k β (Nseq i) 1 (fun _ => a - δ) η := by
    have hb : 0 < Nseq i ^ (-l) * Real.log (Nseq i) ^ (multCount (ratioExp h k) l - 1) :=
      mul_pos (Real.rpow_pos_of_pos (by linarith) _) (pow_pos (Real.log_pos hN1) _)
    exact (div_pos_iff_of_pos_right hb).1 hZmi
  have hgc : Continuous fun u : Fin (n + 1) → ℝ => (Nseq i * ∏ j, u j ^ (2 * k j)) ^ r := by
    fun_prop
  have hg0 : ∀ u ∈ unitBox (n + 1), 0 ≤ (Nseq i * ∏ j, u j ^ (2 * k j)) ^ r := fun u hu => by
    have hu' : ∀ j, 0 < u j ∧ u j ≤ 1 := fun j => Set.mem_univ_pi.1 hu j
    exact pow_nonneg (mul_nonneg (by linarith)
      (Finset.prod_nonneg fun j _ => pow_nonneg (hu' j).1.le _)) _
  obtain ⟨hlo, hhi⟩ := phase_nonneg_observable_sandwich n h k (Nseq i) hβ.le (hξm i) hηc hηnn
    (fun u hu => (hξ i u hu).trans hεi.le) hgc hg0 hZm'
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- **Perturbed posterior mean of `NK`** converges to `μ(a)`. -/
theorem perturbed_energy_mean_tendsto (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    {β : ℝ} (hβ : 0 < β) {cη : CoeffFamily (n + 1)} (hη : AbsSummable cη)
    {η : (Fin (n + 1) → ℝ) → ℝ} (hηc : Continuous η) (hηnn : ∀ u ∈ unitBox (n + 1), 0 ≤ η u)
    (hev : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF cη u = η u) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (hApos : ∀ b,
      0 < familySpectralCoeff n h k β (constFamily b) cη l (multCount (ratioExp h k) l - 1))
    (a : ℝ) {ι : Type*} {F : Filter ι} (Nseq : ι → ℝ) (hN : Tendsto Nseq F atTop)
    (ξ : ι → (Fin (n + 1) → ℝ) → ℝ) (hξm : ∀ i, Measurable (ξ i)) (ε : ι → ℝ)
    (hε : Tendsto ε F (𝓝 0)) (hξ : ∀ i, ∀ u ∈ unitBox (n + 1), |ξ i u - a| ≤ ε i) :
    Tendsto (fun i => (∫ u in unitBox (n + 1),
        phaseIntegrand n h k β (Nseq i) (ξ i) η u * (Nseq i * ∏ j, u j ^ (2 * k j))) /
      origPhaseIntegral n h k β (Nseq i) 1 (ξ i) η) F (𝓝 (phaseLawMean β l a)) := by
  have := perturbed_energy_moment_tendsto n h k hk hβ hη hηc hηnn hev hmin hatt hApos a Nseq hN
    ξ hξm ε hε hξ 1
  simpa [phaseLawMean] using this

/-- **Perturbed posterior variance of `NK`** converges to `v(a)`. -/
theorem perturbed_energy_variance_tendsto (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    {β : ℝ} (hβ : 0 < β) {cη : CoeffFamily (n + 1)} (hη : AbsSummable cη)
    {η : (Fin (n + 1) → ℝ) → ℝ} (hηc : Continuous η) (hηnn : ∀ u ∈ unitBox (n + 1), 0 ≤ η u)
    (hev : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF cη u = η u) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (hApos : ∀ b,
      0 < familySpectralCoeff n h k β (constFamily b) cη l (multCount (ratioExp h k) l - 1))
    (a : ℝ) {ι : Type*} {F : Filter ι} (Nseq : ι → ℝ) (hN : Tendsto Nseq F atTop)
    (ξ : ι → (Fin (n + 1) → ℝ) → ℝ) (hξm : ∀ i, Measurable (ξ i)) (ε : ι → ℝ)
    (hε : Tendsto ε F (𝓝 0)) (hξ : ∀ i, ∀ u ∈ unitBox (n + 1), |ξ i u - a| ≤ ε i) :
    Tendsto (fun i => (∫ u in unitBox (n + 1),
        phaseIntegrand n h k β (Nseq i) (ξ i) η u * (Nseq i * ∏ j, u j ^ (2 * k j)) ^ 2) /
      origPhaseIntegral n h k β (Nseq i) 1 (ξ i) η -
      ((∫ u in unitBox (n + 1),
        phaseIntegrand n h k β (Nseq i) (ξ i) η u * (Nseq i * ∏ j, u j ^ (2 * k j))) /
      origPhaseIntegral n h k β (Nseq i) 1 (ξ i) η) ^ 2) F (𝓝 (phaseLawVar β l a)) := by
  have h2 := perturbed_energy_moment_tendsto n h k hk hβ hη hηc hηnn hev hmin hatt hApos a Nseq
    hN ξ hξm ε hε hξ 2
  have h1 := perturbed_energy_mean_tendsto n h k hk hβ hη hηc hηnn hev hmin hatt hApos a Nseq hN
    ξ hξm ε hε hξ
  simp only [Nat.cast_ofNat] at h2
  unfold phaseLawVar
  exact h2.sub (h1.pow 2)

end Grammar
