/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.AssembledEnergyLaw

/-!
# Stability under spatially varying phase perturbations (unit 351; Astra #42 unit 2)

For a measurable phase `ξ` with `|ξ − a| ≤ ε` on the unit box, the posterior with phase `ξ` is
the normalised tilt `h = e^{β√N u^k (ξ − a)}` of the constant-phase posterior, and
`|h − 1| ≤ e^{βε√N u^k} − 1`.  Hence for every observable `|g| ≤ G`,
`|E_ξ[g] − E_a[g]| ≤ 2G (𝒵_N(a+ε) − 𝒵_N(a))/𝒵_N(a−ε)` at every finite `N`
(`phase_observable_bound`).  With the constant-phase asymptotics `𝒵_N(b)/(N^{-λ}L^{m-1}) → A(b)`
and `A` continuous and positive, a vanishing perturbation `|ξ_N − a| ≤ ε_N → 0` gives
`E_{ξ_N}[g_N] − E_a[g_N] → 0` uniformly over `|g_N| ≤ G` (`phase_perturbation_tendsto`), and the
posterior law of `NK` under the perturbed phase converges weakly to `ρ_a`
(`perturbedEnergyLaw_tendsto_phaseLaw`).  No parameter-uniform higher-order tail estimate is
used: fix `ε`, let `N → ∞`, then let `ε ↓ 0`.
-/

namespace Grammar

open MeasureTheory Filter Topology Set CoeffFamily

/-! ### The integrand with a spatially varying phase -/

/-- The chart integrand with phase function `ξ`. -/
noncomputable def phaseIntegrand (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N : ℝ)
    (ξ η : (Fin (n + 1) → ℝ) → ℝ) (u : Fin (n + 1) → ℝ) : ℝ :=
  η u * (∏ i, u i ^ h i) *
    Real.exp (-(β * N * ∏ i, u i ^ (2 * k i)) + β * (Real.sqrt N * ∏ i, u i ^ k i) * ξ u)

theorem origPhaseIntegral_eq_integral_phaseIntegrand (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N : ℝ)
    (ξ η : (Fin (n + 1) → ℝ) → ℝ) :
    origPhaseIntegral n h k β N 1 ξ η = ∫ u in unitBox (n + 1), phaseIntegrand n h k β N ξ η u :=
  rfl

theorem phaseIntegrand_const (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N : ℝ)
    (η : (Fin (n + 1) → ℝ) → ℝ) (a : ℝ) :
    phaseIntegrand n h k β N (fun _ => a) η = constPhaseIntegrand n h k β N η a := rfl

theorem measurable_phaseIntegrand (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N : ℝ)
    {ξ η : (Fin (n + 1) → ℝ) → ℝ} (hξ : Measurable ξ) (hη : Measurable η) :
    Measurable (phaseIntegrand n h k β N ξ η) := by
  unfold phaseIntegrand
  fun_prop

theorem phaseIntegrand_nonneg (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N : ℝ)
    {ξ η : (Fin (n + 1) → ℝ) → ℝ} (hηnn : ∀ u ∈ unitBox (n + 1), 0 ≤ η u)
    {u : Fin (n + 1) → ℝ} (hu : u ∈ unitBox (n + 1)) : 0 ≤ phaseIntegrand n h k β N ξ η u := by
  have hu' : ∀ i, 0 < u i ∧ u i ≤ 1 := fun i => Set.mem_univ_pi.1 hu i
  exact mul_nonneg (mul_nonneg (hηnn u hu)
    (Finset.prod_nonneg fun i _ => pow_nonneg (hu' i).1.le _)) (Real.exp_pos _).le

/-- The integrand is monotone in the phase on the box (`η ≥ 0`, `β, N ≥ 0`). -/
theorem phaseIntegrand_mono (n : ℕ) (h k : Fin (n + 1) → ℕ) {β : ℝ} (N : ℝ) (hβ : 0 ≤ β)
    {ξ ξ' η : (Fin (n + 1) → ℝ) → ℝ} (hηnn : ∀ u ∈ unitBox (n + 1), 0 ≤ η u)
    {u : Fin (n + 1) → ℝ} (hu : u ∈ unitBox (n + 1)) (hle : ξ u ≤ ξ' u) :
    phaseIntegrand n h k β N ξ η u ≤ phaseIntegrand n h k β N ξ' η u := by
  have hu' : ∀ i, 0 < u i ∧ u i ≤ 1 := fun i => Set.mem_univ_pi.1 hu i
  have hP : 0 ≤ ∏ i, u i ^ k i := Finset.prod_nonneg fun i _ => pow_nonneg (hu' i).1.le _
  unfold phaseIntegrand
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (add_le_add le_rfl ?_))
    (mul_nonneg (hηnn u hu) (Finset.prod_nonneg fun i _ => pow_nonneg (hu' i).1.le _))
  exact mul_le_mul_of_nonneg_left hle (by positivity)

/-- `F_ξ = F_a · e^{β√N u^k (ξ − a)}`. -/
theorem phaseIntegrand_eq_const_mul (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N : ℝ)
    (ξ η : (Fin (n + 1) → ℝ) → ℝ) (a : ℝ) (u : Fin (n + 1) → ℝ) :
    phaseIntegrand n h k β N ξ η u = constPhaseIntegrand n h k β N η a u *
      Real.exp (β * (Real.sqrt N * ∏ i, u i ^ k i) * (ξ u - a)) := by
  unfold phaseIntegrand constPhaseIntegrand
  rw [mul_assoc (η u * ∏ i, u i ^ h i), ← Real.exp_add]
  congr 2
  ring

theorem abs_exp_sub_one_le_exp_abs_sub_one (x : ℝ) : |Real.exp x - 1| ≤ Real.exp |x| - 1 := by
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx, abs_of_nonneg (by linarith [Real.add_one_le_exp x])]
  · rw [abs_of_neg hx, abs_of_nonpos (by linarith [Real.exp_le_one_iff.2 hx.le])]
    have h1 := Real.add_one_le_exp x
    have h2 := Real.add_one_le_exp (-x)
    linarith

/-- Pointwise tilt bound: `|F_ξ − F_a| ≤ F_{a+ε} − F_a` when `|ξ − a| ≤ ε`. -/
theorem abs_phaseIntegrand_sub_le (n : ℕ) (h k : Fin (n + 1) → ℕ) {β : ℝ} (N : ℝ) (hβ : 0 ≤ β)
    {ξ η : (Fin (n + 1) → ℝ) → ℝ} (hηnn : ∀ u ∈ unitBox (n + 1), 0 ≤ η u) {a ε : ℝ}
    {u : Fin (n + 1) → ℝ} (hu : u ∈ unitBox (n + 1)) (hξ : |ξ u - a| ≤ ε) :
    |phaseIntegrand n h k β N ξ η u - constPhaseIntegrand n h k β N η a u| ≤
      constPhaseIntegrand n h k β N η (a + ε) u - constPhaseIntegrand n h k β N η a u := by
  have hu' : ∀ i, 0 < u i ∧ u i ≤ 1 := fun i => Set.mem_univ_pi.1 hu i
  have hP : 0 ≤ ∏ i, u i ^ k i := Finset.prod_nonneg fun i _ => pow_nonneg (hu' i).1.le _
  have hc : 0 ≤ β * (Real.sqrt N * ∏ i, u i ^ k i) := by positivity
  have hF : 0 ≤ constPhaseIntegrand n h k β N η a u :=
    constPhaseIntegrand_nonneg n h k β N hηnn a hu
  rw [phaseIntegrand_eq_const_mul n h k β N ξ η a u,
    show constPhaseIntegrand n h k β N η (a + ε) u = constPhaseIntegrand n h k β N η a u *
      Real.exp (β * (Real.sqrt N * ∏ i, u i ^ k i) * ε) from by
        rw [← phaseIntegrand_const, phaseIntegrand_eq_const_mul n h k β N _ η a u]
        simp,
    ← mul_sub_one, ← mul_sub_one, abs_mul, abs_of_nonneg hF]
  refine mul_le_mul_of_nonneg_left ((abs_exp_sub_one_le_exp_abs_sub_one _).trans ?_) hF
  rw [abs_mul, abs_of_nonneg hc]
  exact sub_le_sub_right (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hξ hc)) 1

theorem integrableOn_phaseIntegrand (n : ℕ) (h k : Fin (n + 1) → ℕ) {β : ℝ} (N : ℝ) (hβ : 0 ≤ β)
    {ξ η : (Fin (n + 1) → ℝ) → ℝ} (hξm : Measurable ξ) (hηc : Continuous η)
    (hηnn : ∀ u ∈ unitBox (n + 1), 0 ≤ η u) {a ε : ℝ}
    (hξ : ∀ u ∈ unitBox (n + 1), |ξ u - a| ≤ ε) :
    IntegrableOn (phaseIntegrand n h k β N ξ η) (unitBox (n + 1)) := by
  refine (integrableOn_unitBox_of_continuous _
    (continuous_constPhaseIntegrand n h k β N hηc (a + ε))).mono'
    (measurable_phaseIntegrand n h k β N hξm hηc.measurable).aestronglyMeasurable ?_
  rw [ae_restrict_iff' (measurableSet_unitBox _)]
  refine Eventually.of_forall fun u hu => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (phaseIntegrand_nonneg n h k β N hηnn hu),
    ← phaseIntegrand_const]
  exact phaseIntegrand_mono n h k N hβ hηnn hu (by linarith [(abs_le.1 (hξ u hu)).2])

/-! ### The finite-`N` observable bound -/

/-- **Stability of bounded observables under a phase perturbation**: for `|ξ − a| ≤ ε` on the box
and `|g| ≤ G`, `|E_ξ[g] − E_a[g]| ≤ 2G (𝒵_N(a+ε) − 𝒵_N(a))/𝒵_N(a−ε)`. -/
theorem phase_observable_bound (n : ℕ) (h k : Fin (n + 1) → ℕ) {β : ℝ} (N : ℝ) (hβ : 0 ≤ β)
    {ξ η : (Fin (n + 1) → ℝ) → ℝ} (hξm : Measurable ξ) (hηc : Continuous η)
    (hηnn : ∀ u ∈ unitBox (n + 1), 0 ≤ η u) {a ε : ℝ} (hε : 0 ≤ ε)
    (hξ : ∀ u ∈ unitBox (n + 1), |ξ u - a| ≤ ε) {g : (Fin (n + 1) → ℝ) → ℝ} (hgm : Measurable g)
    {G : ℝ} (hG0 : 0 ≤ G) (hG : ∀ u ∈ unitBox (n + 1), |g u| ≤ G)
    (hZ : 0 < origPhaseIntegral n h k β N 1 (fun _ => a - ε) η) :
    |(∫ u in unitBox (n + 1), phaseIntegrand n h k β N ξ η u * g u) /
        origPhaseIntegral n h k β N 1 ξ η -
      (∫ u in unitBox (n + 1), constPhaseIntegrand n h k β N η a u * g u) /
        origPhaseIntegral n h k β N 1 (fun _ => a) η| ≤
      2 * G * (origPhaseIntegral n h k β N 1 (fun _ => a + ε) η -
        origPhaseIntegral n h k β N 1 (fun _ => a) η) /
        origPhaseIntegral n h k β N 1 (fun _ => a - ε) η := by
  have hbox := measurableSet_unitBox (n + 1)
  -- integrability
  have iξ := integrableOn_phaseIntegrand n h k N hβ hξm hηc hηnn hξ
  have ia : IntegrableOn (constPhaseIntegrand n h k β N η a) (unitBox (n + 1)) :=
    integrableOn_unitBox_of_continuous _ (continuous_constPhaseIntegrand n h k β N hηc a)
  have ip : IntegrableOn (constPhaseIntegrand n h k β N η (a + ε)) (unitBox (n + 1)) :=
    integrableOn_unitBox_of_continuous _ (continuous_constPhaseIntegrand n h k β N hηc (a + ε))
  have im : IntegrableOn (constPhaseIntegrand n h k β N η (a - ε)) (unitBox (n + 1)) :=
    integrableOn_unitBox_of_continuous _ (continuous_constPhaseIntegrand n h k β N hηc (a - ε))
  have hgbd : ∀ (F : (Fin (n + 1) → ℝ) → ℝ), IntegrableOn F (unitBox (n + 1)) →
      IntegrableOn (fun u => F u * g u) (unitBox (n + 1)) := fun F hF => by
    have := Integrable.bdd_mul (c := G) hF hgm.aestronglyMeasurable (by
      rw [ae_restrict_iff' hbox]
      exact Eventually.of_forall fun u hu => by rw [Real.norm_eq_abs]; exact hG u hu)
    exact this.congr (Eventually.of_forall fun u => mul_comm _ _)
  -- the four masses
  rw [origPhaseIntegral_eq_integral_phaseIntegrand, origPhaseIntegral_eq_integral_integrand,
    origPhaseIntegral_eq_integral_integrand, origPhaseIntegral_eq_integral_integrand] at *
  set Zξ := ∫ u in unitBox (n + 1), phaseIntegrand n h k β N ξ η u with hZξ
  set Za := ∫ u in unitBox (n + 1), constPhaseIntegrand n h k β N η a u with hZa
  set Zp := ∫ u in unitBox (n + 1), constPhaseIntegrand n h k β N η (a + ε) u with hZp
  set Zm := ∫ u in unitBox (n + 1), constPhaseIntegrand n h k β N η (a - ε) u with hZm
  set Iξ := ∫ u in unitBox (n + 1), phaseIntegrand n h k β N ξ η u * g u with hIξ
  set Ia := ∫ u in unitBox (n + 1), constPhaseIntegrand n h k β N η a u * g u with hIa
  have hmξ : Zm ≤ Zξ := setIntegral_mono_on im iξ hbox fun u hu => by
    rw [← phaseIntegrand_const]
    exact phaseIntegrand_mono n h k N hβ hηnn hu (by linarith [(abs_le.1 (hξ u hu)).1])
  have hma : Zm ≤ Za := setIntegral_mono_on im ia hbox fun u hu => by
    rw [← phaseIntegrand_const, ← phaseIntegrand_const]
    exact phaseIntegrand_mono n h k N hβ hηnn hu (by linarith)
  have hZξ0 : 0 < Zξ := lt_of_lt_of_le hZ hmξ
  have hZa0 : 0 < Za := lt_of_lt_of_le hZ hma
  -- the tilt discrepancy `D = ∫ |F_ξ − F_a| ≤ Zp − Za`
  have iD : IntegrableOn (fun u => |phaseIntegrand n h k β N ξ η u -
      constPhaseIntegrand n h k β N η a u|) (unitBox (n + 1)) := (iξ.sub ia).norm
  have hD : ∫ u in unitBox (n + 1), |phaseIntegrand n h k β N ξ η u -
      constPhaseIntegrand n h k β N η a u| ≤ Zp - Za := by
    rw [hZp, hZa, ← integral_sub ip ia]
    exact setIntegral_mono_on iD (ip.sub ia) hbox fun u hu =>
      abs_phaseIntegrand_sub_le n h k N hβ hηnn hu (hξ u hu)
  have hD0 : 0 ≤ Zp - Za := le_trans (integral_nonneg fun _ => abs_nonneg _) hD
  -- `|Iξ − Ia| ≤ G (Zp − Za)`
  have h1 : |Iξ - Ia| ≤ G * (Zp - Za) := by
    rw [hIξ, hIa, ← integral_sub (hgbd _ iξ) (hgbd _ ia), ← Real.norm_eq_abs]
    refine (norm_integral_le_integral_norm _).trans ?_
    refine le_trans (setIntegral_mono_on ((hgbd _ iξ).sub (hgbd _ ia)).norm (iD.const_mul G) hbox
      fun u hu => ?_) ?_
    · change ‖phaseIntegrand n h k β N ξ η u * g u - constPhaseIntegrand n h k β N η a u * g u‖ ≤
        G * |phaseIntegrand n h k β N ξ η u - constPhaseIntegrand n h k β N η a u|
      rw [← sub_mul, norm_mul, mul_comm, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hG u hu) (abs_nonneg _)
    · rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left hD hG0
  -- `|Ia| ≤ G Za`
  have h2 : |Ia| ≤ G * Za := by
    rw [hIa, ← Real.norm_eq_abs]
    refine (norm_integral_le_integral_norm _).trans ?_
    refine le_trans (setIntegral_mono_on (hgbd _ ia).norm (ia.const_mul G) hbox
      fun u hu => ?_) ?_
    · change ‖constPhaseIntegrand n h k β N η a u * g u‖ ≤ G * constPhaseIntegrand n h k β N η a u
      rw [norm_mul, mul_comm, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (constPhaseIntegrand_nonneg n h k β N hηnn a hu)]
      exact mul_le_mul_of_nonneg_right (hG u hu)
        (constPhaseIntegrand_nonneg n h k β N hηnn a hu)
    · rw [integral_const_mul]
  -- `|Zξ − Za| ≤ Zp − Za`
  have h3 : |Zξ - Za| ≤ Zp - Za := by
    rw [hZξ, hZa, ← integral_sub iξ ia, ← Real.norm_eq_abs]
    exact (norm_integral_le_integral_norm _).trans hD
  -- assemble
  have hnum : |Iξ * Za - Zξ * Ia| ≤ 2 * G * (Zp - Za) * Za := by
    have e : Iξ * Za - Zξ * Ia = (Iξ - Ia) * Za - Ia * (Zξ - Za) := by ring
    rw [e]
    calc |(Iξ - Ia) * Za - Ia * (Zξ - Za)| ≤ |(Iξ - Ia) * Za| + |Ia * (Zξ - Za)| := abs_sub _ _
      _ = |Iξ - Ia| * Za + |Ia| * |Zξ - Za| := by
          rw [abs_mul, abs_mul, abs_of_pos hZa0]
      _ ≤ G * (Zp - Za) * Za + G * Za * (Zp - Za) :=
          add_le_add (mul_le_mul_of_nonneg_right h1 hZa0.le)
            (mul_le_mul h2 h3 (abs_nonneg _) (by positivity))
      _ = 2 * G * (Zp - Za) * Za := by ring
  rw [div_sub_div _ _ hZξ0.ne' hZa0.ne', abs_div, abs_of_pos (mul_pos hZξ0 hZa0)]
  calc |Iξ * Za - Zξ * Ia| / (Zξ * Za) ≤ 2 * G * (Zp - Za) * Za / (Zm * Za) :=
        div_le_div₀ (by positivity) hnum (mul_pos hZ hZa0)
          (mul_le_mul_of_nonneg_right hmξ hZa0.le)
    _ = 2 * G * (Zp - Za) / Zm := by
        rw [mul_div_mul_right _ _ hZa0.ne']

/-! ### Vanishing perturbations: asymptotics -/

/-- The finite-`N` bound converges to `2G (A(a+ε) − A(a))/A(a−ε)`. -/
theorem phase_bound_tendsto (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {β : ℝ}
    (hβ : 0 < β) {cη : CoeffFamily (n + 1)} (hη : AbsSummable cη)
    {η : (Fin (n + 1) → ℝ) → ℝ} (hηc : Continuous η)
    (hev : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF cη u = η u) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (hApos : ∀ b,
      0 < familySpectralCoeff n h k β (constFamily b) cη l (multCount (ratioExp h k) l - 1))
    (a ε G : ℝ) :
    Tendsto (fun N => 2 * G * (origPhaseIntegral n h k β N 1 (fun _ => a + ε) η -
        origPhaseIntegral n h k β N 1 (fun _ => a) η) /
        origPhaseIntegral n h k β N 1 (fun _ => a - ε) η) atTop
      (𝓝 (2 * G * (familySpectralCoeff n h k β (constFamily (a + ε)) cη l
          (multCount (ratioExp h k) l - 1) -
        familySpectralCoeff n h k β (constFamily a) cη l (multCount (ratioExp h k) l - 1)) /
        familySpectralCoeff n h k β (constFamily (a - ε)) cη l
          (multCount (ratioExp h k) l - 1))) := by
  have hl0 : 0 < l := ratioExp_min_pos h k hk hatt
  have hZ : ∀ b, Tendsto (fun N => origPhaseIntegral n h k β N 1 (fun _ => b) η /
      (N ^ (-l) * Real.log N ^ (multCount (ratioExp h k) l - 1))) atTop
      (𝓝 (familySpectralCoeff n h k β (constFamily b) cη l (multCount (ratioExp h k) l - 1))) :=
    fun b => by
      have := constPhase_tendsto n h k hk l β hl0 hβ hmin hatt b η hηc
      rwa [← (constPhase_leadingCoeff n h k hk hβ b hη hηc hev hmin hatt).2] at this
  have := (((hZ (a + ε)).sub (hZ a)).const_mul (2 * G)).div (hZ (a - ε)) (hApos _).ne'
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
  have hb : N ^ (-l) * Real.log N ^ (multCount (ratioExp h k) l - 1) ≠ 0 :=
    mul_ne_zero (Real.rpow_pos_of_pos (by linarith) _).ne' (pow_ne_zero _ (Real.log_pos hN).ne')
  simp only [Pi.div_apply]
  rw [← sub_div, ← mul_div_assoc, div_div_div_cancel_right₀ hb]

/-- **Vanishing spatial phase perturbations do not move bounded posterior expectations**:
for `|ξ_N − a| ≤ ε_N → 0` on the box and observables `|g_N| ≤ G`,
`E_{ξ_N}[g_N] − E_a[g_N] → 0`. -/
theorem phase_perturbation_tendsto (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {β : ℝ}
    (hβ : 0 < β) {cη : CoeffFamily (n + 1)} (hη : AbsSummable cη)
    {η : (Fin (n + 1) → ℝ) → ℝ} (hηc : Continuous η) (hηnn : ∀ u ∈ unitBox (n + 1), 0 ≤ η u)
    (hev : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF cη u = η u) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (hApos : ∀ b,
      0 < familySpectralCoeff n h k β (constFamily b) cη l (multCount (ratioExp h k) l - 1))
    (a : ℝ) {ι : Type*} {F : Filter ι} (Nseq : ι → ℝ) (hN : Tendsto Nseq F atTop)
    (ξ : ι → (Fin (n + 1) → ℝ) → ℝ) (hξm : ∀ i, Measurable (ξ i)) (ε : ι → ℝ)
    (hε : Tendsto ε F (𝓝 0)) (hξ : ∀ i, ∀ u ∈ unitBox (n + 1), |ξ i u - a| ≤ ε i)
    (g : ι → (Fin (n + 1) → ℝ) → ℝ) (hgm : ∀ i, Measurable (g i)) {G : ℝ} (hG0 : 0 ≤ G)
    (hG : ∀ i, ∀ u ∈ unitBox (n + 1), |g i u| ≤ G) :
    Tendsto (fun i =>
      (∫ u in unitBox (n + 1), phaseIntegrand n h k β (Nseq i) (ξ i) η u * g i u) /
        origPhaseIntegral n h k β (Nseq i) 1 (ξ i) η -
      (∫ u in unitBox (n + 1), constPhaseIntegrand n h k β (Nseq i) η a u * g i u) /
        origPhaseIntegral n h k β (Nseq i) 1 (fun _ => a) η) F (𝓝 0) := by
  have hl0 : 0 < l := ratioExp_min_pos h k hk hatt
  -- the limiting bound is continuous in `ε` and vanishes at `ε = 0`
  have hAc := continuous_constPhaseCoeff n h k hk hβ hη hl0 (multCount (ratioExp h k) l - 1)
  have hcont : Tendsto (fun ε => 2 * G *
      (familySpectralCoeff n h k β (constFamily (a + ε)) cη l (multCount (ratioExp h k) l - 1) -
        familySpectralCoeff n h k β (constFamily a) cη l (multCount (ratioExp h k) l - 1)) /
      familySpectralCoeff n h k β (constFamily (a - ε)) cη l (multCount (ratioExp h k) l - 1))
      (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous fun ε => 2 * G *
        (familySpectralCoeff n h k β (constFamily (a + ε)) cη l (multCount (ratioExp h k) l - 1) -
          familySpectralCoeff n h k β (constFamily a) cη l (multCount (ratioExp h k) l - 1)) /
        familySpectralCoeff n h k β (constFamily (a - ε)) cη l (multCount (ratioExp h k) l - 1) :=
      (continuous_const.mul ((hAc.comp (continuous_const.add continuous_id)).sub
        continuous_const)).div (hAc.comp (continuous_const.sub continuous_id))
        fun ε => (hApos _).ne'
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using this
  rw [Metric.tendsto_nhds]
  intro δ hδ
  obtain ⟨ε₀, hε₀L, hε₀⟩ := ((hcont.eventually (gt_mem_nhds (half_pos hδ))).and
    self_mem_nhdsWithin).exists
  have hε₀0 : 0 < ε₀ := hε₀
  -- eventually: `ε_N ≤ ε₀`, `N > 1`, `𝒵_N(a−ε₀) > 0`, and the finite-`N` bound is `< δ`
  have hZm := constPhase_tendsto n h k hk l β hl0 hβ hmin hatt (a - ε₀) η hηc
  rw [← (constPhase_leadingCoeff n h k hk hβ (a - ε₀) hη hηc hev hmin hatt).2] at hZm
  filter_upwards [hε.eventually (gt_mem_nhds hε₀0), hN.eventually (eventually_gt_atTop (1 : ℝ)),
    hN.eventually (hZm.eventually (lt_mem_nhds (hApos (a - ε₀)))),
    hN.eventually ((phase_bound_tendsto n h k hk hβ hη hηc hev hmin hatt hApos a ε₀ G).eventually
      (gt_mem_nhds (lt_of_lt_of_le hε₀L (half_le_self hδ.le))))] with i hεN hN1 hZmN hbound
  have hZmN' : 0 < origPhaseIntegral n h k β (Nseq i) 1 (fun _ => a - ε₀) η := by
    have hb : 0 < Nseq i ^ (-l) * Real.log (Nseq i) ^ (multCount (ratioExp h k) l - 1) :=
      mul_pos (Real.rpow_pos_of_pos (by linarith) _) (pow_pos (Real.log_pos hN1) _)
    exact (div_pos_iff_of_pos_right hb).1 hZmN
  rw [dist_zero_right, Real.norm_eq_abs]
  refine lt_of_le_of_lt (phase_observable_bound n h k (Nseq i) hβ.le (hξm i) hηc hηnn
    hε₀0.le (fun u hu => (hξ i u hu).trans hεN.le) (hgm i) hG0 (hG i) hZmN') hbound

/-! ### The perturbed posterior and its energy law -/

/-- The posterior with phase function `ξ` on the unit box. -/
noncomputable def phasePosterior (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N : ℝ)
    (ξ η : (Fin (n + 1) → ℝ) → ℝ) : Measure (Fin (n + 1) → ℝ) :=
  (volume.restrict (unitBox (n + 1))).withDensity fun u =>
    ENNReal.ofReal (phaseIntegrand n h k β N ξ η u / origPhaseIntegral n h k β N 1 ξ η)

theorem phasePosterior_integral (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N : ℝ)
    {ξ η : (Fin (n + 1) → ℝ) → ℝ} (hξm : Measurable ξ) (hηc : Continuous η)
    (hηnn : ∀ u ∈ unitBox (n + 1), 0 ≤ η u) (hZ : 0 < origPhaseIntegral n h k β N 1 ξ η)
    (g : (Fin (n + 1) → ℝ) → ℝ) :
    ∫ u, g u ∂(phasePosterior n h k β N ξ η) =
      (∫ u in unitBox (n + 1), phaseIntegrand n h k β N ξ η u * g u) /
        origPhaseIntegral n h k β N 1 ξ η := by
  unfold phasePosterior
  rw [integral_withDensity_eq_integral_toReal_smul
    (((measurable_phaseIntegrand n h k β N hξm hηc.measurable).div_const _).ennreal_ofReal)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top), ← integral_div]
  refine setIntegral_congr_fun (measurableSet_unitBox _) fun u hu => ?_
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (div_nonneg (phaseIntegrand_nonneg n h k β N hηnn hu) hZ.le)]
  ring

theorem phasePosterior_isProbabilityMeasure (n : ℕ) (h k : Fin (n + 1) → ℕ) {β : ℝ} (N : ℝ)
    (hβ : 0 ≤ β) {ξ η : (Fin (n + 1) → ℝ) → ℝ} (hξm : Measurable ξ) (hηc : Continuous η)
    (hηnn : ∀ u ∈ unitBox (n + 1), 0 ≤ η u) {a ε : ℝ}
    (hξ : ∀ u ∈ unitBox (n + 1), |ξ u - a| ≤ ε) (hZ : 0 < origPhaseIntegral n h k β N 1 ξ η) :
    IsProbabilityMeasure (phasePosterior n h k β N ξ η) := by
  constructor
  unfold phasePosterior
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal]
  · rw [integral_div, ← origPhaseIntegral_eq_integral_phaseIntegrand, div_self hZ.ne',
      ENNReal.ofReal_one]
  · exact (integrableOn_phaseIntegrand n h k N hβ hξm hηc hηnn hξ).div_const _
  · rw [Filter.EventuallyLE, ae_restrict_iff' (measurableSet_unitBox _)]
    exact Eventually.of_forall fun u hu =>
      div_nonneg (phaseIntegrand_nonneg n h k β N hηnn hu) hZ.le

/-- The posterior law of `NK` under the phase `ξ`. -/
noncomputable def phaseEnergyLaw (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N : ℝ)
    (ξ η : (Fin (n + 1) → ℝ) → ℝ) : Measure ℝ :=
  (phasePosterior n h k β N ξ η).map fun u => N * ∏ i, u i ^ (2 * k i)

theorem phaseEnergyLaw_isProbabilityMeasure (n : ℕ) (h k : Fin (n + 1) → ℕ) {β : ℝ} (N : ℝ)
    (hβ : 0 ≤ β) {ξ η : (Fin (n + 1) → ℝ) → ℝ} (hξm : Measurable ξ) (hηc : Continuous η)
    (hηnn : ∀ u ∈ unitBox (n + 1), 0 ≤ η u) {a ε : ℝ}
    (hξ : ∀ u ∈ unitBox (n + 1), |ξ u - a| ≤ ε) (hZ : 0 < origPhaseIntegral n h k β N 1 ξ η) :
    IsProbabilityMeasure (phaseEnergyLaw n h k β N ξ η) :=
  have := phasePosterior_isProbabilityMeasure n h k N hβ hξm hηc hηnn hξ hZ
  Measure.isProbabilityMeasure_map (measurable_energyMap n k N).aemeasurable

theorem phaseEnergyLaw_integral (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N : ℝ)
    {ξ η : (Fin (n + 1) → ℝ) → ℝ} (hξm : Measurable ξ) (hηc : Continuous η)
    (hηnn : ∀ u ∈ unitBox (n + 1), 0 ≤ η u) (hZ : 0 < origPhaseIntegral n h k β N 1 ξ η)
    {f : ℝ → ℝ} (hf : Measurable f) :
    ∫ y, f y ∂(phaseEnergyLaw n h k β N ξ η) =
      (∫ u in unitBox (n + 1), phaseIntegrand n h k β N ξ η u * f (N * ∏ i, u i ^ (2 * k i))) /
        origPhaseIntegral n h k β N 1 ξ η := by
  unfold phaseEnergyLaw
  rw [integral_map (measurable_energyMap n k N).aemeasurable hf.aestronglyMeasurable,
    phasePosterior_integral n h k β N hξm hηc hηnn hZ]

theorem energyLaw_integral' (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N : ℝ)
    {η : (Fin (n + 1) → ℝ) → ℝ} (hηc : Continuous η) (hηnn : ∀ u ∈ unitBox (n + 1), 0 ≤ η u)
    (a : ℝ) (hZ : 0 < origPhaseIntegral n h k β N 1 (fun _ => a) η) {f : ℝ → ℝ}
    (hf : Measurable f) :
    ∫ y, f y ∂(energyLaw n h k β N η a) =
      (∫ u in unitBox (n + 1), constPhaseIntegrand n h k β N η a u *
        f (N * ∏ i, u i ^ (2 * k i))) / origPhaseIntegral n h k β N 1 (fun _ => a) η := by
  unfold energyLaw
  rw [integral_map (measurable_energyMap n k N).aemeasurable hf.aestronglyMeasurable,
    constPhasePosterior_integral n h k β N hηc hηnn a hZ]

/-- **Weak convergence of the posterior law of `NK` under vanishing phase perturbations**: along
`N_m → ∞`, if `|ξ_m − a| ≤ ε_m → 0` on the box (and the chart integrals are positive), the
posterior law of `NK` under the phase `ξ_m` converges weakly to `ρ_a`. -/
theorem perturbedEnergyLaw_tendsto_phaseLaw (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    {β : ℝ} (hβ : 0 < β) {cη : CoeffFamily (n + 1)} (hη : AbsSummable cη)
    {η : (Fin (n + 1) → ℝ) → ℝ} (hηc : Continuous η) (hηnn : ∀ u ∈ unitBox (n + 1), 0 ≤ η u)
    (hev : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF cη u = η u) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (hApos : ∀ b,
      0 < familySpectralCoeff n h k β (constFamily b) cη l (multCount (ratioExp h k) l - 1))
    (a : ℝ) (Nseq : ℕ → ℝ) (hN1 : ∀ m, 1 < Nseq m) (hN : Tendsto Nseq atTop atTop)
    (ξ : ℕ → (Fin (n + 1) → ℝ) → ℝ) (hξm : ∀ m, Measurable (ξ m)) (ε : ℕ → ℝ)
    (hε : Tendsto ε atTop (𝓝 0)) (hξ : ∀ m, ∀ u ∈ unitBox (n + 1), |ξ m u - a| ≤ ε m)
    (hZξ : ∀ m, 0 < origPhaseIntegral n h k β (Nseq m) 1 (ξ m) η)
    (hZa : ∀ m, 0 < origPhaseIntegral n h k β (Nseq m) 1 (fun _ => a) η) :
    Tendsto (β := ProbabilityMeasure ℝ) (fun m => ⟨phaseEnergyLaw n h k β (Nseq m) (ξ m) η,
        phaseEnergyLaw_isProbabilityMeasure n h k (Nseq m) hβ.le (hξm m) hηc hηnn (hξ m)
          (hZξ m)⟩) atTop
      (𝓝 ⟨phaseLaw β a l, @phaseLaw_isProbabilityMeasure β a l ⟨hβ⟩
        ⟨ratioExp_min_pos h k hk hatt⟩⟩) := by
  have hl0 : 0 < l := ratioExp_min_pos h k hk hatt
  have hconst := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1
    (energyLaw_tendsto_phaseLaw n h k hk hβ a hη hηc hηnn hev hmin hatt (hApos a).ne' Nseq hN1 hN
      hZa)
  refine ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.2 fun f => ?_
  change Tendsto (fun m => ∫ y, f y ∂(phaseEnergyLaw n h k β (Nseq m) (ξ m) η)) atTop
    (𝓝 (∫ y, f y ∂(phaseLaw β a l)))
  have hf := hconst f
  change Tendsto (fun m => ∫ y, f y ∂(energyLaw n h k β (Nseq m) η a)) atTop
    (𝓝 (∫ y, f y ∂(phaseLaw β a l))) at hf
  -- the perturbation term vanishes
  have hpert := phase_perturbation_tendsto n h k hk hβ hη hηc hηnn hev hmin hatt hApos a Nseq hN
    ξ hξm ε hε hξ (fun m u => f (Nseq m * ∏ i, u i ^ (2 * k i)))
    (fun m => f.continuous.measurable.comp (measurable_energyMap n k (Nseq m))) (norm_nonneg f)
    (fun m u _ => by rw [← Real.norm_eq_abs]; exact f.norm_coe_le_norm _)
  have := hpert.add hf
  rw [zero_add] at this
  refine this.congr' (Eventually.of_forall fun m => ?_)
  dsimp only
  rw [phaseEnergyLaw_integral n h k β (Nseq m) (hξm m) hηc hηnn (hZξ m)
    f.continuous.measurable, energyLaw_integral' n h k β (Nseq m) hηc hηnn a (hZa m)
    f.continuous.measurable, sub_add_cancel]

end Grammar
