/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.PhaseMomentHierarchy
import Grammar.LaplaceContinuity

/-!
# Weak convergence of the posterior law of `NK` at constant phase (unit 347; Astra #41 unit 5)

The constant-phase posterior on the unit box has density `η(u) u^h e^{-βN u^{2k} + β√N u^k a}/𝒵_N`
(for `η ≥ 0` on the box and `𝒵_N > 0`); the law of the energy `NK = N ∏ u^{2k}` under it is a
probability measure on `[0,∞)` whose Laplace transform is `T_N(a,t)` and whose moments are the
posterior energy moments.  By the Laplace continuity theorem and `T_N(a,t) → ∫ e^{-ty} dρ_a`,
**the posterior law of `NK` converges weakly to `ρ_a`**, the law with density
`∝ y^{λ-1} e^{-βy + βa√y}` — the Gamma law of shape `λ` and rate `β` at `a = 0`.
-/

namespace Grammar

open MeasureTheory Filter Topology Set CoeffFamily

theorem ratioExp_min_pos {d : ℕ} (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) {l : ℝ}
    (hatt : ∃ i, ratioExp h k i = l) : 0 < l := by
  obtain ⟨i, hi⟩ := hatt
  rw [← hi]
  exact ratioExp_pos h k hk i

/-! ### The constant-phase posterior on the unit box -/

/-- The integrand of the constant-phase chart integral. -/
noncomputable def constPhaseIntegrand (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N : ℝ)
    (η : (Fin (n + 1) → ℝ) → ℝ) (a : ℝ) (u : Fin (n + 1) → ℝ) : ℝ :=
  η u * (∏ i, u i ^ h i) *
    Real.exp (-(β * N * ∏ i, u i ^ (2 * k i)) + β * (Real.sqrt N * ∏ i, u i ^ k i) * a)

theorem origPhaseIntegral_eq_integral_integrand (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N : ℝ)
    (η : (Fin (n + 1) → ℝ) → ℝ) (a : ℝ) :
    origPhaseIntegral n h k β N 1 (fun _ => a) η =
      ∫ u in unitBox (n + 1), constPhaseIntegrand n h k β N η a u := rfl

theorem continuous_constPhaseIntegrand (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N : ℝ)
    {η : (Fin (n + 1) → ℝ) → ℝ} (hηc : Continuous η) (a : ℝ) :
    Continuous (constPhaseIntegrand n h k β N η a) := by
  unfold constPhaseIntegrand
  fun_prop

theorem constPhaseIntegrand_nonneg (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N : ℝ)
    {η : (Fin (n + 1) → ℝ) → ℝ} (hηnn : ∀ u ∈ unitBox (n + 1), 0 ≤ η u) (a : ℝ)
    {u : Fin (n + 1) → ℝ} (hu : u ∈ unitBox (n + 1)) :
    0 ≤ constPhaseIntegrand n h k β N η a u := by
  have hu' : ∀ i, 0 < u i ∧ u i ≤ 1 := fun i => Set.mem_univ_pi.1 hu i
  exact mul_nonneg (mul_nonneg (hηnn u hu)
    (Finset.prod_nonneg fun i _ => pow_nonneg (hu' i).1.le _)) (Real.exp_pos _).le

/-- **The constant-phase posterior** on the unit box: density
`η(u) u^h e^{-βN u^{2k} + β√N u^k a}/𝒵_N` with respect to Lebesgue measure. -/
noncomputable def constPhasePosterior (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N : ℝ)
    (η : (Fin (n + 1) → ℝ) → ℝ) (a : ℝ) : Measure (Fin (n + 1) → ℝ) :=
  (volume.restrict (unitBox (n + 1))).withDensity fun u =>
    ENNReal.ofReal (constPhaseIntegrand n h k β N η a u /
      origPhaseIntegral n h k β N 1 (fun _ => a) η)

theorem constPhasePosterior_integral (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N : ℝ)
    {η : (Fin (n + 1) → ℝ) → ℝ} (hηc : Continuous η) (hηnn : ∀ u ∈ unitBox (n + 1), 0 ≤ η u)
    (a : ℝ) (hZ : 0 < origPhaseIntegral n h k β N 1 (fun _ => a) η) (g : (Fin (n + 1) → ℝ) → ℝ) :
    ∫ u, g u ∂(constPhasePosterior n h k β N η a) =
      (∫ u in unitBox (n + 1), constPhaseIntegrand n h k β N η a u * g u) /
        origPhaseIntegral n h k β N 1 (fun _ => a) η := by
  unfold constPhasePosterior
  rw [integral_withDensity_eq_integral_toReal_smul
    (((continuous_constPhaseIntegrand n h k β N hηc a).measurable.div_const _).ennreal_ofReal)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top), ← integral_div]
  refine setIntegral_congr_fun (measurableSet_unitBox _) fun u hu => ?_
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (div_nonneg (constPhaseIntegrand_nonneg n h k β N hηnn a hu) hZ.le)]
  ring

theorem constPhasePosterior_isProbabilityMeasure (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N : ℝ)
    {η : (Fin (n + 1) → ℝ) → ℝ} (hηc : Continuous η) (hηnn : ∀ u ∈ unitBox (n + 1), 0 ≤ η u)
    (a : ℝ) (hZ : 0 < origPhaseIntegral n h k β N 1 (fun _ => a) η) :
    IsProbabilityMeasure (constPhasePosterior n h k β N η a) := by
  constructor
  unfold constPhasePosterior
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal]
  · rw [integral_div, ← origPhaseIntegral_eq_integral_integrand, div_self hZ.ne',
      ENNReal.ofReal_one]
  · exact (integrableOn_unitBox_of_continuous _
      (continuous_constPhaseIntegrand n h k β N hηc a)).div_const _
  · rw [Filter.EventuallyLE, ae_restrict_iff' (measurableSet_unitBox _)]
    exact Eventually.of_forall fun u hu =>
      div_nonneg (constPhaseIntegrand_nonneg n h k β N hηnn a hu) hZ.le

theorem constPhasePosterior_compl (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N : ℝ)
    (η : (Fin (n + 1) → ℝ) → ℝ) (a : ℝ) :
    constPhasePosterior n h k β N η a (unitBox (n + 1))ᶜ = 0 := by
  unfold constPhasePosterior
  rw [withDensity_apply _ (measurableSet_unitBox _).compl]
  refine setLIntegral_measure_zero _ _ ?_
  rw [Measure.restrict_apply (measurableSet_unitBox _).compl, compl_inter_self, measure_empty]

/-! ### The posterior law of the energy -/

theorem measurable_energyMap (n : ℕ) (k : Fin (n + 1) → ℕ) (N : ℝ) :
    Measurable fun u : Fin (n + 1) → ℝ => N * ∏ i, u i ^ (2 * k i) :=
  (by fun_prop : Continuous fun u : Fin (n + 1) → ℝ => N * ∏ i, u i ^ (2 * k i)).measurable

/-- **The posterior law of `NK`** at constant phase: the image of the posterior under
`u ↦ N ∏ u^{2k}`. -/
noncomputable def energyLaw (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N : ℝ)
    (η : (Fin (n + 1) → ℝ) → ℝ) (a : ℝ) : Measure ℝ :=
  (constPhasePosterior n h k β N η a).map fun u => N * ∏ i, u i ^ (2 * k i)

theorem energyLaw_isProbabilityMeasure (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N : ℝ)
    {η : (Fin (n + 1) → ℝ) → ℝ} (hηc : Continuous η) (hηnn : ∀ u ∈ unitBox (n + 1), 0 ≤ η u)
    (a : ℝ) (hZ : 0 < origPhaseIntegral n h k β N 1 (fun _ => a) η) :
    IsProbabilityMeasure (energyLaw n h k β N η a) :=
  haveI := constPhasePosterior_isProbabilityMeasure n h k β N hηc hηnn a hZ
  Measure.isProbabilityMeasure_map (measurable_energyMap n k N).aemeasurable

/-- The energy law is carried by `[0,∞)`. -/
theorem energyLaw_Iio (n : ℕ) (h k : Fin (n + 1) → ℕ) (β : ℝ) {N : ℝ} (hN : 0 ≤ N)
    (η : (Fin (n + 1) → ℝ) → ℝ) (a : ℝ) : energyLaw n h k β N η a (Iio 0) = 0 := by
  unfold energyLaw
  rw [Measure.map_apply (measurable_energyMap n k N) measurableSet_Iio]
  refine measure_mono_null ?_ (constPhasePosterior_compl n h k β N η a)
  intro u hu hbox
  have hu' : ∀ i, 0 < u i ∧ u i ≤ 1 := fun i => Set.mem_univ_pi.1 hbox i
  have : 0 ≤ N * ∏ i, u i ^ (2 * k i) :=
    mul_nonneg hN (Finset.prod_nonneg fun i _ => pow_nonneg (hu' i).1.le _)
  exact absurd hu (not_lt.2 this)

theorem energyLaw_integral (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N : ℝ)
    {η : (Fin (n + 1) → ℝ) → ℝ} (hηc : Continuous η) (hηnn : ∀ u ∈ unitBox (n + 1), 0 ≤ η u)
    (a : ℝ) (hZ : 0 < origPhaseIntegral n h k β N 1 (fun _ => a) η) {g : ℝ → ℝ}
    (hg : Measurable g) :
    ∫ y, g y ∂(energyLaw n h k β N η a) =
      origPhaseIntegral n h k β N 1 (fun _ => a) (fun u => g (N * ∏ i, u i ^ (2 * k i)) * η u) /
        origPhaseIntegral n h k β N 1 (fun _ => a) η := by
  unfold energyLaw
  rw [integral_map (measurable_energyMap n k N).aemeasurable hg.aestronglyMeasurable,
    constPhasePosterior_integral n h k β N hηc hηnn a hZ]
  congr 1
  unfold origPhaseIntegral constPhaseIntegrand
  refine setIntegral_congr_fun (measurableSet_unitBox _) fun u _ => ?_
  ring

/-- The Laplace transform of the energy law is the posterior Laplace transform `T_N(a,t)`. -/
theorem energyLaw_laplace (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N : ℝ)
    {η : (Fin (n + 1) → ℝ) → ℝ} (hηc : Continuous η) (hηnn : ∀ u ∈ unitBox (n + 1), 0 ≤ η u)
    (a : ℝ) (hZ : 0 < origPhaseIntegral n h k β N 1 (fun _ => a) η) (t : ℝ) :
    ∫ y, Real.exp (-(t * y)) ∂(energyLaw n h k β N η a) = constPhaseLaplace n h k β N η a t := by
  rw [energyLaw_integral n h k β N hηc hηnn a hZ
    (by fun_prop : Continuous fun y : ℝ => Real.exp (-(t * y))).measurable]
  unfold constPhaseLaplace
  congr 2
  funext u
  rw [mul_assoc]

/-- The moments of the energy law are the posterior energy moments. -/
theorem energyLaw_moment (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N : ℝ)
    {η : (Fin (n + 1) → ℝ) → ℝ} (hηc : Continuous η) (hηnn : ∀ u ∈ unitBox (n + 1), 0 ≤ η u)
    (a : ℝ) (hZ : 0 < origPhaseIntegral n h k β N 1 (fun _ => a) η) (q : ℕ) :
    ∫ y, y ^ q ∂(energyLaw n h k β N η a) =
      N ^ q * (origPhaseIntegral n h k β N 1 (fun _ => a)
        (fun u => (∏ i, u i ^ (2 * k i)) ^ q * η u) /
      origPhaseIntegral n h k β N 1 (fun _ => a) η) := by
  rw [energyLaw_integral n h k β N hηc hηnn a hZ (continuous_pow q).measurable, ← mul_div_assoc]
  congr 1
  unfold origPhaseIntegral
  rw [← integral_const_mul]
  refine setIntegral_congr_fun (measurableSet_unitBox _) fun u _ => ?_
  dsimp only
  rw [mul_pow]
  ring

theorem phaseLaw_Iio (β a l : ℝ) : phaseLaw β a l (Iio 0) = 0 := by
  unfold phaseLaw
  rw [withDensity_apply _ measurableSet_Iio]
  refine setLIntegral_measure_zero _ _ ?_
  rw [Measure.restrict_apply measurableSet_Iio, Iio_inter_Ioi, Ioo_self, measure_empty]

/-- **Weak convergence of the posterior law of `NK` at constant phase to `ρ_a`.**  Along any
sequence `N_m → ∞` at which the chart integral is positive (as it eventually is when `A(a) > 0`),
the posterior law of `N K` at constant phase `a` converges weakly to the law with density
`∝ y^{λ-1} e^{-βy + βa√y}` on `(0,∞)`. -/
theorem energyLaw_tendsto_phaseLaw (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {β : ℝ}
    (hβ : 0 < β) (a : ℝ) {cη : CoeffFamily (n + 1)} (hη : AbsSummable cη)
    {η : (Fin (n + 1) → ℝ) → ℝ} (hηc : Continuous η) (hηnn : ∀ u ∈ unitBox (n + 1), 0 ≤ η u)
    (hev : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF cη u = η u) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (hA : familySpectralCoeff n h k β (constFamily a) cη l (multCount (ratioExp h k) l - 1) ≠ 0)
    (Nseq : ℕ → ℝ) (hN1 : ∀ m, 1 < Nseq m) (hN : Tendsto Nseq atTop atTop)
    (hZ : ∀ m, 0 < origPhaseIntegral n h k β (Nseq m) 1 (fun _ => a) η) :
    Tendsto (β := ProbabilityMeasure ℝ) (fun m => ⟨energyLaw n h k β (Nseq m) η a,
        energyLaw_isProbabilityMeasure n h k β (Nseq m) hηc hηnn a (hZ m)⟩)
      atTop (𝓝 ⟨phaseLaw β a l,
        @phaseLaw_isProbabilityMeasure β a l ⟨hβ⟩ ⟨ratioExp_min_pos h k hk hatt⟩⟩) := by
  refine tendsto_of_laplace _ _ (fun m => energyLaw_Iio n h k β (by linarith [hN1 m]) η a)
    (phaseLaw_Iio β a l) fun t ht => ?_
  change Tendsto (fun m => ∫ y, Real.exp (-(t * y)) ∂(energyLaw n h k β (Nseq m) η a)) atTop
    (𝓝 (∫ y, Real.exp (-(t * y)) ∂(phaseLaw β a l)))
  have e : ∀ m, ∫ y, Real.exp (-(t * y)) ∂(energyLaw n h k β (Nseq m) η a) =
      constPhaseLaplace n h k β (Nseq m) η a t :=
    fun m => energyLaw_laplace n h k β (Nseq m) hηc hηnn a (hZ m) t
  simp only [e]
  exact (constPhaseLaplace_tendsto_law n h k hk hβ ht a hη hηc hev hmin hatt hA).comp hN

end Grammar
