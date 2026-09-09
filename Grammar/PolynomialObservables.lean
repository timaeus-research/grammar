/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.PerturbedMoments

/-!
# Polynomial-growth observables (unit 353; Astra #43 unit 2)

Weak convergence of probability laws on `ℝ` together with an eventually uniform bound on the
`q`-th absolute moments gives convergence of `∫ f` for every continuous `f` with
`|f(y)| ≤ C(1 + |y|^r)`, `r < q` (`tendsto_integral_of_polynomial_growth`; truncation by the
continuous cutoff `φ_R = max(0, min(1, 2 − |y|/R))`, tails controlled by
`|f|(1 − φ_R) ≤ 2C|y|^q/R^{q−r}`).  Applied to the perturbed posterior energy laws: for
`|ξ_N − a| ≤ ε_N → 0`, `∫ f d(law of NK under ξ_N) → ∫ f dρ_a` for every continuous `f` of
polynomial growth (`perturbedEnergyLaw_integral_tendsto`).  Not claimed: arbitrary measurable
polynomially bounded observables; Wasserstein distances.
-/

namespace Grammar

open MeasureTheory Filter Topology Set CoeffFamily BoundedContinuousFunction

/-! ### The truncation lemma -/

/-- The continuous cutoff `φ_R(y) = max(0, min(1, 2 − |y|/R))`: `1` on `|y| ≤ R`, `0` for
`|y| ≥ 2R`. -/
noncomputable def polyCutoff (R y : ℝ) : ℝ := max 0 (min 1 (2 - |y| / R))

theorem continuous_polyCutoff (R : ℝ) : Continuous (polyCutoff R) := by
  unfold polyCutoff
  fun_prop

theorem polyCutoff_nonneg (R y : ℝ) : 0 ≤ polyCutoff R y := le_max_left _ _

theorem polyCutoff_le_one (R y : ℝ) : polyCutoff R y ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem polyCutoff_eq_one {R y : ℝ} (hR : 0 < R) (hy : |y| ≤ R) : polyCutoff R y = 1 := by
  unfold polyCutoff
  have : 1 ≤ 2 - |y| / R := by
    have := (div_le_one hR).2 hy
    linarith
  rw [min_eq_left this, max_eq_right zero_le_one]

theorem polyCutoff_eq_zero {R y : ℝ} (hR : 0 < R) (hy : 2 * R ≤ |y|) : polyCutoff R y = 0 := by
  unfold polyCutoff
  have : 2 - |y| / R ≤ 0 := by
    have := (le_div_iff₀ hR).2 (by linarith : 2 * R ≤ |y|)
    linarith
  rw [max_eq_left ((min_le_right _ _).trans this)]

/-- Tail bound: `|f(y)| (1 − φ_R(y)) ≤ 2C |y|^q / R^{q−r}` for `R ≥ 1`, `r < q`. -/
theorem tail_bound_cutoff {f : ℝ → ℝ} {C : ℝ} {r q : ℕ} (hrq : r < q)
    (hfC : ∀ y, |f y| ≤ C * (1 + |y| ^ r)) (hC0 : 0 ≤ C) {R : ℝ} (hR : 1 ≤ R) (y : ℝ) :
    |f y - f y * polyCutoff R y| ≤ 2 * C * |y| ^ q / R ^ (q - r) := by
  have hR0 : 0 < R := by linarith
  have hRq : 0 < R ^ (q - r) := pow_pos hR0 _
  rw [← mul_one_sub, abs_mul,
    abs_of_nonneg (show (0 : ℝ) ≤ 1 - polyCutoff R y by linarith [polyCutoff_le_one R y])]
  rcases le_or_gt |y| R with hy | hy
  · rw [polyCutoff_eq_one hR0 hy, sub_self, mul_zero]
    positivity
  · have hy1 : 1 ≤ |y| := hR.trans hy.le
    have h1 : |f y| ≤ 2 * C * |y| ^ r := by
      refine (hfC y).trans ?_
      have : (1 : ℝ) ≤ |y| ^ r := one_le_pow₀ hy1
      have := mul_le_mul_of_nonneg_left this hC0
      linarith
    have h2 : |y| ^ r * R ^ (q - r) ≤ |y| ^ q := by
      calc |y| ^ r * R ^ (q - r) ≤ |y| ^ r * |y| ^ (q - r) :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hR0.le hy.le _) (by positivity)
        _ = |y| ^ q := by rw [← pow_add, Nat.add_sub_cancel' hrq.le]
    have h3 : |y| ^ r ≤ |y| ^ q / R ^ (q - r) := (le_div_iff₀ hRq).2 h2
    calc |f y| * (1 - polyCutoff R y) ≤ |f y| * 1 :=
          mul_le_mul_of_nonneg_left (by linarith [polyCutoff_nonneg R y]) (abs_nonneg _)
      _ ≤ 2 * C * |y| ^ r := by rw [mul_one]; exact h1
      _ ≤ 2 * C * (|y| ^ q / R ^ (q - r)) := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = 2 * C * |y| ^ q / R ^ (q - r) := by ring

theorem abs_pow_le_one_add_abs_pow {y : ℝ} {r q : ℕ} (hrq : r ≤ q) : |y| ^ r ≤ 1 + |y| ^ q := by
  rcases le_or_gt |y| 1 with hy | hy
  · have := pow_le_one₀ (abs_nonneg y) hy (n := r)
    linarith [pow_nonneg (abs_nonneg y) q]
  · have := pow_le_pow_right₀ hy.le hrq
    linarith

/-- The truncated observable as a bounded continuous function. -/
noncomputable def truncObs (f : ℝ → ℝ) (hf : Continuous f) {C : ℝ} {r : ℕ}
    (hfC : ∀ y, |f y| ≤ C * (1 + |y| ^ r)) (hC0 : 0 ≤ C) {R : ℝ} (hR : 0 < R) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun y => f y * polyCutoff R y)
    (hf.mul (continuous_polyCutoff R)) (C * (1 + (2 * R) ^ r)) (fun y => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (polyCutoff_nonneg R y)]
      rcases le_or_gt |y| (2 * R) with hy | hy
      · calc |f y| * polyCutoff R y ≤ |f y| * 1 :=
              mul_le_mul_of_nonneg_left (polyCutoff_le_one R y) (abs_nonneg _)
          _ ≤ C * (1 + (2 * R) ^ r) := by
              rw [mul_one]
              refine (hfC y).trans (mul_le_mul_of_nonneg_left ?_ hC0)
              linarith [pow_le_pow_left₀ (abs_nonneg y) hy r]
      · rw [polyCutoff_eq_zero hR hy.le, mul_zero]
        positivity)

/-- **Weak convergence + uniformly bounded higher moments ⇒ convergence of polynomial-growth
observables.** -/
theorem tendsto_integral_of_polynomial_growth {ν : ℕ → ProbabilityMeasure ℝ}
    {ν₀ : ProbabilityMeasure ℝ} (hν : Tendsto ν atTop (𝓝 ν₀)) {f : ℝ → ℝ} (hf : Continuous f)
    {C : ℝ} {r q : ℕ} (hrq : r < q) (hfC : ∀ y, |f y| ≤ C * (1 + |y| ^ r)) {M : ℝ}
    (hint : ∀ n, Integrable (fun y => |y| ^ q) (ν n : Measure ℝ))
    (hM : ∀ᶠ n in atTop, ∫ y, |y| ^ q ∂(ν n : Measure ℝ) ≤ M)
    (hint₀ : Integrable (fun y => |y| ^ q) (ν₀ : Measure ℝ))
    (hM₀ : ∫ y, |y| ^ q ∂(ν₀ : Measure ℝ) ≤ M) :
    Tendsto (fun n => ∫ y, f y ∂(ν n : Measure ℝ)) atTop (𝓝 (∫ y, f y ∂(ν₀ : Measure ℝ))) := by
  have hC0 : 0 ≤ C := by
    have h := (abs_nonneg (f 0)).trans (hfC 0)
    by_contra hC
    push Not at hC
    have := mul_neg_of_neg_of_pos hC (by positivity : (0 : ℝ) < 1 + |(0 : ℝ)| ^ r)
    exact absurd h (not_le.2 this)
  have hM0 : 0 ≤ M := le_trans (integral_nonneg fun y => by positivity) hM₀
  -- integrability of `f` against every law with a finite `q`-th moment
  have hfint : ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ], Integrable (fun y => |y| ^ q) μ →
      Integrable f μ := fun μ _ hμ => by
    refine ((hμ.add (integrable_const (2 : ℝ))).const_mul C).mono'
      hf.measurable.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs]
    refine (hfC y).trans (mul_le_mul_of_nonneg_left ?_ hC0)
    change 1 + |y| ^ r ≤ |y| ^ q + 2
    linarith [abs_pow_le_one_add_abs_pow (y := y) hrq.le]
  rw [Metric.tendsto_nhds]
  intro ε hε
  -- the truncation radius
  obtain ⟨R, hR1, hRε⟩ : ∃ R : ℝ, 1 ≤ R ∧ 2 * C * M / R ^ (q - r) < ε / 3 := by
    refine ⟨max 1 (6 * C * M / ε + 1), le_max_left _ _, ?_⟩
    have hR0 : 0 < max 1 (6 * C * M / ε + 1) := lt_of_lt_of_le one_pos (le_max_left _ _)
    have hR1 : 1 ≤ max 1 (6 * C * M / ε + 1) := le_max_left _ _
    have hRpow : max 1 (6 * C * M / ε + 1) ≤ max 1 (6 * C * M / ε + 1) ^ (q - r) := by
      have : 1 ≤ q - r := by omega
      calc max 1 (6 * C * M / ε + 1) = max 1 (6 * C * M / ε + 1) ^ 1 := (pow_one _).symm
        _ ≤ max 1 (6 * C * M / ε + 1) ^ (q - r) := pow_le_pow_right₀ hR1 this
    calc 2 * C * M / max 1 (6 * C * M / ε + 1) ^ (q - r)
        ≤ 2 * C * M / max 1 (6 * C * M / ε + 1) :=
          div_le_div_of_nonneg_left (by positivity) hR0 hRpow
      _ < ε / 3 := by
          rw [div_lt_iff₀ hR0]
          have : 6 * C * M / ε + 1 ≤ max 1 (6 * C * M / ε + 1) := le_max_right _ _
          have h7 : ε / 3 * (6 * C * M / ε + 1) = 2 * C * M + ε / 3 := by
            field_simp
            ring
          linarith [mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ ε / 3)]
  have hR0 : 0 < R := by linarith
  set g := truncObs f hf hfC hC0 hR0 with hg
  have hgapp : ∀ y, g y = f y * polyCutoff R y := fun y => rfl
  -- tail estimate for one law
  have htail : ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ], Integrable (fun y => |y| ^ q) μ →
      ∫ y, |y| ^ q ∂μ ≤ M → |∫ y, f y ∂μ - ∫ y, g y ∂μ| ≤ 2 * C * M / R ^ (q - r) := by
    intro μ _ hμ hμM
    rw [← integral_sub (hfint μ hμ) (BoundedContinuousFunction.integrable _ _), ← Real.norm_eq_abs]
    refine (norm_integral_le_integral_norm _).trans ?_
    calc ∫ y, ‖f y - g y‖ ∂μ ≤ ∫ y, 2 * C * |y| ^ q / R ^ (q - r) ∂μ := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun y => norm_nonneg _)
            ((hμ.const_mul (2 * C)).div_const _) (Eventually.of_forall fun y => ?_)
          change ‖f y - g y‖ ≤ 2 * C * |y| ^ q / R ^ (q - r)
          rw [Real.norm_eq_abs, hgapp]
          exact tail_bound_cutoff hrq hfC hC0 hR1 y
      _ = 2 * C * (∫ y, |y| ^ q ∂μ) / R ^ (q - r) := by
          simp only [mul_div_assoc]
          rw [integral_const_mul, integral_div]
      _ ≤ 2 * C * M / R ^ (q - r) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hμM (by positivity))
            (by positivity)
  have hgconv := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hν g).eventually
    (Metric.ball_mem_nhds _ (by positivity : (0 : ℝ) < ε / 3))
  filter_upwards [hM, hgconv] with n hMn hgn
  rw [Real.dist_eq] at hgn
  rw [Real.dist_eq]
  have h1 := htail (ν n) (hint n) hMn
  have h2 := htail ν₀ hint₀ hM₀
  calc |∫ y, f y ∂(ν n : Measure ℝ) - ∫ y, f y ∂(ν₀ : Measure ℝ)|
      = |(∫ y, f y ∂(ν n : Measure ℝ) - ∫ y, g y ∂(ν n : Measure ℝ)) +
          (∫ y, g y ∂(ν n : Measure ℝ) - ∫ y, g y ∂(ν₀ : Measure ℝ)) -
          (∫ y, f y ∂(ν₀ : Measure ℝ) - ∫ y, g y ∂(ν₀ : Measure ℝ))| := by ring_nf
    _ ≤ |∫ y, f y ∂(ν n : Measure ℝ) - ∫ y, g y ∂(ν n : Measure ℝ)| +
          |∫ y, g y ∂(ν n : Measure ℝ) - ∫ y, g y ∂(ν₀ : Measure ℝ)| +
          |∫ y, f y ∂(ν₀ : Measure ℝ) - ∫ y, g y ∂(ν₀ : Measure ℝ)| :=
        (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ < ε / 3 + ε / 3 + ε / 3 := by
        gcongr
        · exact lt_of_le_of_lt h1 hRε
        · exact lt_of_le_of_lt h2 hRε
    _ = ε := by ring

/-! ### Moments of the laws involved -/

theorem phaseEnergyLaw_Iio (n : ℕ) (h k : Fin (n + 1) → ℕ) (β : ℝ) {N : ℝ} (hN : 0 ≤ N)
    (ξ η : (Fin (n + 1) → ℝ) → ℝ) : phaseEnergyLaw n h k β N ξ η (Iio 0) = 0 := by
  unfold phaseEnergyLaw
  rw [Measure.map_apply (measurable_energyMap n k N) measurableSet_Iio]
  have hcompl : phasePosterior n h k β N ξ η (unitBox (n + 1))ᶜ = 0 := by
    unfold phasePosterior
    rw [withDensity_apply _ (measurableSet_unitBox _).compl]
    refine setLIntegral_measure_zero _ _ ?_
    rw [Measure.restrict_apply (measurableSet_unitBox _).compl, compl_inter_self, measure_empty]
  refine measure_mono_null ?_ hcompl
  intro u hu hbox
  have hu' : ∀ i, 0 < u i ∧ u i ≤ 1 := fun i => Set.mem_univ_pi.1 hbox i
  have : 0 ≤ N * ∏ i, u i ^ (2 * k i) :=
    mul_nonneg hN (Finset.prod_nonneg fun i _ => pow_nonneg (hu' i).1.le _)
  exact absurd hu (not_lt.2 this)

/-- The energy is bounded on the box, so every moment of the perturbed energy law is finite. -/
theorem phaseEnergyLaw_integrable_pow (n : ℕ) (h k : Fin (n + 1) → ℕ) {β : ℝ} (N : ℝ)
    (hβ : 0 ≤ β) {ξ η : (Fin (n + 1) → ℝ) → ℝ} (hξm : Measurable ξ) (hηc : Continuous η)
    (hηnn : ∀ u ∈ unitBox (n + 1), 0 ≤ η u) {a ε : ℝ}
    (hξ : ∀ u ∈ unitBox (n + 1), |ξ u - a| ≤ ε) (hZ : 0 < origPhaseIntegral n h k β N 1 ξ η)
    (q : ℕ) : Integrable (fun y => |y| ^ q) (phaseEnergyLaw n h k β N ξ η) := by
  have := phasePosterior_isProbabilityMeasure n h k N hβ hξm hηc hηnn hξ hZ
  unfold phaseEnergyLaw
  rw [integrable_map_measure
    (by fun_prop : Continuous fun y : ℝ => |y| ^ q).measurable.aestronglyMeasurable
    (measurable_energyMap n k N).aemeasurable]
  refine (integrable_const (|N| ^ q)).mono'
    ((by fun_prop : Continuous fun y : ℝ => |y| ^ q).measurable.comp
      (measurable_energyMap n k N)).aestronglyMeasurable ?_
  have hcompl : phasePosterior n h k β N ξ η (unitBox (n + 1))ᶜ = 0 := by
    unfold phasePosterior
    rw [withDensity_apply _ (measurableSet_unitBox _).compl]
    refine setLIntegral_measure_zero _ _ ?_
    rw [Measure.restrict_apply (measurableSet_unitBox _).compl, compl_inter_self, measure_empty]
  have hae : ∀ᵐ u ∂(phasePosterior n h k β N ξ η), u ∈ unitBox (n + 1) := by
    rw [ae_iff]
    exact hcompl
  filter_upwards [hae] with u hu
  have hu' : ∀ i, 0 < u i ∧ u i ≤ 1 := fun i => Set.mem_univ_pi.1 hu i
  have hP0 : 0 ≤ ∏ i, u i ^ (2 * k i) := Finset.prod_nonneg fun i _ => pow_nonneg (hu' i).1.le _
  have hP1 : ∏ i, u i ^ (2 * k i) ≤ 1 :=
    Finset.prod_le_one (fun i _ => pow_nonneg (hu' i).1.le _)
      (fun i _ => pow_le_one₀ (hu' i).1.le (hu' i).2)
  simp only [Function.comp, Real.norm_eq_abs, abs_pow, abs_abs]
  refine pow_le_pow_left₀ (abs_nonneg _) ?_ q
  rw [abs_mul, abs_of_nonneg hP0]
  exact mul_le_of_le_one_right (abs_nonneg N) hP1

theorem phaseLaw_integrable_pow (β a l : ℝ) (hβ : 0 < β) (hl : 0 < l) (q : ℕ) :
    Integrable (fun y => |y| ^ q) (phaseLaw β a l) := by
  unfold phaseLaw
  rw [integrable_withDensity_iff (((measurable_phaseLawKernel β a l).div_const _).ennreal_ofReal)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine ((integrableOn_phaseLawKernel β a (l + q) hβ (by positivity)).div_const
    (fluctMoment β a 0 l 0)).congr ?_
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioi]
  refine Eventually.of_forall fun y hy => ?_
  have hy0 : 0 < y := hy
  rw [ENNReal.toReal_ofReal (div_nonneg (phaseLawKernel_nonneg β a l hy0.le)
    (fluctMoment_pos β a l hβ hl).le)]
  unfold phaseLawKernel
  rw [abs_of_pos hy0, ← Real.rpow_natCast, div_eq_mul_inv, div_eq_mul_inv]
  have : y ^ (l + q - 1) = y ^ (l - 1) * y ^ (q : ℝ) := by
    rw [← Real.rpow_add hy0]
    congr 1
    ring
  rw [this]
  ring

theorem phaseLaw_integral_abs_pow (β a l : ℝ) (hβ : 0 < β) (hl : 0 < l) (q : ℕ) :
    ∫ y, |y| ^ q ∂(phaseLaw β a l) = fluctMoment β a 0 (l + q) 0 / fluctMoment β a 0 l 0 := by
  rw [← phaseLaw_moment β a l hβ hl q]
  refine integral_congr_ae ?_
  have h0 := phaseLaw_Iio β a l
  filter_upwards [ae_nonneg_of_measure_Iio h0] with y hy
  rw [abs_of_nonneg hy]

/-- The `q`-th moment of the perturbed energy law is the perturbed posterior moment. -/
theorem phaseEnergyLaw_integral_abs_pow (n : ℕ) (h k : Fin (n + 1) → ℕ) {β : ℝ} {N : ℝ}
    (hN : 0 ≤ N) (hβ : 0 ≤ β) {ξ η : (Fin (n + 1) → ℝ) → ℝ} (hξm : Measurable ξ)
    (hηc : Continuous η) (hηnn : ∀ u ∈ unitBox (n + 1), 0 ≤ η u)
    (hZ : 0 < origPhaseIntegral n h k β N 1 ξ η) (q : ℕ) :
    ∫ y, |y| ^ q ∂(phaseEnergyLaw n h k β N ξ η) =
      (∫ u in unitBox (n + 1), phaseIntegrand n h k β N ξ η u * (N * ∏ i, u i ^ (2 * k i)) ^ q) /
        origPhaseIntegral n h k β N 1 ξ η := by
  have _ := hβ
  rw [← phaseEnergyLaw_integral n h k β N hξm hηc hηnn hZ (continuous_pow q).measurable]
  refine integral_congr_ae ?_
  filter_upwards [ae_nonneg_of_measure_Iio (phaseEnergyLaw_Iio n h k β hN ξ η)] with y hy
  rw [abs_of_nonneg hy]

/-- **Polynomial-growth observables of the perturbed posterior energy converge**: for
`|ξ_m − a| ≤ ε_m → 0` and continuous `f` with `|f(y)| ≤ C(1 + |y|^r)`,
`∫ f d(law of NK under ξ_m) → ∫ f dρ_a`. -/
theorem perturbedEnergyLaw_integral_tendsto (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
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
    (hZa : ∀ m, 0 < origPhaseIntegral n h k β (Nseq m) 1 (fun _ => a) η)
    {f : ℝ → ℝ} (hf : Continuous f) {C : ℝ} {r : ℕ} (hfC : ∀ y, |f y| ≤ C * (1 + |y| ^ r)) :
    Tendsto (fun m => ∫ y, f y ∂(phaseEnergyLaw n h k β (Nseq m) (ξ m) η)) atTop
      (𝓝 (∫ y, f y ∂(phaseLaw β a l))) := by
  have hl0 : 0 < l := ratioExp_min_pos h k hk hatt
  have hweak := perturbedEnergyLaw_tendsto_phaseLaw n h k hk hβ hη hηc hηnn hev hmin hatt hApos a
    Nseq hN1 hN ξ hξm ε hε hξ hZξ hZa
  -- the `(r+1)`-st moments converge, hence are eventually bounded
  have hmom := perturbed_energy_moment_tendsto n h k hk hβ hη hηc hηnn hev hmin hatt hApos a Nseq
    hN ξ hξm ε hε hξ (r + 1)
  set M := fluctMoment β a 0 (l + (r + 1 : ℕ)) 0 / fluctMoment β a 0 l 0 + 1 with hM
  have hev' : ∀ᶠ m in atTop, ∫ y, |y| ^ (r + 1) ∂(phaseEnergyLaw n h k β (Nseq m) (ξ m) η) ≤ M := by
    filter_upwards [hmom.eventually (Iio_mem_nhds (show fluctMoment β a 0 (l + (r + 1 : ℕ)) 0 /
      fluctMoment β a 0 l 0 < M by rw [hM]; linarith))] with m hm
    rw [phaseEnergyLaw_integral_abs_pow n h k (by linarith [hN1 m]) hβ.le (hξm m) hηc hηnn (hZξ m)]
    exact hm.le
  exact tendsto_integral_of_polynomial_growth (ν := fun m =>
      ⟨phaseEnergyLaw n h k β (Nseq m) (ξ m) η, phaseEnergyLaw_isProbabilityMeasure n h k (Nseq m)
        hβ.le (hξm m) hηc hηnn (hξ m) (hZξ m)⟩)
    (ν₀ := ⟨phaseLaw β a l, @phaseLaw_isProbabilityMeasure β a l ⟨hβ⟩ ⟨hl0⟩⟩) hweak hf
    (Nat.lt_succ_self r) hfC
    (fun m => phaseEnergyLaw_integrable_pow n h k (Nseq m) hβ.le (hξm m) hηc hηnn (hξ m) (hZξ m)
      (r + 1)) hev' (phaseLaw_integrable_pow β a l hβ hl0 (r + 1))
    (by
      change ∫ y, |y| ^ (r + 1) ∂(phaseLaw β a l) ≤ M
      rw [phaseLaw_integral_abs_pow β a l hβ hl0 (r + 1), hM]
      linarith)

end Grammar
