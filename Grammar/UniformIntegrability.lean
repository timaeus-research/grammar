/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.RandomMixedVector
import Grammar.RandomFieldTransfer

/-!
# Expectations under law-level uniform integrability

For probability laws `ν_j ⇒ ν` on `ℝ` with integrable first moments and the
uniform-integrability condition `∀ ε > 0, ∃ R, ∀ j, ∫ |t| 1_{|t| > R} dν_j ≤ ε`, the limit law
has a finite first moment and the means converge
(`integrable_and_tendsto_integral_of_uniformIntegrable`).  The proof truncates:
`|t − clip_R t| = (|t| − R)⁺ ≤ |t| 1_{|t|>R}`, the clipped identity is bounded continuous, and the
excess `(|t| − R)⁺` of the limit law is controlled by monotone convergence through the bounded
continuous truncations `min((|t|−R)⁺, M)`.

Applications: the expectations of the random next-log statistics converge under uniform
integrability of their laws — the posterior energy correction
(`randomEnergyMean_expectation_tendsto`) and the free-energy correction
(`randomFreeEnergy_expectation_tendsto`).  Tightness (automatic on the Polish data space) is not
uniform integrability; the hypothesis is genuinely additional.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

open BoundedContinuousFunction

/-! ### Clipping and excess -/

/-- The excess above level `R`: `(|t| − R)⁺`. -/
def excess (R t : ℝ) : ℝ := max (|t| - R) 0

theorem excess_nonneg (R t : ℝ) : 0 ≤ excess R t := le_max_right _ _

theorem continuous_excess (R : ℝ) : Continuous (excess R) :=
  (continuous_abs.sub continuous_const).max continuous_const

theorem excess_le_abs {R : ℝ} (hR : 0 ≤ R) (t : ℝ) : excess R t ≤ |t| :=
  max_le (by linarith) (abs_nonneg t)

theorem abs_le_add_excess (R t : ℝ) : |t| ≤ R + excess R t := by
  unfold excess
  have := le_max_left (|t| - R) 0
  linarith

/-- `|t − clip_R t| = (|t| − R)⁺`. -/
theorem abs_sub_clipTo_eq_excess {R : ℝ} (hR : 0 ≤ R) (t : ℝ) :
    |t - clipTo R t| = excess R t := by
  unfold clipTo excess
  rcases le_or_gt t (-R) with h1 | h1
  · rw [min_eq_right (by linarith), max_eq_left (by linarith), abs_of_nonpos (by linarith),
      abs_of_nonpos (by linarith), max_eq_left (by linarith)]
    ring
  rcases le_or_gt R t with h2 | h2
  · rw [min_eq_left h2, max_eq_right (by linarith), abs_of_nonneg (by linarith),
      abs_of_nonneg (by linarith), max_eq_left (by linarith)]
  · rw [min_eq_right h2.le, max_eq_right h1.le, sub_self, abs_zero, max_eq_right]
    have := abs_le.2 ⟨h1.le, h2.le⟩
    linarith

/-- The excess is dominated by the tail integrand `|t| 1_{|t| > R}`. -/
theorem excess_le_tail {R : ℝ} (hR : 0 ≤ R) (t : ℝ) :
    excess R t ≤ |t| * ({t : ℝ | R < |t|}.indicator (fun _ => (1 : ℝ)) t) := by
  by_cases h : R < |t|
  · rw [Set.indicator_of_mem (show t ∈ {t : ℝ | R < |t|} from h), mul_one]
    exact excess_le_abs hR t
  · rw [Set.indicator_of_notMem (show t ∉ {t : ℝ | R < |t|} from h), mul_zero]
    unfold excess
    rw [max_eq_right (by push Not at h; linarith)]

/-- The clipped identity as a bounded continuous function. -/
noncomputable def clipBCF (R : ℝ) (hR : 0 ≤ R) : ℝ →ᵇ ℝ :=
  mkOfBound ⟨clipTo R, continuous_clipTo R⟩ (2 * R) fun x y => by
    change dist (clipTo R x) (clipTo R y) ≤ 2 * R
    rw [Real.dist_eq]
    have := abs_sub (clipTo R x) (clipTo R y)
    have := abs_clipTo_le hR x
    have := abs_clipTo_le hR y
    linarith

theorem clipBCF_apply (R : ℝ) (hR : 0 ≤ R) (t : ℝ) : clipBCF R hR t = clipTo R t := rfl

/-- The truncated excess `min((|t|−R)⁺, M)` as a bounded continuous function. -/
noncomputable def excessTruncBCF (R : ℝ) (M : ℕ) : ℝ →ᵇ ℝ :=
  mkOfBound ⟨fun t => min (excess R t) M, (continuous_excess R).min continuous_const⟩ M
    fun x y => by
      change dist (min (excess R x) M) (min (excess R y) M) ≤ M
      rw [Real.dist_eq, abs_sub_le_iff]
      constructor
      · linarith [min_le_right (excess R x) (M : ℝ), le_min (excess_nonneg R y) (Nat.cast_nonneg M)]
      · linarith [min_le_right (excess R y) (M : ℝ), le_min (excess_nonneg R x) (Nat.cast_nonneg M)]

theorem excessTruncBCF_apply (R : ℝ) (M : ℕ) (t : ℝ) :
    excessTruncBCF R M t = min (excess R t) M := rfl

/-! ### The law-level theorem -/

/-- Uniform integrability of a sequence of laws on `ℝ`: uniformly small tails of the first
moment. -/
def UniformIntegrableLaws (ν : ℕ → ProbabilityMeasure ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 ≤ R ∧ ∀ j,
    ∫ t, |t| * ({t : ℝ | R < |t|}.indicator (fun _ => (1 : ℝ)) t) ∂(ν j : Measure ℝ) ≤ ε

theorem integrable_excess_of_integrable_id {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : Integrable id ν) {R : ℝ} (hR : 0 ≤ R) : Integrable (excess R) ν :=
  Integrable.mono' hν.norm (continuous_excess R).measurable.aestronglyMeasurable
    (Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (excess_nonneg R t)]
      exact excess_le_abs hR t)

theorem integrable_tail_of_integrable_id {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : Integrable id ν) (R : ℝ) :
    Integrable (fun t : ℝ => |t| * ({t : ℝ | R < |t|}.indicator (fun _ => (1 : ℝ)) t)) ν := by
  refine Integrable.mono' hν.norm ?_ (Eventually.of_forall fun t => ?_)
  · exact (measurable_id.norm.mul (measurable_one.indicator
      (measurableSet_lt measurable_const measurable_id.norm))).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul, abs_abs]
    change |t| * _ ≤ |t|
    refine (mul_le_of_le_one_right (abs_nonneg t) ?_)
    by_cases ht : t ∈ {t : ℝ | R < |t|}
    · rw [Set.indicator_of_mem ht, abs_one]
    · rw [Set.indicator_of_notMem ht, abs_zero]
      exact zero_le_one

/-- Under uniform integrability the excess integrals are uniformly small. -/
theorem integral_excess_le_of_UI {ν : ℕ → ProbabilityMeasure ℝ}
    (hint : ∀ j, Integrable id (ν j : Measure ℝ)) {R ε : ℝ} (hR : 0 ≤ R)
    (hUI : ∀ j, ∫ t, |t| * ({t : ℝ | R < |t|}.indicator (fun _ => (1 : ℝ)) t) ∂(ν j : Measure ℝ)
      ≤ ε) (j : ℕ) : ∫ t, excess R t ∂(ν j : Measure ℝ) ≤ ε :=
  (integral_mono (integrable_excess_of_integrable_id (hint j) hR)
    (integrable_tail_of_integrable_id (hint j) R) (excess_le_tail hR)).trans (hUI j)

/-- The excess of the limit law is controlled: `∫ (|t|−R)⁺ dν ≤ ε`, and it is integrable
(monotone convergence through the bounded continuous truncations). -/
theorem excess_limit_bound {ν : ℕ → ProbabilityMeasure ℝ} {ν₀ : ProbabilityMeasure ℝ}
    (hν : Tendsto ν atTop (𝓝 ν₀)) (hint : ∀ j, Integrable id (ν j : Measure ℝ)) {R ε : ℝ}
    (hR : 0 ≤ R) (hε : 0 ≤ ε) (hexc : ∀ j, ∫ t, excess R t ∂(ν j : Measure ℝ) ≤ ε) :
    Integrable (excess R) (ν₀ : Measure ℝ) ∧ ∫ t, excess R t ∂(ν₀ : Measure ℝ) ≤ ε := by
  have hmin_int : ∀ (M : ℕ) (μ : Measure ℝ) [IsProbabilityMeasure μ],
      Integrable (fun t => min (excess R t) M) μ := fun M μ _ =>
    Integrable.of_bound
      ((continuous_excess R).min continuous_const).measurable.aestronglyMeasurable M
      (Eventually.of_forall fun t => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_min (excess_nonneg R t) (Nat.cast_nonneg M))]
        exact min_le_right _ _)
  have htrunc : ∀ M : ℕ, ∫ t, min (excess R t) M ∂(ν₀ : Measure ℝ) ≤ ε := fun M => by
    have h1 := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hν (excessTruncBCF R M)
    simp only [excessTruncBCF_apply] at h1
    refine le_of_tendsto h1 (Eventually.of_forall fun j => ?_)
    calc ∫ t, min (excess R t) M ∂(ν j : Measure ℝ) ≤ ∫ t, excess R t ∂(ν j : Measure ℝ) :=
          integral_mono (hmin_int M _) (integrable_excess_of_integrable_id (hint j) hR)
            fun t => min_le_left _ _
      _ ≤ ε := hexc j
  have hsup : ∀ t, (⨆ M : ℕ, ENNReal.ofReal (min (excess R t) M)) = ENNReal.ofReal (excess R t) :=
    fun t => by
      apply le_antisymm
      · exact iSup_le fun M => ENNReal.ofReal_le_ofReal (min_le_left _ _)
      · obtain ⟨M, hM⟩ := exists_nat_ge (excess R t)
        exact le_iSup_of_le M (by rw [min_eq_left hM])
  have hlin : ∫⁻ t, ENNReal.ofReal (excess R t) ∂(ν₀ : Measure ℝ) ≤ ENNReal.ofReal ε := by
    have hmeas : ∀ M : ℕ, Measurable fun t => ENNReal.ofReal (min (excess R t) M) := fun M =>
      ((continuous_excess R).min continuous_const).measurable.ennreal_ofReal
    have hmono : Monotone fun (M : ℕ) (t : ℝ) => ENNReal.ofReal (min (excess R t) M) :=
      fun M M' hMM' => Pi.le_def.2 fun t => by
        dsimp only
        exact ENNReal.ofReal_le_ofReal (min_le_min le_rfl (Nat.cast_le.2 hMM' : (M : ℝ) ≤ M'))
    calc ∫⁻ t, ENNReal.ofReal (excess R t) ∂(ν₀ : Measure ℝ)
        = ∫⁻ t, ⨆ M : ℕ, ENNReal.ofReal (min (excess R t) M) ∂(ν₀ : Measure ℝ) := by
          simp_rw [hsup]
      _ = ⨆ M : ℕ, ∫⁻ t, ENNReal.ofReal (min (excess R t) M) ∂(ν₀ : Measure ℝ) :=
          lintegral_iSup hmeas hmono
      _ ≤ ENNReal.ofReal ε := iSup_le fun M => by
          rw [← ofReal_integral_eq_lintegral_ofReal (hmin_int M _)
            (Eventually.of_forall fun t => le_min (excess_nonneg R t) (Nat.cast_nonneg M))]
          exact ENNReal.ofReal_le_ofReal (htrunc M)
  have hint₀ : Integrable (excess R) (ν₀ : Measure ℝ) :=
    ⟨(continuous_excess R).measurable.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (Eventually.of_forall (excess_nonneg R))).2
        (lt_of_le_of_lt hlin ENNReal.ofReal_lt_top)⟩
  refine ⟨hint₀, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall (excess_nonneg R))
    (continuous_excess R).measurable.aestronglyMeasurable]
  calc (∫⁻ t, ENNReal.ofReal (excess R t) ∂(ν₀ : Measure ℝ)).toReal
      ≤ (ENNReal.ofReal ε).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hlin
    _ = ε := ENNReal.toReal_ofReal hε

/-- **Expectations under law-level uniform integrability**: if `ν_j ⇒ ν₀` on `ℝ`, each `ν_j` has a
finite first moment, and the tails are uniformly small, then `ν₀` has a finite first moment and
`∫ t dν_j → ∫ t dν₀`. -/
theorem integrable_and_tendsto_integral_of_uniformIntegrable {ν : ℕ → ProbabilityMeasure ℝ}
    {ν₀ : ProbabilityMeasure ℝ} (hν : Tendsto ν atTop (𝓝 ν₀))
    (hint : ∀ j, Integrable id (ν j : Measure ℝ)) (hUI : UniformIntegrableLaws ν) :
    Integrable id (ν₀ : Measure ℝ) ∧
      Tendsto (fun j => ∫ t, t ∂(ν j : Measure ℝ)) atTop (𝓝 (∫ t, t ∂(ν₀ : Measure ℝ))) := by
  obtain ⟨R₁, hR₁, hUI₁⟩ := hUI 1 one_pos
  have hex₁ := excess_limit_bound hν hint hR₁ zero_le_one (integral_excess_le_of_UI hint hR₁ hUI₁)
  have hint₀ : Integrable id (ν₀ : Measure ℝ) :=
    Integrable.mono' ((integrable_const R₁).add hex₁.1) measurable_id.aestronglyMeasurable
      (Eventually.of_forall fun t => by
        rw [id, Real.norm_eq_abs]
        exact abs_le_add_excess R₁ t)
  refine ⟨hint₀, ?_⟩
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨R, hR, hUIR⟩ := hUI (ε / 4) (by positivity)
  have hexj := integral_excess_le_of_UI hint hR hUIR
  have hex₀ := excess_limit_bound hν hint hR (by positivity) hexj
  have hclip := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hν (clipBCF R hR)
  simp only [clipBCF_apply] at hclip
  have hcint : ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ], Integrable (clipTo R) μ := fun μ _ =>
    Integrable.of_bound (continuous_clipTo R).measurable.aestronglyMeasurable R
      (Eventually.of_forall fun t => by rw [Real.norm_eq_abs]; exact abs_clipTo_le hR t)
  have hdiff : ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ], Integrable id μ →
      ∫ t, excess R t ∂μ ≤ ε / 4 → |∫ t, t ∂μ - ∫ t, clipTo R t ∂μ| ≤ ε / 4 := fun μ _ hμ hμe => by
    have hμ' : Integrable (fun t : ℝ => t) μ := hμ
    rw [← integral_sub hμ' (hcint μ), ← Real.norm_eq_abs]
    refine (norm_integral_le_integral_norm _).trans ?_
    calc ∫ t, ‖t - clipTo R t‖ ∂μ = ∫ t, excess R t ∂μ :=
          integral_congr_ae (Eventually.of_forall fun t => by
            dsimp only
            rw [Real.norm_eq_abs, abs_sub_clipTo_eq_excess hR])
      _ ≤ ε / 4 := hμe
  filter_upwards [(Metric.tendsto_nhds.1 hclip) (ε / 4) (by positivity)] with j hj
  have h1 := hdiff (ν j : Measure ℝ) (hint j) (hexj j)
  have h3 := hdiff (ν₀ : Measure ℝ) hint₀ hex₀.2
  rw [Real.dist_eq] at hj ⊢
  calc |∫ t, t ∂(ν j : Measure ℝ) - ∫ t, t ∂(ν₀ : Measure ℝ)|
      ≤ |∫ t, t ∂(ν j : Measure ℝ) - ∫ t, clipTo R t ∂(ν j : Measure ℝ)| +
        |∫ t, clipTo R t ∂(ν j : Measure ℝ) - ∫ t, clipTo R t ∂(ν₀ : Measure ℝ)| +
        |∫ t, clipTo R t ∂(ν₀ : Measure ℝ) - ∫ t, t ∂(ν₀ : Measure ℝ)| := by
          have := abs_sub_le (∫ t, t ∂(ν j : Measure ℝ)) (∫ t, clipTo R t ∂(ν j : Measure ℝ))
            (∫ t, t ∂(ν₀ : Measure ℝ))
          have := abs_sub_le (∫ t, clipTo R t ∂(ν j : Measure ℝ))
            (∫ t, clipTo R t ∂(ν₀ : Measure ℝ)) (∫ t, t ∂(ν₀ : Measure ℝ))
          linarith
    _ < ε := by
        rw [abs_sub_comm (∫ t, t ∂(ν₀ : Measure ℝ)) (∫ t, clipTo R t ∂(ν₀ : Measure ℝ))] at h3
        linarith

/-! ### Application: expectations of random next-log statistics -/

/-- The second marginal of a graph law is the law of the map. -/
theorem graphLaw_map_snd {P : Type*} [TopologicalSpace P] [MeasurableSpace P] [BorelSpace P]
    (μ : ProbabilityMeasure P) {S : P → ℝ} (hS : Measurable S) :
    (graphLaw μ hS).map measurable_snd.aemeasurable = μ.map hS.aemeasurable := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [ProbabilityMeasure.toMeasure_map, graphLaw]
  rw [Measure.map_map measurable_snd (measurable_id.prodMk hS)]
  rfl

variable (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {β : ℝ} (hβ : 0 < β) (l : ℝ)
  (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
  (hm : 2 ≤ multCount (ratioExp h k) l) (Nseq : ℕ → ℝ) (hN1 : ∀ m, 1 < Nseq m)
  (hN : Tendsto Nseq atTop atTop)
  {μ : ℕ → ProbabilityMeasure (AdmissibleData n h k (β := β) l)}
  {μ₀ : ProbabilityMeasure (AdmissibleData n h k (β := β) l)} (hμ : Tendsto μ atTop (𝓝 μ₀))

include hk hβ hmin hatt hm hN1 hN hμ in
/-- **Expectation of the random next-log energy correction**: under uniform integrability of the
laws of the statistic, `E[log N_m (E_{Q_{N_m}(X_m)}[N_m K] − μ(X_m))] → E[c₂(X)]`. -/
theorem randomEnergyMean_expectation_tendsto
    (hint : ∀ m, Integrable (energyStatU n h k (β := β) l (Nseq m)) (μ m : Measure _))
    (hUI : UniformIntegrableLaws fun m => (μ m).map
      (measurable_energyStatU n h k hk hβ l (zero_le_one.trans (hN1 m).le)).aemeasurable) :
    Tendsto (fun m => ∫ x, energyStatU n h k (β := β) l (Nseq m) x ∂(μ m : Measure _)) atTop
      (𝓝 (∫ x, energyCorrection n h k (β := β) l x.1
        ∂(μ₀ : Measure (AdmissibleData n h k (β := β) l)))) := by
  have hlaw : Tendsto (fun m => (μ m).map
      (measurable_energyStatU n h k hk hβ l (zero_le_one.trans (hN1 m).le)).aemeasurable) atTop
      (𝓝 (μ₀.map (continuous_energyCorrectionU n h k hk hβ l).measurable.aemeasurable)) := by
    have := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _
      (randomEnergyMean_graphLaw_tendsto' n h k hk hβ l hmin hatt Nseq hN1 hN hm hμ)
      (continuous_snd (X := AdmissibleData n h k (β := β) l) (Y := ℝ))
    simpa only [graphLaw_map_snd] using this
  have hint' : ∀ m, Integrable id ((μ m).map
      (measurable_energyStatU n h k hk hβ l (zero_le_one.trans (hN1 m).le)).aemeasurable :
        Measure ℝ) := fun m => by
    rw [ProbabilityMeasure.toMeasure_map, integrable_map_measure measurable_id.aestronglyMeasurable
      (measurable_energyStatU n h k hk hβ l (zero_le_one.trans (hN1 m).le)).aemeasurable]
    exact hint m
  have := (integrable_and_tendsto_integral_of_uniformIntegrable hlaw hint' hUI).2
  have e0 : ∫ x, energyCorrection n h k (β := β) l x.1
      ∂(μ₀ : Measure (AdmissibleData n h k (β := β) l)) =
      ∫ t, t ∂((μ₀.map (continuous_energyCorrectionU n h k hk hβ l).measurable.aemeasurable :
        ProbabilityMeasure ℝ) : Measure ℝ) := by
    rw [ProbabilityMeasure.toMeasure_map, integral_map (f := fun t : ℝ => t)
      (continuous_energyCorrectionU n h k hk hβ l).measurable.aemeasurable
      measurable_id.aestronglyMeasurable]
  have e1 : ∀ m, ∫ x, energyStatU n h k (β := β) l (Nseq m) x
      ∂(μ m : Measure (AdmissibleData n h k (β := β) l)) =
      ∫ t, t ∂(((μ m).map (measurable_energyStatU n h k hk hβ l
        (zero_le_one.trans (hN1 m).le)).aemeasurable : ProbabilityMeasure ℝ) : Measure ℝ) :=
    fun m => by
      rw [ProbabilityMeasure.toMeasure_map, integral_map (f := fun t : ℝ => t)
        (measurable_energyStatU n h k hk hβ l (zero_le_one.trans (hN1 m).le)).aemeasurable
        measurable_id.aestronglyMeasurable]
  rw [e0]
  exact this.congr fun m => (e1 m).symm

include hk hβ hmin hatt hm hN1 hN hμ in
/-- **Expectation of the random next-log free-energy correction** under uniform integrability. -/
theorem randomFreeEnergy_expectation_tendsto
    (hint : ∀ m, Integrable (freeEnergyStatU n h k (β := β) l (Nseq m)) (μ m : Measure _))
    (hUI : UniformIntegrableLaws fun m => (μ m).map
      (measurable_freeEnergyStatU n h k hk hβ l (zero_le_one.trans (hN1 m).le)).aemeasurable) :
    Tendsto (fun m => ∫ x, freeEnergyStatU n h k (β := β) l (Nseq m) x ∂(μ m : Measure _)) atTop
      (𝓝 (∫ x, -(dataSecond n h k (β := β) l x.1 / dataLead n h k (β := β) l x.1)
        ∂(μ₀ : Measure (AdmissibleData n h k (β := β) l)))) := by
  have hlaw : Tendsto (fun m => (μ m).map
      (measurable_freeEnergyStatU n h k hk hβ l (zero_le_one.trans (hN1 m).le)).aemeasurable) atTop
      (𝓝 (μ₀.map (continuous_freeEnergyCorrectionU n h k hk hβ l).measurable.aemeasurable)) := by
    have := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _
      (randomFreeEnergy_graphLaw_tendsto n h k hk hβ l hmin hatt hm Nseq hN1 hN hμ)
      (continuous_snd (X := AdmissibleData n h k (β := β) l) (Y := ℝ))
    simpa only [graphLaw_map_snd] using this
  have hint' : ∀ m, Integrable id ((μ m).map
      (measurable_freeEnergyStatU n h k hk hβ l (zero_le_one.trans (hN1 m).le)).aemeasurable :
        Measure ℝ) := fun m => by
    rw [ProbabilityMeasure.toMeasure_map, integrable_map_measure measurable_id.aestronglyMeasurable
      (measurable_freeEnergyStatU n h k hk hβ l (zero_le_one.trans (hN1 m).le)).aemeasurable]
    exact hint m
  have := (integrable_and_tendsto_integral_of_uniformIntegrable hlaw hint' hUI).2
  have e0 : ∫ x, -(dataSecond n h k (β := β) l x.1 / dataLead n h k (β := β) l x.1)
      ∂(μ₀ : Measure (AdmissibleData n h k (β := β) l)) =
      ∫ t, t ∂((μ₀.map (continuous_freeEnergyCorrectionU n h k hk hβ l).measurable.aemeasurable :
        ProbabilityMeasure ℝ) : Measure ℝ) := by
    rw [ProbabilityMeasure.toMeasure_map, integral_map (f := fun t : ℝ => t)
      (continuous_freeEnergyCorrectionU n h k hk hβ l).measurable.aemeasurable
      measurable_id.aestronglyMeasurable]
  have e1 : ∀ m, ∫ x, freeEnergyStatU n h k (β := β) l (Nseq m) x
      ∂(μ m : Measure (AdmissibleData n h k (β := β) l)) =
      ∫ t, t ∂(((μ m).map (measurable_freeEnergyStatU n h k hk hβ l
        (zero_le_one.trans (hN1 m).le)).aemeasurable : ProbabilityMeasure ℝ) : Measure ℝ) :=
    fun m => by
      rw [ProbabilityMeasure.toMeasure_map, integral_map (f := fun t : ℝ => t)
        (measurable_freeEnergyStatU n h k hk hβ l (zero_le_one.trans (hN1 m).le)).aemeasurable
        measurable_id.aestronglyMeasurable]
  rw [e0]
  exact this.congr fun m => (e1 m).symm

end Grammar
