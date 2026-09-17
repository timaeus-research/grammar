/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.CompactBaseResponse

/-!
# The joint Gibbs measure on the base and the radial line (§20, replicas)

The limit posterior of a continuous field `g` on the compact base `K` is the probability measure
`μ_g(dx dt) ∝ t^{λ−1} e^{−βt + βg(x)√t} dρ(x) dt` on `K × (0,∞)` (`gibbsJoint`, a `withDensity`
of `ρ ⊗ Lebesgue|_(0,∞)` — Astra #163 §4).  Its reductions identify the moment brackets used so
far with genuine expectations:

* `integral_gibbsJoint_obs`: `∫ φ(x) dμ_g = ⟨φ⟩_g` (`compactAvg`);
* `integral_gibbsJoint_sqrt`: `∫ φ(x)√t dμ_g = ⟨φ√t⟩_g` (`compactSqrtTimeMoment`);
* `integral_gibbsJoint_radial`: `∫ φ(x) t dμ_g = T_g(φ)` (`compactTimeMoment`);
* `integral_gibbsJoint_prod_sqrt`: `∫∫ h(x₁,x₂)√t₁√t₂ dμ_g dμ_g = B_g(h)` (`compactBilocal`),

for bounded measurable `φ` and continuous `h`.  With them the Stein identity of `CompactBaseStein`
takes its **two-replica form**

★★★ `GaussianField.integral_eval_mul_compactAvg_replica`:
`E[G(x₀)⟨f⟩_G] = β E ∬ f(x₁)(√t₁ 𝒞(x₀,x₁) − √t₂ 𝒞(x₀,x₂)) dμ_G(x₁,t₁) dμ_G(x₂,t₂)`.

Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

section Measure

variable {K : Type*} [MeasurableSpace K] (β lam : ℝ) (ρ : Measure K)

/-- The base measure `ρ ⊗ Lebesgue|_(0,∞)`. -/
noncomputable def gibbsBase : Measure (K × ℝ) := ρ.prod (volume.restrict (Ioi (0 : ℝ)))

/-- The normalised joint density `t^{λ−1} e^{−βt + βg(x)√t} / D_ρ(g)`. -/
noncomputable def gibbsDensity (g : K → ℝ) (z : K × ℝ) : ℝ :=
  fluctIntegrandFn β lam (g z.1) z.2 / compactD β lam ρ g

/-- The **joint Gibbs measure** `μ_g` on `K × ℝ` (supported on `t > 0`). -/
noncomputable def gibbsJoint (g : K → ℝ) : Measure (K × ℝ) :=
  (gibbsBase ρ).withDensity fun z => ENNReal.ofReal (gibbsDensity β lam ρ g z)

instance instSFiniteGibbsBase [IsFiniteMeasure ρ] : SFinite (gibbsBase ρ) := by
  unfold gibbsBase; infer_instance

/-- Almost every point of the base has `t > 0`. -/
theorem ae_pos_snd_gibbsBase [SFinite ρ] : ∀ᵐ z ∂gibbsBase ρ, 0 < z.2 := by
  rw [ae_iff]
  have hset : {z : K × ℝ | ¬ 0 < z.2} = univ ×ˢ Iic 0 := by
    ext z; simp [not_lt]
  unfold gibbsBase
  rw [hset, Measure.prod_prod, Measure.restrict_apply measurableSet_Iic, Set.Iic_inter_Ioi,
    Set.Ioc_self, measure_empty, mul_zero]

end Measure

section Norm

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- Continuous observables are bounded by their norm. -/
theorem abs_coe_le_norm (φ : C(X, ℝ)) (x : X) : |φ x| ≤ ‖φ‖ := by
  have := φ.norm_coe_le_norm x
  rwa [Real.norm_eq_abs] at this

end Norm

section Reduction

variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  {β lam : ℝ} (ρ : Measure K) [IsFiniteMeasure ρ] (hβ : 0 < β) (hlam : 0 < lam) (hρ : ρ ≠ 0)
  (g : C(K, ℝ))

omit [CompactSpace K] [BorelSpace K] [IsFiniteMeasure ρ] in
theorem measurable_fluctIntegrandFn_comp (hg : Measurable g) (ν : ℝ) :
    Measurable fun z : K × ℝ => fluctIntegrandFn β ν (g z.1) z.2 := by
  unfold fluctIntegrandFn
  refine (measurable_snd.pow_const _).mul (Real.continuous_exp.measurable.comp ?_)
  exact ((measurable_const.mul measurable_snd).add
    ((measurable_const.mul (hg.comp measurable_fst)).mul
      (Real.continuous_sqrt.measurable.comp measurable_snd)))

omit [CompactSpace K] [BorelSpace K] [IsFiniteMeasure ρ] in
theorem measurable_gibbsDensity (hg : Measurable g) :
    Measurable (gibbsDensity β lam ρ g) :=
  (measurable_fluctIntegrandFn_comp g hg lam).div_const _

include hβ hlam hρ

/-- The core reduction on the base: for a radial weight `w` with `q_λ · w = q_ν` on `t > 0`,
`∫ φ(x) (q_λ/D) w(t) d(ρ ⊗ dt) = ∫ φ S_ν(g) dρ / D`, together with integrability. -/
theorem integrable_and_integral_gibbsBase_weight {ν : ℝ} (hν : 0 < ν) {w : ℝ → ℝ}
    (hw : ∀ a t, 0 < t → fluctIntegrandFn β lam a t * w t = fluctIntegrandFn β ν a t)
    {φ : K → ℝ} (hφm : Measurable φ) {M : ℝ} (hφb : ∀ x, |φ x| ≤ M) :
    Integrable (fun z : K × ℝ => φ z.1 * (gibbsDensity β lam ρ g z * w z.2)) (gibbsBase ρ) ∧
      ∫ z, φ z.1 * (gibbsDensity β lam ρ g z * w z.2) ∂gibbsBase ρ =
        compactWeighted β ν ρ g φ / compactD β lam ρ g := by
  have hD := compactD_pos ρ hβ hlam hρ g
  -- the integrand equals `φ(x) q_ν(g x, t) / D` a.e.
  have hae : (fun z : K × ℝ => φ z.1 * (gibbsDensity β lam ρ g z * w z.2)) =ᵐ[gibbsBase ρ]
      fun z => φ z.1 * (fluctIntegrandFn β ν (g z.1) z.2 / compactD β lam ρ g) := by
    filter_upwards [ae_pos_snd_gibbsBase ρ] with z hz
    unfold gibbsDensity
    rw [div_mul_eq_mul_div, hw _ _ hz]
  have hmeas : AEStronglyMeasurable
      (fun z : K × ℝ => φ z.1 * (fluctIntegrandFn β ν (g z.1) z.2 / compactD β lam ρ g))
      (gibbsBase ρ) :=
    ((hφm.comp measurable_fst).mul
      ((measurable_fluctIntegrandFn_comp g g.continuous.measurable ν).div_const _))
      |>.aestronglyMeasurable
  -- a uniform bound for the inner integrals
  obtain ⟨Sb, hSb⟩ : ∃ Sb, Sb = Real.exp (β * ‖g‖ ^ 2 / 2) * (β / 2) ^ (-ν) * Real.Gamma ν :=
    ⟨_, rfl⟩
  have hS : ∀ x, fluctuation β ν (g x) ≤ Sb := fun x => by
    rw [hSb]
    exact fluctuation_le_of_abs_le hβ hν (by
      have := g.norm_coe_le_norm x
      rwa [Real.norm_eq_abs] at this)
  have hinner : ∀ x, ∫ t in Ioi (0 : ℝ), φ x * (fluctIntegrandFn β ν (g x) t / compactD β lam ρ g) =
      φ x * (fluctuation β ν (g x) / compactD β lam ρ g) := by
    intro x
    rw [integral_const_mul, integral_div, fluctuation_eq_integral]
  have hinner_abs : ∀ x, ∫ t in Ioi (0 : ℝ),
      ‖φ x * (fluctIntegrandFn β ν (g x) t / compactD β lam ρ g)‖ =
        |φ x| * (fluctuation β ν (g x) / compactD β lam ρ g) := by
    intro x
    have : (fun t => ‖φ x * (fluctIntegrandFn β ν (g x) t / compactD β lam ρ g)‖)
        =ᵐ[volume.restrict (Ioi (0 : ℝ))]
          fun t => |φ x| * (fluctIntegrandFn β ν (g x) t / compactD β lam ρ g) := by
      rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioi]
      refine Filter.Eventually.of_forall fun t ht => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_div, abs_of_pos (fluctIntegrandFn_pos ht),
        abs_of_pos hD]
    rw [integral_congr_ae this, integral_const_mul, integral_div, fluctuation_eq_integral]
  have hint : Integrable
      (fun z : K × ℝ => φ z.1 * (fluctIntegrandFn β ν (g z.1) z.2 / compactD β lam ρ g))
      (gibbsBase ρ) := by
    unfold gibbsBase
    refine (integrable_prod_iff hmeas).2 ⟨Filter.Eventually.of_forall fun x => ?_, ?_⟩
    · have := ((integrableOn_fluctIntegrandFn hβ hν (g x)).div_const
        (compactD β lam ρ g)).const_mul (φ x)
      simpa using this
    · refine Integrable.of_bound hmeas.norm.integral_prod_right' (M * (Sb / compactD β lam ρ g))
        (Filter.Eventually.of_forall fun x => ?_)
      dsimp only
      rw [hinner_abs, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _)
        (div_nonneg (fluctuation_pos β ν _ hβ hν).le hD.le))]
      exact mul_le_mul (hφb x) (div_le_div_of_nonneg_right (hS x) hD.le)
        (div_nonneg (fluctuation_pos β ν _ hβ hν).le hD.le) ((abs_nonneg _).trans (hφb x))
  refine ⟨(integrable_congr hae).2 hint, ?_⟩
  rw [integral_congr_ae hae]
  unfold gibbsBase at hint ⊢
  rw [integral_prod _ hint]
  simp_rw [hinner]
  unfold compactWeighted
  rw [← integral_div]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)

/-- `μ_g` is a probability measure. -/
theorem isProbabilityMeasure_gibbsJoint : IsProbabilityMeasure (gibbsJoint β lam ρ g) := by
  constructor
  unfold gibbsJoint
  rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
  have h := integrable_and_integral_gibbsBase_weight ρ hβ hlam hρ g hlam (w := fun _ => 1)
    (fun a t _ => mul_one _) (φ := fun _ => (1 : ℝ)) measurable_const
    (M := 1) (fun _ => by simp)
  simp only [one_mul, mul_one] at h
  obtain ⟨hint, heq⟩ := h
  rw [← ofReal_integral_eq_lintegral_ofReal hint ?_, heq, compactWeighted_one,
    div_self (compactD_pos ρ hβ hlam hρ g).ne', ENNReal.ofReal_one]
  filter_upwards [ae_pos_snd_gibbsBase ρ] with z hz
  exact div_nonneg (fluctIntegrandFn_pos hz).le (compactD_pos ρ hβ hlam hρ g).le

/-- The Bochner integral against `μ_g` of a weighted observable, and its integrability. -/
theorem integrable_and_integral_gibbsJoint_weight {ν : ℝ} (hν : 0 < ν) {w : ℝ → ℝ}
    (hw : ∀ a t, 0 < t → fluctIntegrandFn β lam a t * w t = fluctIntegrandFn β ν a t)
    {φ : K → ℝ} (hφm : Measurable φ) {M : ℝ} (hφb : ∀ x, |φ x| ≤ M) :
    Integrable (fun z : K × ℝ => φ z.1 * w z.2) (gibbsJoint β lam ρ g) ∧
      ∫ z, φ z.1 * w z.2 ∂gibbsJoint β lam ρ g =
        compactWeighted β ν ρ g φ / compactD β lam ρ g := by
  obtain ⟨hint, heq⟩ := integrable_and_integral_gibbsBase_weight ρ hβ hlam hρ g hν hw hφm hφb
  have hdm : Measurable fun z => ENNReal.ofReal (gibbsDensity β lam ρ g z) :=
    ENNReal.measurable_ofReal.comp (measurable_gibbsDensity ρ g g.continuous.measurable)
  have hd0 : ∀ᵐ z ∂gibbsBase ρ, 0 ≤ gibbsDensity β lam ρ g z := by
    filter_upwards [ae_pos_snd_gibbsBase ρ] with z hz
    exact div_nonneg (fluctIntegrandFn_pos hz).le (compactD_pos ρ hβ hlam hρ g).le
  have hsmul : (fun z : K × ℝ => (ENNReal.ofReal (gibbsDensity β lam ρ g z)).toReal •
      (φ z.1 * w z.2)) =ᵐ[gibbsBase ρ] fun z => φ z.1 * (gibbsDensity β lam ρ g z * w z.2) := by
    filter_upwards [hd0] with z hz
    rw [ENNReal.toReal_ofReal hz, smul_eq_mul]
    ring
  constructor
  · unfold gibbsJoint
    rw [integrable_withDensity_iff hdm (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine (integrable_congr ?_).2 hint
    filter_upwards [hd0] with z hz
    rw [ENNReal.toReal_ofReal hz]
    ring
  · unfold gibbsJoint
    rw [integral_withDensity_eq_integral_toReal_smul hdm
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top), integral_congr_ae hsmul, heq]

/-! ### The moment brackets as expectations -/

theorem integral_gibbsJoint_obs {φ : K → ℝ} (hφm : Measurable φ) {M : ℝ} (hφb : ∀ x, |φ x| ≤ M) :
    ∫ z, φ z.1 ∂gibbsJoint β lam ρ g = compactAvg β lam ρ g φ := by
  have h := (integrable_and_integral_gibbsJoint_weight ρ hβ hlam hρ g hlam (w := fun _ => 1)
    (fun a t _ => mul_one _) hφm hφb).2
  simpa only [mul_one, compactAvg] using h

theorem integrable_gibbsJoint_obs {φ : K → ℝ} (hφm : Measurable φ) {M : ℝ}
    (hφb : ∀ x, |φ x| ≤ M) : Integrable (fun z : K × ℝ => φ z.1) (gibbsJoint β lam ρ g) := by
  have h := (integrable_and_integral_gibbsJoint_weight ρ hβ hlam hρ g hlam (w := fun _ => 1)
    (fun a t _ => mul_one _) hφm hφb).1
  simpa only [mul_one] using h

theorem integral_gibbsJoint_sqrt {φ : K → ℝ} (hφm : Measurable φ) {M : ℝ}
    (hφb : ∀ x, |φ x| ≤ M) :
    ∫ z, φ z.1 * Real.sqrt z.2 ∂gibbsJoint β lam ρ g = compactSqrtTimeMoment β lam ρ g φ :=
  (integrable_and_integral_gibbsJoint_weight ρ hβ hlam hρ g (by linarith : (0 : ℝ) < lam + 1 / 2)
    (fun a t ht => fluctIntegrandFn_mul_sqrt a t ht) hφm hφb).2

theorem integrable_gibbsJoint_sqrt {φ : K → ℝ} (hφm : Measurable φ) {M : ℝ}
    (hφb : ∀ x, |φ x| ≤ M) :
    Integrable (fun z : K × ℝ => φ z.1 * Real.sqrt z.2) (gibbsJoint β lam ρ g) :=
  (integrable_and_integral_gibbsJoint_weight ρ hβ hlam hρ g (by linarith : (0 : ℝ) < lam + 1 / 2)
    (fun a t ht => fluctIntegrandFn_mul_sqrt a t ht) hφm hφb).1

theorem integral_gibbsJoint_radial {φ : K → ℝ} (hφm : Measurable φ) {M : ℝ}
    (hφb : ∀ x, |φ x| ≤ M) :
    ∫ z, φ z.1 * z.2 ∂gibbsJoint β lam ρ g = compactTimeMoment β lam ρ g φ :=
  (integrable_and_integral_gibbsJoint_weight ρ hβ hlam hρ g (by linarith : (0 : ℝ) < lam + 1)
    (fun a t ht => fluctIntegrandFn_mul_self a t ht) hφm hφb).2

/-- ★ **The bilocal bracket is a two-replica expectation**:
`∫∫ h(x₁,x₂)√t₁√t₂ dμ_g dμ_g = B_g(h)`. -/
theorem integral_gibbsJoint_prod_sqrt (h : C(K × K, ℝ)) :
    ∫ z, h (z.1.1, z.2.1) * Real.sqrt z.1.2 * Real.sqrt z.2.2
      ∂(gibbsJoint β lam ρ g).prod (gibbsJoint β lam ρ g) = compactBilocal β lam ρ g h := by
  have hD := compactD_pos ρ hβ hlam hρ g
  have hprob := isProbabilityMeasure_gibbsJoint ρ hβ hlam hρ g
  -- inner reduction for fixed `x₁`
  have hinner : ∀ x₁ : K, ∫ z₂ : K × ℝ, h (x₁, z₂.1) * Real.sqrt z₂.2 ∂gibbsJoint β lam ρ g =
      (∫ y, h (x₁, y) * fluctuation β (lam + 1 / 2) (g y) ∂ρ) / compactD β lam ρ g := by
    intro x₁
    rw [integral_gibbsJoint_sqrt ρ hβ hlam hρ g (φ := fun y => h (x₁, y))
      (h.continuous.comp (Continuous.prodMk_right x₁)).measurable (M := ‖h‖)
      (fun y => abs_coe_le_norm h (x₁, y))]
    rfl
  -- the parametric integral is measurable and bounded
  have hSb : ∀ y, fluctuation β (lam + 1 / 2) (g y) ≤
      Real.exp (β * ‖g‖ ^ 2 / 2) * (β / 2) ^ (-(lam + 1 / 2)) * Real.Gamma (lam + 1 / 2) :=
    fun y => fluctuation_le_of_abs_le hβ (by linarith) (abs_coe_le_norm g y)
  have hSpos : ∀ y, 0 < fluctuation β (lam + 1 / 2) (g y) :=
    fun y => fluctuation_pos β _ _ hβ (by linarith)
  set Sb := Real.exp (β * ‖g‖ ^ 2 / 2) * (β / 2) ^ (-(lam + 1 / 2)) * Real.Gamma (lam + 1 / 2)
  set ψ : K → ℝ := fun x₁ => (∫ y, h (x₁, y) * fluctuation β (lam + 1 / 2) (g y) ∂ρ) /
    compactD β lam ρ g with hψ
  have hψm : Measurable ψ := by
    refine Measurable.div_const ?_ _
    exact ((h.continuous.mul ((continuous_fluctuation β (lam + 1 / 2) hβ (by linarith)).comp
      (g.continuous.comp continuous_snd))).measurable.stronglyMeasurable.integral_prod_right'
      (ν := ρ)).measurable
  have hψb : ∀ x₁, |ψ x₁| ≤ ‖h‖ * (Sb * ρ.real univ) / compactD β lam ρ g := by
    intro x₁
    rw [hψ]
    dsimp only
    rw [abs_div, abs_of_pos hD]
    refine div_le_div_of_nonneg_right ?_ hD.le
    refine abs_integral_le_integral_abs.trans ?_
    calc ∫ y, |h (x₁, y) * fluctuation β (lam + 1 / 2) (g y)| ∂ρ ≤ ∫ y, ‖h‖ * Sb ∂ρ := by
          refine integral_mono ((integrable_mul_fluctuation_comp ρ hβ (by linarith) g
            (h.continuous.comp (Continuous.prodMk_right x₁)).measurable (C := ‖h‖)
            fun y => abs_coe_le_norm h (x₁, y)).abs) (integrable_const _) fun y => ?_
          rw [abs_mul, abs_of_pos (hSpos y)]
          exact mul_le_mul (abs_coe_le_norm h (x₁, y)) (hSb y) (hSpos y).le (norm_nonneg _)
      _ = ‖h‖ * (Sb * ρ.real univ) := by rw [integral_const, smul_eq_mul]; ring
  -- integrability on the product: the integrand is `√t₁ · (bounded · √t₂)`
  have h1 : Integrable (fun z : K × ℝ => Real.sqrt z.2) (gibbsJoint β lam ρ g) := by
    have := integrable_gibbsJoint_sqrt ρ hβ hlam hρ g (φ := fun _ => (1 : ℝ)) measurable_const
      (M := 1) (fun _ => by simp)
    simpa only [one_mul] using this
  have hint : Integrable (fun z : (K × ℝ) × (K × ℝ) =>
      h (z.1.1, z.2.1) * Real.sqrt z.1.2 * Real.sqrt z.2.2)
      ((gibbsJoint β lam ρ g).prod (gibbsJoint β lam ρ g)) := by
    refine ((Integrable.mul_prod h1 h1).const_mul ‖h‖).mono' ?_
      (Filter.Eventually.of_forall fun z => ?_)
    · exact (((h.continuous.comp ((continuous_fst.comp continuous_fst).prodMk
        (continuous_fst.comp continuous_snd))).measurable.mul
        (Real.continuous_sqrt.measurable.comp (measurable_snd.comp measurable_fst))).mul
        (Real.continuous_sqrt.measurable.comp (measurable_snd.comp measurable_snd)))
        |>.aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _),
        abs_of_nonneg (Real.sqrt_nonneg _)]
      have := abs_coe_le_norm h (z.1.1, z.2.1)
      have h0 : 0 ≤ Real.sqrt z.1.2 * Real.sqrt z.2.2 := by positivity
      nlinarith [Real.sqrt_nonneg z.1.2, Real.sqrt_nonneg z.2.2, abs_nonneg (h (z.1.1, z.2.1))]
  rw [integral_prod _ hint]
  have hin2 : ∀ z₁ : K × ℝ, ∫ z₂ : K × ℝ, h (z₁.1, z₂.1) * Real.sqrt z₁.2 * Real.sqrt z₂.2
      ∂gibbsJoint β lam ρ g = ψ z₁.1 * Real.sqrt z₁.2 := by
    intro z₁
    have : (fun z₂ : K × ℝ => h (z₁.1, z₂.1) * Real.sqrt z₁.2 * Real.sqrt z₂.2) =
        fun z₂ => Real.sqrt z₁.2 * (h (z₁.1, z₂.1) * Real.sqrt z₂.2) := by
      funext z₂; ring
    rw [this, integral_const_mul, hinner z₁.1, mul_comm]
  simp_rw [hin2]
  rw [integral_gibbsJoint_sqrt ρ hβ hlam hρ g hψm hψb]
  -- `⟨ψ√t⟩ = B_g(h)`
  unfold compactSqrtTimeMoment compactWeighted compactBilocal
  rw [integral_prod _ (integrable_bilocal ρ hβ hlam g h)]
  have hx : ∀ x, ψ x * fluctuation β (lam + 1 / 2) (g x) =
      (∫ y, h (x, y) * fluctuation β (lam + 1 / 2) (g x) * fluctuation β (lam + 1 / 2) (g y) ∂ρ) /
        compactD β lam ρ g := by
    intro x
    rw [hψ]
    dsimp only
    rw [div_mul_eq_mul_div, ← integral_mul_const]
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => by ring)
  simp_rw [hx]
  rw [integral_div, div_div, sq]

end Reduction

section Replica

variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  {𝒞 : PSDKernel K} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (Γ : GaussianField 𝒞 P) {β lam : ℝ} (ρ : Measure K) [IsFiniteMeasure ρ] (hβ : 0 < β)
  (hlam : 0 < lam) (hρ : ρ ≠ 0) [Nonempty K]
include hβ hlam hρ

omit [Nonempty K] in
/-- The Stein right-hand side as a two-replica integral, for a fixed field `g`:
`∬ f(x₁)(√t₁ 𝒞(x₀,x₁) − √t₂ 𝒞(x₀,x₂)) dμ_g dμ_g = ⟨f 𝒞(x₀,·)√t⟩_g − ⟨f⟩_g ⟨𝒞(x₀,·)√t⟩_g`. -/
theorem integral_gibbsJoint_prod_stein (g : C(K, ℝ)) (f : C(K, ℝ)) (x₀ : K) :
    ∫ z, f z.1.1 * (Real.sqrt z.1.2 * 𝒞.C x₀ z.1.1 - Real.sqrt z.2.2 * 𝒞.C x₀ z.2.1)
      ∂(gibbsJoint β lam ρ g).prod (gibbsJoint β lam ρ g) =
      compactSqrtTimeMoment β lam ρ g (f * GaussianField.kernelSection 𝒞 x₀ : C(K, ℝ)) -
        compactAvg β lam ρ g f *
          compactSqrtTimeMoment β lam ρ g (GaussianField.kernelSection 𝒞 x₀) := by
  have hprob := isProbabilityMeasure_gibbsJoint ρ hβ hlam hρ g
  set fc : C(K, ℝ) := f * GaussianField.kernelSection 𝒞 x₀ with hfc
  have hF₁ : Integrable (fun z : K × ℝ => fc z.1 * Real.sqrt z.2) (gibbsJoint β lam ρ g) :=
    integrable_gibbsJoint_sqrt ρ hβ hlam hρ g fc.continuous.measurable (abs_coe_le_norm fc)
  have hF₂ : Integrable (fun z : K × ℝ => f z.1) (gibbsJoint β lam ρ g) :=
    integrable_gibbsJoint_obs ρ hβ hlam hρ g f.continuous.measurable (abs_coe_le_norm f)
  have hG₂ : Integrable (fun z : K × ℝ => GaussianField.kernelSection 𝒞 x₀ z.1 * Real.sqrt z.2)
      (gibbsJoint β lam ρ g) :=
    integrable_gibbsJoint_sqrt ρ hβ hlam hρ g
      (GaussianField.kernelSection 𝒞 x₀).continuous.measurable (abs_coe_le_norm _)
  have hsplit : (fun z : (K × ℝ) × (K × ℝ) =>
      f z.1.1 * (Real.sqrt z.1.2 * 𝒞.C x₀ z.1.1 - Real.sqrt z.2.2 * 𝒞.C x₀ z.2.1)) = fun z =>
        (fc z.1.1 * Real.sqrt z.1.2) * (1 : ℝ) -
          f z.1.1 * (GaussianField.kernelSection 𝒞 x₀ z.2.1 * Real.sqrt z.2.2) := by
    funext z
    simp only [hfc, ContinuousMap.mul_apply, GaussianField.kernelSection_apply]
    ring
  have e1 := integral_prod_mul (μ := gibbsJoint β lam ρ g) (ν := gibbsJoint β lam ρ g)
    (fun p : K × ℝ => fc p.1 * Real.sqrt p.2) (fun _ : K × ℝ => (1 : ℝ))
  have e2 := integral_prod_mul (μ := gibbsJoint β lam ρ g) (ν := gibbsJoint β lam ρ g)
    (fun p : K × ℝ => f p.1)
    (fun p : K × ℝ => GaussianField.kernelSection 𝒞 x₀ p.1 * Real.sqrt p.2)
  rw [hsplit, integral_sub (Integrable.mul_prod hF₁ (integrable_const (1 : ℝ)))
    (Integrable.mul_prod hF₂ hG₂), e1, e2, integral_const, probReal_univ, one_smul, mul_one,
    integral_gibbsJoint_sqrt ρ hβ hlam hρ g fc.continuous.measurable (abs_coe_le_norm fc),
    integral_gibbsJoint_obs ρ hβ hlam hρ g f.continuous.measurable (abs_coe_le_norm f),
    integral_gibbsJoint_sqrt ρ hβ hlam hρ g
      (GaussianField.kernelSection 𝒞 x₀).continuous.measurable (abs_coe_le_norm _)]

/-- ★★★ **Stein's identity for posterior averages in two-replica form**:
`E[G(x₀)⟨f⟩_G] = β E ∬ f(x₁)(√t₁ 𝒞(x₀,x₁) − √t₂ 𝒞(x₀,x₂)) dμ_G dμ_G`. -/
theorem GaussianField.integral_eval_mul_compactAvg_replica (f : C(K, ℝ)) (x₀ : K) :
    ∫ ω, Γ.G ω x₀ * compactAvg β lam ρ (Γ.G ω) f ∂P =
      β * ∫ ω, ∫ z, f z.1.1 * (Real.sqrt z.1.2 * 𝒞.C x₀ z.1.1 - Real.sqrt z.2.2 * 𝒞.C x₀ z.2.1)
        ∂(gibbsJoint β lam ρ (Γ.G ω)).prod (gibbsJoint β lam ρ (Γ.G ω)) ∂P := by
  rw [Γ.integral_eval_mul_compactAvg ρ hβ hlam hρ f x₀]
  congr 1
  exact integral_congr_ae (Filter.Eventually.of_forall fun ω =>
    (integral_gibbsJoint_prod_stein ρ hβ hlam hρ (Γ.G ω) f x₀).symm)

end Replica

end Grammar
