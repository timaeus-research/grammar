/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.GaussianInsertion
import Grammar.GaussianQuartetDet
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# The Gaussian expectation of the fluctuation function, in one variable and in families

* `integral_mul_fluctuation_eq_of_measure`: Fubini for insertions against an arbitrary probability
  measure and an arbitrary real random variable `X` (the `gaussianVector` version is
  `integral_mul_fluctuation_eq`).
* `integral_fluctuation_gaussianReal'` ★★ (variance in `ℝ≥0`; the `toNNReal` form is
  `integral_fluctuation_gaussianReal` in `LeadingCoeffGaussianMoment`): for `G ~ N(0, v)`, `βv < 2`,
  `E S_λ(G) = Γ(λ) (β(1 − βv/2))^{−λ}`; at `β = 1` this is `Γ(λ)(1 − v/2)^{−λ}`.
* `integral_fluctuation_of_map_gaussianReal`: the same for a random variable whose law is
  `N(0, v)`.
* `integral_integral_fluctuation_of_gaussian_marginals` ★★: for a jointly measurable family
  `X(ω, z)` whose one-point laws are all `N(0, v)` and an integrable weight `a`,
  `E ∫ a(z) S_λ(X(ω, z)) dρ(z) = Γ(λ)(1 − v/2)^{−λ} ∫ a dρ` (Fubini; only the one-point law
  enters, no independence across `z`).

Zero `sorry`/`axiom`.
-/

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal

namespace Grammar

/-! ### Fubini for insertions against an arbitrary probability measure -/

variable {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsProbabilityMeasure ν]

/-- **Fubini for insertions, general measure.** If the tilted integrands `P e^{θX}` are
integrable, the absolute tilted moments are bounded by `M(θ)`, and `t ↦ K(t) M(β√t)` is integrable
on `(0, ∞)`, then `P · S_μ(X)` is integrable and `E[P S_μ(X)] = ∫₀^∞ K(t) E[P e^{β√t X}] dt`. -/
theorem integral_mul_fluctuation_eq_of_measure (β μ : ℝ) (X : α → ℝ) (hX : Measurable X)
    (P : α → ℝ) (hP : Measurable P) (M : ℝ → ℝ)
    (hint : ∀ θ, Integrable (fun a => P a * Real.exp (θ * X a)) ν)
    (hM : ∀ θ, ∫ a, |P a| * Real.exp (θ * X a) ∂ν ≤ M θ)
    (hK : IntegrableOn (fun t => radialKernel β μ t * M (β * Real.sqrt t)) (Ioi 0)) :
    Integrable (fun a => P a * fluctuation β μ (X a)) ν ∧
    ∫ a, P a * fluctuation β μ (X a) ∂ν =
      ∫ t in Ioi (0 : ℝ), radialKernel β μ t * ∫ a, P a * Real.exp (β * Real.sqrt t * X a) ∂ν := by
  have hmeas : Measurable (Function.uncurry fun (t : ℝ) (a : α) =>
      radialKernel β μ t * (P a * Real.exp (β * Real.sqrt t * X a))) := by
    change Measurable fun p : ℝ × α =>
      radialKernel β μ p.1 * (P p.2 * Real.exp (β * Real.sqrt p.1 * X p.2))
    exact ((measurable_radialKernel β μ).comp measurable_fst).mul
      ((hP.comp measurable_snd).mul (Measurable.exp ((measurable_const.mul measurable_fst.sqrt).mul
        (hX.comp measurable_snd))))
  have hpt : ∀ a : α, P a * fluctuation β μ (X a) =
      ∫ t in Ioi (0 : ℝ), radialKernel β μ t * (P a * Real.exp (β * Real.sqrt t * X a)) := by
    intro a
    rw [fluctuation_eq_integral_radialKernel, ← integral_const_mul]
    congr 1
    funext t
    ring
  have hf : Integrable (Function.uncurry fun (t : ℝ) (a : α) =>
      radialKernel β μ t * (P a * Real.exp (β * Real.sqrt t * X a)))
      ((volume.restrict (Ioi (0 : ℝ))).prod ν) := by
    refine (integrable_prod_iff hmeas.aestronglyMeasurable).2
      ⟨Filter.Eventually.of_forall fun t => ?_, ?_⟩
    · simp only [Function.uncurry_apply_pair]
      exact (hint (β * Real.sqrt t)).const_mul _
    · refine Integrable.mono' hK hmeas.aestronglyMeasurable.norm.integral_prod_right' ?_
      refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht => ?_)
      have hKn : 0 ≤ radialKernel β μ t := radialKernel_nonneg ht
      have hn : ∀ a : α,
          ‖radialKernel β μ t * (P a * Real.exp (β * Real.sqrt t * X a))‖ =
          radialKernel β μ t * (|P a| * Real.exp (β * Real.sqrt t * X a)) := fun a => by
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hKn, Real.abs_exp]
      simp only [Function.uncurry_apply_pair, hn]
      rw [integral_const_mul, Real.norm_of_nonneg (mul_nonneg hKn
        (integral_nonneg fun a => mul_nonneg (abs_nonneg _) (Real.exp_pos _).le))]
      exact mul_le_mul_of_nonneg_left (hM _) hKn
  refine ⟨?_, ?_⟩
  · have : (fun a : α => P a * fluctuation β μ (X a)) = fun a =>
        ∫ t in Ioi (0 : ℝ), radialKernel β μ t * (P a * Real.exp (β * Real.sqrt t * X a)) :=
      funext hpt
    rw [this]
    exact hf.integral_prod_right
  · simp_rw [hpt]
    rw [← integral_integral_swap hf]
    simp_rw [integral_const_mul]

/-! ### The scalar Gaussian -/

/-- `E e^{θ G} = e^{v θ²/2}` for `G ~ N(0, v)`. -/
theorem integral_exp_mul_gaussianReal_zero (v : ℝ≥0) (θ : ℝ) :
    ∫ x, Real.exp (θ * x) ∂gaussianReal 0 v = Real.exp (θ ^ 2 * (v : ℝ) / 2) := by
  have h := congrFun (mgf_fun_id_gaussianReal (μ := 0) (v := v)) θ
  simp only [zero_mul, zero_add] at h
  rw [show (∫ x, Real.exp (θ * x) ∂gaussianReal 0 v) = mgf (fun x => x) (gaussianReal 0 v) θ from
    rfl, h]
  congr 1
  ring

/-- ★★ **The Gaussian expectation of the fluctuation function**: for `G ~ N(0, v)` with
`βv < 2`, `S_μ(G)` is integrable and `E S_μ(G) = Γ(μ) (β(1 − βv/2))^{−μ}`. -/
theorem integral_fluctuation_gaussianReal' (β μ : ℝ) (hβ : 0 < β) (hμ : 0 < μ) (v : ℝ≥0)
    (hδ : 0 < 1 - β * (v : ℝ) / 2) :
    Integrable (fluctuation β μ) (gaussianReal 0 v) ∧
    ∫ x, fluctuation β μ x ∂gaussianReal 0 v =
      Real.Gamma μ * (β * (1 - β * (v : ℝ) / 2)) ^ (-μ) := by
  have h := integral_mul_fluctuation_eq_of_measure (gaussianReal 0 v) β μ (fun x => x)
    measurable_id (fun _ => 1) measurable_const
    (fun θ => θ ^ 0 * Real.exp (θ ^ 2 * (v : ℝ) / 2))
    (fun θ => by simpa using integrable_exp_mul_gaussianReal (μ := 0) (v := v) θ)
    (fun θ => by
      simp only [abs_one, one_mul, pow_zero]
      exact (integral_exp_mul_gaussianReal_zero v θ).le)
    (integrableOn_radialKernel_mul_tilt β μ (v : ℝ) 0 hβ hμ hδ)
  simp only [one_mul] at h
  refine ⟨h.1, h.2.trans ?_⟩
  simp_rw [integral_exp_mul_gaussianReal_zero]
  have := integral_radialKernel_mul_tilt β μ (v : ℝ) 0 hβ hμ hδ
  simp only [pow_zero, one_mul, Nat.cast_zero, zero_div, add_zero] at this
  exact this

/-- The Gaussian constant at unit temperature: `κ_μ(v) = Γ(μ)(1 − v/2)^{−μ}`. -/
noncomputable def gaussianFluctConst (μ : ℝ) (v : ℝ≥0) : ℝ :=
  Real.Gamma μ * (1 - (v : ℝ) / 2) ^ (-μ)

/-- `E S_μ(G) = κ_μ(v)` at `β = 1`. -/
theorem integral_fluctuation_gaussianReal_one (μ : ℝ) (hμ : 0 < μ) (v : ℝ≥0)
    (hv : (v : ℝ) < 2) :
    Integrable (fluctuation 1 μ) (gaussianReal 0 v) ∧
    ∫ x, fluctuation 1 μ x ∂gaussianReal 0 v = gaussianFluctConst μ v := by
  have h := integral_fluctuation_gaussianReal' 1 μ one_pos hμ v (by linarith)
  refine ⟨h.1, h.2.trans ?_⟩
  unfold gaussianFluctConst
  simp

/-- The fluctuation expectation of a random variable with law `N(0, v)`, `v < 2`. -/
theorem integral_fluctuation_of_map_gaussianReal {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} (hXm : AEMeasurable X P) {v : ℝ≥0} (hlaw : P.map X = gaussianReal 0 v)
    (μ : ℝ) (hμ : 0 < μ) (hv : (v : ℝ) < 2) :
    Integrable (fun ω => fluctuation 1 μ (X ω)) P ∧
    ∫ ω, fluctuation 1 μ (X ω) ∂P = gaussianFluctConst μ v := by
  have hc : Continuous (fluctuation 1 μ) := continuous_fluctuation 1 μ one_pos hμ
  have h := integral_fluctuation_gaussianReal_one μ hμ v hv
  rw [← hlaw] at h
  refine ⟨?_, ?_⟩
  · exact (integrable_map_measure hc.aestronglyMeasurable hXm).1 h.1
  · rw [← h.2, integral_map hXm hc.aestronglyMeasurable]

/-! ### Families with Gaussian one-point marginals -/

/-- ★★ **Fubini for a family with Gaussian one-point laws**: if `X(ω, z)` is jointly measurable
with `X(·, z) ~ N(0, v)` for every `z`, `v < 2`, and `a` is integrable, then
`a(z) S_μ(X(ω, z))` is integrable on the product and
`E ∫ a(z) S_μ(X(ω, z)) dρ(z) = κ_μ(v) ∫ a dρ`. No independence across `z` is used. -/
theorem integral_integral_fluctuation_of_gaussian_marginals {Ω Z : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Z] {P : Measure Ω} [IsProbabilityMeasure P] {ρ : Measure Z} [SFinite ρ]
    {a : Z → ℝ} (ha : Integrable a ρ) {X : Ω × Z → ℝ} (hX : Measurable X) {v : ℝ≥0}
    (hlaw : ∀ z, P.map (fun ω => X (ω, z)) = gaussianReal 0 v) (μ : ℝ) (hμ : 0 < μ)
    (hv : (v : ℝ) < 2) :
    Integrable (fun q : Ω × Z => a q.2 * fluctuation 1 μ (X q)) (P.prod ρ) ∧
    ∫ ω, ∫ z, a z * fluctuation 1 μ (X (ω, z)) ∂ρ ∂P =
      gaussianFluctConst μ v * ∫ z, a z ∂ρ := by
  have hc : Continuous (fluctuation 1 μ) := continuous_fluctuation 1 μ one_pos hμ
  have hone : ∀ z, Integrable (fun ω => fluctuation 1 μ (X (ω, z))) P ∧
      ∫ ω, fluctuation 1 μ (X (ω, z)) ∂P = gaussianFluctConst μ v := fun z =>
    integral_fluctuation_of_map_gaussianReal
      (hX.comp (measurable_id.prodMk measurable_const)).aemeasurable (hlaw z) μ hμ hv
  have hSnn : ∀ x, 0 ≤ fluctuation 1 μ x := fun x => (fluctuation_pos 1 μ x one_pos hμ).le
  have hmeas : AEStronglyMeasurable (fun q : Ω × Z => a q.2 * fluctuation 1 μ (X q))
      (P.prod ρ) :=
    ha.aestronglyMeasurable.comp_snd.mul (hc.measurable.comp hX).aestronglyMeasurable
  have hf : Integrable (fun q : Ω × Z => a q.2 * fluctuation 1 μ (X q)) (P.prod ρ) := by
    refine (integrable_prod_iff' hmeas).2 ⟨Filter.Eventually.of_forall fun z => ?_, ?_⟩
    · exact (hone z).1.const_mul (a z)
    · refine (ha.abs.mul_const (gaussianFluctConst μ v)).congr
        (Filter.Eventually.of_forall fun z => ?_)
      simp only
      have : ∀ ω, ‖a z * fluctuation 1 μ (X (ω, z))‖ = |a z| * fluctuation 1 μ (X (ω, z)) :=
        fun ω => by rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hSnn _)]
      simp_rw [this]
      rw [integral_const_mul, (hone z).2]
  refine ⟨hf, ?_⟩
  have hswap := integral_integral_swap (f := fun ω z => a z * fluctuation 1 μ (X (ω, z))) hf
  rw [hswap]
  have : ∀ z, ∫ ω, a z * fluctuation 1 μ (X (ω, z)) ∂P = a z * gaussianFluctConst μ v :=
    fun z => by rw [integral_const_mul, (hone z).2]
  simp_rw [this]
  rw [integral_mul_const, mul_comm]

end Grammar
