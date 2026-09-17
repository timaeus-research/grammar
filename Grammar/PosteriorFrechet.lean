/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.GibbsJoint

/-!
# The Fréchet derivative of the posterior average on `C(K,ℝ)` (§20, Banach-form Stein)

The weighted functional `N_φ(g) = ∫ φ S_ν(g) dρ` (`weightedFunctional`) is Fréchet differentiable
on `C(K,ℝ)` with the sup norm, with derivative `h ↦ β ∫ φ S_{ν+1/2}(g) h dρ` (`weightedDeriv`,
★ `hasFDerivAt_weightedFunctional`): the pointwise mean value theorem for `S_ν` (derivative
`β S_{ν+1/2}`) and uniform continuity of `S_{ν+1/2}` on compact intervals give the little-o
uniformly in `x`.  By the quotient rule the posterior average `g ↦ ⟨f⟩_g = N_f(g)/D(g)` is Fréchet
differentiable with

★★ `hasFDerivAt_compactAvg`: `D⟨f⟩_g[h] = β(⟨f h√t⟩_g − ⟨f⟩_g ⟨h√t⟩_g)` (`posteriorDeriv`,
`posteriorDeriv_apply`),

and Stein's identity of `CompactBaseStein` takes its **Banach form**

★★★ `GaussianField.integral_eval_mul_compactAvg_fderiv`:
`E[G(x₀) F_f(G)] = E[DF_f(G)[𝒞(x₀,·)]]` for `F_f(g) = ⟨f⟩_g` (Astra #162 §5, #163 candidate V).

Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology Asymptotics

namespace Grammar

section Weighted

variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  (β ν : ℝ) (ρ : Measure K) [IsFiniteMeasure ρ]

/-- The weighted functional `N_φ(g) = ∫ φ S_ν(g) dρ` on `C(K,ℝ)`. -/
noncomputable def weightedFunctional (φ : C(K, ℝ)) (g : C(K, ℝ)) : ℝ :=
  ∫ x, φ x * fluctuation β ν (g x) ∂ρ

variable (hβ : 0 < β) (hν : 0 < ν)
include hβ hν

theorem integrable_weightedDeriv_integrand (φ g h : C(K, ℝ)) :
    Integrable (fun x => φ x * fluctuation β (ν + 1 / 2) (g x) * h x) ρ :=
  integrable_of_continuous_compactSpace ρ ((φ.continuous.mul
    ((continuous_fluctuation β (ν + 1 / 2) hβ (by linarith)).comp g.continuous)).mul h.continuous)

/-- The derivative `h ↦ β ∫ φ S_{ν+1/2}(g) h dρ` as a linear map. -/
noncomputable def weightedDerivLM (φ g : C(K, ℝ)) : C(K, ℝ) →ₗ[ℝ] ℝ where
  toFun h := β * ∫ x, φ x * fluctuation β (ν + 1 / 2) (g x) * h x ∂ρ
  map_add' h₁ h₂ := by
    have := integral_add (integrable_weightedDeriv_integrand β ν ρ hβ hν φ g h₁)
      (integrable_weightedDeriv_integrand β ν ρ hβ hν φ g h₂)
    simp only [ContinuousMap.add_apply, mul_add]
    rw [this]
    ring
  map_smul' c h := by
    simp only [ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply]
    have : (fun x => φ x * fluctuation β (ν + 1 / 2) (g x) * (c * h x)) =
        fun x => c * (φ x * fluctuation β (ν + 1 / 2) (g x) * h x) := by
      funext x; ring
    rw [this, integral_const_mul]
    ring

theorem weightedDerivLM_apply (φ g h : C(K, ℝ)) :
    weightedDerivLM β ν ρ hβ hν φ g h = β * ∫ x, φ x * fluctuation β (ν + 1 / 2) (g x) * h x ∂ρ :=
  rfl

/-- The uniform bound on `S_{ν+1/2}(g x)`. -/
noncomputable def fluctBound (g : C(K, ℝ)) : ℝ :=
  Real.exp (β * ‖g‖ ^ 2 / 2) * (β / 2) ^ (-(ν + 1 / 2)) * Real.Gamma (ν + 1 / 2)

omit [MeasurableSpace K] [BorelSpace K] in
theorem fluctuation_le_fluctBound (g : C(K, ℝ)) (x : K) :
    fluctuation β (ν + 1 / 2) (g x) ≤ fluctBound β ν g :=
  fluctuation_le_of_abs_le hβ (by linarith) (abs_coe_le_norm g x)

omit [MeasurableSpace K] [BorelSpace K] in
theorem fluctBound_nonneg (g : C(K, ℝ)) : 0 ≤ fluctBound β ν g := by
  unfold fluctBound
  have := Real.Gamma_pos_of_pos (by linarith : (0 : ℝ) < ν + 1 / 2)
  positivity

/-- The derivative as a continuous linear map. -/
noncomputable def weightedDeriv (φ g : C(K, ℝ)) : C(K, ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous (weightedDerivLM β ν ρ hβ hν φ g)
    (β * (‖φ‖ * fluctBound β ν g * ρ.real univ)) fun h => by
    rw [weightedDerivLM_apply, Real.norm_eq_abs, abs_mul, abs_of_pos hβ, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hβ.le
    have hb := norm_integral_le_of_norm_le_const (μ := ρ)
      (f := fun x => φ x * fluctuation β (ν + 1 / 2) (g x) * h x)
      (C := ‖φ‖ * fluctBound β ν g * ‖h‖) (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_mul, abs_mul,
          abs_of_pos (fluctuation_pos β _ _ hβ (by linarith))]
        exact mul_le_mul (mul_le_mul (abs_coe_le_norm φ x)
          (fluctuation_le_fluctBound β ν hβ hν g x)
          (fluctuation_pos β _ _ hβ (by linarith)).le (norm_nonneg _)) (abs_coe_le_norm h x)
          (abs_nonneg _) (mul_nonneg (norm_nonneg _) (fluctBound_nonneg β ν hβ hν g)))
    exact hb.trans (le_of_eq (by ring))

theorem weightedDeriv_apply (φ g h : C(K, ℝ)) :
    weightedDeriv β ν ρ hβ hν φ g h = β * ∫ x, φ x * fluctuation β (ν + 1 / 2) (g x) * h x ∂ρ :=
  rfl

/-- **Pointwise mean-value estimate**: for `|a| ≤ R` and `|u| ≤ δ(ε)`,
`|S_ν(a+u) − S_ν(a) − β S_{ν+1/2}(a) u| ≤ β ε |u|`, with `δ` from the uniform continuity of
`S_{ν+1/2}` on `[−(R+1), R+1]`. -/
theorem abs_fluctuation_sub_deriv_le (R : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ a, |a| ≤ R → ∀ u, |u| ≤ δ →
      |fluctuation β ν (a + u) - fluctuation β ν a - β * fluctuation β (ν + 1 / 2) a * u| ≤
        β * ε * |u| := by
  have hcont := (continuous_fluctuation β (ν + 1 / 2) hβ (by linarith)).continuousOn
    (s := Icc (-(R + 1)) (R + 1))
  obtain ⟨δ₀, hδ₀, hδ⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hcont) ε hε
  refine ⟨min (δ₀ / 2) 1, lt_min (by linarith) one_pos, fun a ha u hu => ?_⟩
  have hu1 : |u| ≤ 1 := hu.trans (min_le_right _ _)
  have huδ : |u| ≤ δ₀ / 2 := hu.trans (min_le_left _ _)
  have hderiv : ∀ v, HasDerivAt
      (fun v => fluctuation β ν (a + v) - β * fluctuation β (ν + 1 / 2) a * v)
      (β * fluctuation β (ν + 1 / 2) (a + v) - β * fluctuation β (ν + 1 / 2) a) v := by
    intro v
    have h1 : HasDerivAt (fun v => fluctuation β ν (a + v))
        (β * fluctuation β (ν + 1 / 2) (a + v)) v :=
      (hasDerivAt_fluctuation β ν hβ hν (a + v)).comp_const_add a v
    have h2 : HasDerivAt (fun v => β * fluctuation β (ν + 1 / 2) a * v)
        (β * fluctuation β (ν + 1 / 2) a) v := by
      simpa using (hasDerivAt_id v).const_mul (β * fluctuation β (ν + 1 / 2) a)
    exact h1.sub h2
  have hbound : ∀ v ∈ Icc (-|u|) |u|,
      ‖β * fluctuation β (ν + 1 / 2) (a + v) - β * fluctuation β (ν + 1 / 2) a‖ ≤ β * ε := by
    intro v hv
    have hv' : |v| ≤ |u| := abs_le.2 ⟨hv.1, hv.2⟩
    have hmem1 : a ∈ Icc (-(R + 1)) (R + 1) := by
      rw [mem_Icc]; constructor <;> linarith [abs_le.1 ha]
    have hmem2 : a + v ∈ Icc (-(R + 1)) (R + 1) := by
      rw [mem_Icc]; constructor <;> linarith [abs_le.1 ha, abs_le.1 (hv'.trans hu1)]
    have hdist : dist (a + v) a < δ₀ := by
      rw [Real.dist_eq, add_sub_cancel_left]
      linarith [hv'.trans huδ]
    have := hδ (a + v) hmem2 a hmem1 hdist
    rw [Real.dist_eq] at this
    rw [Real.norm_eq_abs, ← mul_sub, abs_mul, abs_of_pos hβ]
    exact mul_le_mul_of_nonneg_left this.le hβ.le
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun v _ => (hderiv v).hasDerivWithinAt) hbound (convex_Icc _ _)
    (mem_Icc.2 ⟨by linarith [abs_nonneg u], abs_nonneg u⟩ : (0 : ℝ) ∈ Icc (-|u|) |u|)
    (mem_Icc.2 ⟨neg_abs_le u, le_abs_self u⟩ : u ∈ Icc (-|u|) |u|)
  simp only [add_zero, mul_zero, sub_zero, Real.norm_eq_abs] at hmvt
  calc |fluctuation β ν (a + u) - fluctuation β ν a - β * fluctuation β (ν + 1 / 2) a * u| =
        |fluctuation β ν (a + u) - β * fluctuation β (ν + 1 / 2) a * u - fluctuation β ν a| := by
        ring_nf
    _ ≤ β * ε * |u| := hmvt

theorem integrable_weighted_integrand (φ g : C(K, ℝ)) :
    Integrable (fun x => φ x * fluctuation β ν (g x)) ρ :=
  integrable_of_continuous_compactSpace ρ (φ.continuous.mul
    ((continuous_fluctuation β ν hβ hν).comp g.continuous))

/-- ★ **The weighted functional is Fréchet differentiable on `C(K,ℝ)`**, with derivative
`h ↦ β ∫ φ S_{ν+1/2}(g) h dρ`. -/
theorem hasFDerivAt_weightedFunctional (φ g : C(K, ℝ)) :
    HasFDerivAt (weightedFunctional β ν ρ φ) (weightedDeriv β ν ρ hβ hν φ g) g := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  obtain ⟨M, hM⟩ : ∃ M, M = β * (‖φ‖ * ρ.real univ) + 1 := ⟨_, rfl⟩
  have hM0 : 0 < M := by rw [hM]; positivity
  obtain ⟨δ, hδ, hest⟩ := abs_fluctuation_sub_deriv_le β ν hβ hν ‖g‖
    (ε := c / M) (div_pos hc hM0)
  filter_upwards [Metric.ball_mem_nhds (0 : C(K, ℝ)) hδ] with h hh
  rw [Metric.mem_ball, dist_zero_right] at hh
  -- the difference as a single integral
  have hint₁ := integrable_weighted_integrand β ν ρ hβ hν φ (g + h)
  have hint₂ := integrable_weighted_integrand β ν ρ hβ hν φ g
  have hint₃ := (integrable_weightedDeriv_integrand β ν ρ hβ hν φ g h).const_mul β
  have hdiff : weightedFunctional β ν ρ φ (g + h) - weightedFunctional β ν ρ φ g -
      weightedDeriv β ν ρ hβ hν φ g h =
        ∫ x, φ x * (fluctuation β ν (g x + h x) - fluctuation β ν (g x) -
          β * fluctuation β (ν + 1 / 2) (g x) * h x) ∂ρ := by
    have h12 : Integrable (fun x => φ x * fluctuation β ν ((g + h) x) -
        φ x * fluctuation β ν (g x)) ρ := hint₁.sub hint₂
    unfold weightedFunctional
    rw [weightedDeriv_apply, ← integral_const_mul, ← integral_sub hint₁ hint₂,
      ← integral_sub h12 hint₃]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by
      simp only [ContinuousMap.add_apply]; ring)
  rw [hdiff]
  -- pointwise bound
  have hpt : ∀ x, ‖φ x * (fluctuation β ν (g x + h x) - fluctuation β ν (g x) -
      β * fluctuation β (ν + 1 / 2) (g x) * h x)‖ ≤ ‖φ‖ * (β * (c / M) * ‖h‖) := by
    intro x
    rw [Real.norm_eq_abs, abs_mul]
    refine mul_le_mul (abs_coe_le_norm φ x) ?_ (abs_nonneg _) (norm_nonneg _)
    refine (hest (g x) (abs_coe_le_norm g x) (h x) ((abs_coe_le_norm h x).trans hh.le)).trans ?_
    exact mul_le_mul_of_nonneg_left (abs_coe_le_norm h x) (by positivity)
  have hb := norm_integral_le_of_norm_le_const (μ := ρ) (Filter.Eventually.of_forall hpt)
  refine hb.trans ?_
  -- `‖φ‖ β (c/M) ‖h‖ ρ(K) ≤ c ‖h‖` since `β ‖φ‖ ρ(K) ≤ M`
  have hle : ‖φ‖ * β * ρ.real univ ≤ M := by
    rw [hM]
    nlinarith [norm_nonneg φ, measureReal_nonneg (μ := ρ) (s := univ)]
  calc ‖φ‖ * (β * (c / M) * ‖h‖) * ρ.real univ = (‖φ‖ * β * ρ.real univ) / M * (c * ‖h‖) := by
        field_simp
    _ ≤ 1 * (c * ‖h‖) := by
        refine mul_le_mul_of_nonneg_right ((div_le_one hM0).2 hle) (by positivity)
    _ = c * ‖h‖ := one_mul _

end Weighted

section Posterior

variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  {β lam : ℝ} (ρ : Measure K) [IsFiniteMeasure ρ] (hβ : 0 < β) (hlam : 0 < lam) (hρ : ρ ≠ 0)
include hβ hlam hρ

omit [CompactSpace K] [BorelSpace K] [IsFiniteMeasure ρ] hβ hlam hρ in
theorem compactWeighted_eq_weightedFunctional (φ g : C(K, ℝ)) :
    compactWeighted β lam ρ g φ = weightedFunctional β lam ρ φ g := rfl

omit [CompactSpace K] [BorelSpace K] [IsFiniteMeasure ρ] hβ hlam hρ in
theorem compactD_eq_weightedFunctional (g : C(K, ℝ)) :
    compactD β lam ρ g = weightedFunctional β lam ρ 1 g := by
  rw [← compactWeighted_one]; rfl

/-- The Fréchet derivative of `g ↦ ⟨f⟩_g` at `g`, as a continuous linear map:
`(1/D) N_f' − (N_f/D²) D'`. -/
noncomputable def posteriorDeriv (f g : C(K, ℝ)) : C(K, ℝ) →L[ℝ] ℝ :=
  (compactD β lam ρ g)⁻¹ • weightedDeriv β lam ρ hβ hlam f g -
    (compactWeighted β lam ρ g f / compactD β lam ρ g ^ 2) • weightedDeriv β lam ρ hβ hlam 1 g

/-- ★★ **The posterior average is Fréchet differentiable on `C(K,ℝ)`.** -/
theorem hasFDerivAt_compactAvg (f g : C(K, ℝ)) :
    HasFDerivAt (fun g : C(K, ℝ) => compactAvg β lam ρ g f) (posteriorDeriv ρ hβ hlam f g) g := by
  have hD := compactD_pos ρ hβ hlam hρ g
  have hN := hasFDerivAt_weightedFunctional β lam ρ hβ hlam f g
  have hDd := hasFDerivAt_weightedFunctional β lam ρ hβ hlam 1 g
  have hinv := (hasDerivAt_inv (compactD_eq_weightedFunctional ρ g ▸ hD).ne').comp_hasFDerivAt
    g hDd
  have h := hN.mul hinv
  have hfun : (fun g : C(K, ℝ) => compactAvg β lam ρ g f) =
      weightedFunctional β lam ρ f * ((fun y : ℝ => y⁻¹) ∘ weightedFunctional β lam ρ 1) := by
    funext g
    rw [Pi.mul_apply, Function.comp_apply, compactAvg, div_eq_mul_inv,
      compactD_eq_weightedFunctional ρ g]
    rfl
  rw [hfun]
  refine h.congr_fderiv ?_
  ext v
  simp only [add_apply, smul_apply, sub_apply, smul_eq_mul, posteriorDeriv, Function.comp_apply,
    neg_mul, compactWeighted_eq_weightedFunctional, compactD_eq_weightedFunctional ρ]
  have hDne : weightedFunctional β lam ρ 1 g ≠ 0 :=
    (compactD_eq_weightedFunctional ρ g ▸ hD).ne'
  field_simp
  ring

/-- `D⟨f⟩_g[h] = β(⟨f h√t⟩_g − ⟨f⟩_g ⟨h√t⟩_g)`. -/
theorem posteriorDeriv_apply (f g h : C(K, ℝ)) :
    posteriorDeriv ρ hβ hlam f g h =
      β * (compactSqrtTimeMoment β lam ρ g (f * h : C(K, ℝ)) -
        compactAvg β lam ρ g f * compactSqrtTimeMoment β lam ρ g h) := by
  have hD := compactD_pos ρ hβ hlam hρ g
  simp only [posteriorDeriv, sub_apply, smul_apply, smul_eq_mul, weightedDeriv_apply,
    compactSqrtTimeMoment, compactAvg, compactWeighted]
  have e1 : ∫ x, f x * fluctuation β (lam + 1 / 2) (g x) * h x ∂ρ =
      ∫ x, (f * h : C(K, ℝ)) x * fluctuation β (lam + 1 / 2) (g x) ∂ρ :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by
      simp only [ContinuousMap.mul_apply]; ring)
  have e2 : ∫ x, (1 : C(K, ℝ)) x * fluctuation β (lam + 1 / 2) (g x) * h x ∂ρ =
      ∫ x, h x * fluctuation β (lam + 1 / 2) (g x) ∂ρ :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by
      simp only [ContinuousMap.one_apply]; ring)
  rw [e1, e2]
  field_simp

end Posterior

section Banach

variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  {𝒞 : PSDKernel K} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (Γ : GaussianField 𝒞 P) {β lam : ℝ} (ρ : Measure K) [IsFiniteMeasure ρ] (hβ : 0 < β)
  (hlam : 0 < lam) (hρ : ρ ≠ 0) [Nonempty K]
include hβ hlam hρ

/-- ★★★ **Stein's identity in Banach form**: `E[G(x₀) F_f(G)] = E[DF_f(G)[𝒞(x₀,·)]]` for the
posterior average `F_f(g) = ⟨f⟩_g` on `C(K,ℝ)`. -/
theorem GaussianField.integral_eval_mul_compactAvg_fderiv (f : C(K, ℝ)) (x₀ : K) :
    ∫ ω, Γ.G ω x₀ * compactAvg β lam ρ (Γ.G ω) f ∂P =
      ∫ ω, posteriorDeriv ρ hβ hlam f (Γ.G ω) (GaussianField.kernelSection 𝒞 x₀) ∂P := by
  rw [Γ.integral_eval_mul_compactAvg ρ hβ hlam hρ f x₀, ← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall fun ω =>
    (posteriorDeriv_apply ρ hβ hlam hρ f (Γ.G ω) (GaussianField.kernelSection 𝒞 x₀)).symm)

end Banach

end Grammar
