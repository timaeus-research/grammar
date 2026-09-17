/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.GibbsJoint

/-!
# The mean response as a three-replica expectation (§20, replicas)

With the joint Gibbs measure `μ_g` of `GibbsJoint`, the mean response of `CompactBaseResponse`,
`H_f(g) = (β²/2)[(T_g(fc_Δ) − ⟨f⟩_g T_g(c_Δ)) − 2(B_g(𝒞f) − ⟨f⟩_g B_g(𝒞))]`, is a genuine
expectation over three independent replicas of the limit posterior:

★★★ `compactMeanResponse_eq_replica`:
`H_f(g) = (β²/2) E^{⊗3}_{μ_g}[(f(x₁) − f(x₂))(t₁ 𝒞(x₁,x₁) − 2√t₁√t₃ 𝒞(x₁,x₃))]`,

so that the interpolation identity `GaussianField.integral_compactAvg_eq` reads
`E⟨f⟩_G − ρ(f)/ρ(K)
  = (β²/2)∫₀¹ E E^{⊗3}_{μ_{√sG}}[(f(x₁) − f(x₂))(t₁𝒞(x₁,x₁) − 2√t₁√t₃𝒞(x₁,x₃))] ds`
(compose `GaussianField.integral_compactAvg_eq` with this identity pointwise).  The replicas are
organised as
`z = ((x₂,t₂), ((x₁,t₁), (x₃,t₃)))` on `μ_g ⊗ (μ_g ⊗ μ_g)`, so that every term factorises into a
function of replica `2` and a function of the pair `(1,3)`.

Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

section Swap

variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  {β lam : ℝ} (ρ : Measure K) [IsFiniteMeasure ρ] (hβ : 0 < β) (hlam : 0 < lam) (g : C(K, ℝ))
include hβ hlam

/-- The bilocal bracket is symmetric under exchanging the two replicas. -/
theorem compactBilocal_swap (h : C(K × K, ℝ)) :
    compactBilocal β lam ρ g (fun z => h (z.2, z.1)) = compactBilocal β lam ρ g h := by
  unfold compactBilocal
  congr 1
  have hint := integrable_bilocal ρ hβ hlam g h
  rw [← integral_prod_swap]
  exact integral_congr_ae (Filter.Eventually.of_forall fun z => by simp only [Prod.swap]; ring)

end Swap

section Replica

variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  {β lam : ℝ} (ρ : Measure K) [IsFiniteMeasure ρ] (hβ : 0 < β) (hlam : 0 < lam) (hρ : ρ ≠ 0)
  (g : C(K, ℝ)) (𝒞 : PSDKernel K) (f : C(K, ℝ))
include hβ hlam hρ

/-- The pair integrand `√t₁√t₃ h(x₁,x₃)` is integrable on `μ_g ⊗ μ_g`. -/
theorem integrable_gibbsJoint_prod_sqrt (h : C(K × K, ℝ)) :
    Integrable (fun z : (K × ℝ) × (K × ℝ) =>
      h (z.1.1, z.2.1) * Real.sqrt z.1.2 * Real.sqrt z.2.2)
      ((gibbsJoint β lam ρ g).prod (gibbsJoint β lam ρ g)) := by
  have h1 : Integrable (fun z : K × ℝ => Real.sqrt z.2) (gibbsJoint β lam ρ g) := by
    have := integrable_gibbsJoint_sqrt ρ hβ hlam hρ g (φ := fun _ => (1 : ℝ)) measurable_const
      (M := 1) (fun _ => by simp)
    simpa only [one_mul] using this
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

/-- `(x,y) ↦ 𝒞(x,y) f(x)`, the transpose of `kernelObs`. -/
noncomputable def kernelObs' : C(K × K, ℝ) :=
  ⟨fun z => 𝒞.C z.1 z.2 * f z.1, 𝒞.continuous.mul (f.continuous.comp continuous_fst)⟩

omit [CompactSpace K] [MeasurableSpace K] [BorelSpace K] hβ hlam hρ in
theorem kernelObs'_apply (z : K × K) : kernelObs' 𝒞 f z = 𝒞.C z.1 z.2 * f z.1 := rfl

omit hρ in
/-- `B_g(𝒞(x,y)f(x)) = B_g(𝒞(x,y)f(y))` by symmetry of the kernel and of the replicas. -/
theorem compactBilocal_kernelObs' :
    compactBilocal β lam ρ g (kernelObs' 𝒞 f) = compactBilocal β lam ρ g (kernelObs 𝒞 f) := by
  rw [← compactBilocal_swap ρ hβ hlam g (kernelObs 𝒞 f)]
  congr 1
  funext z
  simp only [kernelObs'_apply, kernelObs_apply, 𝒞.symm z.1 z.2]

/-- ★★★ **The mean response is a three-replica expectation**:
`H_f(g) = (β²/2) E^{⊗3}_{μ_g}[(f(x₁) − f(x₂))(t₁ 𝒞(x₁,x₁) − 2√t₁√t₃ 𝒞(x₁,x₃))]`, with the replicas
organised as `z = ((x₂,t₂), ((x₁,t₁), (x₃,t₃)))`. -/
theorem compactMeanResponse_eq_replica :
    compactMeanResponse β lam ρ 𝒞 f g = β ^ 2 / 2 *
      ∫ z, (f z.2.1.1 - f z.1.1) * (z.2.1.2 * 𝒞.C z.2.1.1 z.2.1.1 -
        2 * (Real.sqrt z.2.1.2 * Real.sqrt z.2.2.2 * 𝒞.C z.2.1.1 z.2.2.1))
        ∂(gibbsJoint β lam ρ g).prod ((gibbsJoint β lam ρ g).prod (gibbsJoint β lam ρ g)) := by
  have hprob : IsProbabilityMeasure (gibbsJoint β lam ρ g) :=
    isProbabilityMeasure_gibbsJoint ρ hβ hlam hρ g
  have hfin : IsFiniteMeasure (gibbsJoint β lam ρ g) := inferInstance
  have hsf : SFinite ((gibbsJoint β lam ρ g).prod (gibbsJoint β lam ρ g)) := inferInstance
  -- the four one- and two-replica factors
  have hA : Integrable (fun z : K × ℝ => (f * kernelDiag 𝒞 : C(K, ℝ)) z.1 * z.2)
      (gibbsJoint β lam ρ g) :=
    (integrable_and_integral_gibbsJoint_weight ρ hβ hlam hρ g (by linarith : (0 : ℝ) < lam + 1)
      (fun a t ht => fluctIntegrandFn_mul_self a t ht)
      (f * kernelDiag 𝒞 : C(K, ℝ)).continuous.measurable (abs_coe_le_norm _)).1
  have hAd : Integrable (fun z : K × ℝ => kernelDiag 𝒞 z.1 * z.2) (gibbsJoint β lam ρ g) :=
    (integrable_and_integral_gibbsJoint_weight ρ hβ hlam hρ g (by linarith : (0 : ℝ) < lam + 1)
      (fun a t ht => fluctIntegrandFn_mul_self a t ht)
      (kernelDiag 𝒞).continuous.measurable (abs_coe_le_norm _)).1
  have hf : Integrable (fun z : K × ℝ => f z.1) (gibbsJoint β lam ρ g) :=
    integrable_gibbsJoint_obs ρ hβ hlam hρ g f.continuous.measurable (abs_coe_le_norm f)
  have hone : Integrable (fun _ : K × ℝ => (1 : ℝ)) (gibbsJoint β lam ρ g) := integrable_const _
  have hB := integrable_gibbsJoint_prod_sqrt ρ hβ hlam hρ g (kernelObs' 𝒞 f)
  have hBk := integrable_gibbsJoint_prod_sqrt ρ hβ hlam hρ g (kernelFun 𝒞)
  -- split the integrand into four products `u(z₂) · v(z₁,z₃)`
  have hsplit : (fun z : (K × ℝ) × ((K × ℝ) × (K × ℝ)) =>
      (f z.2.1.1 - f z.1.1) * (z.2.1.2 * 𝒞.C z.2.1.1 z.2.1.1 -
        2 * (Real.sqrt z.2.1.2 * Real.sqrt z.2.2.2 * 𝒞.C z.2.1.1 z.2.2.1))) = fun z =>
      ((1 : ℝ) * ((f * kernelDiag 𝒞 : C(K, ℝ)) z.2.1.1 * z.2.1.2 * (1 : ℝ)) -
        f z.1.1 * (kernelDiag 𝒞 z.2.1.1 * z.2.1.2 * (1 : ℝ))) -
      2 * ((1 : ℝ) * (kernelObs' 𝒞 f (z.2.1.1, z.2.2.1) * Real.sqrt z.2.1.2 *
          Real.sqrt z.2.2.2) -
        f z.1.1 * (kernelFun 𝒞 (z.2.1.1, z.2.2.1) * Real.sqrt z.2.1.2 * Real.sqrt z.2.2.2)) := by
    funext z
    simp only [ContinuousMap.mul_apply, kernelDiag_apply, kernelObs'_apply, kernelFun_apply]
    ring
  -- integrability of the pieces on the triple product
  have i1 : Integrable (fun z : (K × ℝ) × ((K × ℝ) × (K × ℝ)) =>
      (1 : ℝ) * ((f * kernelDiag 𝒞 : C(K, ℝ)) z.2.1.1 * z.2.1.2 * (1 : ℝ)))
      ((gibbsJoint β lam ρ g).prod ((gibbsJoint β lam ρ g).prod (gibbsJoint β lam ρ g))) :=
    Integrable.mul_prod hone (Integrable.mul_prod hA hone)
  have i2 : Integrable (fun z : (K × ℝ) × ((K × ℝ) × (K × ℝ)) =>
      f z.1.1 * (kernelDiag 𝒞 z.2.1.1 * z.2.1.2 * (1 : ℝ)))
      ((gibbsJoint β lam ρ g).prod ((gibbsJoint β lam ρ g).prod (gibbsJoint β lam ρ g))) :=
    Integrable.mul_prod hf (Integrable.mul_prod hAd hone)
  have i3 : Integrable (fun z : (K × ℝ) × ((K × ℝ) × (K × ℝ)) =>
      (1 : ℝ) * (kernelObs' 𝒞 f (z.2.1.1, z.2.2.1) * Real.sqrt z.2.1.2 * Real.sqrt z.2.2.2))
      ((gibbsJoint β lam ρ g).prod ((gibbsJoint β lam ρ g).prod (gibbsJoint β lam ρ g))) :=
    Integrable.mul_prod hone hB
  have i4 : Integrable (fun z : (K × ℝ) × ((K × ℝ) × (K × ℝ)) =>
      f z.1.1 * (kernelFun 𝒞 (z.2.1.1, z.2.2.1) * Real.sqrt z.2.1.2 * Real.sqrt z.2.2.2))
      ((gibbsJoint β lam ρ g).prod ((gibbsJoint β lam ρ g).prod (gibbsJoint β lam ρ g))) :=
    Integrable.mul_prod hf hBk
  have i12 : Integrable (fun z : (K × ℝ) × ((K × ℝ) × (K × ℝ)) =>
      (1 : ℝ) * ((f * kernelDiag 𝒞 : C(K, ℝ)) z.2.1.1 * z.2.1.2 * (1 : ℝ)) -
        f z.1.1 * (kernelDiag 𝒞 z.2.1.1 * z.2.1.2 * (1 : ℝ)))
      ((gibbsJoint β lam ρ g).prod ((gibbsJoint β lam ρ g).prod (gibbsJoint β lam ρ g))) :=
    i1.sub i2
  have i34 : Integrable (fun z : (K × ℝ) × ((K × ℝ) × (K × ℝ)) =>
      2 * ((1 : ℝ) * (kernelObs' 𝒞 f (z.2.1.1, z.2.2.1) * Real.sqrt z.2.1.2 *
          Real.sqrt z.2.2.2) -
        f z.1.1 * (kernelFun 𝒞 (z.2.1.1, z.2.2.1) * Real.sqrt z.2.1.2 * Real.sqrt z.2.2.2)))
      ((gibbsJoint β lam ρ g).prod ((gibbsJoint β lam ρ g).prod (gibbsJoint β lam ρ g))) :=
    (i3.sub i4).const_mul 2
  -- the product integrals
  have e1 := integral_prod_mul (μ := gibbsJoint β lam ρ g)
    (ν := (gibbsJoint β lam ρ g).prod (gibbsJoint β lam ρ g)) (fun _ : K × ℝ => (1 : ℝ))
    (fun p : (K × ℝ) × (K × ℝ) => (f * kernelDiag 𝒞 : C(K, ℝ)) p.1.1 * p.1.2 * (1 : ℝ))
  have e1' := integral_prod_mul (μ := gibbsJoint β lam ρ g) (ν := gibbsJoint β lam ρ g)
    (fun p : K × ℝ => (f * kernelDiag 𝒞 : C(K, ℝ)) p.1 * p.2) (fun _ : K × ℝ => (1 : ℝ))
  have e2 := integral_prod_mul (μ := gibbsJoint β lam ρ g)
    (ν := (gibbsJoint β lam ρ g).prod (gibbsJoint β lam ρ g)) (fun p : K × ℝ => f p.1)
    (fun p : (K × ℝ) × (K × ℝ) => kernelDiag 𝒞 p.1.1 * p.1.2 * (1 : ℝ))
  have e2' := integral_prod_mul (μ := gibbsJoint β lam ρ g) (ν := gibbsJoint β lam ρ g)
    (fun p : K × ℝ => kernelDiag 𝒞 p.1 * p.2) (fun _ : K × ℝ => (1 : ℝ))
  have e3 := integral_prod_mul (μ := gibbsJoint β lam ρ g)
    (ν := (gibbsJoint β lam ρ g).prod (gibbsJoint β lam ρ g)) (fun _ : K × ℝ => (1 : ℝ))
    (fun p : (K × ℝ) × (K × ℝ) =>
      kernelObs' 𝒞 f (p.1.1, p.2.1) * Real.sqrt p.1.2 * Real.sqrt p.2.2)
  have e4 := integral_prod_mul (μ := gibbsJoint β lam ρ g)
    (ν := (gibbsJoint β lam ρ g).prod (gibbsJoint β lam ρ g)) (fun p : K × ℝ => f p.1)
    (fun p : (K × ℝ) × (K × ℝ) =>
      kernelFun 𝒞 (p.1.1, p.2.1) * Real.sqrt p.1.2 * Real.sqrt p.2.2)
  have e34 := integral_const_mul (μ := (gibbsJoint β lam ρ g).prod
    ((gibbsJoint β lam ρ g).prod (gibbsJoint β lam ρ g))) (2 : ℝ)
    (fun z : (K × ℝ) × ((K × ℝ) × (K × ℝ)) =>
      (1 : ℝ) * (kernelObs' 𝒞 f (z.2.1.1, z.2.2.1) * Real.sqrt z.2.1.2 * Real.sqrt z.2.2.2) -
        f z.1.1 * (kernelFun 𝒞 (z.2.1.1, z.2.2.1) * Real.sqrt z.2.1.2 * Real.sqrt z.2.2.2))
  rw [hsplit, integral_sub i12 i34, integral_sub i1 i2, e34, integral_sub i3 i4,
    e1, e2, e3, e4, e1', e2', integral_const, probReal_univ, one_smul,
    integral_gibbsJoint_radial ρ hβ hlam hρ g
      (f * kernelDiag 𝒞 : C(K, ℝ)).continuous.measurable (abs_coe_le_norm _),
    integral_gibbsJoint_radial ρ hβ hlam hρ g (kernelDiag 𝒞).continuous.measurable
      (abs_coe_le_norm _),
    integral_gibbsJoint_obs ρ hβ hlam hρ g f.continuous.measurable (abs_coe_le_norm f),
    integral_gibbsJoint_prod_sqrt ρ hβ hlam hρ g (kernelObs' 𝒞 f),
    integral_gibbsJoint_prod_sqrt ρ hβ hlam hρ g (kernelFun 𝒞),
    compactBilocal_kernelObs' ρ hβ hlam g 𝒞 f]
  unfold compactMeanResponse
  ring

end Replica

end Grammar
