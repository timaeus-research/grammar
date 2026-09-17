/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.PosteriorResponseDet
import Grammar.CompactBaseStein

/-!
# Covariance interpolation for the averaged posterior mean on the compact base (§20)

For a centred Gaussian field `G` with kernel `𝒞` on the compact base `K`, the averaged limit
posterior mean of a continuous observable `f` differs from the zero-field mean `ρ(f)/ρ(K)` by the
integral of the **mean response** along the covariance scale:

★★★ `GaussianField.integral_compactAvg_eq`:
`E⟨f⟩_G = ρ(f)/ρ(K) + ∫₀¹ E[H_f(√s G)] ds`,

`H_f(g) = (β²/2)[(T_g(f c_Δ) − ⟨f⟩_g T_g(c_Δ)) − 2(B_g(𝒞 f) − ⟨f⟩_g B_g(𝒞))]`
(`compactMeanResponse`), with the radial-moment–weighted integrals
`T_g(φ) = ∫ φ S_{λ+1}(g) dρ / D_ρ(g)` (`compactTimeMoment`, `= ⟨φ t⟩_g`), the bilocal
`B_g(h) = ∫∫ h(x,y) S_{λ+1/2}(g x) S_{λ+1/2}(g y) dρ dρ / D_ρ(g)²` (`compactBilocal`,
`= ⟨h(x₁,x₂)√t₁√t₂⟩^{⊗2}_g`), the diagonal `c_Δ(x) = 𝒞(x,x)` and `(𝒞f)(x,y) = 𝒞(x,y) f(y)`.
In replica language
`H_f(g) = (β²/2) E^{⊗3}_{μ_g}[(f(x₁) − f(x₂))(t₁ 𝒞(x₁,x₁) − 2√t₁√t₃ 𝒞(x₁,x₃))]`: three replicas
(Astra #163).

Route: on a quantised base the identity is the finite-atom interpolation `integral_postAvg_eq`
(`GaussianField.integral_compactAvg_map_eq`); the passage to `ρ` is dominated convergence in
`ω` and in `s` with the uniform bound `|H_f(g)| ≤ 5β²‖f‖c(2λ/β + 1/4)(1 + ‖g‖²)`
(`abs_compactMeanResponse_le`, `c` a bound on the kernel), which uses only the field's second
moment.

Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

section Defs

variable {K : Type*} [MeasurableSpace K]

/-- `T_g(φ) = ∫ φ S_{λ+1}(g) dρ / D_ρ(g)`, the radial-first-moment–weighted integral `⟨φ t⟩_g`. -/
noncomputable def compactTimeMoment (β lam : ℝ) (ρ : Measure K) (g φ : K → ℝ) : ℝ :=
  compactWeighted β (lam + 1) ρ g φ / compactD β lam ρ g

/-- `B_g(h) = ∫∫ h(x,y) S_{λ+1/2}(g x) S_{λ+1/2}(g y) dρ dρ / D_ρ(g)²`, the bilocal
`⟨h(x₁,x₂)√t₁√t₂⟩^{⊗2}_g`. -/
noncomputable def compactBilocal (β lam : ℝ) (ρ : Measure K) (g : K → ℝ) (h : K × K → ℝ) : ℝ :=
  (∫ z, h z * fluctuation β (lam + 1 / 2) (g z.1) * fluctuation β (lam + 1 / 2) (g z.2)
    ∂(ρ.prod ρ)) / compactD β lam ρ g ^ 2

end Defs

section Kernel

variable {K : Type*} [TopologicalSpace K] (𝒞 : PSDKernel K)

/-- The diagonal `x ↦ 𝒞(x,x)` as a continuous map. -/
noncomputable def kernelDiag : C(K, ℝ) := ⟨fun x => 𝒞.C x x, 𝒞.continuous_diag⟩

/-- The kernel as a continuous map on `K × K`. -/
noncomputable def kernelFun : C(K × K, ℝ) := ⟨fun z => 𝒞.C z.1 z.2, 𝒞.continuous⟩

/-- `(x,y) ↦ 𝒞(x,y) f(y)` as a continuous map. -/
noncomputable def kernelObs (f : C(K, ℝ)) : C(K × K, ℝ) :=
  ⟨fun z => 𝒞.C z.1 z.2 * f z.2, 𝒞.continuous.mul (f.continuous.comp continuous_snd)⟩

theorem kernelDiag_apply (x : K) : kernelDiag 𝒞 x = 𝒞.C x x := rfl
theorem kernelFun_apply (z : K × K) : kernelFun 𝒞 z = 𝒞.C z.1 z.2 := rfl
theorem kernelObs_apply (f : C(K, ℝ)) (z : K × K) : kernelObs 𝒞 f z = 𝒞.C z.1 z.2 * f z.2 := rfl

/-- The kernel is bounded by its diagonal bound: `|𝒞(x,y)| ≤ c` when `𝒞(x,x) ≤ c`. -/
theorem PSDKernel.abs_le_of_diag_le {c : ℝ} (hc0 : 0 ≤ c) (hc : ∀ x, 𝒞.C x x ≤ c) (x y : K) :
    |𝒞.C x y| ≤ c := by
  have h1 := 𝒞.sq_le x y
  have h2 : 𝒞.C x x * 𝒞.C y y ≤ c * c :=
    mul_le_mul (hc x) (hc y) (𝒞.diag_nonneg y) hc0
  exact abs_le_of_sq_le_sq' (by nlinarith) hc0 |>.2 |> fun h => by
    have := abs_le_of_sq_le_sq' (by nlinarith : 𝒞.C x y ^ 2 ≤ c ^ 2) hc0
    exact abs_le.2 this

/-- The **mean response** of a continuous observable:
`H_f(g) = (β²/2)[(T_g(f c_Δ) − ⟨f⟩_g T_g(c_Δ)) − 2(B_g(𝒞f) − ⟨f⟩_g B_g(𝒞))]`. -/
noncomputable def compactMeanResponse [MeasurableSpace K] (β lam : ℝ) (ρ : Measure K)
    (𝒞 : PSDKernel K) (f : C(K, ℝ)) (g : K → ℝ) : ℝ :=
  β ^ 2 / 2 * ((compactTimeMoment β lam ρ g (f * kernelDiag 𝒞 : C(K, ℝ)) -
      compactAvg β lam ρ g f * compactTimeMoment β lam ρ g (kernelDiag 𝒞)) -
    2 * (compactBilocal β lam ρ g (kernelObs 𝒞 f) -
      compactAvg β lam ρ g f * compactBilocal β lam ρ g (kernelFun 𝒞)))

end Kernel

section Bounds

variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  {β lam : ℝ} (ρ : Measure K) [IsFiniteMeasure ρ] (hβ : 0 < β) (hlam : 0 < lam)
include hβ hlam

/-- `|T_g(φ)| ≤ ‖φ‖ M₂(g)`. -/
theorem abs_compactTimeMoment_le (hρ : ρ ≠ 0) (g : C(K, ℝ)) (φ : C(K, ℝ)) :
    |compactTimeMoment β lam ρ g φ| ≤ ‖φ‖ * compactM2 β lam ρ g := by
  have hD := compactD_pos ρ hβ hlam hρ g
  unfold compactTimeMoment compactWeighted compactM2
  rw [abs_div, abs_of_pos hD, mul_div_assoc', div_le_div_iff_of_pos_right hD]
  refine abs_integral_le_integral_abs.trans ?_
  rw [← integral_const_mul]
  refine integral_mono ((integrable_mul_fluctuation_comp ρ hβ (by linarith) g
    φ.continuous.measurable (C := ‖φ‖) fun x => by
      have := φ.norm_coe_le_norm x
      rwa [Real.norm_eq_abs] at this).abs)
    ((integrable_fluctuation_comp ρ hβ (by linarith) g).const_mul _) fun x => ?_
  have hS := fluctuation_pos β (lam + 1) (g x) hβ (by linarith)
  rw [abs_mul, abs_of_pos hS]
  refine mul_le_mul_of_nonneg_right ?_ hS.le
  have := φ.norm_coe_le_norm x
  rwa [Real.norm_eq_abs] at this

/-- The bilocal integrand is integrable on `ρ ⊗ ρ`. -/
theorem integrable_bilocal (g : C(K, ℝ)) (h : C(K × K, ℝ)) :
    Integrable (fun z : K × K => h z * fluctuation β (lam + 1 / 2) (g z.1) *
      fluctuation β (lam + 1 / 2) (g z.2)) (ρ.prod ρ) := by
  have hc : Continuous fun z : K × K => h z * fluctuation β (lam + 1 / 2) (g z.1) *
      fluctuation β (lam + 1 / 2) (g z.2) :=
    (h.continuous.mul ((continuous_fluctuation β (lam + 1 / 2) hβ (by linarith)).comp
      (g.continuous.comp continuous_fst))).mul
      ((continuous_fluctuation β (lam + 1 / 2) hβ (by linarith)).comp
        (g.continuous.comp continuous_snd))
  exact integrable_of_continuous_compactSpace (ρ.prod ρ) hc

/-- `|B_g(h)| ≤ ‖h‖ (√(2λ/β) + ‖g‖/2)²`. -/
theorem abs_compactBilocal_le (hρ : ρ ≠ 0) (g : C(K, ℝ)) (h : C(K × K, ℝ)) :
    |compactBilocal β lam ρ g h| ≤ ‖h‖ * (Real.sqrt (2 * lam / β) + ‖g‖ / 2) ^ 2 := by
  have hD := compactD_pos ρ hβ hlam hρ g
  have hB : 0 ≤ Real.sqrt (2 * lam / β) + ‖g‖ / 2 := by positivity
  -- pointwise: `S_{λ+1/2}(g x) ≤ (√(2λ/β) + ‖g‖/2) S_λ(g x)`
  have hpt : ∀ x, fluctuation β (lam + 1 / 2) (g x) ≤
      (Real.sqrt (2 * lam / β) + ‖g‖ / 2) * fluctuation β lam (g x) := by
    intro x
    refine (fluctuation_half_le hβ hlam (g x)).trans (mul_le_mul_of_nonneg_right ?_
      (fluctuation_pos β lam _ hβ hlam).le)
    refine (sqrt_le_sqrt_add (2 * lam / β) (max (g x) 0) (by positivity)).trans ?_
    have hgx : |g x| ≤ ‖g‖ := by
      have := g.norm_coe_le_norm x
      rwa [Real.norm_eq_abs] at this
    have : |max (g x) 0| ≤ ‖g‖ := by
      rw [abs_of_nonneg (le_max_right _ _)]
      exact max_le ((le_abs_self _).trans hgx) (norm_nonneg g)
    linarith
  unfold compactBilocal
  rw [abs_div, abs_of_pos (pow_pos hD 2), div_le_iff₀ (pow_pos hD 2)]
  refine abs_integral_le_integral_abs.trans ?_
  -- the product bound integrates to `‖h‖ (√ + ‖g‖/2)² D²`
  have hprod : ∫ z : K × K, ‖h‖ * (Real.sqrt (2 * lam / β) + ‖g‖ / 2) ^ 2 *
      (fluctuation β lam (g z.1) * fluctuation β lam (g z.2)) ∂(ρ.prod ρ) =
        ‖h‖ * (Real.sqrt (2 * lam / β) + ‖g‖ / 2) ^ 2 * compactD β lam ρ g ^ 2 := by
    rw [integral_const_mul, sq (compactD β lam ρ g)]
    unfold compactD
    rw [integral_prod_mul (f := fun x => fluctuation β lam (g x))
      (g := fun x => fluctuation β lam (g x))]
  rw [← hprod]
  refine integral_mono (integrable_bilocal ρ hβ hlam g h).abs
    ((MeasureTheory.Integrable.mul_prod (integrable_fluctuation_comp ρ hβ hlam g)
      (integrable_fluctuation_comp ρ hβ hlam g)).const_mul _) fun z => ?_
  have hS1 := fluctuation_pos β (lam + 1 / 2) (g z.1) hβ (by linarith)
  have hS2 := fluctuation_pos β (lam + 1 / 2) (g z.2) hβ (by linarith)
  have hL1 := fluctuation_pos β lam (g z.1) hβ hlam
  have hL2 := fluctuation_pos β lam (g z.2) hβ hlam
  have hhz : |h z| ≤ ‖h‖ := by
    have := h.norm_coe_le_norm z
    rwa [Real.norm_eq_abs] at this
  rw [abs_mul, abs_mul, abs_of_pos hS1, abs_of_pos hS2]
  calc |h z| * fluctuation β (lam + 1 / 2) (g z.1) * fluctuation β (lam + 1 / 2) (g z.2) ≤
        ‖h‖ * ((Real.sqrt (2 * lam / β) + ‖g‖ / 2) * fluctuation β lam (g z.1)) *
          ((Real.sqrt (2 * lam / β) + ‖g‖ / 2) * fluctuation β lam (g z.2)) := by
        refine mul_le_mul (mul_le_mul hhz (hpt z.1) hS1.le (norm_nonneg _)) (hpt z.2) hS2.le ?_
        exact mul_nonneg (norm_nonneg _) (mul_nonneg hB hL1.le)
    _ = ‖h‖ * (Real.sqrt (2 * lam / β) + ‖g‖ / 2) ^ 2 *
          (fluctuation β lam (g z.1) * fluctuation β lam (g z.2)) := by ring

/-- `√(2λ/β) + x/2 ≤ ...`: the quadratic envelope `(√(2λ/β) + x/2)² ≤ 2(2λ/β + x²/4)`. -/
theorem sq_sqrt_add_half_le (x : ℝ) :
    (Real.sqrt (2 * lam / β) + x / 2) ^ 2 ≤ 2 * (2 * lam / β + x ^ 2 / 4) := by
  have h := Real.sq_sqrt (div_nonneg (by linarith) hβ.le : (0 : ℝ) ≤ 2 * lam / β)
  nlinarith [sq_nonneg (Real.sqrt (2 * lam / β) - x / 2)]

/-- ★ **The mean response is quadratically dominated**:
`|H_f(g)| ≤ 5β² ‖f‖ c (2λ/β + 1/4)(1 + ‖g‖²)` when `𝒞(x,x) ≤ c`. -/
theorem abs_compactMeanResponse_le (hρ : ρ ≠ 0) (𝒞 : PSDKernel K) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ x, 𝒞.C x x ≤ c) (f : C(K, ℝ)) (g : C(K, ℝ)) :
    |compactMeanResponse β lam ρ 𝒞 f g| ≤
      5 * β ^ 2 * ‖f‖ * c * (2 * lam / β + 1 / 4) * (1 + ‖g‖ ^ 2) := by
  have hM2 := compactM2_le ρ hβ hlam g hρ (le_refl ‖g‖)
  have hM20 : 0 ≤ compactM2 β lam ρ g := by
    unfold compactM2
    exact div_nonneg (integral_nonneg fun x => (fluctuation_pos β (lam + 1) _ hβ (by linarith)).le)
      (compactD_pos ρ hβ hlam hρ g).le
  have hF := abs_compactAvg_le ρ hβ hlam hρ g f
  have hQ : 0 ≤ 2 * lam / β + ‖g‖ ^ 2 / 4 := by positivity
  have hQ' : 2 * lam / β + ‖g‖ ^ 2 / 4 ≤ (2 * lam / β + 1 / 4) * (1 + ‖g‖ ^ 2) := by
    nlinarith [sq_nonneg ‖g‖, div_nonneg (by linarith : (0:ℝ) ≤ 2 * lam) hβ.le]
  -- norms of the kernel maps
  have hdiag : ‖kernelDiag 𝒞‖ ≤ c := by
    refine (ContinuousMap.norm_le _ hc0).2 fun x => ?_
    rw [Real.norm_eq_abs, kernelDiag_apply, abs_of_nonneg (𝒞.diag_nonneg x)]
    exact hc x
  have hfdiag : ‖(f * kernelDiag 𝒞 : C(K, ℝ))‖ ≤ ‖f‖ * c := by
    refine (ContinuousMap.norm_le _ (by positivity)).2 fun x => ?_
    rw [ContinuousMap.mul_apply, Real.norm_eq_abs, abs_mul, kernelDiag_apply,
      abs_of_nonneg (𝒞.diag_nonneg x)]
    refine mul_le_mul ?_ (hc x) (𝒞.diag_nonneg x) (norm_nonneg _)
    have := f.norm_coe_le_norm x
    rwa [Real.norm_eq_abs] at this
  have hfun : ‖kernelFun 𝒞‖ ≤ c := by
    refine (ContinuousMap.norm_le _ hc0).2 fun z => ?_
    rw [Real.norm_eq_abs, kernelFun_apply]
    exact 𝒞.abs_le_of_diag_le hc0 hc _ _
  have hobs : ‖kernelObs 𝒞 f‖ ≤ c * ‖f‖ := by
    refine (ContinuousMap.norm_le _ (by positivity)).2 fun z => ?_
    rw [Real.norm_eq_abs, kernelObs_apply, abs_mul]
    refine mul_le_mul (𝒞.abs_le_of_diag_le hc0 hc _ _) ?_ (abs_nonneg _) hc0
    have := f.norm_coe_le_norm z.2
    rwa [Real.norm_eq_abs] at this
  -- the four terms
  have h1 := abs_compactTimeMoment_le ρ hβ hlam hρ g (f * kernelDiag 𝒞)
  have h2 := abs_compactTimeMoment_le ρ hβ hlam hρ g (kernelDiag 𝒞)
  have h3 := abs_compactBilocal_le ρ hβ hlam hρ g (kernelObs 𝒞 f)
  have h4 := abs_compactBilocal_le ρ hβ hlam hρ g (kernelFun 𝒞)
  have hsq := sq_sqrt_add_half_le hβ hlam ‖g‖
  have hsq0 : 0 ≤ (Real.sqrt (2 * lam / β) + ‖g‖ / 2) ^ 2 := sq_nonneg _
  have e1 : |compactTimeMoment β lam ρ g (f * kernelDiag 𝒞 : C(K, ℝ))| ≤
      ‖f‖ * c * compactM2 β lam ρ g := h1.trans (mul_le_mul_of_nonneg_right hfdiag hM20)
  have e2 : |compactAvg β lam ρ g f * compactTimeMoment β lam ρ g (kernelDiag 𝒞)| ≤
      ‖f‖ * c * compactM2 β lam ρ g := by
    rw [abs_mul]
    calc |compactAvg β lam ρ g f| * |compactTimeMoment β lam ρ g (kernelDiag 𝒞)| ≤
          ‖f‖ * (c * compactM2 β lam ρ g) :=
          mul_le_mul hF (h2.trans (mul_le_mul_of_nonneg_right hdiag hM20)) (abs_nonneg _)
            (norm_nonneg _)
      _ = ‖f‖ * c * compactM2 β lam ρ g := by ring
  have e3 : |compactBilocal β lam ρ g (kernelObs 𝒞 f)| ≤
      c * ‖f‖ * (2 * (2 * lam / β + ‖g‖ ^ 2 / 4)) :=
    h3.trans (mul_le_mul hobs hsq hsq0 (by positivity))
  have e4 : |compactAvg β lam ρ g f * compactBilocal β lam ρ g (kernelFun 𝒞)| ≤
      ‖f‖ * (c * (2 * (2 * lam / β + ‖g‖ ^ 2 / 4))) := by
    rw [abs_mul]
    exact mul_le_mul hF (h4.trans (mul_le_mul hfun hsq hsq0 hc0)) (abs_nonneg _) (norm_nonneg _)
  unfold compactMeanResponse
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < β ^ 2 / 2)]
  have hT : |compactTimeMoment β lam ρ g (f * kernelDiag 𝒞 : C(K, ℝ)) -
      compactAvg β lam ρ g f * compactTimeMoment β lam ρ g (kernelDiag 𝒞)| ≤
        2 * (‖f‖ * c * compactM2 β lam ρ g) := (abs_sub _ _).trans (by linarith)
  have hBt : |compactBilocal β lam ρ g (kernelObs 𝒞 f) -
      compactAvg β lam ρ g f * compactBilocal β lam ρ g (kernelFun 𝒞)| ≤
        2 * (c * ‖f‖ * (2 * (2 * lam / β + ‖g‖ ^ 2 / 4))) := (abs_sub _ _).trans (by linarith)
  have hall : |compactTimeMoment β lam ρ g (f * kernelDiag 𝒞 : C(K, ℝ)) -
      compactAvg β lam ρ g f * compactTimeMoment β lam ρ g (kernelDiag 𝒞) -
      2 * (compactBilocal β lam ρ g (kernelObs 𝒞 f) -
        compactAvg β lam ρ g f * compactBilocal β lam ρ g (kernelFun 𝒞))| ≤
      2 * (‖f‖ * c * compactM2 β lam ρ g) +
        2 * (2 * (c * ‖f‖ * (2 * (2 * lam / β + ‖g‖ ^ 2 / 4)))) := by
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_two]
    linarith
  refine (mul_le_mul_of_nonneg_left hall (by positivity)).trans ?_
  have hfc : 0 ≤ ‖f‖ * c := by positivity
  have hM2' : ‖f‖ * c * compactM2 β lam ρ g ≤ ‖f‖ * c * ((2 * lam / β + 1 / 4) * (1 + ‖g‖ ^ 2)) :=
    mul_le_mul_of_nonneg_left (hM2.trans hQ') hfc
  have hQ'' : c * ‖f‖ * (2 * (2 * lam / β + ‖g‖ ^ 2 / 4)) ≤
      c * ‖f‖ * (2 * ((2 * lam / β + 1 / 4) * (1 + ‖g‖ ^ 2))) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  nlinarith [hM2', hQ'', sq_nonneg β]

end Bounds

section Quantised

variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  {β lam : ℝ} (ρ : Measure K) [IsFiniteMeasure ρ] (hβ : 0 < β) (hlam : 0 < lam)
  (g : C(K, ℝ)) {q : K → K} (hq : Measurable q)
include hβ hlam hq

omit [CompactSpace K] [IsFiniteMeasure ρ] in
theorem compactTimeMoment_map (φ : C(K, ℝ)) :
    compactTimeMoment β lam (ρ.map q) g φ =
      (∫ x, φ (q x) * fluctuation β (lam + 1) (g (q x)) ∂ρ) / compactD β lam (ρ.map q) g := by
  unfold compactTimeMoment
  rw [compactWeighted_map ρ hβ g hq (lam + 1) (by linarith)]

theorem compactBilocal_map (h : C(K × K, ℝ)) :
    compactBilocal β lam (ρ.map q) g h =
      (∫ z : K × K, h (q z.1, q z.2) * fluctuation β (lam + 1 / 2) (g (q z.1)) *
        fluctuation β (lam + 1 / 2) (g (q z.2)) ∂(ρ.prod ρ)) / compactD β lam (ρ.map q) g ^ 2 := by
  unfold compactBilocal
  have hc : Continuous fun z : K × K => h z * fluctuation β (lam + 1 / 2) (g z.1) *
      fluctuation β (lam + 1 / 2) (g z.2) :=
    (h.continuous.mul ((continuous_fluctuation β (lam + 1 / 2) hβ (by linarith)).comp
      (g.continuous.comp continuous_fst))).mul
      ((continuous_fluctuation β (lam + 1 / 2) hβ (by linarith)).comp
        (g.continuous.comp continuous_snd))
  rw [Measure.map_prod_map _ _ hq hq, integral_map (hq.prodMap hq).aemeasurable
    hc.measurable.aestronglyMeasurable]
  rfl

variable (hfin : (Set.range q).Finite)
include hfin

theorem compactTimeMoment_map_eq (φ : C(K, ℝ)) :
    compactTimeMoment β lam (ρ.map q) g φ =
      ∑ i, φ (atomPt ρ hfin i) *
        quartetR β lam (atomWt ρ hfin) i (fun i => g (atomPt ρ hfin i)) := by
  rw [compactTimeMoment_map ρ hβ hlam g hq, integral_comp_finiteRange_atoms ρ hq hfin
    (fun x => φ x * fluctuation β (lam + 1) (g x)), compactD_map_eq ρ hβ hlam g hq hfin]
  unfold quartetR
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem compactBilocal_map_eq (h : C(K × K, ℝ)) :
    compactBilocal β lam (ρ.map q) g h =
      ∑ i, ∑ j, h (atomPt ρ hfin i, atomPt ρ hfin j) *
        quartetW β lam (atomWt ρ hfin) i (fun i => g (atomPt ρ hfin i)) *
        quartetW β lam (atomWt ρ hfin) j (fun i => g (atomPt ρ hfin i)) := by
  set F : K × K → ℝ := fun z => h z * fluctuation β (lam + 1 / 2) (g z.1) *
    fluctuation β (lam + 1 / 2) (g z.2) with hF
  have hFc : Continuous F :=
    (h.continuous.mul ((continuous_fluctuation β (lam + 1 / 2) hβ (by linarith)).comp
      (g.continuous.comp continuous_fst))).mul
      ((continuous_fluctuation β (lam + 1 / 2) hβ (by linarith)).comp
        (g.continuous.comp continuous_snd))
  set Fc : C(K × K, ℝ) := ⟨F, hFc⟩ with hFc'
  have hint : Integrable (fun z : K × K => F (q z.1, q z.2)) (ρ.prod ρ) :=
    Integrable.of_bound (hFc.measurable.comp
      (((hq.comp measurable_fst).prodMk (hq.comp measurable_snd)))).aestronglyMeasurable ‖Fc‖
      (Filter.Eventually.of_forall fun z => Fc.norm_coe_le_norm (q z.1, q z.2))
  rw [compactBilocal_map ρ hβ hlam g hq, compactD_map_eq ρ hβ hlam g hq hfin]
  have hnum : ∫ z : K × K, h (q z.1, q z.2) * fluctuation β (lam + 1 / 2) (g (q z.1)) *
      fluctuation β (lam + 1 / 2) (g (q z.2)) ∂(ρ.prod ρ) =
        ∑ i, ∑ j, atomWt ρ hfin i * atomWt ρ hfin j * F (atomPt ρ hfin i, atomPt ρ hfin j) := by
    change ∫ z : K × K, F (q z.1, q z.2) ∂(ρ.prod ρ) = _
    rw [integral_prod _ hint]
    have hin : ∀ x, ∫ y, F (q x, q y) ∂ρ = ∑ j, atomWt ρ hfin j * F (q x, atomPt ρ hfin j) :=
      fun x => integral_comp_finiteRange_atoms ρ hq hfin (fun b => F (q x, b))
    simp_rw [hin]
    have hout := integral_comp_finiteRange_atoms ρ hq hfin
      (fun a => ∑ j, atomWt ρ hfin j * F (a, atomPt ρ hfin j))
    beta_reduce at hout
    rw [hout]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hnum, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold quartetW quartetN
  simp only [hF]
  field_simp

/-- The quantised mean response is the finite-atom response with the kernel matrix. -/
theorem compactMeanResponse_map_eq (𝒞 : PSDKernel K) (f : C(K, ℝ)) :
    compactMeanResponse β lam (ρ.map q) 𝒞 f g =
      postResp β lam (atomWt ρ hfin) (fun i => f (atomPt ρ hfin i))
        (𝒞.kernelMatrix (atomPt ρ hfin)) (fun i => g (atomPt ρ hfin i)) := by
  unfold compactMeanResponse postResp
  rw [compactTimeMoment_map_eq ρ hβ hlam g hq hfin, compactTimeMoment_map_eq ρ hβ hlam g hq hfin,
    compactBilocal_map_eq ρ hβ hlam g hq hfin, compactBilocal_map_eq ρ hβ hlam g hq hfin,
    compactAvg_map_eq ρ hβ hlam g hq hfin]
  congr 1
  have hT : ∑ i, (f * kernelDiag 𝒞 : C(K, ℝ)) (atomPt ρ hfin i) *
      quartetR β lam (atomWt ρ hfin) i (fun i => g (atomPt ρ hfin i)) -
      postAvg β lam (atomWt ρ hfin) (fun i => f (atomPt ρ hfin i)) (fun i => g (atomPt ρ hfin i)) *
        ∑ i, kernelDiag 𝒞 (atomPt ρ hfin i) *
          quartetR β lam (atomWt ρ hfin) i (fun i => g (atomPt ρ hfin i)) =
      ∑ j, 𝒞.kernelMatrix (atomPt ρ hfin) j j *
        quartetR β lam (atomWt ρ hfin) j (fun i => g (atomPt ρ hfin i)) *
        (f (atomPt ρ hfin j) - postAvg β lam (atomWt ρ hfin) (fun i => f (atomPt ρ hfin i))
          (fun i => g (atomPt ρ hfin i))) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [ContinuousMap.mul_apply, kernelDiag_apply, PSDKernel.kernelMatrix, Matrix.of_apply]
    ring
  have hB : ∑ i, ∑ j, kernelObs 𝒞 f (atomPt ρ hfin i, atomPt ρ hfin j) *
      quartetW β lam (atomWt ρ hfin) i (fun i => g (atomPt ρ hfin i)) *
      quartetW β lam (atomWt ρ hfin) j (fun i => g (atomPt ρ hfin i)) -
      postAvg β lam (atomWt ρ hfin) (fun i => f (atomPt ρ hfin i)) (fun i => g (atomPt ρ hfin i)) *
        ∑ i, ∑ j, kernelFun 𝒞 (atomPt ρ hfin i, atomPt ρ hfin j) *
          quartetW β lam (atomWt ρ hfin) i (fun i => g (atomPt ρ hfin i)) *
          quartetW β lam (atomWt ρ hfin) j (fun i => g (atomPt ρ hfin i)) =
      ∑ i, ∑ j, 𝒞.kernelMatrix (atomPt ρ hfin) i j *
        quartetW β lam (atomWt ρ hfin) i (fun i => g (atomPt ρ hfin i)) *
        quartetW β lam (atomWt ρ hfin) j (fun i => g (atomPt ρ hfin i)) *
        (f (atomPt ρ hfin j) - postAvg β lam (atomWt ρ hfin) (fun i => f (atomPt ρ hfin i))
          (fun i => g (atomPt ρ hfin i))) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [kernelObs_apply, kernelFun_apply, PSDKernel.kernelMatrix, Matrix.of_apply]
    ring
  rw [hT, hB]

end Quantised

section Convergence

variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  {β lam : ℝ} (ρ : Measure K) [IsFiniteMeasure ρ] (hβ : 0 < β) (hlam : 0 < lam) (hρ : ρ ≠ 0)
  (g : C(K, ℝ)) {q : ℕ → K → K} (hq : ∀ n, Measurable (q n)) {ε : ℕ → ℝ}
  (hε : Tendsto ε atTop (𝓝 0)) (hqε : ∀ n x, dist x (q n x) < ε n)
include hβ hlam hρ hq hε hqε

theorem tendsto_compactTimeMoment_map (φ : C(K, ℝ)) :
    Tendsto (fun n => compactTimeMoment β lam (ρ.map (q n)) g φ) atTop
      (𝓝 (compactTimeMoment β lam ρ g φ)) := by
  simp_rw [compactTimeMoment_map ρ hβ hlam g (hq _)]
  exact (tendsto_integral_comp_quantise ρ (weightedFluctC hβ (lam + 1) (by linarith) φ g)
    hq hε hqε).div (tendsto_compactD_map ρ hβ hlam g hq hε hqε) (compactD_pos ρ hβ hlam hρ g).ne'

theorem tendsto_compactBilocal_map (h : C(K × K, ℝ)) :
    Tendsto (fun n => compactBilocal β lam (ρ.map (q n)) g h) atTop
      (𝓝 (compactBilocal β lam ρ g h)) := by
  simp_rw [compactBilocal_map ρ hβ hlam g (hq _)]
  have hFc : Continuous fun z : K × K => h z * fluctuation β (lam + 1 / 2) (g z.1) *
      fluctuation β (lam + 1 / 2) (g z.2) :=
    (h.continuous.mul ((continuous_fluctuation β (lam + 1 / 2) hβ (by linarith)).comp
      (g.continuous.comp continuous_fst))).mul
      ((continuous_fluctuation β (lam + 1 / 2) hβ (by linarith)).comp
        (g.continuous.comp continuous_snd))
  exact (tendsto_integral_prod_comp_quantise ρ ⟨_, hFc⟩ hq hε hqε).div
    ((tendsto_compactD_map ρ hβ hlam g hq hε hqε).pow 2) (pow_ne_zero 2
      (compactD_pos ρ hβ hlam hρ g).ne')

theorem tendsto_compactMeanResponse_map (𝒞 : PSDKernel K) (f : C(K, ℝ)) :
    Tendsto (fun n => compactMeanResponse β lam (ρ.map (q n)) 𝒞 f g) atTop
      (𝓝 (compactMeanResponse β lam ρ 𝒞 f g)) := by
  unfold compactMeanResponse
  refine tendsto_const_nhds.mul (Tendsto.sub (Tendsto.sub ?_ (Tendsto.mul ?_ ?_))
    (tendsto_const_nhds.mul (Tendsto.sub ?_ (Tendsto.mul ?_ ?_))))
  · exact tendsto_compactTimeMoment_map ρ hβ hlam hρ g hq hε hqε _
  · exact tendsto_compactAvg_map ρ hβ hlam g hρ f hq hε hqε
  · exact tendsto_compactTimeMoment_map ρ hβ hlam hρ g hq hε hqε _
  · exact tendsto_compactBilocal_map ρ hβ hlam hρ g hq hε hqε _
  · exact tendsto_compactAvg_map ρ hβ hlam g hρ f hq hε hqε
  · exact tendsto_compactBilocal_map ρ hβ hlam hρ g hq hε hqε _

end Convergence

namespace GaussianField

variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  {𝒞 : PSDKernel K} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (Γ : GaussianField 𝒞 P) {β lam : ℝ} (ρ : Measure K) [IsFiniteMeasure ρ] (hβ : 0 < β)
  (hlam : 0 < lam) (hρ : ρ ≠ 0)
include hβ hlam hρ

section Quantised

variable {q : K → K} (hq : Measurable q) (hfin : (Set.range q).Finite)
include hq hfin

omit [IsProbabilityMeasure P] in
theorem measurable_compactMeanResponse_map_smul (f : C(K, ℝ)) (s : ℝ) :
    Measurable fun ω =>
      compactMeanResponse β lam (ρ.map q) 𝒞 f (Real.sqrt s • Γ.G ω : C(K, ℝ)) := by
  have := nonempty_atoms ρ hq hfin hρ
  have hfun : (fun ω =>
      compactMeanResponse β lam (ρ.map q) 𝒞 f (Real.sqrt s • Γ.G ω : C(K, ℝ))) = fun ω =>
        postResp β lam (atomWt ρ hfin) (fun i => f (atomPt ρ hfin i))
          (𝒞.kernelMatrix (atomPt ρ hfin)) (Real.sqrt s • fun i => Γ.G ω (atomPt ρ hfin i)) :=
    funext fun ω => by
      rw [compactMeanResponse_map_eq ρ hβ hlam _ hq hfin 𝒞 f]
      rfl
  rw [hfun]
  exact ((continuous_postResp _ hβ hlam (atomWt_pos ρ hfin) _).comp
    ((continuous_const (y := Real.sqrt s)).smul (continuous_id (X := Fin _ → ℝ)))).measurable.comp
    (measurable_pi_lambda _ fun i => Γ.measurable_eval _)

omit [IsProbabilityMeasure P] in
/-- `E H^{(q)}_f(√s G)` is the finite `postInterpResp` of the law matrix. -/
theorem integral_compactMeanResponse_map_smul_eq {n : ℕ}
    (A : Matrix (Fin (posAtoms ρ hfin).card) (Fin (n + 1)) ℝ)
    (hAB : A * A.transpose = 𝒞.kernelMatrix (atomPt ρ hfin))
    (hA : P.map (fun ω => fun i => Γ.G ω (atomPt ρ hfin i)) = gaussianVector A) (f : C(K, ℝ))
    (s : ℝ) :
    ∫ ω, compactMeanResponse β lam (ρ.map q) 𝒞 f (Real.sqrt s • Γ.G ω : C(K, ℝ)) ∂P =
      postInterpResp β lam (atomWt ρ hfin) (fun i => f (atomPt ρ hfin i)) A s := by
  have := nonempty_atoms ρ hq hfin hρ
  have hw := atomWt_pos ρ hfin
  have hV : ∀ ω, compactMeanResponse β lam (ρ.map q) 𝒞 f (Real.sqrt s • Γ.G ω : C(K, ℝ)) =
      postResp β lam (atomWt ρ hfin) (fun i => f (atomPt ρ hfin i)) (A * A.transpose)
        (Real.sqrt s • fun i => Γ.G ω (atomPt ρ hfin i)) := by
    intro ω
    rw [compactMeanResponse_map_eq ρ hβ hlam (Real.sqrt s • Γ.G ω) hq hfin 𝒞 f, hAB]
    rfl
  simp_rw [hV]
  have hsm : Measurable fun v : Fin (posAtoms ρ hfin).card → ℝ =>
      postResp β lam (atomWt ρ hfin) (fun i => f (atomPt ρ hfin i)) (A * A.transpose)
        (Real.sqrt s • v) :=
    ((continuous_postResp _ hβ hlam hw (A * A.transpose)).comp
      ((continuous_const (y := Real.sqrt s)).smul (continuous_id (X := Fin _ → ℝ)))).measurable
  rw [Γ.integral_eval _ A hA hsm, integral_gaussianVector _ _ hsm]
  unfold postInterpResp
  rfl

omit [IsProbabilityMeasure P] in
theorem continuousOn_integral_compactMeanResponse_map_smul (f : C(K, ℝ)) :
    ContinuousOn (fun s => ∫ ω, compactMeanResponse β lam (ρ.map q) 𝒞 f
      (Real.sqrt s • Γ.G ω : C(K, ℝ)) ∂P) (Icc 0 1) := by
  have := nonempty_atoms ρ hq hfin hρ
  obtain ⟨n, A, hAB, hA⟩ := Γ.law _ (atomPt ρ hfin)
  simp_rw [Γ.integral_compactMeanResponse_map_smul_eq ρ hβ hlam hρ hq hfin A hAB hA f]
  exact continuousOn_postInterpResp _ A hβ hlam (atomWt_pos ρ hfin)

omit [IsProbabilityMeasure P] in
/-- **The interpolation identity on a quantised base**:
`E⟨f⟩_{ρ∘q⁻¹}(G) = ∫ f∘q dρ / ρ(K) + ∫₀¹ E H^{(q)}_f(√s G) ds`. -/
theorem integral_compactAvg_map_eq (f : C(K, ℝ)) :
    ∫ ω, compactAvg β lam (ρ.map q) (Γ.G ω) f ∂P =
      (∫ x, f (q x) ∂ρ) / ρ.real univ + ∫ s in (0 : ℝ)..1,
        ∫ ω, compactMeanResponse β lam (ρ.map q) 𝒞 f (Real.sqrt s • Γ.G ω : C(K, ℝ)) ∂P := by
  have := nonempty_atoms ρ hq hfin hρ
  obtain ⟨n, A, hAB, hA⟩ := Γ.law _ (atomPt ρ hfin)
  have hw := atomWt_pos ρ hfin
  simp_rw [compactAvg_map_eq ρ hβ hlam (Γ.G _) hq hfin f,
    Γ.integral_compactMeanResponse_map_smul_eq ρ hβ hlam hρ hq hfin A hAB hA f]
  rw [Γ.integral_eval _ A hA (continuous_postAvg hβ hlam hw _).measurable,
    integral_postAvg_eq _ A hβ hlam hw, integral_comp_finiteRange_atoms ρ hq hfin f,
    sum_atomWt ρ hq hfin]
  congr 2
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

end Quantised

section Limit

variable [Nonempty K]

/-- ★★★ **Covariance interpolation for the averaged posterior mean on the compact base**:
`E⟨f⟩_G = ρ(f)/ρ(K) + ∫₀¹ E[H_f(√s G)] ds` for every centred Gaussian field with kernel `𝒞`
and every continuous observable `f`. -/
theorem integral_compactAvg_eq (f : C(K, ℝ)) :
    ∫ ω, compactAvg β lam ρ (Γ.G ω) f ∂P =
      (∫ x, f x ∂ρ) / ρ.real univ + ∫ s in (0 : ℝ)..1,
        ∫ ω, compactMeanResponse β lam ρ 𝒞 f (Real.sqrt s • Γ.G ω : C(K, ℝ)) ∂P := by
  obtain ⟨q, hq, hfin, hqε⟩ := exists_quantisation_seq (K := K)
  have hε := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  obtain ⟨c, hc0, hc⟩ := 𝒞.exists_diag_bound
  -- the left side converges
  have hL : Tendsto (fun n => ∫ ω, compactAvg β lam (ρ.map (q n)) (Γ.G ω) f ∂P) atTop
      (𝓝 (∫ ω, compactAvg β lam ρ (Γ.G ω) f ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => ‖f‖)
      (fun n => (Γ.measurable_compactAvg_map_comp ρ hβ hlam hρ (hq n) (hfin n)
        f).aestronglyMeasurable)
      (integrable_const _) (fun n => Eventually.of_forall fun ω => ?_)
      (Eventually.of_forall fun ω => tendsto_compactAvg_map ρ hβ hlam (Γ.G ω) hρ f hq hε hqε)
    rw [Real.norm_eq_abs]
    exact abs_compactAvg_le (ρ.map (q n)) hβ hlam (map_quantise_ne_zero ρ (hq n) hρ) (Γ.G ω) f
  -- the zero-field term converges
  have h0 : Tendsto (fun n => (∫ x, f (q n x) ∂ρ) / ρ.real univ) atTop
      (𝓝 ((∫ x, f x ∂ρ) / ρ.real univ)) :=
    (tendsto_integral_comp_quantise ρ f hq hε hqε).div_const _
  -- the response term converges
  obtain ⟨Cb, hCb⟩ : ∃ Cb, Cb = 5 * β ^ 2 * ‖f‖ * c * (2 * lam / β + 1 / 4) := ⟨_, rfl⟩
  have hCb0 : 0 ≤ Cb := by rw [hCb]; positivity
  have hM2 : 0 ≤ ∫ ω, ‖Γ.G ω‖ ^ 2 ∂P := integral_nonneg fun ω => sq_nonneg _
  have hbnd : ∀ (ρ' : Measure K) [IsFiniteMeasure ρ'], ρ' ≠ 0 → ∀ (s : ℝ), s ≤ 1 → ∀ ω,
      |compactMeanResponse β lam ρ' 𝒞 f (Real.sqrt s • Γ.G ω : C(K, ℝ))| ≤
        Cb * (1 + ‖Γ.G ω‖ ^ 2) := by
    intro ρ' _ hρ' s hs ω
    refine (abs_compactMeanResponse_le ρ' hβ hlam hρ' 𝒞 hc0 hc f _).trans ?_
    rw [← hCb]
    refine mul_le_mul_of_nonneg_left ?_ hCb0
    have : ‖(Real.sqrt s • Γ.G ω : C(K, ℝ))‖ ≤ ‖Γ.G ω‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg s)]
      exact mul_le_of_le_one_left (norm_nonneg _) (Real.sqrt_le_one.2 hs)
    nlinarith [norm_nonneg (Real.sqrt s • Γ.G ω : C(K, ℝ)), norm_nonneg (Γ.G ω)]
  have hR : Tendsto (fun n => ∫ s in (0 : ℝ)..1, ∫ ω, compactMeanResponse β lam (ρ.map (q n)) 𝒞 f
      (Real.sqrt s • Γ.G ω : C(K, ℝ)) ∂P) atTop
      (𝓝 (∫ s in (0 : ℝ)..1, ∫ ω, compactMeanResponse β lam ρ 𝒞 f
        (Real.sqrt s • Γ.G ω : C(K, ℝ)) ∂P)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ => Cb * (1 + ∫ ω, ‖Γ.G ω‖ ^ 2 ∂P))
      (Eventually.of_forall fun n => ?_) (Eventually.of_forall fun n => ?_)
      intervalIntegrable_const (Eventually.of_forall fun s hs => ?_)
    · have hcont := Γ.continuousOn_integral_compactMeanResponse_map_smul ρ hβ hlam hρ (hq n)
        (hfin n) f
      have := hcont.aestronglyMeasurable (μ := volume) measurableSet_Icc
      exact this.mono_measure (Measure.restrict_mono
        (by rw [Set.uIoc_of_le zero_le_one]; exact Ioc_subset_Icc_self) le_rfl)
    · refine Eventually.of_forall fun s hs => ?_
      rw [Set.uIoc_of_le zero_le_one] at hs
      have hint : Integrable (fun ω => compactMeanResponse β lam (ρ.map (q n)) 𝒞 f
          (Real.sqrt s • Γ.G ω : C(K, ℝ))) P :=
        Integrable.mono' (integrable_const_mul_one_add_sq P Γ.G Γ.integrable_sq_norm Cb)
          (Γ.measurable_compactMeanResponse_map_smul ρ hβ hlam hρ (hq n) (hfin n) f
            s).aestronglyMeasurable
          (Eventually.of_forall fun ω => by
            rw [Real.norm_eq_abs]
            exact hbnd _ (map_quantise_ne_zero ρ (hq n) hρ) s hs.2 ω)
      rw [Real.norm_eq_abs]
      refine abs_integral_le_integral_abs.trans ?_
      calc ∫ ω, |compactMeanResponse β lam (ρ.map (q n)) 𝒞 f
            (Real.sqrt s • Γ.G ω : C(K, ℝ))| ∂P ≤ ∫ ω, Cb * (1 + ‖Γ.G ω‖ ^ 2) ∂P :=
            integral_mono hint.abs (integrable_const_mul_one_add_sq P Γ.G Γ.integrable_sq_norm Cb)
              fun ω => hbnd _ (map_quantise_ne_zero ρ (hq n) hρ) s hs.2 ω
        _ = Cb * (1 + ∫ ω, ‖Γ.G ω‖ ^ 2 ∂P) := by
            rw [integral_const_mul, integral_add (integrable_const _) Γ.integrable_sq_norm,
              integral_const, probReal_univ, one_smul]
    · refine tendsto_integral_of_dominated_convergence (fun ω => Cb * (1 + ‖Γ.G ω‖ ^ 2))
        (fun n => (Γ.measurable_compactMeanResponse_map_smul ρ hβ hlam hρ (hq n) (hfin n) f
          s).aestronglyMeasurable)
        (integrable_const_mul_one_add_sq P Γ.G Γ.integrable_sq_norm Cb)
        (fun n => Eventually.of_forall fun ω => ?_)
        (Eventually.of_forall fun ω => tendsto_compactMeanResponse_map ρ hβ hlam hρ
          (Real.sqrt s • Γ.G ω) hq hε hqε 𝒞 f)
      rw [Real.norm_eq_abs]
      rw [Set.uIoc_of_le zero_le_one] at hs
      exact hbnd _ (map_quantise_ne_zero ρ (hq n) hρ) s hs.2 ω
  refine tendsto_nhds_unique hL ?_
  refine (h0.add hR).congr fun n => ?_
  exact (Γ.integral_compactAvg_map_eq ρ hβ hlam hρ (hq n) (hfin n) f).symm

end Limit

end GaussianField

end Grammar
