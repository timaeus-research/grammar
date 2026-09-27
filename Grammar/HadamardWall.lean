/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.TieFormulaSmooth

/-!
# The wall decomposition of a smooth amplitude and the tie formula for arbitrary smooth `η`

Every `C²` function `η` on `ℝ²` decomposes along the two coordinate walls as

  `η(u, v) = η(0) + u g₁(u) + v g₂(v) + u v ρ(u, v)`  (★★ `hadamard_decomp`),

with the continuous wall profiles given by the integral representations

  `g₁(u) = ∫₀¹ ∂₁η(tu, 0) dt`,  `g₂(v) = ∫₀¹ ∂₂η(0, tv) dt`,  `ρ(u,v) = ∫₀¹∫₀¹ ∂₂∂₁η(tu, rv) dr dt`

(`hadG₁`, `hadG₂`, `hadRho`; Hadamard's lemma, proved by the fundamental theorem of calculus along
segments, `sub_eq_integral_fderiv`, applied twice, with continuity from the continuity of
parametric integrals over `[0,1]`).  Feeding the decomposition into
`chartPolarCoeff_tieAmp_half'` gives the tie formula for an ARBITRARY smooth amplitude on the
blow-up chart `h = (1,0)`, `k = (2,1)` (★★★ `chartPolarCoeff_smooth_half`):

  `C_{½,2}[η] = η(0)/8`,   `C_{½,1}[η] = −½ ∫₀¹ g₁ − ¼ ∫₀¹ g₂`,

where `g₁(u) = (η(u,0) − η(0,0))/u` for `u ≠ 0` (`hadG₁_eq_div`) — the paper's
`A_{½,1}[η] = ½∫₀¹(η(u,0)−η(0,0))/u du + ¼∫₀¹(η(0,v)−η(0,0))/v dv` up to the sign convention of
`polarPart` (examples_slop §4; Astra round-3 target 1).  Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology intervalIntegral
open scoped ContDiff

namespace Grammar

/-- The coordinate vectors of `ℝ²`. -/
def e₀ : Fin 2 → ℝ := Pi.single 0 1

def e₁ : Fin 2 → ℝ := Pi.single 1 1

@[simp] theorem e₀_zero : e₀ 0 = 1 := by simp [e₀]
@[simp] theorem e₀_one : e₀ 1 = 0 := by simp [e₀]
@[simp] theorem e₁_zero : e₁ 0 = 0 := by simp [e₁]
@[simp] theorem e₁_one : e₁ 1 = 1 := by simp [e₁]

theorem vec_eq (u : Fin 2 → ℝ) : u = u 0 • e₀ + u 1 • e₁ := by
  funext i
  fin_cases i <;> simp

theorem continuous_seg (x v : Fin 2 → ℝ) : Continuous fun t : ℝ => x + t • v := by fun_prop

/-- ★ **The fundamental theorem of calculus along a segment**: for `C¹` `f`,
`f(x + v) − f(x) = ∫₀¹ Df(x + t v)[v] dt`. -/
theorem sub_eq_integral_fderiv {f : (Fin 2 → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) (x v : Fin 2 → ℝ) :
    f (x + v) - f x = ∫ t in (0 : ℝ)..1, fderiv ℝ f (x + t • v) v := by
  have hγ : ∀ t : ℝ, HasDerivAt (fun t : ℝ => x + t • v) v t := fun t => by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  have hd : ∀ t ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => f (x + t • v)) (fderiv ℝ f (x + t • v) v) t := fun t _ =>
    (hf.differentiable one_ne_zero (x + t • v)).hasFDerivAt.comp_hasDerivAt t (hγ t)
  have hc : Continuous fun t : ℝ => fderiv ℝ f (x + t • v) v :=
    ((hf.continuous_fderiv one_ne_zero).comp (continuous_seg x v)).clm_apply continuous_const
  rw [integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable 0 1)]
  simp

/-- The partial derivatives `∂₁η`, `∂₂η` and the mixed derivative `∂₂∂₁η`. -/
noncomputable def d₁ (η : (Fin 2 → ℝ) → ℝ) (x : Fin 2 → ℝ) : ℝ := fderiv ℝ η x e₀

noncomputable def d₂ (η : (Fin 2 → ℝ) → ℝ) (x : Fin 2 → ℝ) : ℝ := fderiv ℝ η x e₁

noncomputable def d₂₁ (η : (Fin 2 → ℝ) → ℝ) (x : Fin 2 → ℝ) : ℝ := fderiv ℝ (d₁ η) x e₁

theorem continuous_d₁ {η : (Fin 2 → ℝ) → ℝ} (hη : ContDiff ℝ 1 η) : Continuous (d₁ η) :=
  (hη.continuous_fderiv one_ne_zero).clm_apply continuous_const

theorem continuous_d₂ {η : (Fin 2 → ℝ) → ℝ} (hη : ContDiff ℝ 1 η) : Continuous (d₂ η) :=
  (hη.continuous_fderiv one_ne_zero).clm_apply continuous_const

theorem contDiff_d₁ {η : (Fin 2 → ℝ) → ℝ} (hη : ContDiff ℝ 2 η) : ContDiff ℝ 1 (d₁ η) :=
  (hη.fderiv_right (by norm_num)).clm_apply contDiff_const

theorem continuous_d₂₁ {η : (Fin 2 → ℝ) → ℝ} (hη : ContDiff ℝ 2 η) : Continuous (d₂₁ η) :=
  ((contDiff_d₁ hη).continuous_fderiv one_ne_zero).clm_apply continuous_const

/-- The wall profiles and the mixed profile. -/
noncomputable def hadG₁ (η : (Fin 2 → ℝ) → ℝ) (a : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, d₁ η ((t * a) • e₀)

noncomputable def hadG₂ (η : (Fin 2 → ℝ) → ℝ) (b : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, d₂ η ((t * b) • e₁)

noncomputable def hadRho (η : (Fin 2 → ℝ) → ℝ) (u : Fin 2 → ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1, d₂₁ η ((t * u 0) • e₀ + (r * u 1) • e₁)

/-- `η(a, 0) − η(0) = a g₁(a)`. -/
theorem sub_eq_mul_hadG₁ {η : (Fin 2 → ℝ) → ℝ} (hη : ContDiff ℝ 1 η) (a : ℝ) :
    η (a • e₀) - η 0 = a * hadG₁ η a := by
  have h := sub_eq_integral_fderiv hη 0 (a • e₀)
  rw [zero_add] at h
  rw [h]
  unfold hadG₁ d₁
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [zero_add, smul_smul, map_smul, smul_eq_mul]

theorem sub_eq_mul_hadG₂ {η : (Fin 2 → ℝ) → ℝ} (hη : ContDiff ℝ 1 η) (b : ℝ) :
    η (b • e₁) - η 0 = b * hadG₂ η b := by
  have h := sub_eq_integral_fderiv hη 0 (b • e₁)
  rw [zero_add] at h
  rw [h]
  unfold hadG₂ d₂
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [zero_add, smul_smul, map_smul, smul_eq_mul]

/-- `g₁(a) = (η(a,0) − η(0))/a` for `a ≠ 0`. -/
theorem hadG₁_eq_div {η : (Fin 2 → ℝ) → ℝ} (hη : ContDiff ℝ 1 η) {a : ℝ} (ha : a ≠ 0) :
    hadG₁ η a = (η (a • e₀) - η 0) / a := by
  rw [sub_eq_mul_hadG₁ hη, mul_div_cancel_left₀ _ ha]

theorem hadG₂_eq_div {η : (Fin 2 → ℝ) → ℝ} (hη : ContDiff ℝ 1 η) {b : ℝ} (hb : b ≠ 0) :
    hadG₂ η b = (η (b • e₁) - η 0) / b := by
  rw [sub_eq_mul_hadG₂ hη, mul_div_cancel_left₀ _ hb]

/-- The mixed second difference: `∂₁η(y + b e₁) − ∂₁η(y) = b ∫₀¹ ∂₂∂₁η(y + r b e₁) dr`. -/
theorem d₁_sub_eq {η : (Fin 2 → ℝ) → ℝ} (hη : ContDiff ℝ 2 η) (y : Fin 2 → ℝ) (b : ℝ) :
    d₁ η (y + b • e₁) - d₁ η y = b * ∫ r in (0 : ℝ)..1, d₂₁ η (y + (r * b) • e₁) := by
  rw [sub_eq_integral_fderiv (contDiff_d₁ hη) y (b • e₁), ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun r _ => ?_
  unfold d₂₁
  simp only [smul_smul, map_smul, smul_eq_mul]

/-- The mixed second difference of `η` is `a b ρ(a, b)`. -/
theorem mixed_diff_eq {η : (Fin 2 → ℝ) → ℝ} (hη : ContDiff ℝ 2 η) (a b : ℝ) :
    η (a • e₀ + b • e₁) - η (a • e₀) - η (b • e₁) + η 0 =
      a * b * ∫ t in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1, d₂₁ η ((t * a) • e₀ + (r * b) • e₁) := by
  have hη1 : ContDiff ℝ 1 η := hη.of_le (by norm_num)
  set Δ : (Fin 2 → ℝ) → ℝ := fun x => η (x + b • e₁) - η x with hΔ
  have hΔc : ContDiff ℝ 1 Δ := (hη1.comp (contDiff_id.add contDiff_const)).sub hη1
  have hΔd : ∀ y : Fin 2 → ℝ, fderiv ℝ Δ y = fderiv ℝ η (y + b • e₁) - fderiv ℝ η y := by
    intro y
    have hf : DifferentiableAt ℝ (fun x => η (x + b • e₁)) y :=
      (hη1.differentiable one_ne_zero (y + b • e₁)).comp y (differentiableAt_id.add_const _)
    have hg : DifferentiableAt ℝ η y := hη1.differentiable one_ne_zero y
    have h := (hf.hasFDerivAt.sub hg.hasFDerivAt).fderiv
    rw [hΔ]
    exact h.trans (by rw [fderiv_comp_add_right])
  have h1 : Δ (a • e₀) - Δ 0 = η (a • e₀ + b • e₁) - η (a • e₀) - η (b • e₁) + η 0 := by
    simp only [hΔ, zero_add]
    ring
  rw [← h1]
  have h2 := sub_eq_integral_fderiv hΔc 0 (a • e₀)
  rw [zero_add] at h2
  rw [h2, mul_assoc, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun t _ => ?_
  rw [zero_add, hΔd, sub_apply, smul_smul, map_smul, map_smul, smul_eq_mul,
    smul_eq_mul, ← mul_sub]
  congr 1
  have := d₁_sub_eq hη ((t * a) • e₀) b
  unfold d₁ at this
  rw [this]

/-- ★★ **Hadamard's wall decomposition**: `η = η(0) + u g₁(u) + v g₂(v) + u v ρ(u,v)`. -/
theorem hadamard_decomp {η : (Fin 2 → ℝ) → ℝ} (hη : ContDiff ℝ 2 η) :
    η = tieAmp (η 0) (hadG₁ η) (hadG₂ η) (hadRho η) := by
  have hη1 : ContDiff ℝ 1 η := hη.of_le (by norm_num)
  funext u
  have hu : u = u 0 • e₀ + u 1 • e₁ := vec_eq u
  have h1 := sub_eq_mul_hadG₁ hη1 (u 0)
  have h2 := sub_eq_mul_hadG₂ hη1 (u 1)
  have h3 := mixed_diff_eq hη (u 0) (u 1)
  unfold tieAmp hadRho
  rw [← hu] at h3
  linear_combination h1 + h2 + h3

/-! ### Continuity of the profiles -/

theorem continuous_hadG₁ {η : (Fin 2 → ℝ) → ℝ} (hη : ContDiff ℝ 1 η) : Continuous (hadG₁ η) := by
  unfold hadG₁
  refine continuous_parametric_intervalIntegral_of_continuous'
    (f := fun a t => d₁ η ((t * a) • e₀)) ?_ 0 1
  exact (continuous_d₁ hη).comp (by fun_prop)

theorem continuous_hadG₂ {η : (Fin 2 → ℝ) → ℝ} (hη : ContDiff ℝ 1 η) : Continuous (hadG₂ η) := by
  unfold hadG₂
  refine continuous_parametric_intervalIntegral_of_continuous'
    (f := fun b t => d₂ η ((t * b) • e₁)) ?_ 0 1
  exact (continuous_d₂ hη).comp (by fun_prop)

theorem continuous_hadRho {η : (Fin 2 → ℝ) → ℝ} (hη : ContDiff ℝ 2 η) : Continuous (hadRho η) := by
  unfold hadRho
  have hinner : Continuous fun p : (Fin 2 → ℝ) × ℝ =>
      ∫ r in (0 : ℝ)..1, d₂₁ η ((p.2 * p.1 0) • e₀ + (r * p.1 1) • e₁) := by
    refine continuous_parametric_intervalIntegral_of_continuous'
      (f := fun (p : (Fin 2 → ℝ) × ℝ) (r : ℝ) => d₂₁ η ((p.2 * p.1 0) • e₀ + (r * p.1 1) • e₁))
      ?_ 0 1
    exact (continuous_d₂₁ hη).comp (by fun_prop)
  exact continuous_parametric_intervalIntegral_of_continuous'
    (f := fun (u : Fin 2 → ℝ) t => ∫ r in (0 : ℝ)..1, d₂₁ η ((t * u 0) • e₀ + (r * u 1) • e₁))
    hinner 0 1

/-! ### The tie formula for arbitrary smooth amplitudes -/

/-- ★★★ **The tie formula for an arbitrary smooth amplitude on the blow-up chart**: for smooth
`η` on the chart `h = (1,0)`, `k = (2,1)`, `C_{½,2}[η] = η(0)/8` and
`C_{½,1}[η] = −½ ∫₀¹ g₁ − ¼ ∫₀¹ g₂` with the Hadamard wall profiles `g₁, g₂`. -/
theorem chartPolarCoeff_smooth_half {η : (Fin 2 → ℝ) → ℝ} (hη : ContDiff ℝ ∞ η) :
    ∀ q ≤ 1, chartPolarCoeff ![1, 1] η tieH tieK (1 / 2) q =
      tieSmoothA (η 0) (hadG₁ η) (hadG₂ η) q := by
  have hη2 : ContDiff ℝ 2 η := hη.of_le (WithTop.coe_le_coe.2 le_top)
  have hη1 : ContDiff ℝ 1 η := hη.of_le (WithTop.coe_le_coe.2 le_top)
  have h := hadamard_decomp hη2
  intro q hq
  have hF : ContDiff ℝ ∞ (tieAmp (η 0) (hadG₁ η) (hadG₂ η) (hadRho η)) := by rw [← h]; exact hη
  have := chartPolarCoeff_tieAmp_half' (η 0) hF (continuous_hadG₁ hη1) (continuous_hadG₂ hη1)
    (continuous_hadRho hη2) q hq
  rw [← h] at this
  exact this

end Grammar
