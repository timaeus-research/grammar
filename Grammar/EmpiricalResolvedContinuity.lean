/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.EmpiricalRectContinuity
import Grammar.EmpiricalResolvedStratumFormula

/-!
# Continuity of the resolved empirical coefficients in the branch representatives
(§20, consult #144 unit C)

For smooth root fields `ξₙ → ξ` whose branch representatives converge on every piece in
`C^{R_p}` on the compact chart image `K_p` of the piece (`chartImage`: all chart points
`Tm p s v`, `s` in the base, `v` in the closed piece box; `R_p = pieceOrder`, the canonical depth
of the piece at `μ`), the resolved empirical coefficient at the top power `(μ, c − 1)` of an
observable vanishing near `D_{c+1}` converges (★★★ `tendsto_resolvedCoeff_top`). Route: the
affine chart map of a piece is `v ↦ T v + s'` with `‖T‖ ≤ 1` (`affineLin`, `affineMap_eq_lin_add`,
`norm_affineLin_le`), so jets transfer along it without loss (`iteratedFDeriv_comp_affineMap`,
`norm_iteratedFDeriv_comp_affineMap_le`, `jetBoundOn_comp_affineMap`, `jetClose_comp_affineMap`)
— uniformly in the base point; the replaced amplitudes are then close with a constant uniform in
the base point (`exists_jetClose_replaced_uniform`), the cube replacement rule and the coefficient
bound give a pointwise bound uniform in `s` (`abs_pieceKernel_sub_le`), and the base integrals
converge on the finite base measure (★★ `tendsto_pieceCoeff_top`). Deterministic and sequential;
no agreement of the branch representatives across the walls is imposed (Astra #144).
Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology Finset
open scoped ENNReal ContDiff Manifold
open Monomialize.VolumeScaling Monomialize.Transport Monomialize.Manifold
open Grammar.NormalCrossing Grammar.NormalCrossing.EvenChartBoxDepth

namespace Grammar

namespace SmoothEngine

/-! ### Jets along the affine chart map of a piece -/

section Affine

variable {d da : ℕ} {J : Finset (Fin d)} (e : Fin da ≃ {i // inJ J i})
  (σ : WaterFilling.CoordSign d)

/-- The linear part of the affine chart map: the signed coordinate embedding. -/
noncomputable def affineLin : (Fin da → ℝ) →L[ℝ] (Fin d → ℝ) :=
  ContinuousLinearMap.pi fun i : Fin d =>
    if h : i ∈ J then
      WaterFilling.sgn σ i • (ContinuousLinearMap.proj (e.symm ⟨i, h⟩) : (Fin da → ℝ) →L[ℝ] ℝ)
    else 0

theorem affineMap_eq_lin_add (s : {i // ¬ inJ J i} → ℝ) (v : Fin da → ℝ) :
    affineMap e σ s v = affineLin e σ v + glue J 0 s := by
  funext i
  by_cases hi : i ∈ J
  · rw [affineMap_apply_of_mem e σ s v hi, Pi.add_apply, affineLin, ContinuousLinearMap.pi_apply,
      dif_pos hi,
      smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
      glue_apply_of_mem J 0 s hi, Pi.zero_apply, add_zero]
  · rw [affineMap_apply_of_not_mem e σ s v hi, Pi.add_apply, affineLin,
      ContinuousLinearMap.pi_apply, dif_neg hi, zero_apply, glue_apply_of_not_mem J 0 s hi,
      zero_add]

theorem norm_affineLin_le : ‖affineLin e σ‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
  rw [one_mul, pi_norm_le_iff_of_nonneg (norm_nonneg v)]
  intro i
  rw [affineLin, ContinuousLinearMap.pi_apply]
  by_cases hi : i ∈ J
  · rw [dif_pos hi, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
      Real.norm_eq_abs, abs_mul, WaterFilling.abs_sgn, one_mul, ← Real.norm_eq_abs]
    exact norm_le_pi_norm v _
  · rw [dif_neg hi, zero_apply, norm_zero]
    exact norm_nonneg v

variable {L L₁ L₂ : (Fin d → ℝ) → ℝ}

/-- The iterated derivative of `L ∘ (affine chart map)`. -/
theorem iteratedFDeriv_comp_affineMap (hL : ContDiff ℝ ∞ L) (s : {i // ¬ inJ J i} → ℝ) (r : ℕ)
    (v : Fin da → ℝ) :
    iteratedFDeriv ℝ r (fun v => L (affineMap e σ s v)) v =
      (iteratedFDeriv ℝ r L (affineMap e σ s v)).compContinuousLinearMap
        fun _ => affineLin e σ := by
  have hfun : (fun v => L (affineMap e σ s v)) =
      (fun w => L (w + glue J 0 s)) ∘ affineLin e σ := by
    funext v
    rw [Function.comp_apply, affineMap_eq_lin_add]
  have hL' : ContDiff ℝ ∞ fun w : Fin d → ℝ => L (w + glue J 0 s) :=
    hL.comp (contDiff_id.add contDiff_const)
  rw [hfun, ContinuousLinearMap.iteratedFDeriv_comp_right (affineLin e σ) hL' v
    (natCast_le_infty r), iteratedFDeriv_comp_add_right, ← affineMap_eq_lin_add]

/-- ★ Jets do not grow along the affine chart map (`‖T‖ ≤ 1`). -/
theorem norm_iteratedFDeriv_comp_affineMap_le (hL : ContDiff ℝ ∞ L) (s : {i // ¬ inJ J i} → ℝ)
    (r : ℕ) (v : Fin da → ℝ) :
    ‖iteratedFDeriv ℝ r (fun v => L (affineMap e σ s v)) v‖ ≤
      ‖iteratedFDeriv ℝ r L (affineMap e σ s v)‖ := by
  rw [iteratedFDeriv_comp_affineMap e σ hL s r v]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  refine mul_le_of_le_one_right (norm_nonneg _) ?_
  exact Finset.prod_le_one (fun _ _ => norm_nonneg _) fun _ _ => norm_affineLin_le e σ

theorem jetBoundOn_comp_affineMap (hL : ContDiff ℝ ∞ L) (s : {i // ¬ inJ J i} → ℝ) {R : ℕ}
    {K : Set (Fin d → ℝ)} {K' : Set (Fin da → ℝ)} {B : ℝ} (hB : JetBoundOn R K L B)
    (hmaps : ∀ v ∈ K', affineMap e σ s v ∈ K) :
    JetBoundOn R K' (fun v => L (affineMap e σ s v)) B := fun r hr v hv =>
  (norm_iteratedFDeriv_comp_affineMap_le e σ hL s r v).trans (hB r hr _ (hmaps v hv))

theorem jetClose_comp_affineMap (hL₁ : ContDiff ℝ ∞ L₁) (hL₂ : ContDiff ℝ ∞ L₂)
    (s : {i // ¬ inJ J i} → ℝ) {R : ℕ} {K : Set (Fin d → ℝ)} {K' : Set (Fin da → ℝ)} {ε : ℝ}
    (hc : JetClose R K L₁ L₂ ε) (hmaps : ∀ v ∈ K', affineMap e σ s v ∈ K) :
    JetClose R K' (fun v => L₁ (affineMap e σ s v)) (fun v => L₂ (affineMap e σ s v)) ε := by
  intro r hr v hv
  have h1 : ContDiff ℝ ∞ fun v => L₁ (affineMap e σ s v) := hL₁.comp (contDiff_affineMap e σ s)
  have h2 : ContDiff ℝ ∞ fun v => L₂ (affineMap e σ s v) := hL₂.comp (contDiff_affineMap e σ s)
  rw [← iteratedFDeriv_sub_apply (h1.of_le (natCast_le_infty r)).contDiffAt
    (h2.of_le (natCast_le_infty r)).contDiffAt]
  have hfun : ((fun v => L₁ (affineMap e σ s v)) - fun v => L₂ (affineMap e σ s v)) =
      fun v => (L₁ - L₂) (affineMap e σ s v) := rfl
  rw [hfun]
  have hd : ContDiff ℝ ∞ (L₁ - L₂) := hL₁.sub hL₂
  refine (norm_iteratedFDeriv_comp_affineMap_le e σ hd s r v).trans ?_
  rw [iteratedFDeriv_sub_apply (hL₁.of_le (natCast_le_infty r)).contDiffAt
    (hL₂.of_le (natCast_le_infty r)).contDiffAt]
  exact hc r hr _ (hmaps v hv)

end Affine

/-! ### Replaced amplitudes: closeness uniform in the amplitude -/

variable {d : ℕ}

/-- ★★ `exists_jetClose_replaced` with the amplitude varying under a fixed jet bound. -/
theorem exists_jetClose_replaced_uniform {μ : ℝ} (hμ : 0 < μ) (R : ℕ) (b : ℝ) {Bη B : ℝ}
    (hBη : 0 ≤ Bη) (hB : 0 ≤ B) :
    ∃ C, 0 ≤ C ∧ ∀ η ζ₁ ζ₂ : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ η → ContDiff ℝ ∞ ζ₁ →
      ContDiff ℝ ∞ ζ₂ → JetBoundOn R (closedBox d b) η Bη → JetBoundOn R (closedBox d b) ζ₂ B →
      ∀ ε, 0 ≤ ε → ε ≤ 1 → JetClose R (closedBox d b) ζ₁ ζ₂ ε →
      JetClose R (closedBox d b) (fun v => η v * fluctuation 1 μ (ζ₁ v) / Real.Gamma μ)
        (fun v => η v * fluctuation 1 μ (ζ₂ v) / Real.Gamma μ) (C * ε) := by
  have hS : ContDiff ℝ ∞ (fluctuation 1 μ) := contDiff_fluctuation 1 μ one_pos hμ
  obtain ⟨C₀, hC₀, hcomp⟩ := exists_jetClose_comp hS R (closedBox d b) hB
  refine ⟨|(Real.Gamma μ)⁻¹| * (2 ^ R * Bη * C₀), by positivity, ?_⟩
  intro η ζ₁ ζ₂ hη hζ₁ hζ₂ hηB hB₂ ε hε0 hε1 hc
  have h1 := hcomp ζ₁ ζ₂ hζ₁ hζ₂ hB₂ ε hε0 hε1 hc
  have h2 := JetClose.mul_left hη hηB hBη (hS.comp hζ₁) (hS.comp hζ₂) (mul_nonneg hC₀ hε0) h1
  have h3 := JetClose.const_smul (hη.mul (hS.comp hζ₁)) (hη.mul (hS.comp hζ₂)) h2
    (Real.Gamma μ)⁻¹
  rw [replaced_eq_smul, replaced_eq_smul]
  refine h3.mono_eps (le_of_eq ?_)
  ring

namespace ResolvedData

variable (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)

/-! ### The compact chart image of a piece -/

/-- The chart image of a piece: all chart points `Tm p s v` with `s` in the base and `v` in the
closed piece box. -/
def chartImage (p : (Ξ.X Y).PIdx) : Set (Fin d → ℝ) :=
  (fun z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × (Fin ((Ξ.X Y).da p) → ℝ) =>
    (Ξ.X Y).Tm p z.1 z.2) '' (univ ×ˢ closedBox ((Ξ.X Y).da p) (Y.T.a p.1))

theorem isCompact_chartImage (p : (Ξ.X Y).PIdx) : IsCompact (Ξ.chartImage Y p) :=
  (isCompact_univ.prod (isCompact_closedBox _)).image ((Ξ.X Y).continuous_Tm p)

theorem Tm_mem_chartImage (p : (Ξ.X Y).PIdx) (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1))
    {v : Fin ((Ξ.X Y).da p) → ℝ} (hv : v ∈ closedBox _ (Y.T.a p.1)) :
    (Ξ.X Y).Tm p s v ∈ Ξ.chartImage Y p :=
  ⟨(s, v), ⟨mem_univ _, hv⟩, rfl⟩

/-- The canonical order of a piece at `μ`: the total canonical depth
`Σ (2kᵢ·cutoffOf h μ − hᵢ)` of the piece exponents. -/
noncomputable def pieceOrder (p : (Ξ.X Y).PIdx) (μ : ℝ) : ℕ :=
  ∑ i, depthOf ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) (cutoffOf ((Ξ.X Y).hA p) μ) i

/-! ### Convergence of the piece coefficients -/

/-- ★★ **Convergence of a piece coefficient at the top power** when the branch representatives
converge in `C^{R_p}` on the chart image of the piece. -/
theorem tendsto_pieceCoeff_top {c : ℕ} (hc : 1 ≤ c)
    (hF : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), Ξ.F P = 0) {μ : ℝ} (hμ : 0 < μ) (p : (Ξ.X Y).PIdx)
    (ξ : ℕ → Ξ.SmoothRootField Y) (ξ₀ : Ξ.SmoothRootField Y) {M : ℕ → ℝ} (hM0' : ∀ n, 0 ≤ M n)
    (hM : ∀ n, JetClose (Ξ.pieceOrder Y p μ) (Ξ.chartImage Y p) ((ξ n).Lψ p) (ξ₀.Lψ p) (M n))
    (hM0 : Tendsto M atTop (𝓝 0)) :
    Tendsto (fun n => (ξ n).pieceCoeff p μ (c - 1)) atTop (𝓝 (ξ₀.pieceCoeff p μ (c - 1))) := by
  have := (Ξ.piecePresentation Y p).isFiniteMeasure_ν
  have ha : 0 < Y.T.a p.1 := Y.T.a_pos p.1
  have hkA := (Ξ.X Y).kA_pos p
  unfold pieceOrder at hM
  obtain ⟨BG, hBG0, hBG⟩ := exists_jetBoundOn (Ξ.contDiff_G Y p.1) _ (Ξ.isCompact_chartImage Y p)
  obtain ⟨BL, hBL0, hBL⟩ := exists_jetBoundOn (ξ₀.Lψ_smooth p) _ (Ξ.isCompact_chartImage Y p)
  obtain ⟨C, hC0, hrep⟩ := exists_jetClose_replaced_uniform hμ
    (∑ i, depthOf ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) (cutoffOf ((Ξ.X Y).hA p) μ) i) (Y.T.a p.1) hBG0
    hBL0
  have hmaps : ∀ s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1), ∀ v ∈ closedBox _ (Y.T.a p.1),
      affineMap ((Ξ.X Y).eqv p) p.2 ((Ξ.X Y).sc p s) v ∈ Ξ.chartImage Y p :=
    fun s v hv => Ξ.Tm_mem_chartImage Y p s hv
  -- the kernels
  set a : ℕ → Base ((Ξ.X Y).act p.1) (Y.T.a p.1) → ℝ := fun n s =>
    empCoeffRect (fun v => Ξ.G Y p.1 (affineMap ((Ξ.X Y).eqv p) p.2 ((Ξ.X Y).sc p s) v))
      (fun v => (ξ n).Lψ p (affineMap ((Ξ.X Y).eqv p) p.2 ((Ξ.X Y).sc p s) v))
      ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) (fun _ => Y.T.a p.1) μ (c - 1) with ha_def
  set a₀ : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) → ℝ := fun s =>
    empCoeffRect (fun v => Ξ.G Y p.1 (affineMap ((Ξ.X Y).eqv p) p.2 ((Ξ.X Y).sc p s) v))
      (fun v => ξ₀.Lψ p (affineMap ((Ξ.X Y).eqv p) p.2 ((Ξ.X Y).sc p s) v))
      ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) (fun _ => Y.T.a p.1) μ (c - 1) with ha₀_def
  set Kc : ℝ := coeffBoundConstant ((Ξ.X Y).hA p) ((Ξ.X Y).kA p)
    (depthOf ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) (cutoffOf ((Ξ.X Y).hA p) μ)) 1 (Y.T.a p.1) μ (c - 1)
    with hKc
  have hKc0 : 0 ≤ Kc := coeffBoundConstant_nonneg _ _ _ _ _ _ _
  -- integrability of the kernels
  have hint : ∀ L : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ L → Integrable (fun s =>
      empCoeffRect (fun v => Ξ.G Y p.1 (affineMap ((Ξ.X Y).eqv p) p.2 ((Ξ.X Y).sc p s) v))
        (fun v => L (affineMap ((Ξ.X Y).eqv p) p.2 ((Ξ.X Y).sc p s) v))
        ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) (fun _ => Y.T.a p.1) μ (c - 1))
      (Ξ.piecePresentation Y p).ν := by
    intro L hL
    obtain ⟨B, hB⟩ := exists_abs_empCoeffRect_le_pieceFam ((Ξ.X Y).eqv p) p.2 (Ξ.G Y p.1) L
      (Ξ.contDiff_G Y p.1) hL ((Ξ.X Y).continuous_sc p) ha ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) hkA μ
      (c - 1)
    refine Integrable.mono' (integrable_const B) (measurable_empCoeffRect_pieceFam
      ((Ξ.X Y).eqv p) p.2 (Ξ.G Y p.1) L (Ξ.contDiff_G Y p.1) hL ((Ξ.X Y).continuous_sc p)
      ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) μ (c - 1)).aestronglyMeasurable (ae_of_all _ fun s => ?_)
    rw [Real.norm_eq_abs]
    exact hB s
  -- the pointwise bound, uniform in the base point
  have hpt : ∀ n, M n ≤ 1 → ∀ s, |a n s - a₀ s| ≤ Kc * (C * M n) := by
    intro n hn s
    have hηc : ContDiff ℝ ∞ fun v =>
        Ξ.G Y p.1 (affineMap ((Ξ.X Y).eqv p) p.2 ((Ξ.X Y).sc p s) v) :=
      (Ξ.contDiff_G Y p.1).comp (contDiff_affineMap _ _ _)
    have hζn : ContDiff ℝ ∞ fun v =>
        (ξ n).Lψ p (affineMap ((Ξ.X Y).eqv p) p.2 ((Ξ.X Y).sc p s) v) :=
      ((ξ n).Lψ_smooth p).comp (contDiff_affineMap _ _ _)
    have hζ₀ : ContDiff ℝ ∞ fun v =>
        ξ₀.Lψ p (affineMap ((Ξ.X Y).eqv p) p.2 ((Ξ.X Y).sc p s) v) :=
      (ξ₀.Lψ_smooth p).comp (contDiff_affineMap _ _ _)
    have hdeep : DeepVanishing
        (fun v => Ξ.G Y p.1 (affineMap ((Ξ.X Y).eqv p) p.2 ((Ξ.X Y).sc p s) v)) (Y.T.a p.1) c :=
      Ξ.deepVanishing_amp Y hF p s
    simp only [ha_def, ha₀_def]
    rw [empCoeffRect_top_eq_smoothCoeff hηc hζn hkA ha hμ hc hdeep,
      empCoeffRect_top_eq_smoothCoeff hηc hζ₀ hkA ha hμ hc hdeep]
    refine abs_smoothCoeff_sub_le ((contDiff_mul_fluctuation hηc hζn hμ).div_const _)
      ((contDiff_mul_fluctuation hηc hζ₀ hμ).div_const _) hkA one_pos ha
      (rectBound_of_jetClose ((contDiff_mul_fluctuation hηc hζn hμ).div_const _)
        ((contDiff_mul_fluctuation hηc hζ₀ hμ).div_const _) _ ?_) (c - 1)
    exact hrep _ _ _ hηc hζn hζ₀
      (jetBoundOn_comp_affineMap _ _ (Ξ.contDiff_G Y p.1) _ hBG (hmaps s))
      (jetBoundOn_comp_affineMap _ _ (ξ₀.Lψ_smooth p) _ hBL (hmaps s)) (M n) (hM0' n) hn
      (jetClose_comp_affineMap _ _ ((ξ n).Lψ_smooth p) (ξ₀.Lψ_smooth p) _ (hM n) (hmaps s))
  -- convergence of the base integrals
  have hev : ∀ᶠ n in atTop, M n ≤ 1 := hM0.eventually (Iic_mem_nhds zero_lt_one)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) (hev.mono fun n hn => ?_)
    (g := fun n => Kc * (C * M n) * (Ξ.piecePresentation Y p).ν.real univ) ?_
  · have hZn : (ξ n).pieceCoeff p μ (c - 1) = ∫ s, a n s ∂(Ξ.piecePresentation Y p).ν := rfl
    have hZ₀ : ξ₀.pieceCoeff p μ (c - 1) = ∫ s, a₀ s ∂(Ξ.piecePresentation Y p).ν := rfl
    rw [hZn, hZ₀, ← integral_sub (hint _ ((ξ n).Lψ_smooth p)) (hint _ (ξ₀.Lψ_smooth p))]
    refine norm_integral_le_of_norm_le_const (ae_of_all _ fun s => ?_)
    rw [Real.norm_eq_abs]
    exact hpt n hn s
  · have h1 : Tendsto (fun n => Kc * (C * M n) * (Ξ.piecePresentation Y p).ν.real univ) atTop
        (𝓝 (Kc * (C * 0) * (Ξ.piecePresentation Y p).ν.real univ)) :=
      ((hM0.const_mul C).const_mul Kc).mul_const _
    simpa using h1

/-- ★★★ **Continuity of the resolved empirical coefficients in the branch representatives**: if
the smooth root fields `ξₙ → ξ` in the sense that on every piece the branch representatives
converge in `C^{R_p}` on the chart image of the piece, then for every `c ≥ 1` and observable
vanishing near `D_{c+1}` the resolved coefficients at `(μ, c − 1)` converge. -/
theorem tendsto_resolvedCoeff_top {c : ℕ} (hc : 1 ≤ c)
    (hF : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), Ξ.F P = 0) {μ : ℝ} (hμ : 0 < μ)
    (ξ : ℕ → Ξ.SmoothRootField Y) (ξ₀ : Ξ.SmoothRootField Y) {M : ℕ → ℝ} (hM0' : ∀ n, 0 ≤ M n)
    (hM : ∀ n p, JetClose (Ξ.pieceOrder Y p μ) (Ξ.chartImage Y p) ((ξ n).Lψ p) (ξ₀.Lψ p) (M n))
    (hM0 : Tendsto M atTop (𝓝 0)) :
    Tendsto (fun n => (ξ n).resolvedCoeff μ (c - 1)) atTop (𝓝 (ξ₀.resolvedCoeff μ (c - 1))) := by
  unfold SmoothRootField.resolvedCoeff
  exact tendsto_finsetSum _ fun p _ =>
    Ξ.tendsto_pieceCoeff_top Y hc hF hμ p ξ ξ₀ hM0' (fun n => hM n p) hM0

end ResolvedData

end SmoothEngine

end Grammar
