/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.AEDisjointSourceAssembly
import Grammar.CompactSourceLocalization
import Grammar.GlobalExponentHironaka
import Grammar.HironakaAdapter

/-!
# The certified resolution theorem for the explicit coefficient (CCLXXIX)

The user-facing conditional theorem of the resolved-space programme (consult #85 unit 6), stated
honestly:

* **uniqueness**: two certified source decompositions of the SAME function with nonzero
  coefficients have the same pair (`sourceDecomp_pair_unique`) and then the same coefficient
  (`sourceDecomp_coeff_unique`) — the assembled coefficient is independent of the boxes, cutoffs,
  charts and packages of any certificate, but NOT of the target region;
* **a partial resolution as a certificate producer**: the region `N` of hironaka's
  `PartialResolution d K N` is covered a.e. by the chart images, which lie in `N`, so the target
  integral over `N` is the Boltzmann integral of the induced cover
  (`targetIntegral_eq_boltzmannIntegral_ofPartialResolution`); if the chart images are a.e.-disjoint
  and the charts carry one-chart variable-unit product packages, ★★
  `targetIntegral_isEquivalent_ofPartialResolution`:
  `∫_N F p e^{−nK} ~ c n^{−λ*}(log n)^{k*}` with `c > 0` explicit (the tied source coefficients),
  and the posterior expectation `∫_N F p e^{−nK} / ∫_N p e^{−nK} → c_F / c_1`
  (`tendsto_posteriorExpectation_ofPartialResolution`);
* **what `Q_all` supplies**: for analytic `K ≥ 0` near a zero `w` there is a compact neighbourhood
  `N` with a monomial partial resolution (`exists_monomialResolution_of_analytic`, hironaka's
  `exists_monomialResolution_at` with `Q_all`); the a.e.-disjointness of its images and the product
  packages of its charts are the SUPPLIED inputs of the theorem above. The explicit-coefficient
  theorem for the original target integral is not obtained from the exposed hironaka interface
  alone (the blow-up wedge obstruction of consult #84).

The region warning stands: this is a statement about `N`, not about a small ball, unless the
certificate is for that ball.
-/

open MeasureTheory Set Filter Topology Asymptotics Monomialize.VolumeScaling

namespace Grammar

/-! ### Uniqueness of the certified coefficient -/

section Unique

variable {d : ℕ} {K : (Fin d → ℝ) → ℝ} {p : TubeWeight d} {Z : ℝ → ℝ}
  {ι₁ : Type*} [Fintype ι₁] (R₁ : ResolutionCover d ι₁)
  (Ps₁ : ∀ i, ProductMonomialChartVar (ResolutionCover.ofChart (R₁.chart i)) () K)
  (χ₁ : ι₁ → (Fin d → ℝ) → ℝ) {ι₂ : Type*} [Fintype ι₂] (R₂ : ResolutionCover d ι₂)
  (Ps₂ : ∀ i, ProductMonomialChartVar (ResolutionCover.ofChart (R₂.chart i)) () K)
  (χ₂ : ι₂ → (Fin d → ℝ) → ℝ) (hK0 : ∀ x, 0 ≤ K x) {ε₁ ε₂ : ℝ} (hε₁ : 0 < ε₁) (hε₂ : 0 < ε₂)
  (hεb₁ : ∀ i, ε₁ ≤ (Ps₁ i).b) (hεb₂ : ∀ i, ε₂ ≤ (Ps₂ i).b)
  (hpc₁ : ∀ i, ContinuousOn (fun y => p.w ((R₁.chart i).φ y)) (Ps₁ i).W)
  (hpc₂ : ∀ i, ContinuousOn (fun y => p.w ((R₂.chart i).φ y)) (Ps₂ i).W)
  (hχm₁ : ∀ i, Measurable (χ₁ i)) (hχc₁ : ∀ i, ContinuousOn (χ₁ i) (R₁.chart i).dom)
  (hχm₂ : ∀ i, Measurable (χ₂ i)) (hχc₂ : ∀ i, ContinuousOn (χ₂ i) (R₂.chart i).dom)
  (hK : Measurable K) (hne₁ : (R₁.activeCharts Ps₁).Nonempty)
  (hne₂ : (R₂.activeCharts Ps₂).Nonempty) (S₁ : R₁.SourceDecomposition χ₁ K p Z)
  (S₂ : R₂.SourceDecomposition χ₂ K p Z)
  (hrem₁ : S₁.rem =o[atTop] powLogScale (R₁.partitionLam' Ps₁ hne₁) (R₁.partitionDeg' Ps₁ hne₁))
  (hrem₂ : S₂.rem =o[atTop] powLogScale (R₂.partitionLam' Ps₂ hne₂) (R₂.partitionDeg' Ps₂ hne₂))

include hK0 hε₁ hε₂ hεb₁ hεb₂ hpc₁ hpc₂ hχm₁ hχc₁ hχm₂ hχc₂ hK S₁ S₂ hrem₁ hrem₂ in
/-- **Two certified decompositions of the same function with nonzero coefficients have the same
pair.** -/
theorem sourceDecomp_pair_unique
    (hc₁ : R₁.sourceDecompCoeff Ps₁ χ₁ hK0 hε₁ hεb₁ hpc₁ hχm₁ hχc₁ hK hne₁ ≠ 0)
    (hc₂ : R₂.sourceDecompCoeff Ps₂ χ₂ hK0 hε₂ hεb₂ hpc₂ hχm₂ hχc₂ hK hne₂ ≠ 0) :
    R₁.partitionLam' Ps₁ hne₁ = R₂.partitionLam' Ps₂ hne₂ ∧
      R₁.partitionDeg' Ps₁ hne₁ = R₂.partitionDeg' Ps₂ hne₂ :=
  (R₁.hasLeadingTerm_of_sourceDecomposition Ps₁ χ₁ hK0 hε₁ hεb₁ hpc₁ hχm₁ hχc₁ hK hne₁ S₁
    hrem₁).pair_unique hc₁
    (R₂.hasLeadingTerm_of_sourceDecomposition Ps₂ χ₂ hK0 hε₂ hεb₂ hpc₂ hχm₂ hχc₂ hK hne₂ S₂ hrem₂)
    hc₂

include hK0 hε₁ hε₂ hεb₁ hεb₂ hpc₁ hpc₂ hχm₁ hχc₁ hχm₂ hχc₂ hK S₁ S₂ hrem₁ hrem₂ in
/-- **Two certified decompositions of the same function at the same pair have the same
coefficient** — independence from boxes, cutoffs, charts and packages. -/
theorem sourceDecomp_coeff_unique (hlam : R₁.partitionLam' Ps₁ hne₁ = R₂.partitionLam' Ps₂ hne₂)
    (hk : R₁.partitionDeg' Ps₁ hne₁ = R₂.partitionDeg' Ps₂ hne₂) :
    R₁.sourceDecompCoeff Ps₁ χ₁ hK0 hε₁ hεb₁ hpc₁ hχm₁ hχc₁ hK hne₁ =
      R₂.sourceDecompCoeff Ps₂ χ₂ hK0 hε₂ hεb₂ hpc₂ hχm₂ hχc₂ hK hne₂ := by
  have h₂ := R₂.hasLeadingTerm_of_sourceDecomposition Ps₂ χ₂ hK0 hε₂ hεb₂ hpc₂ hχm₂ hχc₂ hK hne₂
    S₂ hrem₂
  rw [← hlam, ← hk] at h₂
  exact (R₁.hasLeadingTerm_of_sourceDecomposition Ps₁ χ₁ hK0 hε₁ hεb₁ hpc₁ hχm₁ hχc₁ hK hne₁ S₁
    hrem₁).coeff_unique h₂

end Unique

/-! ### A partial resolution as a certificate producer -/

namespace ResolutionCover

variable {d : ℕ} {K : (Fin d → ℝ) → ℝ} {N : Set (Fin d → ℝ)} (R : PartialResolution d K N)

/-- The chart images of a partial resolution lie in its region. -/
theorem iUnion_image_ofPartialResolution_subset : ⋃ i, (ofPartialResolution R).image i ⊆ N :=
  iUnion_subset fun i => (PartialResolution.mapsTo R i).image_subset

/-- **The target integral over the region of a partial resolution is the Boltzmann integral of
the induced cover** (the images cover the region a.e. and lie in it). -/
theorem targetIntegral_eq_boltzmannIntegral_ofPartialResolution (F : (Fin d → ℝ) → ℝ)
    (p : TubeWeight d) (N' : ℝ) :
    targetIntegral N F K p N' = (ofPartialResolution R).boltzmannIntegral F K p N' :=
  (ofPartialResolution R).targetIntegral_eq_boltzmannIntegral_of_ae_eq R.cover
    (by rw [diff_eq_empty.2 (iUnion_image_ofPartialResolution_subset R), measure_empty]) F K p N'

variable (Ps : ∀ i, ProductMonomialChartVar (ofChart ((ofPartialResolution R).chart i)) () K)
  (hK0 : ∀ x, 0 ≤ K x) {ε : ℝ} (hε : 0 < ε) (hεb : ∀ i, ε ≤ (Ps i).b) {p : TubeWeight d}
  (hpc : ∀ i, ContinuousOn (fun y => p.w (R.φ i y)) (Ps i).W) {F : (Fin d → ℝ) → ℝ}
  (hFc : ∀ i, ContinuousOn (fun y => F (R.φ i y)) (Ps i).W) (hFm : Measurable F)
  (hK : Measurable K) (hne : ((ofPartialResolution R).activeCharts Ps).Nonempty)

include hK0 hε hεb hpc hFc hFm hK in
/-- ★★ **The certified resolution theorem**: a monomial partial resolution of `N` whose chart images
are a.e.-disjoint and whose charts carry one-chart variable-unit product packages gives
`∫_N F p e^{−nK} ~ c n^{−λ*}(log n)^{k*}` with the explicit positive coefficient, under the
dominant-face positivity of one tied chart. -/
theorem targetIntegral_isEquivalent_ofPartialResolution
    (hdisj : (ofPartialResolution R).AEDisjointImages)
    (hF : Integrable (fun x => F x * p.w x) (volume.restrict N)) (hF0 : ∀ x, 0 ≤ F x)
    (hp0 : ∀ x, 0 ≤ p.w x) (hr0 : ∀ i x, 0 ≤ (Ps i).r x) (i₀ : R.ι) (hact₀ : (Ps i₀).IsActive)
    (htied : (ofPartialResolution R).chartLam' Ps i₀ =
        (ofPartialResolution R).partitionLam' Ps hne ∧
      (ofPartialResolution R).chartDeg' Ps i₀ = (ofPartialResolution R).partitionDeg' Ps hne)
    (I₀ : Finset (Fin d)) (hI₀ : I₀ ⊆ (Ps i₀).e.support) (hne₀ : I₀.Nonempty)
    (hall : ∀ j ∈ I₀, (Ps i₀).ratio j = (ofPartialResolution R).chartLam' Ps i₀)
    (hdeg : I₀.card - 1 = (ofPartialResolution R).chartDeg' Ps i₀)
    (hpos : 0 < volume ((Ps i₀).sourceDominantFace (fun _ => (Ps i₀).e.support) ε I₀ hne₀
      (fun y => F (((ofPartialResolution R).chart i₀).Φ y)) p)) :
    0 < (ofPartialResolution R).aeDisjointCoeff Ps hK0 hε hεb hpc hFc hFm hK hne ∧
      targetIntegral N F K p ~[atTop] fun n =>
        (ofPartialResolution R).aeDisjointCoeff Ps hK0 hε hεb hpc hFc hFm hK hne *
          powLogScale ((ofPartialResolution R).partitionLam' Ps hne)
            ((ofPartialResolution R).partitionDeg' Ps hne) n :=
  (ofPartialResolution R).targetIntegral_isEquivalent_of_aeDisjoint Ps hK0 hε hεb hpc hFc hFm hK
    hne hdisj R.cover
    (by rw [diff_eq_empty.2 (iUnion_image_ofPartialResolution_subset R), measure_empty])
    (IntegrableOn.mono_set hF (iUnion_image_ofPartialResolution_subset R)) hF0 hp0 hr0 i₀ hact₀
    htied I₀ hI₀ hne₀ hall hdeg hpos

include hK0 hε hεb hpc hFc hFm hK in
/-- ★ **The leading-order posterior expectation over the region of a certified resolution**:
`∫_N F p e^{−nK} / ∫_N p e^{−nK} → c_F / c_1`. -/
theorem tendsto_posteriorExpectation_ofPartialResolution
    (hdisj : (ofPartialResolution R).AEDisjointImages)
    (hF : Integrable (fun x => F x * p.w x) (volume.restrict N))
    (hp : Integrable p.w (volume.restrict N)) (hp0 : ∀ x, 0 ≤ p.w x)
    (hr0 : ∀ i x, 0 ≤ (Ps i).r x) (i₀ : R.ι) (hact₀ : (Ps i₀).IsActive)
    (htied : (ofPartialResolution R).chartLam' Ps i₀ =
        (ofPartialResolution R).partitionLam' Ps hne ∧
      (ofPartialResolution R).chartDeg' Ps i₀ = (ofPartialResolution R).partitionDeg' Ps hne)
    (I₀ : Finset (Fin d)) (hI₀ : I₀ ⊆ (Ps i₀).e.support) (hne₀ : I₀.Nonempty)
    (hall : ∀ j ∈ I₀, (Ps i₀).ratio j = (ofPartialResolution R).chartLam' Ps i₀)
    (hdeg : I₀.card - 1 = (ofPartialResolution R).chartDeg' Ps i₀)
    (hpos : 0 < volume ((Ps i₀).sourceDominantFace (fun _ => (Ps i₀).e.support) ε I₀ hne₀
      (fun _ => (1 : ℝ)) p)) :
    0 < (ofPartialResolution R).aeDisjointNormaliser Ps hK0 hε hεb hpc hK hne ∧
      Tendsto (fun n => targetIntegral N F K p n / targetIntegral N (fun _ => (1 : ℝ)) K p n)
        atTop (𝓝 ((ofPartialResolution R).aeDisjointCoeff Ps hK0 hε hεb hpc hFc hFm hK hne /
          (ofPartialResolution R).aeDisjointNormaliser Ps hK0 hε hεb hpc hK hne)) := by
  have h := (ofPartialResolution R).tendsto_posteriorExpectation_of_aeDisjoint Ps hK0 hε hεb hpc
    hFc hFm hK hne hdisj (IntegrableOn.mono_set hF (iUnion_image_ofPartialResolution_subset R))
    (IntegrableOn.mono_set hp (iUnion_image_ofPartialResolution_subset R)) hp0 hr0 i₀ hact₀ htied
    I₀ hI₀ hne₀ hall hdeg hpos
  refine ⟨h.1, ?_⟩
  refine h.2.congr' (Eventually.of_forall fun n => ?_)
  beta_reduce
  unfold ResolutionCover.posteriorExpectation
  rw [targetIntegral_eq_boltzmannIntegral_ofPartialResolution R,
    targetIntegral_eq_boltzmannIntegral_ofPartialResolution R]

end ResolutionCover

/-! ### What hironaka supplies -/

/-- **Hironaka's input** (`Q_all`): for analytic `K` near a zero `w` at which `K` is not locally
zero, some compact neighbourhood `N` of `w` has a monomial partial
resolution. The a.e.-disjointness of its chart images and the product packages of its charts are
the supplied inputs of `targetIntegral_isEquivalent_ofPartialResolution`. -/
theorem exists_monomialResolution_of_analytic {d : ℕ} {U : Set (Fin d → ℝ)} (hU : IsOpen U)
    {K : (Fin d → ℝ) → ℝ} (hK : AnalyticOnNhd ℝ K U) {w : Fin d → ℝ} (hw : w ∈ U) (hKw : K w = 0)
    (hne : ¬ K =ᶠ[𝓝 w] 0) :
    ∃ N : Set (Fin d → ℝ), IsCompact N ∧ N ∈ 𝓝 w ∧ ∃ R : PartialResolution d K N, R.IsMonomial :=
  Monomialize.Analytic.exists_monomialResolution_at (Monomialize.Analytic.Q_all d) hU hK hw hKw hne

end Grammar
