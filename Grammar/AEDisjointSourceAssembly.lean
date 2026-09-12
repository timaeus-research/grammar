/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SourceDecompositionAssembly

/-!
# Assembly over almost-everywhere disjoint chart images (CCLXXVIII)

The second honest producer of a source decomposition certificate (consult #85 unit 5): a
resolution cover whose chart images are **pairwise almost-everywhere disjoint**
(`AEDisjointImages`: `volume (φ_i(dom_i) ∩ φ_j(dom_j)) = 0` for `i ≠ j`). Then the resolved
Boltzmann integral is the sum of the ONE-CHART Boltzmann integrals
(`boltzmannIntegral_eq_sum_ofChart`, from `integral_iUnion_ae`), each of which is the source chart
integral with the pulled-back observable (CCLXXV), so the cover carries the exact certificate
`sourceDecompositionOfAEDisjoint` with amplitudes `F ∘ Φ_i` and remainder `0` — singleton packages
with weight `1`, no counting weight (which is not `1` pointwise on shared boundaries and need not
satisfy the package's weight factorisation). CCLXXVI then gives:

* ★ `hasLeadingTerm_boltzmannIntegral_of_aeDisjoint` at the extremal pair over the active charts;
* ★★ `boltzmannIntegral_isEquivalent_of_aeDisjoint` (`c > 0` under the dominant-face positivity of
  one tied chart), `tendsto_freeEnergy_of_aeDisjoint`;
* ★ `tendsto_posteriorExpectation_of_aeDisjoint`: `E_N[F] = Z_N[F]/Z_N[1] → c_F / c_1` for every
  admissible observable (the numerator coefficient may vanish);
* the transfer to a target region `Rg` whose symmetric difference with the union of the images
  is null (`targetIntegral_eq_boltzmannIntegral_of_ae_eq`,
  `targetIntegral_isEquivalent_of_aeDisjoint`).

Almost-everywhere disjointness solves the overlap of chart images; it does not localise an
arbitrary compact chart domain into product boxes (the packages are supplied).
-/

open MeasureTheory Set Filter Topology Asymptotics

namespace Grammar

/-- **The integral over a finite almost-everywhere disjoint union** is the sum of the integrals. -/
theorem integral_iUnion_eq_sum_of_aeDisjoint {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {ι : Type*} [Fintype ι] {s : ι → Set X} (hm : ∀ i, MeasurableSet (s i))
    (hd : ∀ i j, i ≠ j → μ (s i ∩ s j) = 0) {f : X → ℝ} (hf : IntegrableOn f (⋃ i, s i) μ) :
    ∫ x in ⋃ i, s i, f x ∂μ = ∑ i, ∫ x in s i, f x ∂μ := by
  rw [integral_iUnion_ae (fun i => (hm i).nullMeasurableSet) (fun i j hij => hd i j hij) hf,
    tsum_fintype]

namespace ResolutionCover

variable {d : ℕ} {ι : Type*} [Fintype ι] (R : ResolutionCover d ι)

/-- **Pairwise almost-everywhere disjoint chart images.** -/
def AEDisjointImages : Prop := ∀ i j, i ≠ j → volume (R.image i ∩ R.image j) = 0

variable {F K : (Fin d → ℝ) → ℝ} {p : TubeWeight d}

/-- **The Boltzmann integral of a cover with a.e.-disjoint images is the sum of the one-chart
Boltzmann integrals.** -/
theorem boltzmannIntegral_eq_sum_ofChart (hdisj : R.AEDisjointImages)
    (hF : Integrable (fun x => F x * p.w x) (volume.restrict (⋃ i, R.image i)))
    (hK : Measurable K) (hK0 : ∀ x, 0 ≤ K x) {N : ℝ} (hN : 0 ≤ N) :
    R.boltzmannIntegral F K p N = ∑ i, (ofChart (R.chart i)).boltzmannIntegral F K p N := by
  rw [boltzmannIntegral_eq, integral_iUnion_eq_sum_of_aeDisjoint (fun i => R.measurableSet_image i)
    hdisj (R.integrable_boltzmann hF hK hK0 hN)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ofChart_boltzmannIntegral]
  rfl

/-- The target integrability restricts to each chart image. -/
theorem integrable_restrict_ofChart
    (hF : Integrable (fun x => F x * p.w x) (volume.restrict (⋃ i, R.image i))) (i : ι) :
    Integrable (fun x => F x * p.w x) (volume.restrict (⋃ j, (ofChart (R.chart i)).image j)) := by
  rw [ofChart_iUnion_image]
  exact IntegrableOn.mono_set hF (subset_iUnion R.image i)

/-- **The certified source decomposition of a cover with a.e.-disjoint images**: amplitudes the
pulled-back observable `F ∘ Φ_i`, remainder `0`. -/
noncomputable def sourceDecompositionOfAEDisjoint (hdisj : R.AEDisjointImages)
    (hFc : ∀ i, ContinuousOn (fun y => F ((R.chart i).φ y)) (R.chart i).dom) (hFm : Measurable F)
    (hF : Integrable (fun x => F x * p.w x) (volume.restrict (⋃ i, R.image i)))
    (hK : Measurable K) (hK0 : ∀ x, 0 ≤ K x) :
    R.SourceDecomposition (fun i y => F ((R.chart i).Φ y)) K p (R.boltzmannIntegral F K p) where
  rem := fun _ => 0
  decomp := fun N hN => by
    rw [add_zero, R.boltzmannIntegral_eq_sum_ofChart hdisj hF hK hK0 hN]
    exact Finset.sum_congr rfl fun i _ =>
      (sourceChartIntegral_pullback (R.chart i) (hFc i) subset_rfl hFm
        (R.integrable_restrict_ofChart hF i) hK hK0 hN).symm

/-! ### The leading term, equivalence, posterior and free energy -/

variable (Ps : ∀ i, ProductMonomialChartVar (ofChart (R.chart i)) () K) (hK0 : ∀ x, 0 ≤ K x)
  {ε : ℝ} (hε : 0 < ε) (hεb : ∀ i, ε ≤ (Ps i).b)
  (hpc : ∀ i, ContinuousOn (fun y => p.w ((R.chart i).φ y)) (Ps i).W)
  (hFc : ∀ i, ContinuousOn (fun y => F ((R.chart i).φ y)) (Ps i).W) (hFm : Measurable F)
  (hK : Measurable K) (hne : (R.activeCharts Ps).Nonempty)

include hFc in
/-- The pulled-back observable is continuous on each chart domain. -/
theorem continuousOn_pullback_dom (i : ι) :
    ContinuousOn (fun y => F ((R.chart i).φ y)) (R.chart i).dom :=
  (hFc i).mono (Ps i).dom_subset

include hK0 hε hεb hpc hFc hFm hK in
/-- **The assembled coefficient of a cover with a.e.-disjoint images**: the source decomposition
coefficient with amplitudes `F ∘ Φ_i`. -/
noncomputable def aeDisjointCoeff : ℝ :=
  R.sourceDecompCoeff Ps (fun i y => F ((R.chart i).Φ y)) hK0 hε hεb hpc
    (fun i => hFm.comp (R.chart i).measurable_Φ)
    (fun i => continuousOn_pullback_Φ (R.chart i) (hFc i) (Ps i).dom_subset) hK hne

include hK0 hε hεb hpc hFc hFm hK in
/-- ★ **The leading term of a cover with a.e.-disjoint images** at the extremal pair over the
active charts (signed observable). -/
theorem hasLeadingTerm_boltzmannIntegral_of_aeDisjoint (hdisj : R.AEDisjointImages)
    (hF : Integrable (fun x => F x * p.w x) (volume.restrict (⋃ i, R.image i))) :
    HasLeadingTerm (R.boltzmannIntegral F K p)
      (R.aeDisjointCoeff Ps hK0 hε hεb hpc hFc hFm hK hne) (R.partitionLam' Ps hne)
      (R.partitionDeg' Ps hne) :=
  R.hasLeadingTerm_of_sourceDecomposition Ps _ hK0 hε hεb hpc _ _ hK hne
    (R.sourceDecompositionOfAEDisjoint hdisj (R.continuousOn_pullback_dom Ps hFc) hFm hF hK hK0)
    (isLittleO_zero _ _)

include hK0 hε hεb hpc hFc hFm hK in
/-- ★★ **Asymptotic equivalence for a cover with a.e.-disjoint images**: `Z_N[F] ~ c N^{−λ*}
(log N)^{k*}` with `c > 0` when some tied active chart has an all-minimal stratum at the pair whose
dominant face has positive measure. -/
theorem boltzmannIntegral_isEquivalent_of_aeDisjoint (hdisj : R.AEDisjointImages)
    (hF : Integrable (fun x => F x * p.w x) (volume.restrict (⋃ i, R.image i)))
    (hF0 : ∀ x, 0 ≤ F x) (hp0 : ∀ x, 0 ≤ p.w x) (hr0 : ∀ i x, 0 ≤ (Ps i).r x) (i₀ : ι)
    (hact₀ : (Ps i₀).IsActive)
    (htied : R.chartLam' Ps i₀ = R.partitionLam' Ps hne ∧
      R.chartDeg' Ps i₀ = R.partitionDeg' Ps hne)
    (I₀ : Finset (Fin d)) (hI₀ : I₀ ⊆ (Ps i₀).e.support) (hne₀ : I₀.Nonempty)
    (hall : ∀ j ∈ I₀, (Ps i₀).ratio j = R.chartLam' Ps i₀)
    (hdeg : I₀.card - 1 = R.chartDeg' Ps i₀)
    (hpos : 0 < volume ((Ps i₀).sourceDominantFace (fun _ => (Ps i₀).e.support) ε I₀ hne₀
      (fun y => F ((R.chart i₀).Φ y)) p)) :
    0 < R.aeDisjointCoeff Ps hK0 hε hεb hpc hFc hFm hK hne ∧
      R.boltzmannIntegral F K p ~[atTop] fun N =>
        R.aeDisjointCoeff Ps hK0 hε hεb hpc hFc hFm hK hne *
          powLogScale (R.partitionLam' Ps hne) (R.partitionDeg' Ps hne) N :=
  R.isEquivalent_of_sourceDecomposition Ps _ hK0 hε hεb hpc _ _ hK hne
    (R.sourceDecompositionOfAEDisjoint hdisj (R.continuousOn_pullback_dom Ps hFc) hFm hF hK hK0)
    (isLittleO_zero _ _) (fun _ _ => hF0 _) hp0 hr0 i₀ hact₀ htied I₀ hI₀ hne₀ hall hdeg hpos

include hK0 hε hεb hpc hFc hFm hK in
/-- **The free energy for a cover with a.e.-disjoint images.** -/
theorem tendsto_freeEnergy_of_aeDisjoint (hdisj : R.AEDisjointImages)
    (hF : Integrable (fun x => F x * p.w x) (volume.restrict (⋃ i, R.image i)))
    (hc : 0 < R.aeDisjointCoeff Ps hK0 hε hεb hpc hFc hFm hK hne) :
    Tendsto (fun N => -Real.log (R.boltzmannIntegral F K p N) -
      (R.partitionLam' Ps hne * Real.log N - R.partitionDeg' Ps hne * Real.log (Real.log N)))
      atTop (𝓝 (-Real.log (R.aeDisjointCoeff Ps hK0 hε hεb hpc hFc hFm hK hne))) :=
  (R.hasLeadingTerm_boltzmannIntegral_of_aeDisjoint Ps hK0 hε hεb hpc hFc hFm hK hne hdisj
    hF).tendsto_neg_log hc

include hK0 hε hεb hpc hK in
/-- The constant observable's coefficient for a cover with a.e.-disjoint images. -/
noncomputable def aeDisjointNormaliser : ℝ :=
  R.aeDisjointCoeff Ps hK0 hε hεb hpc (F := fun _ => (1 : ℝ)) (fun _ => continuousOn_const)
    measurable_const hK hne

include hK0 hε hεb hpc hFc hFm hK in
/-- ★ **The leading-order posterior expectation for a cover with a.e.-disjoint images**:
`E_N[F] = Z_N[F]/Z_N[1] → c_F / c_1` for every admissible observable, the normaliser's coefficient
being positive under the dominant-face hypothesis for the constant observable. -/
theorem tendsto_posteriorExpectation_of_aeDisjoint (hdisj : R.AEDisjointImages)
    (hF : Integrable (fun x => F x * p.w x) (volume.restrict (⋃ i, R.image i)))
    (hp : Integrable p.w (volume.restrict (⋃ i, R.image i))) (hp0 : ∀ x, 0 ≤ p.w x)
    (hr0 : ∀ i x, 0 ≤ (Ps i).r x) (i₀ : ι) (hact₀ : (Ps i₀).IsActive)
    (htied : R.chartLam' Ps i₀ = R.partitionLam' Ps hne ∧
      R.chartDeg' Ps i₀ = R.partitionDeg' Ps hne)
    (I₀ : Finset (Fin d)) (hI₀ : I₀ ⊆ (Ps i₀).e.support) (hne₀ : I₀.Nonempty)
    (hall : ∀ j ∈ I₀, (Ps i₀).ratio j = R.chartLam' Ps i₀)
    (hdeg : I₀.card - 1 = R.chartDeg' Ps i₀)
    (hpos : 0 < volume ((Ps i₀).sourceDominantFace (fun _ => (Ps i₀).e.support) ε I₀ hne₀
      (fun _ => (1 : ℝ)) p)) :
    0 < R.aeDisjointNormaliser Ps hK0 hε hεb hpc hK hne ∧
      Tendsto (R.posteriorExpectation K p F) atTop
        (𝓝 (R.aeDisjointCoeff Ps hK0 hε hεb hpc hFc hFm hK hne /
          R.aeDisjointNormaliser Ps hK0 hε hεb hpc hK hne)) := by
  have hp' : Integrable (fun x => (fun _ => (1 : ℝ)) x * p.w x)
      (volume.restrict (⋃ i, R.image i)) := by
    simpa using hp
  have h1 := R.boltzmannIntegral_isEquivalent_of_aeDisjoint Ps hK0 hε hεb hpc
    (F := fun _ => (1 : ℝ)) (fun _ => continuousOn_const) measurable_const hK hne hdisj hp'
    (fun _ => zero_le_one) hp0 hr0 i₀ hact₀ htied I₀ hI₀ hne₀ hall hdeg hpos
  refine ⟨h1.1, ?_⟩
  exact (R.hasLeadingTerm_boltzmannIntegral_of_aeDisjoint Ps hK0 hε hεb hpc hFc hFm hK hne hdisj
    hF).tendsto_div_same_pair
    (R.hasLeadingTerm_boltzmannIntegral_of_aeDisjoint Ps hK0 hε hεb hpc
      (F := fun _ => (1 : ℝ)) (fun _ => continuousOn_const) measurable_const hK hne hdisj hp')
    h1.1.ne'

/-! ### Transfer to a target region -/

/-- A target region whose symmetric difference with the union of the chart images is null has the
Boltzmann integral of the cover. -/
theorem targetIntegral_eq_boltzmannIntegral_of_ae_eq {Rg : Set (Fin d → ℝ)}
    (h₁ : volume (Rg \ ⋃ i, R.image i) = 0) (h₂ : volume ((⋃ i, R.image i) \ Rg) = 0)
    (F K : (Fin d → ℝ) → ℝ) (p : TubeWeight d) (N : ℝ) :
    targetIntegral Rg F K p N = R.boltzmannIntegral F K p N := by
  rw [boltzmannIntegral_eq]
  exact setIntegral_congr_set (ae_eq_set.2 ⟨h₁, h₂⟩)

include hK0 hε hεb hpc hFc hFm hK in
/-- ★★ **The explicit leading coefficient of a target region** covered, up to a null set, by the
a.e.-disjoint images of a cover of one-chart product packages. -/
theorem targetIntegral_isEquivalent_of_aeDisjoint (hdisj : R.AEDisjointImages)
    {Rg : Set (Fin d → ℝ)} (h₁ : volume (Rg \ ⋃ i, R.image i) = 0)
    (h₂ : volume ((⋃ i, R.image i) \ Rg) = 0)
    (hF : Integrable (fun x => F x * p.w x) (volume.restrict (⋃ i, R.image i)))
    (hF0 : ∀ x, 0 ≤ F x) (hp0 : ∀ x, 0 ≤ p.w x) (hr0 : ∀ i x, 0 ≤ (Ps i).r x) (i₀ : ι)
    (hact₀ : (Ps i₀).IsActive)
    (htied : R.chartLam' Ps i₀ = R.partitionLam' Ps hne ∧
      R.chartDeg' Ps i₀ = R.partitionDeg' Ps hne)
    (I₀ : Finset (Fin d)) (hI₀ : I₀ ⊆ (Ps i₀).e.support) (hne₀ : I₀.Nonempty)
    (hall : ∀ j ∈ I₀, (Ps i₀).ratio j = R.chartLam' Ps i₀)
    (hdeg : I₀.card - 1 = R.chartDeg' Ps i₀)
    (hpos : 0 < volume ((Ps i₀).sourceDominantFace (fun _ => (Ps i₀).e.support) ε I₀ hne₀
      (fun y => F ((R.chart i₀).Φ y)) p)) :
    0 < R.aeDisjointCoeff Ps hK0 hε hεb hpc hFc hFm hK hne ∧
      targetIntegral Rg F K p ~[atTop] fun N =>
        R.aeDisjointCoeff Ps hK0 hε hεb hpc hFc hFm hK hne *
          powLogScale (R.partitionLam' Ps hne) (R.partitionDeg' Ps hne) N := by
  have h := R.boltzmannIntegral_isEquivalent_of_aeDisjoint Ps hK0 hε hεb hpc hFc hFm hK hne hdisj
    hF hF0 hp0 hr0 i₀ hact₀ htied I₀ hI₀ hne₀ hall hdeg hpos
  refine ⟨h.1, ?_⟩
  have heq : targetIntegral Rg F K p = R.boltzmannIntegral F K p :=
    funext fun N => R.targetIntegral_eq_boltzmannIntegral_of_ae_eq h₁ h₂ F K p N
  rw [heq]
  exact h.2

end ResolutionCover

end Grammar
