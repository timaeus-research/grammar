/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SourceAmplitudeLeadingTerm
import Grammar.VariableNoActiveAssembly

/-!
# Certified source decompositions and their leading terms (CCLXXVI)

The **source decomposition certificate** (consult #85 unit 3): a function `Z` of `N` (the target
integral `∫_{Rg} F p e^{−NK}`, `targetIntegral`) is, for every `N ≥ 0`, the sum of finitely many
source-weighted one-chart integrals `∫ χ_i · |det Dφ_i| · (p∘φ_i) · (F∘φ_i) · e^{−N K∘φ_i}` over the
charts of a cover `R`, plus a remainder (`SourceDecomposition`). The certificate is exact; the
remainder control is a separate hypothesis (`o` of the extremal scale, or an exponential bound).

Given one-chart variable-unit product packages `Ps i` for the charts and source amplitudes `χ i`
(measurable, continuous on the chart domains), with the extremal pair `(λ*, k*)` over the ACTIVE
charts of CCLXIX (`partitionLam'`, `partitionDeg'`, `tiedCharts'`):

* `sourceChartCoeff' i`: the source coefficient of chart `i` at its own extremal pair (`0` if
  inactive), `hasLeadingTerm_sourceChart'_of_active`, `hasLeadingTerm_sourceChart'_of_inactive`;
* `sourceDecompCoeff := ∑_{tied} sourceChartCoeff' i`;
* ★ `hasLeadingTerm_of_sourceDecomposition`: `Z = sourceDecompCoeff · N^{−λ*}(log N)^{k*} + o(·)`
  when the remainder is `o` of the scale; `_exponential` for an exponentially small remainder;
* `sourceDecompCoeff_nonneg`, ★ `sourceDecompCoeff_pos` (one tied chart with an all-minimal
  stratum at the pair whose source dominant face has positive measure) and
  ★★ `isEquivalent_of_sourceDecomposition`: `Z ~ c N^{−λ*}(log N)^{k*}`, `c > 0` explicit;
* the ratio of two certified decompositions over the same packages converges to the ratio of the
  coefficients when the denominator's is positive (`tendsto_div_of_sourceDecompositions`), the
  leading-order posterior expectation with a numerator coefficient that may vanish.

Positivity is required at the extremal pair selected over all active charts, before any zero
coefficient is discarded: a zero coefficient is only `o` at the chart's own scale.
-/

open MeasureTheory Set Filter Topology Asymptotics

namespace Grammar

/-- **The target integral** `∫_{Rg} F p e^{−NK}` as a function of `N`. -/
noncomputable def targetIntegral {d : ℕ} (Rg : Set (Fin d → ℝ)) (F K : (Fin d → ℝ) → ℝ)
    (p : TubeWeight d) (N : ℝ) : ℝ :=
  ∫ x in Rg, F x * p.w x * Real.exp (-N * K x)

namespace ResolutionCover

variable {d : ℕ} {ι : Type*} [Fintype ι] (R : ResolutionCover d ι)

/-- **A certified finite source decomposition** of `Z` into the source-weighted one-chart integrals
of the charts of `R` with source amplitudes `χ`, plus a remainder, exactly for every `N ≥ 0`. -/
structure SourceDecomposition (χ : ι → (Fin d → ℝ) → ℝ) (K : (Fin d → ℝ) → ℝ) (p : TubeWeight d)
    (Z : ℝ → ℝ) where
  /-- The remainder. -/
  rem : ℝ → ℝ
  /-- The exact decomposition. -/
  decomp : ∀ N : ℝ, 0 ≤ N →
    Z N = (∑ i, (ofChart (R.chart i)).sourceChartIntegral () (χ i) K p N) + rem N

variable {K : (Fin d → ℝ) → ℝ} (Ps : ∀ i, ProductMonomialChartVar (ofChart (R.chart i)) () K)
  (χ : ι → (Fin d → ℝ) → ℝ) (hK0 : ∀ x, 0 ≤ K x) {ε : ℝ} (hε : 0 < ε)
  (hεb : ∀ i, ε ≤ (Ps i).b) {p : TubeWeight d}
  (hpc : ∀ i, ContinuousOn (fun y => p.w ((R.chart i).φ y)) (Ps i).W)
  (hχm : ∀ i, Measurable (χ i)) (hχc : ∀ i, ContinuousOn (χ i) (R.chart i).dom)
  (hK : Measurable K)

include hK0 hε hχm hχc hK in
/-- An inactive chart's source-weighted integral is negligible at every scale. -/
theorem hasLeadingTerm_sourceChartIntegral_of_inactive {i : ι} (h : ¬ (Ps i).IsActive)
    (lam : ℝ) (k : ℕ) :
    HasLeadingTerm ((ofChart (R.chart i)).sourceChartIntegral () (χ i) K p) 0 lam k := by
  have hno : (Ps i).e.support = ∅ := Finset.not_nonempty_iff_eq_empty.1 h
  have hempty := (ofChart (R.chart i)).hasLeadingTerm_sourcePieceIntegral_empty_of_monomial ()
    (p := p) (fun _ => (Ps i).e.support) ε (Ps i).monomial rfl hε (hχm i) (hχc i) hK hK0 lam k
  refine hempty.congr' ((eventually_ge_atTop 0).mono fun N hN => ?_)
  rw [(ofChart (R.chart i)).sourceChartIntegral_eq_sum_pieces () (fun _ => (Ps i).e.support) ε
    (hχm i) (hχc i) hK hK0 hN]
  have h0 : ((Ps i).e.support.powerset.filter fun I => I.Nonempty) = ∅ := by
    rw [hno, Finset.powerset_empty, Finset.filter_singleton]
    simp
  rw [h0, Finset.sum_empty, zero_add]

open scoped Classical in
include hK0 hε hεb hpc hχm hχc hK in
/-- The source coefficient of chart `i` at its extremal pair (`0` if inactive). -/
noncomputable def sourceChartCoeff' (i : ι) : ℝ :=
  if _ : (Ps i).IsActive then
    (Ps i).sourceCoeff hK0 hε (hεb i) (hpc i) (hχm i) (hχc i) hK (R.chartLam' Ps i)
      (R.chartDeg' Ps i)
  else 0

include hK0 hε hεb hpc hχm hχc hK in
/-- The one-chart source certificate of an active chart. -/
theorem hasLeadingTerm_sourceChart'_of_active {i : ι} (h : (Ps i).IsActive) :
    HasLeadingTerm ((ofChart (R.chart i)).sourceChartIntegral () (χ i) K p)
      (R.sourceChartCoeff' Ps χ hK0 hε hεb hpc hχm hχc hK i) (R.chartLam' Ps i)
      (R.chartDeg' Ps i) := by
  unfold sourceChartCoeff'
  rw [dif_pos h]
  have := (Ps i).hasLeadingTerm_sourceChartIntegral_extremal hK0 hε (hεb i) (hpc i) (hχm i)
    (hχc i) hK ((R.activeCoordsV_ofChart_nonempty_iff Ps i).2 h)
  rw [chartLam'_of_active R Ps h, chartDeg'_of_active R Ps h]
  exact this

variable (hne : (R.activeCharts Ps).Nonempty)

include hK0 hε hεb hpc hχm hχc hK in
/-- **The assembled source coefficient**: the sum over the tied active charts. -/
noncomputable def sourceDecompCoeff : ℝ :=
  ∑ i ∈ R.tiedCharts' Ps hne, R.sourceChartCoeff' Ps χ hK0 hε hεb hpc hχm hχc hK i

include hK0 hε hεb hpc hχm hχc hK in
/-- The sum of the source-weighted one-chart integrals has the assembled leading term. -/
theorem hasLeadingTerm_sum_sourceChartIntegral :
    HasLeadingTerm (fun N => ∑ i, (ofChart (R.chart i)).sourceChartIntegral () (χ i) K p N)
      (R.sourceDecompCoeff Ps χ hK0 hε hεb hpc hχm hχc hK hne) (R.partitionLam' Ps hne)
      (R.partitionDeg' Ps hne) := by
  classical
  have hact := hasLeadingTerm_sum_of_extremal (R.activeCharts Ps)
    (fun i N => (ofChart (R.chart i)).sourceChartIntegral () (χ i) K p N)
    (R.sourceChartCoeff' Ps χ hK0 hε hεb hpc hχm hχc hK) (R.chartLam' Ps) (R.chartDeg' Ps)
    (R.partitionLam' Ps hne) (R.partitionDeg' Ps hne)
    (fun i hi => R.hasLeadingTerm_sourceChart'_of_active Ps χ hK0 hε hεb hpc hχm hχc hK
      ((R.mem_activeCharts Ps).1 hi))
    (fun i hi => R.partitionLam'_le Ps hne ((R.mem_activeCharts Ps).1 hi))
    (fun i hi hl => R.chartDeg'_le_partitionDeg' Ps hne ((R.mem_activeCharts Ps).1 hi) hl)
  have hinact := HasLeadingTerm.sum (Finset.univ \ R.activeCharts Ps)
    (Z := fun i N => (ofChart (R.chart i)).sourceChartIntegral () (χ i) K p N)
    (c := fun _ => (0 : ℝ)) (lam := R.partitionLam' Ps hne) (k := R.partitionDeg' Ps hne)
    fun i hi => R.hasLeadingTerm_sourceChartIntegral_of_inactive Ps χ hK0 hε hχm hχc hK
      (fun h => (Finset.mem_sdiff.1 hi).2 ((R.mem_activeCharts Ps).2 h)) _ _
  have htotal := hact.add hinact
  rw [Finset.sum_const_zero, add_zero] at htotal
  refine htotal.congr' (Eventually.of_forall fun N => ?_)
  exact Finset.sum_add_sum_compl (R.activeCharts Ps) _

include hK0 hε hεb hpc hχm hχc hK in
/-- ★ **The leading term of a certified source decomposition** whose remainder is `o` of the
extremal scale. -/
theorem hasLeadingTerm_of_sourceDecomposition {Z : ℝ → ℝ} (S : R.SourceDecomposition χ K p Z)
    (hrem : S.rem =o[atTop] powLogScale (R.partitionLam' Ps hne) (R.partitionDeg' Ps hne)) :
    HasLeadingTerm Z (R.sourceDecompCoeff Ps χ hK0 hε hεb hpc hχm hχc hK hne)
      (R.partitionLam' Ps hne) (R.partitionDeg' Ps hne) :=
  ((R.hasLeadingTerm_sum_sourceChartIntegral Ps χ hK0 hε hεb hpc hχm hχc hK hne).add_isLittleO
    hrem).congr' ((eventually_ge_atTop 0).mono fun N hN => (S.decomp N hN).symm)

include hK0 hε hεb hpc hχm hχc hK in
/-- ★ **The leading term of a certified source decomposition with an exponentially small
remainder.** -/
theorem hasLeadingTerm_of_sourceDecomposition_exponential {Z : ℝ → ℝ}
    (S : R.SourceDecomposition χ K p Z) (hrem : HasExponentialBound S.rem) :
    HasLeadingTerm Z (R.sourceDecompCoeff Ps χ hK0 hε hεb hpc hχm hχc hK hne)
      (R.partitionLam' Ps hne) (R.partitionDeg' Ps hne) :=
  R.hasLeadingTerm_of_sourceDecomposition Ps χ hK0 hε hεb hpc hχm hχc hK hne S
    (hrem.isLittleO_powLogScale _ _)

/-! ### Nonnegativity, positivity, equivalence, ratios -/

include hK0 hε hεb hpc hχm hχc hK in
theorem sourceChartCoeff'_nonneg (hχ0 : ∀ i y, 0 ≤ χ i y) (hp0 : ∀ x, 0 ≤ p.w x)
    (hr0 : ∀ i x, 0 ≤ (Ps i).r x) (i : ι) :
    0 ≤ R.sourceChartCoeff' Ps χ hK0 hε hεb hpc hχm hχc hK i := by
  unfold sourceChartCoeff'
  split_ifs with h
  · exact (Ps i).sourceCoeff_nonneg hK0 hε (hεb i) (hpc i) (hχm i) (hχc i) hK (hχ0 i) hp0 (hr0 i)
      _ _
  · exact le_rfl

include hK0 hε hεb hpc hχm hχc hK in
theorem sourceDecompCoeff_nonneg (hχ0 : ∀ i y, 0 ≤ χ i y) (hp0 : ∀ x, 0 ≤ p.w x)
    (hr0 : ∀ i x, 0 ≤ (Ps i).r x) :
    0 ≤ R.sourceDecompCoeff Ps χ hK0 hε hεb hpc hχm hχc hK hne :=
  Finset.sum_nonneg fun i _ =>
    R.sourceChartCoeff'_nonneg Ps χ hK0 hε hεb hpc hχm hχc hK hχ0 hp0 hr0 i

include hK0 hε hεb hpc hχm hχc hK in
/-- ★ **The assembled coefficient is positive** when some tied active chart `i₀` has an all-minimal
stratum at its pair whose source dominant face has positive measure. -/
theorem sourceDecompCoeff_pos (hχ0 : ∀ i y, 0 ≤ χ i y) (hp0 : ∀ x, 0 ≤ p.w x)
    (hr0 : ∀ i x, 0 ≤ (Ps i).r x) (i₀ : ι) (hact₀ : (Ps i₀).IsActive)
    (htied : R.chartLam' Ps i₀ = R.partitionLam' Ps hne ∧
      R.chartDeg' Ps i₀ = R.partitionDeg' Ps hne)
    (I₀ : Finset (Fin d)) (hI₀ : I₀ ⊆ (Ps i₀).e.support) (hne₀ : I₀.Nonempty)
    (hall : ∀ j ∈ I₀, (Ps i₀).ratio j = R.chartLam' Ps i₀)
    (hdeg : I₀.card - 1 = R.chartDeg' Ps i₀)
    (hpos : 0 < volume ((Ps i₀).sourceDominantFace (fun _ => (Ps i₀).e.support) ε I₀ hne₀ (χ i₀)
      p)) :
    0 < R.sourceDecompCoeff Ps χ hK0 hε hεb hpc hχm hχc hK hne := by
  classical
  refine Finset.sum_pos'
    (fun i _ => R.sourceChartCoeff'_nonneg Ps χ hK0 hε hεb hpc hχm hχc hK hχ0 hp0 hr0 i)
    ⟨i₀, Finset.mem_filter.2 ⟨(R.mem_activeCharts Ps).2 hact₀, htied⟩, ?_⟩
  unfold sourceChartCoeff'
  rw [dif_pos hact₀]
  exact (Ps i₀).sourceCoeff_pos hK0 hε (hεb i₀) (hpc i₀) (hχm i₀) (hχc i₀) hK (hχ0 i₀) hp0
    (hr0 i₀) I₀ hI₀ hne₀ hall hdeg hpos

include hK0 hε hεb hpc hχm hχc hK in
/-- ★★ **Asymptotic equivalence of a certified source decomposition**: `Z ~ c N^{−λ*}(log N)^{k*}`
with the explicit positive coefficient. -/
theorem isEquivalent_of_sourceDecomposition {Z : ℝ → ℝ} (S : R.SourceDecomposition χ K p Z)
    (hrem : S.rem =o[atTop] powLogScale (R.partitionLam' Ps hne) (R.partitionDeg' Ps hne))
    (hχ0 : ∀ i y, 0 ≤ χ i y) (hp0 : ∀ x, 0 ≤ p.w x) (hr0 : ∀ i x, 0 ≤ (Ps i).r x) (i₀ : ι)
    (hact₀ : (Ps i₀).IsActive)
    (htied : R.chartLam' Ps i₀ = R.partitionLam' Ps hne ∧
      R.chartDeg' Ps i₀ = R.partitionDeg' Ps hne)
    (I₀ : Finset (Fin d)) (hI₀ : I₀ ⊆ (Ps i₀).e.support) (hne₀ : I₀.Nonempty)
    (hall : ∀ j ∈ I₀, (Ps i₀).ratio j = R.chartLam' Ps i₀)
    (hdeg : I₀.card - 1 = R.chartDeg' Ps i₀)
    (hpos : 0 < volume ((Ps i₀).sourceDominantFace (fun _ => (Ps i₀).e.support) ε I₀ hne₀ (χ i₀)
      p)) :
    0 < R.sourceDecompCoeff Ps χ hK0 hε hεb hpc hχm hχc hK hne ∧
      Z ~[atTop] fun N => R.sourceDecompCoeff Ps χ hK0 hε hεb hpc hχm hχc hK hne *
        powLogScale (R.partitionLam' Ps hne) (R.partitionDeg' Ps hne) N :=
  have hc := R.sourceDecompCoeff_pos Ps χ hK0 hε hεb hpc hχm hχc hK hne hχ0 hp0 hr0 i₀ hact₀ htied
    I₀ hI₀ hne₀ hall hdeg hpos
  ⟨hc, (R.hasLeadingTerm_of_sourceDecomposition Ps χ hK0 hε hεb hpc hχm hχc hK hne S
    hrem).isEquivalent hc.ne'⟩

include hK0 hε hεb hpc hχm hχc hK in
/-- **The free energy of a certified source decomposition**:
`−log Z − (λ* log N − k* log log N) → −log c`. -/
theorem tendsto_freeEnergy_of_sourceDecomposition {Z : ℝ → ℝ} (S : R.SourceDecomposition χ K p Z)
    (hrem : S.rem =o[atTop] powLogScale (R.partitionLam' Ps hne) (R.partitionDeg' Ps hne))
    (hc : 0 < R.sourceDecompCoeff Ps χ hK0 hε hεb hpc hχm hχc hK hne) :
    Tendsto (fun N => -Real.log (Z N) -
      (R.partitionLam' Ps hne * Real.log N - R.partitionDeg' Ps hne * Real.log (Real.log N)))
      atTop (𝓝 (-Real.log (R.sourceDecompCoeff Ps χ hK0 hε hεb hpc hχm hχc hK hne))) :=
  (R.hasLeadingTerm_of_sourceDecomposition Ps χ hK0 hε hεb hpc hχm hχc hK hne S
    hrem).tendsto_neg_log hc

include hK0 hε hεb hpc hK in
/-- ★ **Ratios of certified decompositions over the same packages** (the leading-order posterior
expectation): the pair is geometric, so the ratio converges to the ratio of the coefficients when
the denominator's coefficient is positive — the numerator's may vanish. -/
theorem tendsto_div_of_sourceDecompositions {χ₁ χ₂ : ι → (Fin d → ℝ) → ℝ}
    (hχm₁ : ∀ i, Measurable (χ₁ i)) (hχc₁ : ∀ i, ContinuousOn (χ₁ i) (R.chart i).dom)
    (hχm₂ : ∀ i, Measurable (χ₂ i)) (hχc₂ : ∀ i, ContinuousOn (χ₂ i) (R.chart i).dom)
    {Z₁ Z₂ : ℝ → ℝ} (S₁ : R.SourceDecomposition χ₁ K p Z₁) (S₂ : R.SourceDecomposition χ₂ K p Z₂)
    (hrem₁ : S₁.rem =o[atTop] powLogScale (R.partitionLam' Ps hne) (R.partitionDeg' Ps hne))
    (hrem₂ : S₂.rem =o[atTop] powLogScale (R.partitionLam' Ps hne) (R.partitionDeg' Ps hne))
    (hc₂ : R.sourceDecompCoeff Ps χ₂ hK0 hε hεb hpc hχm₂ hχc₂ hK hne ≠ 0) :
    Tendsto (fun N => Z₁ N / Z₂ N) atTop
      (𝓝 (R.sourceDecompCoeff Ps χ₁ hK0 hε hεb hpc hχm₁ hχc₁ hK hne /
        R.sourceDecompCoeff Ps χ₂ hK0 hε hεb hpc hχm₂ hχc₂ hK hne)) :=
  (R.hasLeadingTerm_of_sourceDecomposition Ps χ₁ hK0 hε hεb hpc hχm₁ hχc₁ hK hne S₁
    hrem₁).tendsto_div_same_pair
    (R.hasLeadingTerm_of_sourceDecomposition Ps χ₂ hK0 hε hεb hpc hχm₂ hχc₂ hK hne S₂ hrem₂) hc₂

end ResolutionCover

end Grammar
