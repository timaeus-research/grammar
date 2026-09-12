/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.PartitionLocalisation
import Grammar.ProductChartVarPosterior

/-!
# Assembly along a supplied partition of unity (CCLXV)

Each chart `i` of a cover carries a one-chart variable-unit product package `Ps i` (for the
one-chart cover `ofChart (R.chart i)`, whose counting weight is `1`), and a supplied partition of
unity `ψ_i` (CCLXIV) whose pullbacks `ψ_i ∘ φ_i` are continuous on the chart neighbourhoods.
Applying the one-chart theorem with prior `p ψ_i` chart by chart and summing
(`hasLeadingTerm_sum_extremal`):

* `chartLam`, `chartDeg`, `chartCoeff`: the extremal pair and coefficient of chart `i` with prior
  `p ψ_i`; `partitionLam = min_i chartLam i`, `partitionDeg = max_{attaining} chartDeg i`,
  `partitionCoeff = ∑_{tied charts} chartCoeff i`;
* ★ `hasLeadingTerm_boltzmannIntegral_of_partition` (signed observable): `Z_N[F]` has the
  certificate at `(λ*, k*)` with the summed tied coefficients;
* nonnegativity (`chartCoeff_nonneg`, `partitionCoeff_nonneg`) and positivity from one tied chart
  whose dominant face (for the prior `p ψ_i`) has positive measure (`partitionCoeff_pos`);
* ★★ `boltzmannIntegral_isEquivalent_of_partition`: `Z_N[F] ~ c N^{−λ*} (log N)^{k*}`, `c > 0`;
* ★ `tendsto_posteriorExpectation_of_partition`: `E_N[F] → partitionCoeff F / partitionCoeff 1`.

The cover weight no longer has to factor through the inactive coordinates (consult #83, R3): the
supplied weights enter through the prior and may depend on all coordinates.
-/

open MeasureTheory Set Filter Topology Asymptotics

namespace Grammar

namespace ResolutionCover

variable {d : ℕ} {ι : Type*} [Fintype ι] (R : ResolutionCover d ι) {K : (Fin d → ℝ) → ℝ}
  (Ps : ∀ i, ProductMonomialChartVar (ofChart (R.chart i)) () K) (P : SubordinatePartition R)
  (hK0 : ∀ x, 0 ≤ K x) {ε : ℝ} (hε : 0 < ε) (hεb : ∀ i, ε ≤ (Ps i).b) {p : TubeWeight d}
  (hpc : ∀ i, ContinuousOn (fun y => p.w ((R.chart i).φ y)) (Ps i).W)
  (hψ : ∀ i, ContinuousOn (fun y => P.ψ i ((R.chart i).φ y)) (Ps i).W) (hK : Measurable K)
  (hact : ∀ i, ((ofChart (R.chart i)).activeCoordsV (fun _ => Ps i)).Nonempty)

/-! ### The per-chart data -/

/-- The extremal exponent of chart `i`. -/
noncomputable def chartLam (i : ι) : ℝ :=
  (ofChart (R.chart i)).coverLamV (fun _ => Ps i) (hact i)

/-- The extremal log degree of chart `i`. -/
noncomputable def chartDeg (i : ι) : ℕ :=
  (ofChart (R.chart i)).coverDegV (fun _ => Ps i) (hact i)

variable {F : (Fin d → ℝ) → ℝ} (hFc : ∀ i, ContinuousOn (fun y => F ((R.chart i).φ y)) (Ps i).W)
  (hFm : Measurable F) (hF : Integrable (fun x => F x * p.w x) (volume.restrict (⋃ i, R.image i)))

include hK0 hε hεb hpc hψ hK hact hFc hFm hF in
/-- The coefficient of chart `i` at its extremal pair, with prior `p ψ_i`. -/
noncomputable def chartCoeff (i : ι) : ℝ :=
  (ofChart (R.chart i)).productCoeffV (fun _ => Ps i) hK0 hε (fun _ => hεb i) (fun _ => hFc i)
    (fun _ => (hpc i).mul (hψ i)) hFm (R.integrable_mulPartition P i hF) hK
    (R.chartLam Ps hact i) (R.chartDeg Ps hact i)

include hK0 hε hεb hpc hψ hK hact hFc hFm hF in
/-- The one-chart certificate of chart `i` with prior `p ψ_i`. -/
theorem hasLeadingTerm_chart (i : ι) :
    HasLeadingTerm ((ofChart (R.chart i)).boltzmannIntegral F K (p.mulPartition P i))
      (R.chartCoeff Ps P hK0 hε hεb hpc hψ hK hact hFc hFm hF i) (R.chartLam Ps hact i)
      (R.chartDeg Ps hact i) :=
  (ofChart (R.chart i)).hasLeadingTerm_boltzmannIntegral_of_productChartsV_extremal (fun _ => Ps i)
    hK0 hε (fun _ => hεb i) (fun _ => hFc i) (fun _ => (hpc i).mul (hψ i)) hFm
    (R.integrable_mulPartition P i hF) hK (hact i)

include hK0 hε hεb hpc hψ hK hact hFc hFm hF in
/-- Every chart coefficient is nonnegative for nonnegative `F`, `p` and inactive weight factors. -/
theorem chartCoeff_nonneg (hF0 : ∀ x, 0 ≤ F x) (hp0 : ∀ x, 0 ≤ p.w x)
    (hr0 : ∀ i x, 0 ≤ (Ps i).r x) (i : ι) :
    0 ≤ R.chartCoeff Ps P hK0 hε hεb hpc hψ hK hact hFc hFm hF i := by
  unfold chartCoeff ResolutionCover.productCoeffV
  refine Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun I _ => ?_
  exact (ofChart (R.chart i)).leadingAtlasPieceCoeff_productAtlasesV_nonneg (fun _ => Ps i) hK0 hε
    (fun _ => hεb i) (fun _ => hFc i) (fun _ => (hpc i).mul (hψ i)) hFm
    (R.integrable_mulPartition P i hF) hK hF0
    (fun x => mul_nonneg (hp0 x) (P.nonneg i x)) (fun _ x => hr0 i x) _ _ j I

/-! ### The extremal pair over the charts -/

variable [Nonempty ι]

/-- **The extremal exponent of the cover**: the minimum of the chart exponents. -/
noncomputable def partitionLam : ℝ :=
  extremalExponent Finset.univ (R.chartLam Ps hact) Finset.univ_nonempty

/-- **The extremal log degree of the cover**: the maximum over the charts attaining the exponent. -/
noncomputable def partitionDeg : ℕ :=
  extremalDegree Finset.univ (R.chartLam Ps hact) (R.chartDeg Ps hact) Finset.univ_nonempty

/-- The tied charts. -/
noncomputable def tiedCharts : Finset ι :=
  Finset.univ.filter fun i =>
    R.chartLam Ps hact i = R.partitionLam Ps hact ∧ R.chartDeg Ps hact i = R.partitionDeg Ps hact

theorem partitionLam_le (i : ι) : R.partitionLam Ps hact ≤ R.chartLam Ps hact i :=
  extremalExponent_le _ _ _ (Finset.mem_univ i)

theorem chartDeg_le_partitionDeg (i : ι) (h : R.chartLam Ps hact i = R.partitionLam Ps hact) :
    R.chartDeg Ps hact i ≤ R.partitionDeg Ps hact :=
  le_extremalDegree _ _ _ _ (Finset.mem_univ i) h

include hK0 hε hεb hpc hψ hK hact hFc hFm hF in
/-- **The total coefficient**: the sum of the coefficients of the tied charts. -/
noncomputable def partitionCoeff : ℝ :=
  ∑ i ∈ R.tiedCharts Ps hact, R.chartCoeff Ps P hK0 hε hεb hpc hψ hK hact hFc hFm hF i

include hK0 hε hεb hpc hψ hK hact hFc hFm hF in
/-- ★ **The leading term of the resolved Boltzmann integral along a supplied partition** (signed
observable): at the extremal pair over the charts, with the summed tied coefficients. -/
theorem hasLeadingTerm_boltzmannIntegral_of_partition :
    HasLeadingTerm (R.boltzmannIntegral F K p)
      (R.partitionCoeff Ps P hK0 hε hεb hpc hψ hK hact hFc hFm hF) (R.partitionLam Ps hact)
      (R.partitionDeg Ps hact) := by
  have h := hasLeadingTerm_sum_extremal Finset.univ
    (fun i N => (ofChart (R.chart i)).boltzmannIntegral F K (p.mulPartition P i) N)
    (R.chartCoeff Ps P hK0 hε hεb hpc hψ hK hact hFc hFm hF) (R.chartLam Ps hact)
    (R.chartDeg Ps hact) Finset.univ_nonempty
    (fun i _ => R.hasLeadingTerm_chart Ps P hK0 hε hεb hpc hψ hK hact hFc hFm hF i)
  exact h.congr' ((eventually_ge_atTop 0).mono fun N hN =>
    (R.boltzmannIntegral_eq_sum_partition P hF hK hK0 hN).symm)

/-! ### Nonnegativity and positivity -/

include hK0 hε hεb hpc hψ hK hact hFc hFm hF in
theorem partitionCoeff_nonneg (hF0 : ∀ x, 0 ≤ F x) (hp0 : ∀ x, 0 ≤ p.w x)
    (hr0 : ∀ i x, 0 ≤ (Ps i).r x) :
    0 ≤ R.partitionCoeff Ps P hK0 hε hεb hpc hψ hK hact hFc hFm hF :=
  Finset.sum_nonneg fun i _ =>
    R.chartCoeff_nonneg Ps P hK0 hε hεb hpc hψ hK hact hFc hFm hF hF0 hp0 hr0 i

include hK0 hε hεb hpc hψ hK hact hFc hFm hF in
/-- **The total coefficient is positive** when some tied chart `i₀` has an all-minimal stratum at
its pair whose dominant face (for the prior `p ψ_{i₀}`) has positive measure. -/
theorem partitionCoeff_pos (hF0 : ∀ x, 0 ≤ F x) (hp0 : ∀ x, 0 ≤ p.w x)
    (hr0 : ∀ i x, 0 ≤ (Ps i).r x) (i₀ : ι)
    (htied : R.chartLam Ps hact i₀ = R.partitionLam Ps hact ∧
      R.chartDeg Ps hact i₀ = R.partitionDeg Ps hact)
    (I₀ : Finset (Fin d)) (hI₀ : I₀ ⊆ (Ps i₀).e.support) (hne₀ : I₀.Nonempty)
    (hall : ∀ j ∈ I₀, (Ps i₀).ratio j = R.chartLam Ps hact i₀)
    (hdeg : I₀.card - 1 = R.chartDeg Ps hact i₀)
    (hpos : 0 < volume ((Ps i₀).dominantFace (fun _ => (Ps i₀).e.support) ε I₀ hne₀ F
      (p.mulPartition P i₀))) :
    0 < R.partitionCoeff Ps P hK0 hε hεb hpc hψ hK hact hFc hFm hF :=
  Finset.sum_pos'
    (fun i _ => R.chartCoeff_nonneg Ps P hK0 hε hεb hpc hψ hK hact hFc hFm hF hF0 hp0 hr0 i)
    ⟨i₀, Finset.mem_filter.2 ⟨Finset.mem_univ _, htied⟩,
      (ofChart (R.chart i₀)).productCoeffV_pos (fun _ => Ps i₀) hK0 hε (fun _ => hεb i₀)
        (fun _ => hFc i₀) (fun _ => (hpc i₀).mul (hψ i₀)) hFm (R.integrable_mulPartition P i₀ hF)
        hK hF0 (fun x => mul_nonneg (hp0 x) (P.nonneg i₀ x)) (fun _ x => hr0 i₀ x) () I₀ hI₀ hne₀
        hall hdeg hpos⟩

include hK0 hε hεb hpc hψ hK hact hFc hFm hF in
/-- ★★ **Asymptotic equivalence along a supplied partition of unity**:
`Z_N[F] ~ c · N^{−λ*} (log N)^{k*}` with `c > 0` — the supplied weights may depend on all
coordinates. -/
theorem boltzmannIntegral_isEquivalent_of_partition (hF0 : ∀ x, 0 ≤ F x) (hp0 : ∀ x, 0 ≤ p.w x)
    (hr0 : ∀ i x, 0 ≤ (Ps i).r x) (i₀ : ι)
    (htied : R.chartLam Ps hact i₀ = R.partitionLam Ps hact ∧
      R.chartDeg Ps hact i₀ = R.partitionDeg Ps hact)
    (I₀ : Finset (Fin d)) (hI₀ : I₀ ⊆ (Ps i₀).e.support) (hne₀ : I₀.Nonempty)
    (hall : ∀ j ∈ I₀, (Ps i₀).ratio j = R.chartLam Ps hact i₀)
    (hdeg : I₀.card - 1 = R.chartDeg Ps hact i₀)
    (hpos : 0 < volume ((Ps i₀).dominantFace (fun _ => (Ps i₀).e.support) ε I₀ hne₀ F
      (p.mulPartition P i₀))) :
    0 < R.partitionCoeff Ps P hK0 hε hεb hpc hψ hK hact hFc hFm hF ∧
      R.boltzmannIntegral F K p ~[atTop] fun N =>
        R.partitionCoeff Ps P hK0 hε hεb hpc hψ hK hact hFc hFm hF *
          powLogScale (R.partitionLam Ps hact) (R.partitionDeg Ps hact) N :=
  have hc := R.partitionCoeff_pos Ps P hK0 hε hεb hpc hψ hK hact hFc hFm hF hF0 hp0 hr0 i₀ htied
    I₀ hI₀ hne₀ hall hdeg hpos
  ⟨hc, (R.hasLeadingTerm_boltzmannIntegral_of_partition Ps P hK0 hε hεb hpc hψ hK hact hFc hFm
    hF).isEquivalent hc.ne'⟩

/-! ### The posterior limit -/

omit hFc hFm hF in
include hK0 hε hεb hpc hψ hK hact in
/-- The normalising coefficient along the partition. -/
noncomputable def partitionNormaliser (hp : Integrable p.w (volume.restrict (⋃ i, R.image i))) :
    ℝ :=
  R.partitionCoeff Ps P hK0 hε hεb hpc hψ hK hact (fun _ => continuousOn_const) measurable_const
    (R.integrable_one_mul_weight hp)

include hK0 hε hεb hpc hψ hK hact hFc hFm hF in
/-- ★ **The leading-order posterior expectation along a supplied partition of unity**: for any
admissible observable `F` (no sign condition), `p ≥ 0`, `r ≥ 0`, and a tied chart with an
all-minimal stratum whose dominant face (for `p ψ_{i₀}`, observable `1`) has positive measure,
`E_N[F] → partitionCoeff F / partitionCoeff 1`. -/
theorem tendsto_posteriorExpectation_of_partition
    (hp : Integrable p.w (volume.restrict (⋃ i, R.image i))) (hp0 : ∀ x, 0 ≤ p.w x)
    (hr0 : ∀ i x, 0 ≤ (Ps i).r x) (i₀ : ι)
    (htied : R.chartLam Ps hact i₀ = R.partitionLam Ps hact ∧
      R.chartDeg Ps hact i₀ = R.partitionDeg Ps hact)
    (I₀ : Finset (Fin d)) (hI₀ : I₀ ⊆ (Ps i₀).e.support) (hne₀ : I₀.Nonempty)
    (hall : ∀ j ∈ I₀, (Ps i₀).ratio j = R.chartLam Ps hact i₀)
    (hdeg : I₀.card - 1 = R.chartDeg Ps hact i₀)
    (hpos : 0 < volume ((Ps i₀).dominantFace (fun _ => (Ps i₀).e.support) ε I₀ hne₀
      (fun _ => (1 : ℝ)) (p.mulPartition P i₀))) :
    0 < R.partitionNormaliser Ps P hK0 hε hεb hpc hψ hK hact hp ∧
      (∀ᶠ N in atTop, 0 < R.boltzmannIntegral (fun _ => 1) K p N) ∧
      Tendsto (R.posteriorExpectation K p F) atTop
        (𝓝 (R.partitionCoeff Ps P hK0 hε hεb hpc hψ hK hact hFc hFm hF /
          R.partitionNormaliser Ps P hK0 hε hεb hpc hψ hK hact hp)) :=
  have hc₁ := R.partitionCoeff_pos Ps P hK0 hε hεb hpc hψ hK hact (fun _ => continuousOn_const)
    measurable_const (R.integrable_one_mul_weight hp) (fun _ => zero_le_one) hp0 hr0 i₀ htied I₀
    hI₀ hne₀ hall hdeg hpos
  ⟨hc₁, R.tendsto_posteriorExpectation_of_hasLeadingTerm
    (R.hasLeadingTerm_boltzmannIntegral_of_partition Ps P hK0 hε hεb hpc hψ hK hact hFc hFm hF)
    (R.hasLeadingTerm_boltzmannIntegral_of_partition Ps P hK0 hε hεb hpc hψ hK hact
      (fun _ => continuousOn_const) measurable_const (R.integrable_one_mul_weight hp)) hc₁⟩

end ResolutionCover

end Grammar
