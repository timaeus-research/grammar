/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.PartitionAssembly
import Grammar.LeadingTermConsequences

/-!
# Assembly along a supplied partition without the active-chart hypothesis (CCLXIX)

CCLXV assumed that every chart carries an active divisor coordinate. A chart `i` without one
(`supp e_i = ∅`) has no nonempty stratum, so its piece decomposition consists of the empty stratum
alone and its Boltzmann integral has the certificate with coefficient `0` at EVERY pair
(`hasLeadingTerm_boltzmannIntegral_of_no_activeV`, the variable-unit copy of CCXLIII's scalar
lemma) — no exponential estimate is needed. The assembly therefore runs over the active charts:

* `ProductMonomialChartVar.IsActive`, `activeCharts`, the per-chart pair `chartLam'`/`chartDeg'`
  (defined by cases), `partitionLam'`/`partitionDeg'` (extremal over the active charts),
  `partitionCoeff'` (sum over the tied active charts);
* ★ `hasLeadingTerm_boltzmannIntegral_of_partition'` (signed observable), positivity from one tied
  active chart (`partitionCoeff'_pos`), ★★ `boltzmannIntegral_isEquivalent_of_partition'`,
  ★ `tendsto_posteriorExpectation_of_partition'`, and the free energy
  (`tendsto_freeEnergy_of_partition'`);
* the all-inactive case: coefficient `0` at every pair
  (`hasLeadingTerm_boltzmannIntegral_of_all_inactive`).
-/

open MeasureTheory Set Filter Topology Asymptotics Monomialize.Analytic Monomialize.VolumeScaling

namespace Grammar

namespace ResolutionCover

variable {d : ℕ} {ι : Type*} [Fintype ι] (R : ResolutionCover d ι) {K : (Fin d → ℝ) → ℝ}

/-- **No active divisor coordinate**: the integral of a variable-unit product cover is negligible at
every power–log scale. -/
theorem hasLeadingTerm_boltzmannIntegral_of_no_activeV (Ps : ∀ i, ProductMonomialChartVar R i K)
    (hK0 : ∀ x, 0 ≤ K x) {ε : ℝ} (hε : 0 < ε) {F : (Fin d → ℝ) → ℝ} {p : TubeWeight d}
    (hFm : Measurable F)
    (hF : Integrable (fun x => F x * p.w x) (volume.restrict (⋃ i, R.image i))) (hK : Measurable K)
    (hno : ∀ i, (Ps i).e.support = ∅) (lam : ℝ) (k : ℕ) :
    HasLeadingTerm (R.boltzmannIntegral F K p) 0 lam k := by
  have h := R.hasLeadingTerm_boltzmannIntegral_of_monomial (fun i => (Ps i).e) (fun i => (Ps i).h)
    (fun i => (Ps i).W) (fun i => (Ps i).monomial) hε hFm hF hK hK0 (fun _ _ => 0) (fun _ _ => lam)
    (fun _ _ => k) lam k
    (fun i I hI => by
      rw [hno i, Finset.powerset_empty, Finset.filter_singleton] at hI
      simp only [Finset.not_nonempty_empty, if_false, Finset.notMem_empty] at hI)
    (fun _ _ _ => le_rfl) (fun _ _ _ _ => le_rfl)
  have hzero : (∑ i, ∑ I ∈ ((Ps i).e.support.powerset.filter (fun I => I.Nonempty)).filter
      (fun I => (fun _ _ => lam) i I = lam ∧ (fun _ _ => k) i I = k), (0 : ℝ)) = 0 := by
    simp only [Finset.sum_const_zero]
  rwa [hzero] at h

end ResolutionCover

/-- A variable-unit product chart is **active** when it has an active divisor coordinate. -/
def ProductMonomialChartVar.IsActive {d : ℕ} {ι : Type*} [Fintype ι] {R : ResolutionCover d ι}
    {i : ι} {K : (Fin d → ℝ) → ℝ} (P : ProductMonomialChartVar R i K) : Prop :=
  P.e.support.Nonempty

namespace ResolutionCover

variable {d : ℕ} {ι : Type*} [Fintype ι] (R : ResolutionCover d ι) {K : (Fin d → ℝ) → ℝ}
  (Ps : ∀ i, ProductMonomialChartVar (ofChart (R.chart i)) () K)

/-- The active coordinates of a one-chart cover are nonempty iff the chart is active. -/
theorem activeCoordsV_ofChart_nonempty_iff (i : ι) :
    ((ofChart (R.chart i)).activeCoordsV (fun _ => Ps i)).Nonempty ↔ (Ps i).IsActive := by
  unfold activeCoordsV ProductMonomialChartVar.IsActive
  constructor
  · rintro ⟨⟨_, j⟩, hj⟩
    exact ⟨j, (Finset.mem_sigma.1 hj).2⟩
  · rintro ⟨j, hj⟩
    exact ⟨⟨(), j⟩, Finset.mem_sigma.2 ⟨Finset.mem_univ _, hj⟩⟩

open scoped Classical in
/-- The active charts. -/
noncomputable def activeCharts : Finset ι := Finset.univ.filter fun i => (Ps i).IsActive

theorem mem_activeCharts {i : ι} : i ∈ R.activeCharts Ps ↔ (Ps i).IsActive := by
  unfold activeCharts
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

open scoped Classical in
/-- The extremal exponent of chart `i` (`0` for an inactive chart). -/
noncomputable def chartLam' (i : ι) : ℝ :=
  if h : (Ps i).IsActive then
    (ofChart (R.chart i)).coverLamV (fun _ => Ps i)
      ((R.activeCoordsV_ofChart_nonempty_iff Ps i).2 h)
  else 0

open scoped Classical in
/-- The extremal log degree of chart `i` (`0` for an inactive chart). -/
noncomputable def chartDeg' (i : ι) : ℕ :=
  if h : (Ps i).IsActive then
    (ofChart (R.chart i)).coverDegV (fun _ => Ps i)
      ((R.activeCoordsV_ofChart_nonempty_iff Ps i).2 h)
  else 0

theorem chartLam'_of_active {i : ι} (h : (Ps i).IsActive) :
    R.chartLam' Ps i = (ofChart (R.chart i)).coverLamV (fun _ => Ps i)
      ((R.activeCoordsV_ofChart_nonempty_iff Ps i).2 h) := by
  unfold chartLam'
  rw [dif_pos h]

theorem chartDeg'_of_active {i : ι} (h : (Ps i).IsActive) :
    R.chartDeg' Ps i = (ofChart (R.chart i)).coverDegV (fun _ => Ps i)
      ((R.activeCoordsV_ofChart_nonempty_iff Ps i).2 h) := by
  unfold chartDeg'
  rw [dif_pos h]

variable (P : SubordinatePartition R) (hK0 : ∀ x, 0 ≤ K x) {ε : ℝ} (hε : 0 < ε)
  (hεb : ∀ i, ε ≤ (Ps i).b) {p : TubeWeight d}
  (hpc : ∀ i, ContinuousOn (fun y => p.w ((R.chart i).φ y)) (Ps i).W)
  (hψ : ∀ i, ContinuousOn (fun y => P.ψ i ((R.chart i).φ y)) (Ps i).W) (hK : Measurable K)
  {F : (Fin d → ℝ) → ℝ} (hFc : ∀ i, ContinuousOn (fun y => F ((R.chart i).φ y)) (Ps i).W)
  (hFm : Measurable F) (hF : Integrable (fun x => F x * p.w x) (volume.restrict (⋃ i, R.image i)))

open scoped Classical in
include hK0 hε hεb hpc hψ hK hFc hFm hF in
/-- The coefficient of chart `i` at its extremal pair with prior `p ψ_i` (`0` if inactive). -/
noncomputable def chartCoeff' (i : ι) : ℝ :=
  if _ : (Ps i).IsActive then
    (ofChart (R.chart i)).productCoeffV (fun _ => Ps i) hK0 hε (fun _ => hεb i) (fun _ => hFc i)
      (fun _ => (hpc i).mul (hψ i)) hFm (R.integrable_mulPartition P i hF) hK
      (R.chartLam' Ps i) (R.chartDeg' Ps i)
  else 0

include hK0 hε hεb hpc hψ hK hFc hFm hF in
/-- The one-chart certificate of an active chart with prior `p ψ_i`. -/
theorem hasLeadingTerm_chart'_of_active {i : ι} (h : (Ps i).IsActive) :
    HasLeadingTerm ((ofChart (R.chart i)).boltzmannIntegral F K (p.mulPartition P i))
      (R.chartCoeff' Ps P hK0 hε hεb hpc hψ hK hFc hFm hF i) (R.chartLam' Ps i)
      (R.chartDeg' Ps i) := by
  unfold chartCoeff'
  rw [dif_pos h]
  have := (ofChart (R.chart i)).hasLeadingTerm_boltzmannIntegral_of_productChartsV_extremal
    (fun _ => Ps i) hK0 hε (fun _ => hεb i) (fun _ => hFc i) (fun _ => (hpc i).mul (hψ i)) hFm
    (R.integrable_mulPartition P i hF) hK ((R.activeCoordsV_ofChart_nonempty_iff Ps i).2 h)
  rw [chartLam'_of_active R Ps h, chartDeg'_of_active R Ps h]
  exact this

include hK0 hε hK hFm hF in
/-- An inactive chart has the zero certificate at every pair. -/
theorem hasLeadingTerm_chart'_of_inactive {i : ι} (h : ¬ (Ps i).IsActive) (lam : ℝ) (k : ℕ) :
    HasLeadingTerm ((ofChart (R.chart i)).boltzmannIntegral F K (p.mulPartition P i)) 0 lam k :=
  (ofChart (R.chart i)).hasLeadingTerm_boltzmannIntegral_of_no_activeV (fun _ => Ps i) hK0 hε hFm
    (R.integrable_mulPartition P i hF) hK
    (fun _ => Finset.not_nonempty_iff_eq_empty.1 h) lam k

/-! ### The extremal pair over the active charts -/

variable (hne : (R.activeCharts Ps).Nonempty)

/-- **The extremal exponent of the cover** over the active charts. -/
noncomputable def partitionLam' : ℝ := extremalExponent (R.activeCharts Ps) (R.chartLam' Ps) hne

/-- **The extremal log degree of the cover** over the active charts. -/
noncomputable def partitionDeg' : ℕ :=
  extremalDegree (R.activeCharts Ps) (R.chartLam' Ps) (R.chartDeg' Ps) hne

theorem partitionLam'_le {i : ι} (h : (Ps i).IsActive) :
    R.partitionLam' Ps hne ≤ R.chartLam' Ps i :=
  extremalExponent_le _ _ _ ((R.mem_activeCharts Ps).2 h)

theorem chartDeg'_le_partitionDeg' {i : ι} (h : (Ps i).IsActive)
    (hlam : R.chartLam' Ps i = R.partitionLam' Ps hne) :
    R.chartDeg' Ps i ≤ R.partitionDeg' Ps hne :=
  le_extremalDegree _ _ _ _ ((R.mem_activeCharts Ps).2 h) hlam

open scoped Classical in
/-- The tied active charts. -/
noncomputable def tiedCharts' : Finset ι :=
  (R.activeCharts Ps).filter fun i =>
    R.chartLam' Ps i = R.partitionLam' Ps hne ∧ R.chartDeg' Ps i = R.partitionDeg' Ps hne

include hK0 hε hεb hpc hψ hK hFc hFm hF in
/-- **The total coefficient**: the sum over the tied active charts. -/
noncomputable def partitionCoeff' : ℝ :=
  ∑ i ∈ R.tiedCharts' Ps hne, R.chartCoeff' Ps P hK0 hε hεb hpc hψ hK hFc hFm hF i

include hK0 hε hεb hpc hψ hK hFc hFm hF in
/-- ★ **The leading term along a supplied partition, active charts only** (signed observable). -/
theorem hasLeadingTerm_boltzmannIntegral_of_partition' :
    HasLeadingTerm (R.boltzmannIntegral F K p)
      (R.partitionCoeff' Ps P hK0 hε hεb hpc hψ hK hFc hFm hF hne) (R.partitionLam' Ps hne)
      (R.partitionDeg' Ps hne) := by
  classical
  -- the active charts, summed at the extremal pair
  have hact := hasLeadingTerm_sum_of_extremal (R.activeCharts Ps)
    (fun i N => (ofChart (R.chart i)).boltzmannIntegral F K (p.mulPartition P i) N)
    (R.chartCoeff' Ps P hK0 hε hεb hpc hψ hK hFc hFm hF) (R.chartLam' Ps) (R.chartDeg' Ps)
    (R.partitionLam' Ps hne) (R.partitionDeg' Ps hne)
    (fun i hi => R.hasLeadingTerm_chart'_of_active Ps P hK0 hε hεb hpc hψ hK hFc hFm hF
      ((R.mem_activeCharts Ps).1 hi))
    (fun i hi => R.partitionLam'_le Ps hne ((R.mem_activeCharts Ps).1 hi))
    (fun i hi hl => R.chartDeg'_le_partitionDeg' Ps hne ((R.mem_activeCharts Ps).1 hi) hl)
  -- the inactive charts, with zero certificates
  have hinact := HasLeadingTerm.sum (Finset.univ \ R.activeCharts Ps)
    (Z := fun i N => (ofChart (R.chart i)).boltzmannIntegral F K (p.mulPartition P i) N)
    (c := fun _ => (0 : ℝ)) (lam := R.partitionLam' Ps hne) (k := R.partitionDeg' Ps hne)
    fun i hi => R.hasLeadingTerm_chart'_of_inactive Ps P hK0 hε hK hFm hF
      (fun h => (Finset.mem_sdiff.1 hi).2 ((R.mem_activeCharts Ps).2 h)) _ _
  have htotal := hact.add hinact
  rw [Finset.sum_const_zero, add_zero] at htotal
  have hsplit : ∀ N, (∑ i ∈ R.activeCharts Ps,
      (ofChart (R.chart i)).boltzmannIntegral F K (p.mulPartition P i) N) +
      ∑ i ∈ Finset.univ \ R.activeCharts Ps,
        (ofChart (R.chart i)).boltzmannIntegral F K (p.mulPartition P i) N =
      ∑ i, (ofChart (R.chart i)).boltzmannIntegral F K (p.mulPartition P i) N := fun N =>
    Finset.sum_add_sum_compl (R.activeCharts Ps) _
  refine htotal.congr' ((eventually_ge_atTop 0).mono fun N hN => ?_)
  change (∑ i ∈ R.activeCharts Ps,
      (ofChart (R.chart i)).boltzmannIntegral F K (p.mulPartition P i) N) +
    ∑ i ∈ Finset.univ \ R.activeCharts Ps,
      (ofChart (R.chart i)).boltzmannIntegral F K (p.mulPartition P i) N = _
  rw [hsplit N, R.boltzmannIntegral_eq_sum_partition P hF hK hK0 hN]

/-! ### Nonnegativity, positivity, equivalence, posterior, free energy -/

include hK0 hε hεb hpc hψ hK hFc hFm hF in
theorem chartCoeff'_nonneg (hF0 : ∀ x, 0 ≤ F x) (hp0 : ∀ x, 0 ≤ p.w x)
    (hr0 : ∀ i x, 0 ≤ (Ps i).r x) (i : ι) :
    0 ≤ R.chartCoeff' Ps P hK0 hε hεb hpc hψ hK hFc hFm hF i := by
  unfold chartCoeff'
  split_ifs with h
  · unfold ResolutionCover.productCoeffV
    refine Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun I _ => ?_
    exact (ofChart (R.chart i)).leadingAtlasPieceCoeff_productAtlasesV_nonneg (fun _ => Ps i) hK0 hε
      (fun _ => hεb i) (fun _ => hFc i) (fun _ => (hpc i).mul (hψ i)) hFm
      (R.integrable_mulPartition P i hF) hK hF0
      (fun x => mul_nonneg (hp0 x) (P.nonneg i x)) (fun _ x => hr0 i x) _ _ j I
  · exact le_rfl

include hK0 hε hεb hpc hψ hK hFc hFm hF in
/-- **The total coefficient is positive** when some tied active chart `i₀` has an all-minimal
stratum at its pair whose dominant face (for the prior `p ψ_{i₀}`) has positive measure. -/
theorem partitionCoeff'_pos (hF0 : ∀ x, 0 ≤ F x) (hp0 : ∀ x, 0 ≤ p.w x)
    (hr0 : ∀ i x, 0 ≤ (Ps i).r x) (i₀ : ι) (hact₀ : (Ps i₀).IsActive)
    (htied : R.chartLam' Ps i₀ = R.partitionLam' Ps hne ∧
      R.chartDeg' Ps i₀ = R.partitionDeg' Ps hne)
    (I₀ : Finset (Fin d)) (hI₀ : I₀ ⊆ (Ps i₀).e.support) (hne₀ : I₀.Nonempty)
    (hall : ∀ j ∈ I₀, (Ps i₀).ratio j = R.chartLam' Ps i₀)
    (hdeg : I₀.card - 1 = R.chartDeg' Ps i₀)
    (hpos : 0 < volume ((Ps i₀).dominantFace (fun _ => (Ps i₀).e.support) ε I₀ hne₀ F
      (p.mulPartition P i₀))) :
    0 < R.partitionCoeff' Ps P hK0 hε hεb hpc hψ hK hFc hFm hF hne := by
  classical
  refine Finset.sum_pos'
    (fun i _ => R.chartCoeff'_nonneg Ps P hK0 hε hεb hpc hψ hK hFc hFm hF hF0 hp0 hr0 i)
    ⟨i₀, Finset.mem_filter.2 ⟨(R.mem_activeCharts Ps).2 hact₀, htied⟩, ?_⟩
  unfold chartCoeff'
  rw [dif_pos hact₀]
  exact (ofChart (R.chart i₀)).productCoeffV_pos (fun _ => Ps i₀) hK0 hε (fun _ => hεb i₀)
    (fun _ => hFc i₀) (fun _ => (hpc i₀).mul (hψ i₀)) hFm (R.integrable_mulPartition P i₀ hF)
    hK hF0 (fun x => mul_nonneg (hp0 x) (P.nonneg i₀ x)) (fun _ x => hr0 i₀ x) () I₀ hI₀ hne₀
    hall hdeg hpos

include hK0 hε hεb hpc hψ hK hFc hFm hF in
/-- ★★ **Asymptotic equivalence along a supplied partition of unity, active charts only.** -/
theorem boltzmannIntegral_isEquivalent_of_partition' (hF0 : ∀ x, 0 ≤ F x) (hp0 : ∀ x, 0 ≤ p.w x)
    (hr0 : ∀ i x, 0 ≤ (Ps i).r x) (i₀ : ι) (hact₀ : (Ps i₀).IsActive)
    (htied : R.chartLam' Ps i₀ = R.partitionLam' Ps hne ∧
      R.chartDeg' Ps i₀ = R.partitionDeg' Ps hne)
    (I₀ : Finset (Fin d)) (hI₀ : I₀ ⊆ (Ps i₀).e.support) (hne₀ : I₀.Nonempty)
    (hall : ∀ j ∈ I₀, (Ps i₀).ratio j = R.chartLam' Ps i₀)
    (hdeg : I₀.card - 1 = R.chartDeg' Ps i₀)
    (hpos : 0 < volume ((Ps i₀).dominantFace (fun _ => (Ps i₀).e.support) ε I₀ hne₀ F
      (p.mulPartition P i₀))) :
    0 < R.partitionCoeff' Ps P hK0 hε hεb hpc hψ hK hFc hFm hF hne ∧
      R.boltzmannIntegral F K p ~[atTop] fun N =>
        R.partitionCoeff' Ps P hK0 hε hεb hpc hψ hK hFc hFm hF hne *
          powLogScale (R.partitionLam' Ps hne) (R.partitionDeg' Ps hne) N :=
  have hc := R.partitionCoeff'_pos Ps P hK0 hε hεb hpc hψ hK hFc hFm hF hne hF0 hp0 hr0 i₀ hact₀
    htied I₀ hI₀ hne₀ hall hdeg hpos
  ⟨hc, (R.hasLeadingTerm_boltzmannIntegral_of_partition' Ps P hK0 hε hεb hpc hψ hK hFc hFm hF
    hne).isEquivalent hc.ne'⟩

include hK0 hε hεb hpc hψ hK hFc hFm hF in
/-- **The free energy along a supplied partition, active charts only.** -/
theorem tendsto_freeEnergy_of_partition' (hF0 : ∀ x, 0 ≤ F x) (hp0 : ∀ x, 0 ≤ p.w x)
    (hr0 : ∀ i x, 0 ≤ (Ps i).r x) (i₀ : ι) (hact₀ : (Ps i₀).IsActive)
    (htied : R.chartLam' Ps i₀ = R.partitionLam' Ps hne ∧
      R.chartDeg' Ps i₀ = R.partitionDeg' Ps hne)
    (I₀ : Finset (Fin d)) (hI₀ : I₀ ⊆ (Ps i₀).e.support) (hne₀ : I₀.Nonempty)
    (hall : ∀ j ∈ I₀, (Ps i₀).ratio j = R.chartLam' Ps i₀)
    (hdeg : I₀.card - 1 = R.chartDeg' Ps i₀)
    (hpos : 0 < volume ((Ps i₀).dominantFace (fun _ => (Ps i₀).e.support) ε I₀ hne₀ F
      (p.mulPartition P i₀))) :
    Tendsto (fun N => -Real.log (R.boltzmannIntegral F K p N) -
        (R.partitionLam' Ps hne * Real.log N - R.partitionDeg' Ps hne * Real.log (Real.log N)))
      atTop (𝓝 (-Real.log (R.partitionCoeff' Ps P hK0 hε hεb hpc hψ hK hFc hFm hF hne))) :=
  (R.hasLeadingTerm_boltzmannIntegral_of_partition' Ps P hK0 hε hεb hpc hψ hK hFc hFm hF
    hne).tendsto_neg_log
    (R.partitionCoeff'_pos Ps P hK0 hε hεb hpc hψ hK hFc hFm hF hne hF0 hp0 hr0 i₀ hact₀ htied I₀
      hI₀ hne₀ hall hdeg hpos)

omit hFc hFm hF in
include hK0 hε hεb hpc hψ hK in
/-- The normalising coefficient along the partition, active charts only. -/
noncomputable def partitionNormaliser' (hp : Integrable p.w (volume.restrict (⋃ i, R.image i))) :
    ℝ :=
  R.partitionCoeff' Ps P hK0 hε hεb hpc hψ hK (fun _ => continuousOn_const) measurable_const
    (R.integrable_one_mul_weight hp) hne

include hK0 hε hεb hpc hψ hK hFc hFm hF in
/-- ★ **The leading-order posterior expectation along a supplied partition, active charts only.** -/
theorem tendsto_posteriorExpectation_of_partition'
    (hp : Integrable p.w (volume.restrict (⋃ i, R.image i))) (hp0 : ∀ x, 0 ≤ p.w x)
    (hr0 : ∀ i x, 0 ≤ (Ps i).r x) (i₀ : ι) (hact₀ : (Ps i₀).IsActive)
    (htied : R.chartLam' Ps i₀ = R.partitionLam' Ps hne ∧
      R.chartDeg' Ps i₀ = R.partitionDeg' Ps hne)
    (I₀ : Finset (Fin d)) (hI₀ : I₀ ⊆ (Ps i₀).e.support) (hne₀ : I₀.Nonempty)
    (hall : ∀ j ∈ I₀, (Ps i₀).ratio j = R.chartLam' Ps i₀)
    (hdeg : I₀.card - 1 = R.chartDeg' Ps i₀)
    (hpos : 0 < volume ((Ps i₀).dominantFace (fun _ => (Ps i₀).e.support) ε I₀ hne₀
      (fun _ => (1 : ℝ)) (p.mulPartition P i₀))) :
    0 < R.partitionNormaliser' Ps P hK0 hε hεb hpc hψ hK hne hp ∧
      (∀ᶠ N in atTop, 0 < R.boltzmannIntegral (fun _ => 1) K p N) ∧
      Tendsto (R.posteriorExpectation K p F) atTop
        (𝓝 (R.partitionCoeff' Ps P hK0 hε hεb hpc hψ hK hFc hFm hF hne /
          R.partitionNormaliser' Ps P hK0 hε hεb hpc hψ hK hne hp)) :=
  have hc₁ := R.partitionCoeff'_pos Ps P hK0 hε hεb hpc hψ hK (fun _ => continuousOn_const)
    measurable_const (R.integrable_one_mul_weight hp) hne (fun _ => zero_le_one) hp0 hr0 i₀ hact₀
    htied I₀ hI₀ hne₀ hall hdeg hpos
  ⟨hc₁, R.tendsto_posteriorExpectation_of_hasLeadingTerm
    (R.hasLeadingTerm_boltzmannIntegral_of_partition' Ps P hK0 hε hεb hpc hψ hK hFc hFm hF hne)
    (R.hasLeadingTerm_boltzmannIntegral_of_partition' Ps P hK0 hε hεb hpc hψ hK
      (fun _ => continuousOn_const) measurable_const (R.integrable_one_mul_weight hp) hne) hc₁⟩

omit hne in
include P hK0 hε hK hFm hF in
/-- **All charts inactive**: the integral is negligible at every power–log scale. -/
theorem hasLeadingTerm_boltzmannIntegral_of_all_inactive (hno : ∀ i, ¬ (Ps i).IsActive)
    (lam : ℝ) (k : ℕ) : HasLeadingTerm (R.boltzmannIntegral F K p) 0 lam k := by
  have h := HasLeadingTerm.sum Finset.univ
    (Z := fun i N => (ofChart (R.chart i)).boltzmannIntegral F K (p.mulPartition P i) N)
    (c := fun _ => (0 : ℝ)) (lam := lam) (k := k)
    fun i _ => R.hasLeadingTerm_chart'_of_inactive Ps P hK0 hε hK hFm hF (hno i) lam k
  rw [Finset.sum_const_zero] at h
  exact h.congr' ((eventually_ge_atTop 0).mono fun N hN =>
    (R.boltzmannIntegral_eq_sum_partition P hF hK hK0 hN).symm)

end ResolutionCover

end Grammar
