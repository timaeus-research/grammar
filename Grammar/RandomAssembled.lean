/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.ChartAllocation
import Grammar.RandomNextLogFreeEnergy

/-!
# One joint random assembled law

Generic finite-chart setting on a Polish common data space `P`: chart evidences `Z i N x`
(measurable in `x`), exponents `lam i`, multiplicities `mult i`, continuous coefficients `F i`,
`B i`, and the compact-uniform two-term expansions of every chart on every compact set.  On the
Polish admissible domain `{A > 0}` the vector statistic

  `T_N(x) = (log N (G_N − A), −log N (log G_N − log A), (log N (p_{i,N} − a_i/A))_i)`

(assembled evidence remainder, assembled free-energy correction, chart-allocation corrections)
converges continuously to `(D₁, −D₁/A, (h_i)_i)` (`continuouslyConverges_assembledMixedStat`), and
for random data `X_m ⇒ X` on the admissible domain and `N_m → ∞`,
`(X_m, T_{N_m}(X_m)) ⇒ (X, T(X))` (`randomAssembled_graphLaw_tendsto`) — the joint random
assembled law, retaining the entire common datum.

Non-claims: joint convergence of the chart data is the hypothesis (marginals are insufficient); no
independence; no statement when the total leading coefficient vanishes; expectations only under the
uniform-integrability hypothesis of CIII.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

/-- Uniform convergence of finite vectors is coordinatewise (any index filter). -/
theorem tendstoUniformlyOn_pi_of_forall' {α P ι : Type*} [Fintype ι] {p : Filter α} {K : Set P}
    {F : α → P → ι → ℝ} {f : P → ι → ℝ}
    (h : ∀ i, TendstoUniformlyOn (fun a x => F a x i) (fun x => f x i) p K) :
    TendstoUniformlyOn F f p K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have := fun i => Metric.tendstoUniformlyOn_iff.1 (h i) ε hε
  filter_upwards [Filter.eventually_all.2 this] with a ha x hx
  exact (dist_pi_lt_iff hε).2 fun i => ha i x hx

section assembledRandom

variable {ι : Type*} [Fintype ι] {P : Type*} [MetricSpace P] [CompleteSpace P]
  [SecondCountableTopology P] [MeasurableSpace P] [BorelSpace P]
  (Z : ι → ℝ → P → ℝ) (lam : ι → ℝ) (mult : ι → ℕ) (F B : ι → P → ℝ) {l : ℝ} {m : ℕ}

/-- The admissible domain of the assembled model, `{A > 0}`. -/
def AssembledAdmissible : Type _ := {x : P // 0 < assembledLead lam mult F l m x}

noncomputable instance : MetricSpace (AssembledAdmissible lam mult F (l := l) (m := m)) :=
  Subtype.metricSpace
noncomputable instance : MeasurableSpace (AssembledAdmissible lam mult F (l := l) (m := m)) :=
  Subtype.instMeasurableSpace
instance : BorelSpace (AssembledAdmissible lam mult F (l := l) (m := m)) := Subtype.borelSpace _

/-- The joint assembled statistic: evidence remainder, free-energy correction, allocation
corrections. -/
noncomputable def assembledMixedStat (N : ℝ)
    (x : AssembledAdmissible lam mult F (l := l) (m := m)) : Fin 2 ⊕ ι → ℝ :=
  Sum.elim ![Real.log N * (assembledScaled Z l m N x.1 - assembledLead lam mult F l m x.1),
    -(Real.log N * (Real.log (assembledScaled Z l m N x.1) -
      Real.log (assembledLead lam mult F l m x.1)))]
    fun i => Real.log N * (chartAlloc Z i N x.1 - chartAllocLead lam mult F (l := l) (m := m) i x.1)

/-- The vector of limits `(D₁, −D₁/A, (h_i)_i)`. -/
noncomputable def assembledMixedLimit (x : AssembledAdmissible lam mult F (l := l) (m := m)) :
    Fin 2 ⊕ ι → ℝ :=
  Sum.elim ![assembledCorrection lam mult F B l m x.1,
    -(assembledCorrection lam mult F B l m x.1 / assembledLead lam mult F l m x.1)]
    fun i => chartAllocCorrection lam mult F B (l := l) (m := m) i x.1

variable (hFc : ∀ i, Continuous (F i)) (hBc : ∀ i, Continuous (B i))

include hFc in
theorem polishSpace_assembledAdmissible :
    PolishSpace (AssembledAdmissible lam mult F (l := l) (m := m)) :=
  (isOpen_lt continuous_const (continuous_assembledLead lam mult hFc l m)).polishSpace

include hFc hBc in
theorem continuous_assembledMixedLimit :
    Continuous (assembledMixedLimit lam mult F B (l := l) (m := m)) := by
  have hA : Continuous fun x : AssembledAdmissible lam mult F (l := l) (m := m) =>
      assembledLead lam mult F l m x.1 :=
    (continuous_assembledLead lam mult hFc l m).comp continuous_subtype_val
  have hD : Continuous fun x : AssembledAdmissible lam mult F (l := l) (m := m) =>
      assembledCorrection lam mult F B l m x.1 :=
    (continuous_assembledCorrection lam mult hFc hBc l m).comp continuous_subtype_val
  refine continuous_pi fun i => ?_
  rcases i with i | i
  · fin_cases i
    · exact hD
    · exact (hD.div hA fun x => x.2.ne').neg
  · change Continuous fun x : AssembledAdmissible lam mult F (l := l) (m := m) =>
      chartAllocCorrection lam mult F B (l := l) (m := m) i x.1
    unfold chartAllocCorrection
    exact (Continuous.div ((((continuous_chartSecond lam mult hFc hBc i).comp
      continuous_subtype_val).mul hA).sub (((continuous_chartLead lam mult hFc i).comp
        continuous_subtype_val).mul hD)) (hA.pow 2) fun x => pow_ne_zero _ x.2.ne')

variable (hZm : ∀ i N, Measurable (Z i N))

include hZm hFc in
theorem measurable_assembledMixedStat (N : ℝ) :
    Measurable (assembledMixedStat Z lam mult F (l := l) (m := m) N) := by
  have hG : Measurable fun x : P => assembledScaled Z l m N x := by
    unfold assembledScaled
    exact (Finset.measurable_sum _ fun i _ => hZm i N).div_const _
  have hA := (continuous_assembledLead lam mult hFc l m).measurable
  refine measurable_pi_iff.2 fun i => ?_
  rcases i with i | i
  · fin_cases i
    · exact (measurable_const.mul (hG.sub hA)).comp measurable_subtype_coe
    · exact (measurable_const.mul ((Real.measurable_log.comp hG).sub
        (Real.measurable_log.comp hA))).neg.comp measurable_subtype_coe
  · change Measurable fun x : AssembledAdmissible lam mult F (l := l) (m := m) => Real.log N *
      (chartAlloc Z i N x.1 - chartAllocLead lam mult F (l := l) (m := m) i x.1)
    unfold chartAlloc chartAllocLead
    exact (measurable_const.mul (((hZm i N).div (Finset.measurable_sum _ fun j _ => hZm j N)).sub
      ((continuous_chartLead lam mult hFc i).measurable.div hA))).comp measurable_subtype_coe

variable (hl : ∀ i, l ≤ lam i) (hm : ∀ i, lam i = l → mult i ≤ m) (hm1 : ∀ i, 1 ≤ mult i)
  (hlead : ∀ K : Set P, IsCompact K → ∀ i, TendstoUniformlyOn (fun N x => Z i N x /
    (N ^ (-lam i) * Real.log N ^ (mult i - 1))) (F i) atTop K)
  (htwo : ∀ K : Set P, IsCompact K → ∀ i, lam i = l → mult i = m →
    TendstoUniformlyOn (fun N x => Real.log N *
      (Z i N x / (N ^ (-l) * Real.log N ^ (m - 1)) - F i x)) (B i) atTop K)
  (Nseq : ℕ → ℝ) (hN1 : ∀ m, 1 < Nseq m) (hN : Tendsto Nseq atTop atTop)

include hFc hBc hl hm hm1 hlead htwo hN in
/-- **Continuous convergence of the joint assembled statistic** on the admissible domain. -/
theorem continuouslyConverges_assembledMixedStat :
    ContinuouslyConverges (fun j => assembledMixedStat Z lam mult F (l := l) (m := m) (Nseq j))
      (assembledMixedLimit lam mult F B (l := l) (m := m)) := by
  refine continuouslyConverges_of_tendstoUniformlyOn_compacts
    (continuous_assembledMixedLimit lam mult F B hFc hBc) fun K hK => ?_
  have hK' : IsCompact (Subtype.val '' K) := hK.image continuous_subtype_val
  have hpos : ∀ x ∈ Subtype.val '' K, 0 < assembledLead lam mult F l m x := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  -- the three families on the image, then pulled back
  have hE := tendstoUniformlyOn_assembled Z lam mult F B hl hm hm1 hFc hK' (hlead _ hK')
    (htwo _ hK')
  have hFE : TendstoUniformlyOn (fun N x => -(Real.log N * (Real.log (assembledScaled Z l m N x) -
      Real.log (assembledLead lam mult F l m x))))
      (fun x => -(assembledCorrection lam mult F B l m x / assembledLead lam mult F l m x)) atTop
      (Subtype.val '' K) := by
    rcases (Subtype.val '' K).eq_empty_or_nonempty with hKe | hKne
    · rw [hKe]
      simp [TendstoUniformlyOn]
    obtain ⟨MB, hMB⟩ := hK'.exists_bound_of_continuousOn
      (continuous_assembledCorrection lam mult hFc hBc l m).continuousOn
    obtain ⟨x₀, hx₀, hmin₀⟩ :=
      hK'.exists_isMinOn hKne (continuous_assembledLead lam mult hFc l m).continuousOn
    exact (tendstoUniformlyOn_nextLog_log hE (fun x hx => (Real.norm_eq_abs _).symm.trans_le
      (hMB x hx)) (hpos x₀ hx₀) fun x hx => hmin₀ hx).neg
  have hP := tendstoUniformlyOn_chartAlloc_pi Z lam mult F B hl hm hm1 hFc hK' (hlead _ hK')
    (htwo _ hK') hBc hpos
  refine tendstoUniformlyOn_pi_of_forall' fun i => ?_
  rcases i with i | i
  · fin_cases i
    · exact (tendstoUniformlyOn_comp_seq hE hN).comp Subtype.val |>.mono
        (Set.subset_preimage_image _ _)
    · exact (tendstoUniformlyOn_comp_seq hFE hN).comp Subtype.val |>.mono
        (Set.subset_preimage_image _ _)
  · exact (tendstoUniformlyOn_comp_seq (tendstoUniformlyOn_chartAlloc Z lam mult F B hl hm hm1 hFc
      hK' (hlead _ hK') (htwo _ hK') hBc hpos i) hN).comp Subtype.val |>.mono
        (Set.subset_preimage_image _ _)

include hFc hBc hZm hl hm hm1 hlead htwo hN in
/-- **The joint random assembled law**: for random data `X_m ⇒ X` on the Polish admissible domain
`{A > 0}` and `N_m → ∞`, the assembled evidence remainder, the assembled free-energy correction and
all chart-allocation corrections converge jointly with the data,
`(X_m, T_{N_m}(X_m)) ⇒ (X, (D₁, −D₁/A, (h_i)_i)(X))`. -/
theorem randomAssembled_graphLaw_tendsto
    {μ : ℕ → ProbabilityMeasure (AssembledAdmissible lam mult F (l := l) (m := m))}
    {μ₀ : ProbabilityMeasure (AssembledAdmissible lam mult F (l := l) (m := m))}
    (hμ : Tendsto μ atTop (𝓝 μ₀)) :
    Tendsto (fun j => graphLaw (μ j)
        (measurable_assembledMixedStat Z lam mult F hFc hZm (Nseq j))) atTop
      (𝓝 (graphLaw μ₀ (continuous_assembledMixedLimit lam mult F B hFc hBc).measurable)) :=
  haveI := polishSpace_assembledAdmissible lam mult F (l := l) (m := m) hFc
  tendsto_graphLaw_of_continuouslyConverges hμ (tight_of_tendsto_polish hμ)
    (fun j => measurable_assembledMixedStat Z lam mult F hFc hZm (Nseq j))
    (continuouslyConverges_assembledMixedStat Z lam mult F B hFc hBc hl hm hm1 hlead htwo Nseq hN)

end assembledRandom

end Grammar
