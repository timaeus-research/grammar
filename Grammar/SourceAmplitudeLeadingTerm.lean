/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SourceAmplitudeBridge
import Grammar.LeadingTermNegligible

/-!
# The leading term of a source-weighted chart integral (CCLXXV)

For a chart `i` of a cover and a source amplitude `G` (measurable, continuous on the chart domain)
the **source chart integral** is
`∫ y, w_i(N)(y) · G(y) = ∫_{dom_i} |det Dφ_i| · ρ_i(φ_i y) · p(φ_i y) · G(y) · e^{−N K(φ_i y)} dy`
(`sourceChartIntegral`; for a one-chart cover the weight `ρ` is `1`, `ofChart_sourceChartIntegral`).
It is the sum of its source-weighted stratum pieces plus the divisor-free piece
(`sourceChartIntegral_eq_sum_pieces`), the divisor-free piece is negligible at every scale on a
monomial chart (`hasLeadingTerm_sourcePieceIntegral_empty_of_monomial`), and a family of leading
atlases of the nonempty pieces gives the leading term
(`hasLeadingTerm_sourceChartIntegral_of_leadingAtlases`).

For a one-chart variable-unit product package `P` (consult #85 unit 2, second half):

* `P.sourceCoeff G lam₀ k₀`: the sum over the strata of the tied cell coefficients of the chosen
  source-weighted atlases;
* ★ `hasLeadingTerm_sourceChartIntegral`: the **zero-compatible expansion**
  `∫ … G … = sourceCoeff · N^{−λ₀}(log N)^{k₀} + o(·)` at any pair dominating every stratum pair, in
  particular at the extremal pair `(λ*, k*)` of the chart (`_extremal`);
* `sourceCoeff_nonneg` (for `G, p, r ≥ 0`), ★ `sourceCoeff_pos` when an all-minimal stratum at the
  pair has a source dominant face of positive measure, and the equivalence
  `sourceChartIntegral_isEquivalent`;
* compatibility: with `G = F ∘ Φ` the source chart integral is the one-chart Boltzmann integral of
  `F` (`sourceChartIntegral_pullback`) and the source coefficient is `productCoeffV`
  (`sourceCoeff_pullback`), by uniqueness of certificates.

The coefficient may vanish (localisation amplitudes vanish on many faces); positivity is a separate
hypothesis at the extremal pair, selected before any zero coefficient is discarded.
-/

open MeasureTheory Set Filter Topology Asymptotics Monomialize.Analytic Monomialize.VolumeScaling

namespace Grammar

namespace ResolutionCover

variable {d : ℕ} {ι : Type*} [Fintype ι] (R : ResolutionCover d ι) (i : ι)
  {G K : (Fin d → ℝ) → ℝ} {p : TubeWeight d}

/-- **The source-weighted chart integral** `∫ w_i(N) · G` (the chart density at `N` includes the
domain indicator, the Jacobian, the cover weight, the prior and the Boltzmann factor). -/
noncomputable def sourceChartIntegral (G K : (Fin d → ℝ) → ℝ) (p : TubeWeight d) (N : ℝ) : ℝ :=
  ∫ y, R.boltzmannChartDensity i N K p y * G y

/-- The chart density at `N` times a source amplitude is integrable. -/
theorem integrable_boltzmannChartDensity_mul_source (hGm : Measurable G)
    (hGc : ContinuousOn G (R.chart i).dom) (hK : Measurable K) (hK0 : ∀ x, 0 ≤ K x) {N : ℝ}
    (hN : 0 ≤ N) : Integrable fun y => R.boltzmannChartDensity i N K p y * G y := by
  obtain ⟨C, hC⟩ := (R.chart i).dom_compact.exists_bound_of_continuousOn hGc
  have h := (R.integrable_boltzmannChartDensity_zero_mul_source i (p := p) hGm
    (fun y hy => (Real.norm_eq_abs _).symm.trans_le (hC y hy)) hK hK0).bdd_mul (c := 1)
    (f := fun y => Real.exp (-N * K ((R.chart i).Φ y)))
    (Real.measurable_exp.comp (measurable_const.mul
      (hK.comp (R.measurable_chart_Φ i)))).aestronglyMeasurable
    (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff, neg_mul]
      exact neg_nonpos.2 (mul_nonneg hN (hK0 _)))
  refine h.congr (Eventually.of_forall fun y => ?_)
  beta_reduce
  rw [R.boltzmannChartDensity_eq_exp_mul i N K p y]
  ring

/-- **The source chart integral is the sum of its stratum pieces plus the divisor-free piece.** -/
theorem sourceChartIntegral_eq_sum_pieces (D : ι → Finset (Fin d)) (ε : ℝ) (hGm : Measurable G)
    (hGc : ContinuousOn G (R.chart i).dom) (hK : Measurable K) (hK0 : ∀ x, 0 ≤ K x) {N : ℝ}
    (hN : 0 ≤ N) :
    R.sourceChartIntegral i G K p N =
      (∑ I ∈ (D i).powerset.filter (fun I => I.Nonempty),
        R.sourcePieceIntegral D ε i I G K p N) + R.sourcePieceIntegral D ε i ∅ G K p N :=
  integral_eq_sum_pieces_nonempty_add (D i) (ε := ε)
    (R.chartWeight i (TubeWeight.boltzmann N hN K hK hK0 p)) (F := G)
    (R.integrable_boltzmannChartDensity_mul_source i hGm hGc hK hK0 hN)

/-- Source amplitudes agreeing on the chart domain have the same piece integrals. -/
theorem sourcePieceIntegral_congr_dom (D : ι → Finset (Fin d)) (ε : ℝ) (I : Finset (Fin d))
    {G' : (Fin d → ℝ) → ℝ} (hGG' : ∀ y ∈ (R.chart i).dom, G y = G' y) (N : ℝ) :
    R.sourcePieceIntegral D ε i I G K p N = R.sourcePieceIntegral D ε i I G' K p N := by
  unfold sourcePieceIntegral
  refine setIntegral_congr_fun (measurableSet_sizePiece (D i) ε I) fun y _ => ?_
  by_cases hy : y ∈ (R.chart i).dom
  · rw [hGG' y hy]
  · have h0 : R.boltzmannChartDensity i N K p y = 0 := by
      unfold boltzmannChartDensity
      rw [indicator_of_notMem hy]
    rw [h0, zero_mul, zero_mul]

/-- Source amplitudes agreeing on the chart domain have the same chart integral. -/
theorem sourceChartIntegral_congr_dom {G' : (Fin d → ℝ) → ℝ}
    (hGG' : ∀ y ∈ (R.chart i).dom, G y = G' y) (N : ℝ) :
    R.sourceChartIntegral i G K p N = R.sourceChartIntegral i G' K p N := by
  unfold sourceChartIntegral
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  beta_reduce
  by_cases hy : y ∈ (R.chart i).dom
  · rw [hGG' y hy]
  · have h0 : R.boltzmannChartDensity i N K p y = 0 := by
      unfold boltzmannChartDensity
      rw [indicator_of_notMem hy]
    rw [h0, zero_mul, zero_mul]

/-! ### The divisor-free piece -/

variable (D : ι → Finset (Fin d)) (ε : ℝ) (I : Finset (Fin d))

/-- **The exponential bound on a source-weighted piece with phase `≥ δ`.** -/
theorem abs_sourcePieceIntegral_le_exp (hGm : Measurable G)
    (hGc : ContinuousOn G (R.chart i).dom) (hK : Measurable K) (hK0 : ∀ x, 0 ≤ K x) {δ : ℝ}
    (hδK : ∀ y ∈ (R.chart i).dom ∩ sizePiece (D i) ε I, δ ≤ K ((R.chart i).φ y)) {N : ℝ}
    (hN : 0 ≤ N) :
    |R.sourcePieceIntegral D ε i I G K p N| ≤
      (∫ y in sizePiece (D i) ε I, |R.boltzmannChartDensity i 0 K p y * G y|) *
        Real.exp (-δ * N) := by
  obtain ⟨C, hC⟩ := (R.chart i).dom_compact.exists_bound_of_continuousOn hGc
  have hint := R.integrable_boltzmannChartDensity_zero_mul_source i (p := p) hGm
    (fun y hy => (Real.norm_eq_abs _).symm.trans_le (hC y hy)) hK hK0
  unfold sourcePieceIntegral
  refine abs_integral_le_integral_abs.trans ?_
  rw [mul_comm, ← integral_const_mul]
  refine integral_mono_of_nonneg (Eventually.of_forall fun y => abs_nonneg _)
    (hint.abs.integrableOn.const_mul _) ?_
  refine (ae_restrict_iff' (measurableSet_sizePiece (D i) ε I)).2
    (Eventually.of_forall fun y hy => ?_)
  beta_reduce
  rw [R.boltzmannChartDensity_eq_exp_mul i N K p y, mul_assoc, abs_mul,
    abs_of_pos (Real.exp_pos _)]
  by_cases hdom : y ∈ (R.chart i).dom
  · refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    rw [Real.exp_le_exp, (R.chart i).Φ_eqOn hdom]
    have h := hδK y ⟨hdom, hy⟩
    nlinarith
  · have h0 : R.boltzmannChartDensity i 0 K p y = 0 := by
      unfold boltzmannChartDensity
      rw [indicator_of_notMem hdom]
    rw [h0, zero_mul, abs_zero, mul_zero, mul_zero]

/-- **A source-weighted piece on which the phase is bounded below is negligible at every scale.** -/
theorem hasLeadingTerm_sourcePieceIntegral_zero_of_phase_bound (hGm : Measurable G)
    (hGc : ContinuousOn G (R.chart i).dom) (hK : Measurable K) (hK0 : ∀ x, 0 ≤ K x) {δ : ℝ}
    (hδ : 0 < δ) (hδK : ∀ y ∈ (R.chart i).dom ∩ sizePiece (D i) ε I, δ ≤ K ((R.chart i).φ y))
    (lam : ℝ) (k : ℕ) : HasLeadingTerm (R.sourcePieceIntegral D ε i I G K p) 0 lam k :=
  HasLeadingTerm.of_exp_bound hδ ((eventually_ge_atTop 0).mono fun _ hN =>
    R.abs_sourcePieceIntegral_le_exp i D ε I hGm hGc hK hK0 hδK hN) lam k

/-- **The divisor-free source-weighted piece of a monomial chart is negligible at every scale.** -/
theorem hasLeadingTerm_sourcePieceIntegral_empty_of_monomial {e h : Fin d →₀ ℕ}
    {W : Set (Fin d → ℝ)} (hc : IsMonomialChart K (R.chart i).φ (R.chart i).dom e h W)
    (hD : D i = e.support) (hε : 0 < ε) (hGm : Measurable G)
    (hGc : ContinuousOn G (R.chart i).dom) (hK : Measurable K) (hK0 : ∀ x, 0 ≤ K x) (lam : ℝ)
    (k : ℕ) : HasLeadingTerm (R.sourcePieceIntegral D ε i ∅ G K p) 0 lam k := by
  obtain ⟨δ, hδ, hδK⟩ :=
    IsMonomialChart.exists_phase_lower_bound_divisorFree hc (R.chart i).dom_compact hK0 hε
  refine R.hasLeadingTerm_sourcePieceIntegral_zero_of_phase_bound i D ε ∅ hGm hGc hK hK0 hδ ?_
    lam k
  rw [hD]
  exact hδK

/-! ### The one-chart assembly over leading atlases -/

/-- The tied coefficient selector of a family of piece atlases of one chart. -/
noncomputable def sourceAtlasPieceCoeff {e : Fin d →₀ ℕ} {Z : Finset (Fin d) → ℝ → ℝ}
    (At : ∀ I : Finset (Fin d), I ⊆ e.support → I.Nonempty → FiniteLeadingAtlas (Z I))
    (lam₀ : ℝ) (k₀ : ℕ) (I : Finset (Fin d)) : ℝ :=
  open scoped Classical in
  if hI : I ⊆ e.support ∧ I.Nonempty then
    ∑ j ∈ (At I hI.1 hI.2).tied lam₀ k₀, ((At I hI.1 hI.2).cell j).coeff
  else 0

theorem sourceAtlasPieceCoeff_of_mem {e : Fin d →₀ ℕ} {Z : Finset (Fin d) → ℝ → ℝ}
    (At : ∀ I : Finset (Fin d), I ⊆ e.support → I.Nonempty → FiniteLeadingAtlas (Z I))
    (lam₀ : ℝ) (k₀ : ℕ) (I : Finset (Fin d)) (hI : I ⊆ e.support) (hne : I.Nonempty) :
    sourceAtlasPieceCoeff At lam₀ k₀ I =
      ∑ j ∈ (At I hI hne).tied lam₀ k₀, ((At I hI hne).cell j).coeff :=
  dif_pos ⟨hI, hne⟩

/-- **The leading term of a source chart integral from leading atlases of its nonempty pieces**,
at a pair dominating every cell: coefficient the sum of the tied cell coefficients. -/
theorem hasLeadingTerm_sourceChartIntegral_of_leadingAtlases (e h : Fin d →₀ ℕ)
    {W : Set (Fin d → ℝ)} (hc : IsMonomialChart K (R.chart i).φ (R.chart i).dom e h W)
    (hε : 0 < ε) (hGm : Measurable G) (hGc : ContinuousOn G (R.chart i).dom) (hK : Measurable K)
    (hK0 : ∀ x, 0 ≤ K x)
    (At : ∀ I : Finset (Fin d), I ⊆ e.support → I.Nonempty →
      FiniteLeadingAtlas (R.sourcePieceIntegral (fun _ => e.support) ε i I G K p))
    (lam₀ : ℝ) (k₀ : ℕ)
    (hlam : ∀ (I : Finset (Fin d)) (hI : I ⊆ e.support) (hne : I.Nonempty) (j : (At I hI hne).ι),
      lam₀ ≤ ((At I hI hne).cell j).lam)
    (hk : ∀ (I : Finset (Fin d)) (hI : I ⊆ e.support) (hne : I.Nonempty) (j : (At I hI hne).ι),
      ((At I hI hne).cell j).lam = lam₀ → ((At I hI hne).cell j).mult - 1 ≤ k₀) :
    HasLeadingTerm (R.sourceChartIntegral i G K p)
      (∑ I ∈ e.support.powerset.filter (fun I => I.Nonempty),
        sourceAtlasPieceCoeff At lam₀ k₀ I) lam₀ k₀ := by
  have hpieces : HasLeadingTerm (fun N => ∑ I ∈ e.support.powerset.filter (fun I => I.Nonempty),
      R.sourcePieceIntegral (fun _ => e.support) ε i I G K p N)
      (∑ I ∈ e.support.powerset.filter (fun I => I.Nonempty),
        sourceAtlasPieceCoeff At lam₀ k₀ I) lam₀ k₀ :=
    HasLeadingTerm.sum _ fun I hI => by
      obtain ⟨hpow, hne⟩ := Finset.mem_filter.1 hI
      have hsub : I ⊆ e.support := Finset.mem_powerset.1 hpow
      rw [sourceAtlasPieceCoeff_of_mem At lam₀ k₀ I hsub hne]
      exact (At I hsub hne).hasLeadingTerm_of_extremal lam₀ k₀ (hlam I hsub hne) (hk I hsub hne)
  have hempty := R.hasLeadingTerm_sourcePieceIntegral_empty_of_monomial i (p := p)
    (fun _ => e.support) ε hc rfl hε hGm hGc hK hK0 lam₀ k₀
  have h := hpieces.add hempty
  rw [add_zero] at h
  refine h.congr' ((eventually_ge_atTop 0).mono fun N hN => ?_)
  exact (R.sourceChartIntegral_eq_sum_pieces i (fun _ => e.support) ε hGm hGc hK hK0 hN).symm

end ResolutionCover

/-! ### The one-chart source chart integral -/

namespace ResolutionCover

variable {d : ℕ} (C : ResolutionChart d) {G K : (Fin d → ℝ) → ℝ} {p : TubeWeight d}

/-- **The one-chart source integral in explicit form**: the cover weight is `1`. -/
theorem ofChart_sourceChartIntegral (G K : (Fin d → ℝ) → ℝ) (p : TubeWeight d) (N : ℝ) :
    (ofChart C).sourceChartIntegral () G K p N =
      ∫ y in C.dom, G y * C.jac y * p.w (C.φ y) * Real.exp (-N * K (C.φ y)) := by
  unfold sourceChartIntegral boltzmannChartDensity
  have : (fun y => (C.dom.indicator fun y => C.jac y * ((ofChart C).weight () (C.Φ y) *
      (Real.exp (-N * K (C.Φ y)) * p.w (C.Φ y)))) y * G y) =
      C.dom.indicator fun y => G y * C.jac y * p.w (C.φ y) * Real.exp (-N * K (C.φ y)) := by
    ext y
    by_cases hy : y ∈ C.dom
    · rw [indicator_of_mem hy, indicator_of_mem hy, ofChart_weight_Φ C hy, C.Φ_eqOn hy]
      ring
    · rw [indicator_of_notMem hy, indicator_of_notMem hy, zero_mul]
  change ∫ y, (fun y => (C.dom.indicator fun y => C.jac y * ((ofChart C).weight () (C.Φ y) *
      (Real.exp (-N * K (C.Φ y)) * p.w (C.Φ y)))) y * G y) y = _
  rw [this, integral_indicator C.measurableSet_dom]

/-- The pulled-back observable, along the modified chart map, is continuous on the domain. -/
theorem continuousOn_pullback_Φ {F : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
    (hFc : ContinuousOn (fun y => F (C.φ y)) W) (hsub : C.dom ⊆ W) :
    ContinuousOn (fun y => F (C.Φ y)) C.dom :=
  (hFc.mono hsub).congr fun y hy => by simp only [C.Φ_eqOn hy]

/-- **Compatibility**: with the pulled-back observable as source amplitude, the source chart
integral is the one-chart Boltzmann integral. -/
theorem sourceChartIntegral_pullback {F : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
    (hFc : ContinuousOn (fun y => F (C.φ y)) W) (hsub : C.dom ⊆ W) (hFm : Measurable F)
    (hF : Integrable (fun x => F x * p.w x) (volume.restrict (⋃ i, (ofChart C).image i)))
    (hK : Measurable K) (hK0 : ∀ x, 0 ≤ K x) {N : ℝ} (hN : 0 ≤ N) :
    (ofChart C).sourceChartIntegral () (fun y => F (C.Φ y)) K p N =
      (ofChart C).boltzmannIntegral F K p N := by
  have hGm : Measurable fun y => F (C.Φ y) := hFm.comp C.measurable_Φ
  have hGc := continuousOn_pullback_Φ C hFc hsub
  rw [(ofChart C).boltzmannIntegral_eq_sum_pieces (fun _ => (∅ : Finset (Fin d))) 1 hFm hF hK hK0
    hN, Fintype.sum_unique,
    (ofChart C).sourceChartIntegral_eq_sum_pieces () (fun _ => (∅ : Finset (Fin d))) 1 hGm hGc hK
      hK0 hN]
  have hcongr : ∀ I : Finset (Fin d),
      (ofChart C).sourcePieceIntegral (fun _ => (∅ : Finset (Fin d))) 1 () I
        (fun y => F (C.Φ y)) K p N =
      (ofChart C).pieceIntegral (fun _ => (∅ : Finset (Fin d))) 1 () I F K p N := fun I =>
    (ofChart C).sourcePieceIntegral_congr_dom () _ _ I (fun y hy => by rw [C.Φ_eqOn hy]; rfl) N
  simp only [hcongr]

end ResolutionCover

/-! ### The source coefficient of a one-chart product package -/

namespace ProductMonomialChartVar

open ResolutionCover (ofChart)

variable {d : ℕ} {C : ResolutionChart d} {K : (Fin d → ℝ) → ℝ}
  (P : ProductMonomialChartVar (ofChart C) () K) (hK0 : ∀ x, 0 ≤ K x) {ε : ℝ} (hε : 0 < ε)
  (hεb : ε ≤ P.b) {G : (Fin d → ℝ) → ℝ} {p : TubeWeight d}
  (hpc : ContinuousOn (fun y => p.w (C.φ y)) P.W) (hGm : Measurable G)
  (hGc : ContinuousOn G C.dom) (hK : Measurable K)

include hK0 hε hεb hpc hGm hGc hK in
/-- **The chosen source-weighted piece atlases of the strata.** -/
noncomputable def sourceAtlases : ∀ I : Finset (Fin d), I ⊆ P.e.support → I.Nonempty →
    FiniteVarUnitAtlas (d - (I.card - 1 + 1))
      ((ofChart C).sourcePieceIntegral (fun _ => P.e.support) ε () I G K p) :=
  fun I hI hne => P.sourcePieceAtlasV hK0 hε hεb rfl hpc hGm hGc hK I hI hne

include hK0 hε hεb hpc hGm hGc hK in
/-- **The source coefficient** at `(λ₀, k₀)`: the sum over the strata of the tied cell
coefficients of the chosen source-weighted atlases. -/
noncomputable def sourceCoeff (lam₀ : ℝ) (k₀ : ℕ) : ℝ :=
  ∑ I ∈ P.e.support.powerset.filter (fun I => I.Nonempty),
    ResolutionCover.sourceAtlasPieceCoeff
      (fun I hI hne => (P.sourceAtlases hK0 hε hεb hpc hGm hGc hK I hI hne).toLeading) lam₀ k₀ I

include hK0 hε hεb hpc hGm hGc hK in
/-- ★ **The zero-compatible expansion of a source-weighted one-chart integral** at any pair
dominating every stratum pair: `∫ … G … = sourceCoeff · N^{−λ₀}(log N)^{k₀} + o(·)`. -/
theorem hasLeadingTerm_sourceChartIntegral (lam₀ : ℝ) (k₀ : ℕ)
    (hlam : ∀ I, I ⊆ P.e.support → ∀ hne : I.Nonempty, lam₀ ≤ P.pieceLam I hne)
    (hk : ∀ I, I ⊆ P.e.support → ∀ hne : I.Nonempty,
      P.pieceLam I hne = lam₀ → P.pieceMult I hne - 1 ≤ k₀) :
    HasLeadingTerm ((ofChart C).sourceChartIntegral () G K p)
      (P.sourceCoeff hK0 hε hεb hpc hGm hGc hK lam₀ k₀) lam₀ k₀ :=
  (ofChart C).hasLeadingTerm_sourceChartIntegral_of_leadingAtlases () ε P.e P.h P.monomial hε hGm
    hGc hK hK0 (fun I hI hne => (P.sourceAtlases hK0 hε hεb hpc hGm hGc hK I hI hne).toLeading)
    lam₀ k₀
    (fun I hI hne j => (hlam I hI hne).trans_eq
      (P.sourcePieceAtlasV_cell_lam hK0 hε hεb rfl hpc hGm hGc hK I hI hne j).symm)
    (fun I hI hne j hj => by
      have hj' : P.pieceLam I hne = lam₀ :=
        (P.sourcePieceAtlasV_cell_lam hK0 hε hεb rfl hpc hGm hGc hK I hI hne j).symm.trans hj
      have hm := P.sourcePieceAtlasV_cell_mult hK0 hε hεb rfl hpc hGm hGc hK I hI hne j
      calc ((P.sourceAtlases hK0 hε hεb hpc hGm hGc hK I hI hne).toLeading.cell j).mult - 1
          = P.pieceMult I hne - 1 := by
            change ((P.sourcePieceAtlasV hK0 hε hεb rfl hpc hGm hGc hK I hI hne).cell j).mult - 1
              = _
            rw [hm]
        _ ≤ k₀ := hk I hI hne hj')

include hK0 hε hεb hpc hGm hGc hK in
/-- **The expansion at the extremal pair of the chart.** -/
theorem hasLeadingTerm_sourceChartIntegral_extremal
    (hact : ((ofChart C).activeCoordsV (fun _ => P)).Nonempty) :
    HasLeadingTerm ((ofChart C).sourceChartIntegral () G K p)
      (P.sourceCoeff hK0 hε hεb hpc hGm hGc hK ((ofChart C).coverLamV (fun _ => P) hact)
        ((ofChart C).coverDegV (fun _ => P) hact))
      ((ofChart C).coverLamV (fun _ => P) hact) ((ofChart C).coverDegV (fun _ => P) hact) :=
  P.hasLeadingTerm_sourceChartIntegral hK0 hε hεb hpc hGm hGc hK _ _
    (fun I hI hne => (ofChart C).coverLamV_le_pieceLam (fun _ => P) hact () I hI hne)
    (fun I hI hne hl => (ofChart C).pieceMult_le_coverDegV (fun _ => P) hact () I hI hne hl)

include hK0 hε hεb hpc hGm hGc hK in
/-- Every stratum term of the source coefficient is nonnegative for `G, p, r ≥ 0`. -/
theorem sourceAtlasPieceCoeff_nonneg (hG0 : ∀ y, 0 ≤ G y) (hp0 : ∀ x, 0 ≤ p.w x)
    (hr0 : ∀ x, 0 ≤ P.r x) (lam₀ : ℝ) (k₀ : ℕ) (I : Finset (Fin d)) :
    0 ≤ ResolutionCover.sourceAtlasPieceCoeff
      (fun I hI hne => (P.sourceAtlases hK0 hε hεb hpc hGm hGc hK I hI hne).toLeading) lam₀ k₀
        I := by
  unfold ResolutionCover.sourceAtlasPieceCoeff
  split_ifs with hI
  · exact Finset.sum_nonneg fun σ _ =>
      P.sourceCell_coeff_nonneg_of_data hK0 hε hεb rfl hGm hGc hK I hI.1 hI.2 hG0 hp0 hr0
        (P.sourcePieceAtlasV_data hK0 hε hεb rfl hpc hGm hGc hK I hI.1 hI.2) σ
  · exact le_rfl

include hK0 hε hεb hpc hGm hGc hK in
/-- **The stratum term of an all-minimal stratum at its own pair is positive** when its source
dominant face has positive measure. -/
theorem sourceAtlasPieceCoeff_pos (hG0 : ∀ y, 0 ≤ G y) (hp0 : ∀ x, 0 ≤ p.w x)
    (hr0 : ∀ x, 0 ≤ P.r x) {lam₀ : ℝ} {k₀ : ℕ} (I₀ : Finset (Fin d)) (hI₀ : I₀ ⊆ P.e.support)
    (hne₀ : I₀.Nonempty) (hall : ∀ j ∈ I₀, P.ratio j = lam₀) (hdeg : I₀.card - 1 = k₀)
    (hpos : 0 < volume (P.sourceDominantFace (fun _ => P.e.support) ε I₀ hne₀ G p)) :
    0 < ResolutionCover.sourceAtlasPieceCoeff
      (fun I hI hne => (P.sourceAtlases hK0 hε hεb hpc hGm hGc hK I hI hne).toLeading) lam₀ k₀
        I₀ := by
  have hlam := P.pieceLam_eq_of_forall hne₀ hall
  have hall' : ∀ j ∈ I₀, P.ratio j = P.pieceLam I₀ hne₀ := fun j hj => (hall j hj).trans hlam.symm
  rw [ResolutionCover.sourceAtlasPieceCoeff_of_mem _ lam₀ k₀ I₀ hI₀ hne₀]
  refine FiniteVarUnitAtlas.tiedCoeff_pos (P.sourceAtlases hK0 hε hεb hpc hGm hGc hK I₀ hI₀ hne₀)
    lam₀ k₀ (fun σ _ =>
    P.sourceCell_coeff_nonneg_of_data hK0 hε hεb rfl hGm hGc hK I₀ hI₀ hne₀ hG0 hp0 hr0
      (P.sourcePieceAtlasV_data hK0 hε hεb rfl hpc hGm hGc hK I₀ hI₀ hne₀) σ) ?_
  obtain ⟨σ, hσ⟩ := P.exists_sourceCell_coeff_pos_of_data hK0 hε hεb rfl hGm hGc hK I₀ hI₀ hne₀
    hG0 hp0 hr0 hall' hpos (P.sourcePieceAtlasV_data hK0 hε hεb rfl hpc hGm hGc hK I₀ hI₀ hne₀)
  have h1 : ((P.sourceAtlases hK0 hε hεb hpc hGm hGc hK I₀ hI₀ hne₀).cell σ).lam = lam₀ :=
    (P.sourcePieceAtlasV_cell_lam hK0 hε hεb rfl hpc hGm hGc hK I₀ hI₀ hne₀ σ).trans hlam
  have h2 : ((P.sourceAtlases hK0 hε hεb hpc hGm hGc hK I₀ hI₀ hne₀).cell σ).mult - 1 = k₀ := by
    change ((P.sourcePieceAtlasV hK0 hε hεb rfl hpc hGm hGc hK I₀ hI₀ hne₀).cell σ).mult - 1 = k₀
    rw [P.sourcePieceAtlasV_cell_mult hK0 hε hεb rfl hpc hGm hGc hK I₀ hI₀ hne₀ σ,
      P.pieceMult_eq_card_of_forall hne₀ hall, hdeg]
  exact ⟨σ, Finset.mem_filter.2 ⟨Finset.mem_univ _, h1, h2⟩, hσ⟩

include hK0 hε hεb hpc hGm hGc hK in
/-- **The source coefficient is nonnegative** for `G, p, r ≥ 0`. -/
theorem sourceCoeff_nonneg (hG0 : ∀ y, 0 ≤ G y) (hp0 : ∀ x, 0 ≤ p.w x) (hr0 : ∀ x, 0 ≤ P.r x)
    (lam₀ : ℝ) (k₀ : ℕ) : 0 ≤ P.sourceCoeff hK0 hε hεb hpc hGm hGc hK lam₀ k₀ :=
  Finset.sum_nonneg fun I _ =>
    P.sourceAtlasPieceCoeff_nonneg hK0 hε hεb hpc hGm hGc hK hG0 hp0 hr0 lam₀ k₀ I

include hK0 hε hεb hpc hGm hGc hK in
/-- ★ **The source coefficient is positive** when some all-minimal stratum at `(λ₀, k₀)` has a
source dominant face of positive measure. -/
theorem sourceCoeff_pos (hG0 : ∀ y, 0 ≤ G y) (hp0 : ∀ x, 0 ≤ p.w x) (hr0 : ∀ x, 0 ≤ P.r x)
    {lam₀ : ℝ} {k₀ : ℕ} (I₀ : Finset (Fin d)) (hI₀ : I₀ ⊆ P.e.support) (hne₀ : I₀.Nonempty)
    (hall : ∀ j ∈ I₀, P.ratio j = lam₀) (hdeg : I₀.card - 1 = k₀)
    (hpos : 0 < volume (P.sourceDominantFace (fun _ => P.e.support) ε I₀ hne₀ G p)) :
    0 < P.sourceCoeff hK0 hε hεb hpc hGm hGc hK lam₀ k₀ :=
  Finset.sum_pos'
    (fun I _ => P.sourceAtlasPieceCoeff_nonneg hK0 hε hεb hpc hGm hGc hK hG0 hp0 hr0 lam₀ k₀ I)
    ⟨I₀, Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hI₀, hne₀⟩,
      P.sourceAtlasPieceCoeff_pos hK0 hε hεb hpc hGm hGc hK hG0 hp0 hr0 I₀ hI₀ hne₀ hall hdeg
        hpos⟩

include hK0 hε hεb hpc hGm hGc hK in
/-- ★ **Asymptotic equivalence of a source-weighted one-chart integral** with positive explicit
coefficient. -/
theorem sourceChartIntegral_isEquivalent (lam₀ : ℝ) (k₀ : ℕ)
    (hlam : ∀ I, I ⊆ P.e.support → ∀ hne : I.Nonempty, lam₀ ≤ P.pieceLam I hne)
    (hk : ∀ I, I ⊆ P.e.support → ∀ hne : I.Nonempty,
      P.pieceLam I hne = lam₀ → P.pieceMult I hne - 1 ≤ k₀)
    (hG0 : ∀ y, 0 ≤ G y) (hp0 : ∀ x, 0 ≤ p.w x) (hr0 : ∀ x, 0 ≤ P.r x) (I₀ : Finset (Fin d))
    (hI₀ : I₀ ⊆ P.e.support) (hne₀ : I₀.Nonempty) (hall : ∀ j ∈ I₀, P.ratio j = lam₀)
    (hdeg : I₀.card - 1 = k₀)
    (hpos : 0 < volume (P.sourceDominantFace (fun _ => P.e.support) ε I₀ hne₀ G p)) :
    0 < P.sourceCoeff hK0 hε hεb hpc hGm hGc hK lam₀ k₀ ∧
      (ofChart C).sourceChartIntegral () G K p ~[atTop] fun N =>
        P.sourceCoeff hK0 hε hεb hpc hGm hGc hK lam₀ k₀ * powLogScale lam₀ k₀ N :=
  have hc := P.sourceCoeff_pos hK0 hε hεb hpc hGm hGc hK hG0 hp0 hr0 I₀ hI₀ hne₀ hall hdeg hpos
  ⟨hc, (P.hasLeadingTerm_sourceChartIntegral hK0 hε hεb hpc hGm hGc hK lam₀ k₀ hlam
    hk).isEquivalent hc.ne'⟩

include hK0 hε hεb hpc hK in
/-- **Compatibility of the coefficients**: with the pulled-back observable as source amplitude the
source coefficient is the product-chart coefficient `productCoeffV` of the one-chart cover (by
uniqueness of certificates). -/
theorem sourceCoeff_pullback {F : (Fin d → ℝ) → ℝ}
    (hFc : ContinuousOn (fun y => F (C.φ y)) P.W) (hFm : Measurable F)
    (hF : Integrable (fun x => F x * p.w x) (volume.restrict (⋃ i, (ofChart C).image i)))
    (lam₀ : ℝ) (k₀ : ℕ)
    (hlam : ∀ I, I ⊆ P.e.support → ∀ hne : I.Nonempty, lam₀ ≤ P.pieceLam I hne)
    (hk : ∀ I, I ⊆ P.e.support → ∀ hne : I.Nonempty,
      P.pieceLam I hne = lam₀ → P.pieceMult I hne - 1 ≤ k₀) :
    P.sourceCoeff hK0 hε hεb hpc (hFm.comp C.measurable_Φ)
        (ResolutionCover.continuousOn_pullback_Φ C hFc P.dom_subset) hK lam₀ k₀ =
      (ofChart C).productCoeffV (fun _ => P) hK0 hε (fun _ => hεb) (fun _ => hFc) (fun _ => hpc)
        hFm hF hK lam₀ k₀ := by
  have h1 := P.hasLeadingTerm_sourceChartIntegral hK0 hε hεb hpc (hFm.comp C.measurable_Φ)
    (ResolutionCover.continuousOn_pullback_Φ C hFc P.dom_subset) hK lam₀ k₀ hlam hk
  have h2 := (ofChart C).hasLeadingTerm_boltzmannIntegral_of_productChartsV (fun _ => P) hK0 hε
    (fun _ => hεb) (fun _ => hFc) (fun _ => hpc) hFm hF hK lam₀ k₀
    (fun _ I hI hne => (hlam I hI hne).trans_eq
      ((ofChart C).productPieceLamV_eq (fun _ => P) hK0 _ I hI hne).symm)
    (fun _ I hI hne hl => by
      rw [(ofChart C).productPieceLamV_eq (fun _ => P) hK0 _ I hI hne] at hl
      rw [(ofChart C).productPieceMultV_eq (fun _ => P) hK0 _ I hI hne]
      exact hk I hI hne hl)
  refine h1.coeff_unique (h2.congr' ((eventually_ge_atTop 0).mono fun N hN => ?_))
  exact (ResolutionCover.sourceChartIntegral_pullback C hFc P.dom_subset hFm hF hK hK0 hN).symm

end ProductMonomialChartVar

end Grammar
