/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.ProductChartPositivity
import Grammar.PosteriorTransfer

/-!
# The leading-order posterior expectation for a cover of product charts

Unit 2 of consult #79 (`tide-log/gpt6_bigpicture_v79.md`). For a cover of centred product monomial
charts (CCXLI–CCXLV) the constant observable `1` satisfies the analytic package, so the normaliser
`Z_N[1]` has the certificate at the extremal pair `(λ*, k*)` with coefficient `c₁ = normaliserCoeff`
(`hasLeadingTerm_normaliser_extremal`), positive under `p ≥ 0`, `r ≥ 0` and one extremal stratum
whose dominant face (for `F = 1`) has positive measure (`normaliserCoeff_pos`). Any admissible
observable `F` — continuous pull-backs, measurable, `F·p` integrable, **no sign condition** — has
the certificate at `(λ*, k*)` with coefficient `productCoeffD F`
(`hasLeadingTerm_boltzmannIntegral_of_productChartsD_extremal`), and CCXLVI transfers the pair of
certificates to the posterior expectation:

★ `tendsto_posteriorExpectation_of_productCharts`: `0 < c₁`, `Z_N[1] > 0` eventually, and
`E_N[F] = Z_N[F]/Z_N[1] → productCoeffD F / c₁`.

The coefficient is intrinsic: linear in the observable (`productCoeffD_add`,
`productCoeffD_const_mul`, `productCoeffD_const`) and independent of the cutoff `ε` and of the
choice-selected atlases
(`productCoeffD_eq_of_cutoff`), all by uniqueness of the coefficient at a fixed pair
(`HasLeadingTerm.coeff_unique`). Consequently `E_N[a] → a`, and the limit functional
`F ↦ productCoeffD F / c₁` is linear.
-/

open MeasureTheory Set Filter Topology Asymptotics

namespace Grammar

namespace ResolutionCover

variable {d : ℕ} {ι : Type*} [Fintype ι] (R : ResolutionCover d ι) {K : (Fin d → ℝ) → ℝ}
  (Ps : ∀ i, ProductMonomialChart R i K) (hK0 : ∀ x, 0 ≤ K x) {ε : ℝ} (hε : 0 < ε)
  (hεb : ∀ i, ε ≤ (Ps i).b) {p : TubeWeight d}
  (hpc : ∀ i, ContinuousOn (fun y => p.w ((R.chart i).φ y)) (Ps i).W)
  (hp : Integrable p.w (volume.restrict (⋃ i, R.image i))) (hK : Measurable K)

/-! ### The certificate at the extremal pair for an arbitrary admissible observable -/

include hK0 hε hεb hpc hK in
/-- **The end-to-end certificate at the extremal pair with exposed atlases** (CCXLIII for
`productAtlasesD`). -/
theorem hasLeadingTerm_boltzmannIntegral_of_productChartsD_extremal {F : (Fin d → ℝ) → ℝ}
    (hFc : ∀ i, ContinuousOn (fun y => F ((R.chart i).φ y)) (Ps i).W) (hFm : Measurable F)
    (hF : Integrable (fun x => F x * p.w x) (volume.restrict (⋃ i, R.image i)))
    (hact : (R.activeCoords Ps).Nonempty) :
    HasLeadingTerm (R.boltzmannIntegral F K p)
      (R.productCoeffD Ps hK0 hε hεb hFc hpc hFm hF hK (R.coverLam Ps hact) (R.coverDeg Ps hact))
      (R.coverLam Ps hact) (R.coverDeg Ps hact) :=
  R.hasLeadingTerm_boltzmannIntegral_of_productChartsD Ps hK0 hε hεb hFc hpc hFm hF hK
    (R.coverLam Ps hact) (R.coverDeg Ps hact)
    (fun i I hI hne => by
      rw [R.productPieceLam_eq Ps hK0 i I hI hne]
      exact R.coverLam_le_pieceLam Ps hact i I hI hne)
    (fun i I hI hne hlam => by
      rw [R.productPieceLam_eq Ps hK0 i I hI hne] at hlam
      rw [R.productPieceMult_eq Ps hK0 i I hI hne]
      exact R.pieceMult_le_coverDeg Ps hact i I hI hne hlam)

/-! ### The normaliser `Z_N[1]` -/

include hp in
/-- The constant observable `1` is admissible: `1 · p` is integrable when `p` is. -/
theorem integrable_one_mul_weight :
    Integrable (fun x => (fun _ : Fin d → ℝ => (1 : ℝ)) x * p.w x)
      (volume.restrict (⋃ i, R.image i)) :=
  hp.congr (Eventually.of_forall fun x => (one_mul (p.w x)).symm)

include hK0 hε hεb hpc hp hK in
/-- **The normalising coefficient** `c₁`: the coefficient of `Z_N[1]` at `(λ₀, k₀)`. -/
noncomputable def normaliserCoeff (lam₀ : ℝ) (k₀ : ℕ) : ℝ :=
  R.productCoeffD Ps hK0 hε hεb (fun _ => continuousOn_const) hpc measurable_const
    (R.integrable_one_mul_weight hp) hK lam₀ k₀

include hK0 hε hεb hpc hp hK in
/-- The normaliser has the certificate at the extremal pair. -/
theorem hasLeadingTerm_normaliser_extremal (hact : (R.activeCoords Ps).Nonempty) :
    HasLeadingTerm (R.boltzmannIntegral (fun _ => 1) K p)
      (R.normaliserCoeff Ps hK0 hε hεb hpc hp hK (R.coverLam Ps hact) (R.coverDeg Ps hact))
      (R.coverLam Ps hact) (R.coverDeg Ps hact) :=
  R.hasLeadingTerm_boltzmannIntegral_of_productChartsD_extremal Ps hK0 hε hεb hpc hK
    (fun _ => continuousOn_const) measurable_const (R.integrable_one_mul_weight hp) hact

include hK0 hε hεb hpc hp hK in
/-- **The normalising coefficient is positive** under `p ≥ 0`, `r ≥ 0` and an extremal stratum whose
dominant face (for the observable `1`) has positive measure. -/
theorem normaliserCoeff_pos (hact : (R.activeCoords Ps).Nonempty) (hp0 : ∀ x, 0 ≤ p.w x)
    (hr0 : ∀ i x, 0 ≤ (Ps i).r x) (i₀ : ι) (I₀ : Finset (Fin d)) (hI₀ : I₀ ⊆ (Ps i₀).e.support)
    (hne₀ : I₀.Nonempty) (hall : ∀ j ∈ I₀, (Ps i₀).ratio j = R.coverLam Ps hact)
    (hdeg : I₀.card - 1 = R.coverDeg Ps hact)
    (hpos : 0 < volume ((Ps i₀).dominantFace (fun i => (Ps i).e.support) ε I₀ hne₀
      (fun _ => (1 : ℝ)) p)) :
    0 < R.normaliserCoeff Ps hK0 hε hεb hpc hp hK (R.coverLam Ps hact) (R.coverDeg Ps hact) :=
  R.productCoeffD_pos Ps hK0 hε hεb (fun _ => continuousOn_const) hpc measurable_const
    (R.integrable_one_mul_weight hp) hK (fun _ => zero_le_one) hp0 hr0 i₀ I₀ hI₀ hne₀ hall hdeg hpos

/-! ### The leading-order posterior expectation -/

include hK0 hε hεb hpc hp hK in
/-- ★ **THE LEADING-ORDER POSTERIOR EXPECTATION FOR A COVER OF PRODUCT CHARTS**: for any admissible
observable `F` (no sign condition), with `p ≥ 0`, `r ≥ 0` and an extremal stratum of positive
dominant-face measure, the normalising coefficient is positive, `Z_N[1] > 0` eventually, and
`E_N[F] → productCoeffD F / c₁`. -/
theorem tendsto_posteriorExpectation_of_productCharts (hact : (R.activeCoords Ps).Nonempty)
    {F : (Fin d → ℝ) → ℝ} (hFc : ∀ i, ContinuousOn (fun y => F ((R.chart i).φ y)) (Ps i).W)
    (hFm : Measurable F) (hF : Integrable (fun x => F x * p.w x) (volume.restrict (⋃ i, R.image i)))
    (hp0 : ∀ x, 0 ≤ p.w x) (hr0 : ∀ i x, 0 ≤ (Ps i).r x) (i₀ : ι) (I₀ : Finset (Fin d))
    (hI₀ : I₀ ⊆ (Ps i₀).e.support) (hne₀ : I₀.Nonempty)
    (hall : ∀ j ∈ I₀, (Ps i₀).ratio j = R.coverLam Ps hact)
    (hdeg : I₀.card - 1 = R.coverDeg Ps hact)
    (hpos : 0 < volume ((Ps i₀).dominantFace (fun i => (Ps i).e.support) ε I₀ hne₀
      (fun _ => (1 : ℝ)) p)) :
    0 < R.normaliserCoeff Ps hK0 hε hεb hpc hp hK (R.coverLam Ps hact) (R.coverDeg Ps hact) ∧
      (∀ᶠ N in atTop, 0 < R.boltzmannIntegral (fun _ => 1) K p N) ∧
      Tendsto (R.posteriorExpectation K p F) atTop
        (𝓝 (R.productCoeffD Ps hK0 hε hεb hFc hpc hFm hF hK (R.coverLam Ps hact)
          (R.coverDeg Ps hact) /
          R.normaliserCoeff Ps hK0 hε hεb hpc hp hK (R.coverLam Ps hact) (R.coverDeg Ps hact))) :=
  have hc₁ := R.normaliserCoeff_pos Ps hK0 hε hεb hpc hp hK hact hp0 hr0 i₀ I₀ hI₀ hne₀ hall hdeg
    hpos
  ⟨hc₁, R.tendsto_posteriorExpectation_of_hasLeadingTerm
    (R.hasLeadingTerm_boltzmannIntegral_of_productChartsD_extremal Ps hK0 hε hεb hpc hK hFc hFm hF
      hact)
    (R.hasLeadingTerm_normaliser_extremal Ps hK0 hε hεb hpc hp hK hact) hc₁⟩

/-! ### The coefficient is intrinsic -/

include hK0 hε hεb hpc hK in
/-- **Additivity of the coefficient in the observable** (any admissibility proofs for `F + G`). -/
theorem productCoeffD_add {F G : (Fin d → ℝ) → ℝ}
    (hFc : ∀ i, ContinuousOn (fun y => F ((R.chart i).φ y)) (Ps i).W)
    (hGc : ∀ i, ContinuousOn (fun y => G ((R.chart i).φ y)) (Ps i).W)
    (hFm : Measurable F) (hGm : Measurable G)
    (hF : Integrable (fun x => F x * p.w x) (volume.restrict (⋃ i, R.image i)))
    (hG : Integrable (fun x => G x * p.w x) (volume.restrict (⋃ i, R.image i)))
    (hFGc : ∀ i, ContinuousOn (fun y => (fun x => F x + G x) ((R.chart i).φ y)) (Ps i).W)
    (hFGm : Measurable fun x => F x + G x)
    (hFG : Integrable (fun x => (fun x => F x + G x) x * p.w x) (volume.restrict (⋃ i, R.image i)))
    (lam₀ : ℝ) (k₀ : ℕ)
    (hlam : ∀ i I, I ⊆ (Ps i).e.support → ∀ hne : I.Nonempty, lam₀ ≤ R.productPieceLam Ps i I hne)
    (hk : ∀ i I, I ⊆ (Ps i).e.support → ∀ hne : I.Nonempty,
      R.productPieceLam Ps i I hne = lam₀ → R.productPieceMult Ps i I hne - 1 ≤ k₀) :
    R.productCoeffD Ps hK0 hε hεb hFGc hpc hFGm hFG hK lam₀ k₀ =
      R.productCoeffD Ps hK0 hε hεb hFc hpc hFm hF hK lam₀ k₀ +
        R.productCoeffD Ps hK0 hε hεb hGc hpc hGm hG hK lam₀ k₀ :=
  HasLeadingTerm.coeff_unique
    (R.hasLeadingTerm_boltzmannIntegral_of_productChartsD Ps hK0 hε hεb hFGc hpc hFGm hFG hK lam₀
      k₀ hlam hk)
    (R.hasLeadingTerm_boltzmannIntegral_add hF hG hK hK0
      (R.hasLeadingTerm_boltzmannIntegral_of_productChartsD Ps hK0 hε hεb hFc hpc hFm hF hK lam₀
        k₀ hlam hk)
      (R.hasLeadingTerm_boltzmannIntegral_of_productChartsD Ps hK0 hε hεb hGc hpc hGm hG hK lam₀
        k₀ hlam hk))

include hK0 hε hεb hpc hK in
/-- **Homogeneity of the coefficient in the observable.** -/
theorem productCoeffD_const_mul {F : (Fin d → ℝ) → ℝ} (a : ℝ)
    (hFc : ∀ i, ContinuousOn (fun y => F ((R.chart i).φ y)) (Ps i).W) (hFm : Measurable F)
    (hF : Integrable (fun x => F x * p.w x) (volume.restrict (⋃ i, R.image i)))
    (haFc : ∀ i, ContinuousOn (fun y => (fun x => a * F x) ((R.chart i).φ y)) (Ps i).W)
    (haFm : Measurable fun x => a * F x)
    (haF : Integrable (fun x => (fun x => a * F x) x * p.w x) (volume.restrict (⋃ i, R.image i)))
    (lam₀ : ℝ) (k₀ : ℕ)
    (hlam : ∀ i I, I ⊆ (Ps i).e.support → ∀ hne : I.Nonempty, lam₀ ≤ R.productPieceLam Ps i I hne)
    (hk : ∀ i I, I ⊆ (Ps i).e.support → ∀ hne : I.Nonempty,
      R.productPieceLam Ps i I hne = lam₀ → R.productPieceMult Ps i I hne - 1 ≤ k₀) :
    R.productCoeffD Ps hK0 hε hεb haFc hpc haFm haF hK lam₀ k₀ =
      a * R.productCoeffD Ps hK0 hε hεb hFc hpc hFm hF hK lam₀ k₀ :=
  HasLeadingTerm.coeff_unique
    (R.hasLeadingTerm_boltzmannIntegral_of_productChartsD Ps hK0 hε hεb haFc hpc haFm haF hK lam₀
      k₀ hlam hk)
    (R.hasLeadingTerm_boltzmannIntegral_const_mul a
      (R.hasLeadingTerm_boltzmannIntegral_of_productChartsD Ps hK0 hε hεb hFc hpc hFm hF hK lam₀
        k₀ hlam hk))

include hK0 hε hεb hpc hp hK in
/-- **Constant observables**: the coefficient of `a` is `a · c₁`. -/
theorem productCoeffD_const (a : ℝ)
    (hac : ∀ i, ContinuousOn (fun y => (fun _ : Fin d → ℝ => a) ((R.chart i).φ y)) (Ps i).W)
    (ham : Measurable fun _ : Fin d → ℝ => a)
    (ha : Integrable (fun x => (fun _ : Fin d → ℝ => a) x * p.w x)
      (volume.restrict (⋃ i, R.image i)))
    (lam₀ : ℝ) (k₀ : ℕ)
    (hlam : ∀ i I, I ⊆ (Ps i).e.support → ∀ hne : I.Nonempty, lam₀ ≤ R.productPieceLam Ps i I hne)
    (hk : ∀ i I, I ⊆ (Ps i).e.support → ∀ hne : I.Nonempty,
      R.productPieceLam Ps i I hne = lam₀ → R.productPieceMult Ps i I hne - 1 ≤ k₀) :
    R.productCoeffD Ps hK0 hε hεb hac hpc ham ha hK lam₀ k₀ =
      a * R.normaliserCoeff Ps hK0 hε hεb hpc hp hK lam₀ k₀ :=
  HasLeadingTerm.coeff_unique
    (R.hasLeadingTerm_boltzmannIntegral_of_productChartsD Ps hK0 hε hεb hac hpc ham ha hK lam₀ k₀
      hlam hk)
    (((R.hasLeadingTerm_boltzmannIntegral_of_productChartsD Ps hK0 hε hεb
      (fun _ => continuousOn_const) hpc measurable_const (R.integrable_one_mul_weight hp) hK lam₀ k₀
      hlam hk).const_mul a).congr' (Eventually.of_forall fun N =>
        (R.boltzmannIntegral_const a K p N).symm))

include hK0 hpc hK in
/-- **Cutoff independence**: the total coefficient at a fixed pair does not depend on the common
cutoff `ε` (nor on the choice-selected atlases). -/
theorem productCoeffD_eq_of_cutoff {ε₁ ε₂ : ℝ} (hε₁ : 0 < ε₁) (hεb₁ : ∀ i, ε₁ ≤ (Ps i).b)
    (hε₂ : 0 < ε₂) (hεb₂ : ∀ i, ε₂ ≤ (Ps i).b) {F : (Fin d → ℝ) → ℝ}
    (hFc : ∀ i, ContinuousOn (fun y => F ((R.chart i).φ y)) (Ps i).W) (hFm : Measurable F)
    (hF : Integrable (fun x => F x * p.w x) (volume.restrict (⋃ i, R.image i)))
    (lam₀ : ℝ) (k₀ : ℕ)
    (hlam : ∀ i I, I ⊆ (Ps i).e.support → ∀ hne : I.Nonempty, lam₀ ≤ R.productPieceLam Ps i I hne)
    (hk : ∀ i I, I ⊆ (Ps i).e.support → ∀ hne : I.Nonempty,
      R.productPieceLam Ps i I hne = lam₀ → R.productPieceMult Ps i I hne - 1 ≤ k₀) :
    R.productCoeffD Ps hK0 hε₁ hεb₁ hFc hpc hFm hF hK lam₀ k₀ =
      R.productCoeffD Ps hK0 hε₂ hεb₂ hFc hpc hFm hF hK lam₀ k₀ :=
  HasLeadingTerm.coeff_unique
    (R.hasLeadingTerm_boltzmannIntegral_of_productChartsD Ps hK0 hε₁ hεb₁ hFc hpc hFm hF hK lam₀ k₀
      hlam hk)
    (R.hasLeadingTerm_boltzmannIntegral_of_productChartsD Ps hK0 hε₂ hεb₂ hFc hpc hFm hF hK lam₀ k₀
      hlam hk)

end ResolutionCover

end Grammar
