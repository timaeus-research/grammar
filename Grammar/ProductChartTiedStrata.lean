/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.ProductChartPosterior

/-!
# Tied strata of a cover of product charts and the all-minimal coefficient formula

Unit 3 of consult #79 (`tide-log/gpt6_bigpicture_v79.md`). Fix the extremal pair `(λ*, k*)` of a
cover of product charts and let `M_i = {j ∈ supp e_i : (h_ij+1)/e_ij = λ*}` be the **minimal set**
of chart `i` (`ProductMonomialChart.minimalSet`).

* **Classification.** Since `λ*` is a global lower bound of the ratios, a stratum `I ⊆ supp e_i` has
  exponent `λ*` iff it meets `M_i` (`pieceLam_eq_iff`), and then its multiplicity is `|I ∩ M_i|`
  (`pieceMult_eq_card_inter`); `|M_i| − 1 ≤ k*` (`card_minimalSet_le`). Hence a piece is **tied**
  at `(λ*, k*)` iff `M_i ⊆ I` and `|M_i| = k* + 1` (`tied_iff`): tied pieces are exactly the
  supersets of the full minimal set of a chart attaining the maximal minimal multiplicity, and the
  all-minimal tied piece is `I = M_i` (`eq_minimalSet_of_all_minimal`).
* **The all-minimal formula.** Every cell of a piece atlas of an all-minimal stratum is tied and has
  the same coefficient, so the tied sum is `2^{|I|}` times the orthant coefficient
  (`pieceAtlas_sum_tied`), and CCXXXIX's all-minimal formula with the exposed cells of CCXLV gives
  `∑_{tied} coeff = 2^{|I|} · Γ(λ*)/(|I|−1)! · ∏_{j∈I} 1/e_j · ∫_base β(z) q(z)^{−λ*} A(z,0) dz`
  with `q = scalarPhase` and `A(·,0) = pieceAmp(·,0) = |v|·|tangential monomial|·(p∘φ)(F∘φ)` at the
  foot points (`ProductMonomialChart.tiedSum_of_all_minimal`, `scalarAtlasPieceCoeff'_minimalSet`).
* **The total.** Untied pieces contribute zero (`scalarAtlasPieceCoeff'_eq_zero_of_not_tied`), so
  the total coefficient at `(λ*, k*)` is the sum over charts with `|M_i| = k* + 1` of the sum over
  strata `M_i ⊆ I ⊆ supp e_i` (`productCoeffD_extremal_eq_sum_tied`); when every such chart has
  `M_i = supp e_i` (all active coordinates minimal) only `I = M_i` survives and the total is the sum
  of the explicit all-minimal formulas (`productCoeffD_extremal_eq_sum_minimal`). The residual-face
  formula for `I ⊋ M_i` is unit 4.
-/

open MeasureTheory Set Filter Topology Asymptotics
open scoped ENNReal

namespace Grammar

/-! ### Tied sums of an atlas whose cells share one pair -/

namespace FiniteScalarUnitAtlas

variable {t : ℕ} {Z : ℝ → ℝ} (At : FiniteScalarUnitAtlas t Z)

theorem sum_tied_eq_card_mul (lam₀ : ℝ) (k₀ : ℕ) (c₀ : ℝ)
    (hall : ∀ σ, (At.cell σ).lam = lam₀ ∧ (At.cell σ).mult - 1 = k₀)
    (hcoeff : ∀ σ, (At.cell σ).coeff = c₀) :
    ∑ σ ∈ At.tied lam₀ k₀, (At.cell σ).coeff = (Fintype.card At.ι : ℝ) * c₀ := by
  unfold tied
  rw [Finset.filter_true_of_mem fun σ _ => hall σ]
  simp only [hcoeff, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem sum_tied_eq_zero (lam₀ : ℝ) (k₀ : ℕ)
    (h : ∀ σ, ¬ ((At.cell σ).lam = lam₀ ∧ (At.cell σ).mult - 1 = k₀)) :
    ∑ σ ∈ At.tied lam₀ k₀, (At.cell σ).coeff = 0 := by
  unfold tied
  rw [Finset.filter_eq_empty_iff.2 fun σ _ => h σ, Finset.sum_empty]

end FiniteScalarUnitAtlas

/-! ### The tied sum of an all-minimal piece atlas -/

namespace ResolutionCover

variable {d : ℕ} {ι : Type*} [Fintype ι] (R : ResolutionCover d ι) (i : ι)
  (D : ι → Finset (Fin d)) {ε : ℝ} (hε : 0 < ε) (I : Finset (Fin d)) (hne : I.Nonempty)
  {F K : (Fin d → ℝ) → ℝ} {p : TubeWeight d}
  (Ad : AdaptedProductDensity (stratumSplit I hne) (R.boltzmannChartDensity i 0 K p)
    (sizePiece (D i) ε I))
  (hbase : IsCompact Ad.base) (hβ : IntegrableOn Ad.beta Ad.base)
  (hbox : Ad.normalBox = Metric.ball 0 ε)
  (h k : Fin (I.card - 1 + 1) → ℕ) (hk : ∀ j, 0 < k j)
  (q : (Fin (d - (I.card - 1 + 1)) → ℝ) → ℝ) (hq : Continuous q) (hq_pos : ∀ z ∈ Ad.base, 0 < q z)
  (A : (Fin (d - (I.card - 1 + 1)) → ℝ) → (Fin (I.card - 1 + 1) → ℝ) → ℝ)
  (hA : Continuous (Function.uncurry A))
  (hamp : ∀ z ∈ Ad.base, ∀ n ∈ Metric.ball (0 : Fin (I.card - 1 + 1) → ℝ) ε,
    Ad.amp z n * F ((R.chart i).φ (planeSplit (stratumSplit I hne) (z, n))) =
      A z n * ∏ j, |n j| ^ h j)
  (hphase : ∀ z ∈ Ad.base, ∀ n ∈ Metric.ball (0 : Fin (I.card - 1 + 1) → ℝ) ε,
    K ((R.chart i).Φ (planeSplit (stratumSplit I hne) (z, n))) = q z * ∏ j, n j ^ (2 * k j))
  (hFm : Measurable F)
  (hF : Integrable (fun x => F x * p.w x) (volume.restrict (⋃ i, R.image i)))
  (hK : Measurable K) (hK0 : ∀ x, 0 ≤ K x)

include hbox hamp hphase hFm hF hK hK0 in
/-- **The tied sum of an all-minimal piece atlas**: all `2^{|I|}` cells are tied with the orthant
coefficient `Γ(λ)/(|I|−1)! ∏_a 1/(2k_a) · ∫_base β q^{−λ} A(·,0)`. -/
theorem pieceAtlas_sum_tied {lam₀ : ℝ} {k₀ : ℕ} (hall : ∀ a, ratioExp h k a = minRatio h k)
    (hlam : minRatio h k = lam₀) (hk₀ : multCount (ratioExp h k) (minRatio h k) - 1 = k₀) :
    ∑ σ ∈ (R.pieceAtlas i D hε I hne Ad hbase hβ hbox h k hk q hq hq_pos A hA hamp hphase hFm hF
        hK hK0).tied lam₀ k₀,
      ((R.pieceAtlas i D hε I hne Ad hbase hβ hbox h k hk q hq hq_pos A hA hamp hphase hFm hF hK
        hK0).cell σ).coeff =
      2 ^ I.card * ((Real.Gamma lam₀ / ((I.card - 1).factorial : ℝ) * ∏ a, 1 / (2 * (k a : ℝ))) *
        ∫ z in Ad.base, Ad.beta z * (q z ^ (-lam₀) * A z 0)) := by
  rw [FiniteScalarUnitAtlas.sum_tied_eq_card_mul (R.pieceAtlas i D hε I hne Ad hbase hβ hbox h k hk
      q hq hq_pos A hA hamp hphase hFm hF hK hK0) lam₀ k₀
    (R.pieceCell i D hε I hne Ad hbase hβ h k hk q hq hq_pos A hA).coeff (fun _ => ⟨hlam, hk₀⟩)
    (fun σ => (R.pieceCell i D hε I hne Ad hbase hβ h k hk q hq hq_pos
      A hA).reflected_coeff_of_all_minimal hall σ),
    (R.pieceCell i D hε I hne Ad hbase hβ h k hk q hq hq_pos A hA).coeff_of_all_minimal' hall]
  have hcard : (Fintype.card (R.pieceAtlas i D hε I hne Ad hbase hβ hbox h k hk q hq hq_pos A hA
      hamp hphase hFm hF hK hK0).ι : ℝ) = 2 ^ I.card := by
    rw [Fintype.card_eq_nat_card]
    change ((Nat.card (Fin (I.card - 1 + 1) → Bool) : ℕ) : ℝ) = _
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
      Nat.sub_add_cancel (Finset.card_pos.2 hne)]
    simp only [Nat.cast_pow, Nat.cast_ofNat]
  rw [hcard]
  congr 1
  congr 1
  · change Real.Gamma (minRatio h k) / ((I.card - 1).factorial : ℝ) * ∏ a, 1 / (2 * (k a : ℝ)) = _
    rw [hlam]
  · change ∫ z in Ad.base, Ad.beta z * (q z ^ (-(minRatio h k)) * A z 0) = _
    rw [hlam]

end ResolutionCover

/-! ### The minimal set of a product chart and the classification of tied strata -/

namespace ProductMonomialChart

variable {d : ℕ} {ι : Type*} [Fintype ι] {R : ResolutionCover d ι} {i : ι} {K : (Fin d → ℝ) → ℝ}
  (P : ProductMonomialChart R i K)

/-- **The minimal set** of the chart at level `lam`: the active coordinates of ratio `lam`. -/
noncomputable def minimalSet (lam : ℝ) : Finset (Fin d) :=
  P.e.support.filter fun j => P.ratio j = lam

theorem minimalSet_subset (lam : ℝ) : P.minimalSet lam ⊆ P.e.support := Finset.filter_subset _ _

theorem ratio_eq_of_mem_minimalSet {lam : ℝ} {j : Fin d} (hj : j ∈ P.minimalSet lam) :
    P.ratio j = lam :=
  (Finset.mem_filter.1 hj).2

section Classification

variable {lam : ℝ} (hlam : ∀ j ∈ P.e.support, lam ≤ P.ratio j)
include hlam

theorem le_pieceLam (I : Finset (Fin d)) (hI : I ⊆ P.e.support) (hne : I.Nonempty) :
    lam ≤ P.pieceLam I hne :=
  Finset.le_inf' hne _ fun j hj => hlam j (hI hj)

/-- A stratum has exponent `lam` iff it meets the minimal set. -/
theorem pieceLam_eq_iff (I : Finset (Fin d)) (hI : I ⊆ P.e.support) (hne : I.Nonempty) :
    P.pieceLam I hne = lam ↔ (I ∩ P.minimalSet lam).Nonempty := by
  constructor
  · intro h
    obtain ⟨j₀, hj₀, hmin⟩ := Finset.exists_mem_eq_inf' hne P.ratio
    refine ⟨j₀, Finset.mem_inter.2 ⟨hj₀, Finset.mem_filter.2 ⟨hI hj₀, ?_⟩⟩⟩
    unfold pieceLam at h
    rw [← hmin]
    exact h
  · rintro ⟨j₀, hj₀⟩
    rw [Finset.mem_inter, minimalSet, Finset.mem_filter] at hj₀
    exact le_antisymm ((Finset.inf'_le _ hj₀.1).trans_eq hj₀.2.2) (P.le_pieceLam hlam I hI hne)

omit hlam in
/-- At exponent `lam` the multiplicity of a stratum is the size of its intersection with the
minimal set. -/
theorem pieceMult_eq_card_inter (I : Finset (Fin d)) (hI : I ⊆ P.e.support) (hne : I.Nonempty)
    (h : P.pieceLam I hne = lam) : P.pieceMult I hne = (I ∩ P.minimalSet lam).card := by
  unfold pieceMult
  rw [h]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_inter, minimalSet]
  exact ⟨fun h => ⟨h.1, hI h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩

end Classification

/-- The normal half-exponents of a stratum are the halved active exponents: `∏_a 1/(2k_a) =
∏_{j∈I} 1/e_j`. -/
theorem prod_normalHalfExp_inv (hK0 : ∀ x, 0 ≤ K x) (I : Finset (Fin d)) (hI : I ⊆ P.e.support)
    (hne : I.Nonempty) :
    ∏ a, 1 / (2 * (normalHalfExp I hne P.e a : ℝ)) = ∏ j ∈ I, 1 / (P.e j : ℝ) := by
  refine Finset.prod_nbij (fun a => (stratumSplit I hne).symm (Sum.inr a))
    (fun a _ => stratumSplit_symm_inr_mem I hne a)
    (fun a _ b _ hab => Sum.inr_injective ((stratumSplit I hne).symm.injective hab))
    (fun j hj => ?_) (fun a _ => ?_)
  · obtain ⟨a, ha⟩ := exists_inr_of_mem I hne (Finset.mem_coe.1 hj)
    exact ⟨a, Finset.mem_coe.2 (Finset.mem_univ a), ha.symm⟩
  · congr 1
    have := P.normalExp_eq_two_mul hK0 I hI hne a
    unfold normalExp at this
    exact_mod_cast this.symm

section Atlas

variable (hK0 : ∀ x, 0 ≤ K x) {ε : ℝ} (hε : 0 < ε) (hεb : ε ≤ P.b)
  {D : ι → Finset (Fin d)} (hD : D i = P.e.support) {F : (Fin d → ℝ) → ℝ} {p : TubeWeight d}
  (hFm : Measurable F)
  (hF : Integrable (fun x => F x * p.w x) (volume.restrict (⋃ i, R.image i)))
  (hK : Measurable K) (I : Finset (Fin d)) (hI : I ⊆ P.e.support) (hne : I.Nonempty)

/-- **The all-minimal tied sum in chart data**: for a certified piece atlas of an all-minimal
stratum (`ratio_j = λ₀` on `I`, `|I| − 1 = k₀`),
`∑_{tied} coeff = 2^{|I|} · Γ(λ₀)/(|I|−1)! · ∏_{j∈I} 1/e_j · ∫_base β · scalarPhase^{−λ₀} ·
pieceAmp(·, 0)`. -/
theorem tiedSum_of_all_minimal {lam₀ : ℝ} {k₀ : ℕ} (hall : ∀ j ∈ I, P.ratio j = lam₀)
    (hdeg : I.card - 1 = k₀)
    {At : FiniteScalarUnitAtlas (d - (I.card - 1 + 1)) (R.pieceIntegral D ε i I F K p)}
    (hAt : P.IsPieceAtlasData hK0 hε hεb hD hFm hF hK I hI hne At) :
    ∑ σ ∈ At.tied lam₀ k₀, (At.cell σ).coeff =
      2 ^ I.card * ((Real.Gamma lam₀ / ((I.card - 1).factorial : ℝ) * ∏ j ∈ I, 1 / (P.e j : ℝ)) *
        ∫ z in (P.pieceDensity hε hεb hD I hI hne p).base,
          (P.pieceDensity hε hεb hD I hI hne p).beta z *
            (scalarPhase I hne P.u P.e z ^ (-lam₀) *
              R.pieceAmp i I hne P.h P.v (F := F) (p := p) z 0)) := by
  obtain ⟨q', A', hq'c, hq'pos, hA'c, hk, hbase, hβ, hamp', hphase', hq', hA', rfl⟩ := hAt
  have hmin : minRatio (normalExp I hne P.h) (normalHalfExp I hne P.e) = lam₀ :=
    (P.pieceLam_eq hK0 I hI hne).trans (P.pieceLam_eq_of_forall hne hall)
  have hmult : multCount (ratioExp (normalExp I hne P.h) (normalHalfExp I hne P.e))
      (minRatio (normalExp I hne P.h) (normalHalfExp I hne P.e)) = I.card :=
    (P.pieceMult_eq hK0 I hI hne).trans (P.pieceMult_eq_card_of_forall hne hall)
  have hallc : ∀ a, ratioExp (normalExp I hne P.h) (normalHalfExp I hne P.e) a =
      minRatio (normalExp I hne P.h) (normalHalfExp I hne P.e) := fun a => by
    rw [ratioExp_normal_eq I hne P.e P.h (P.normalExp_eq_two_mul hK0 I hI hne) a, hmin]
    exact hall _ (stratumSplit_symm_inr_mem I hne a)
  have hbaseM : MeasurableSet (P.pieceDensity hε hεb hD I hI hne p).base :=
    hbase.isClosed.measurableSet
  rw [R.pieceAtlas_sum_tied i D hε I hne _ hbase hβ rfl _ _ hk q' hq'c hq'pos A' hA'c hamp' hphase'
    hFm hF hK hK0 hallc hmin (by rw [hmult]; exact hdeg), P.prod_normalHalfExp_inv hK0 I hI hne]
  congr 2
  refine setIntegral_congr_fun hbaseM fun z hz => ?_
  rw [hq' z hz, hA' z hz 0 (Metric.mem_closedBall_self hε.le)]

end Atlas

end ProductMonomialChart

/-! ### Tied strata of the cover and the total coefficient at the extremal pair -/

namespace ResolutionCover

variable {d : ℕ} {ι : Type*} [Fintype ι] (R : ResolutionCover d ι) {K : (Fin d → ℝ) → ℝ}
  (Ps : ∀ i, ProductMonomialChart R i K) (hact : (R.activeCoords Ps).Nonempty)

theorem coverLam_le_ratio_of_mem (i : ι) : ∀ j ∈ (Ps i).e.support,
    R.coverLam Ps hact ≤ (Ps i).ratio j :=
  fun _ hj => R.coverLam_le_ratio Ps hact hj

theorem support_inter_minimalSet (i : ι) :
    (Ps i).e.support ∩ (Ps i).minimalSet (R.coverLam Ps hact) =
      (Ps i).minimalSet (R.coverLam Ps hact) :=
  inf_eq_right.2 ((Ps i).minimalSet_subset _)

/-- **The minimal multiplicity of any chart is at most `k* + 1`.** -/
theorem card_minimalSet_le (i : ι) (hne : ((Ps i).minimalSet (R.coverLam Ps hact)).Nonempty) :
    ((Ps i).minimalSet (R.coverLam Ps hact)).card - 1 ≤ R.coverDeg Ps hact := by
  have hsupp : (Ps i).e.support.Nonempty := hne.mono ((Ps i).minimalSet_subset _)
  have hlam : (Ps i).pieceLam (Ps i).e.support hsupp = R.coverLam Ps hact :=
    ((Ps i).pieceLam_eq_iff (R.coverLam_le_ratio_of_mem Ps hact i) _ subset_rfl hsupp).2
      (by rw [R.support_inter_minimalSet Ps hact i]; exact hne)
  have := R.pieceMult_le_coverDeg Ps hact i _ subset_rfl hsupp hlam
  rwa [(Ps i).pieceMult_eq_card_inter _ subset_rfl hsupp hlam,
    R.support_inter_minimalSet Ps hact i] at this

/-- **Classification of the tied strata**: a stratum `I ⊆ supp e_i` is tied at `(λ*, k*)` iff it
contains the minimal set `M_i` and `|M_i| = k* + 1`. -/
theorem tied_iff (i : ι) (I : Finset (Fin d)) (hI : I ⊆ (Ps i).e.support) (hne : I.Nonempty) :
    ((Ps i).pieceLam I hne = R.coverLam Ps hact ∧ (Ps i).pieceMult I hne - 1 = R.coverDeg Ps hact) ↔
      ((Ps i).minimalSet (R.coverLam Ps hact) ⊆ I ∧
        ((Ps i).minimalSet (R.coverLam Ps hact)).card = R.coverDeg Ps hact + 1) := by
  have hlow := R.coverLam_le_ratio_of_mem Ps hact i
  constructor
  · rintro ⟨h1, h2⟩
    have hM := (Ps i).pieceMult_eq_card_inter I hI hne h1
    have hneIM : (I ∩ (Ps i).minimalSet (R.coverLam Ps hact)).Nonempty :=
      ((Ps i).pieceLam_eq_iff hlow I hI hne).1 h1
    have hpos : 0 < (I ∩ (Ps i).minimalSet (R.coverLam Ps hact)).card := Finset.card_pos.2 hneIM
    have hle : (I ∩ (Ps i).minimalSet (R.coverLam Ps hact)).card ≤
        ((Ps i).minimalSet (R.coverLam Ps hact)).card :=
      Finset.card_le_card Finset.inter_subset_right
    have hMle := R.card_minimalSet_le Ps hact i (hneIM.mono Finset.inter_subset_right)
    have hMcard : ((Ps i).minimalSet (R.coverLam Ps hact)).card = R.coverDeg Ps hact + 1 := by
      omega
    have heq : I ∩ (Ps i).minimalSet (R.coverLam Ps hact) =
        (Ps i).minimalSet (R.coverLam Ps hact) :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
    exact ⟨inf_eq_right.1 heq, hMcard⟩
  · rintro ⟨hsub, hcard⟩
    have heq : I ∩ (Ps i).minimalSet (R.coverLam Ps hact) =
        (Ps i).minimalSet (R.coverLam Ps hact) :=
      inf_eq_right.2 hsub
    have hneM : ((Ps i).minimalSet (R.coverLam Ps hact)).Nonempty := Finset.card_pos.1 (by omega)
    have h1 : (Ps i).pieceLam I hne = R.coverLam Ps hact :=
      ((Ps i).pieceLam_eq_iff hlow I hI hne).2 (by rw [heq]; exact hneM)
    refine ⟨h1, ?_⟩
    rw [(Ps i).pieceMult_eq_card_inter I hI hne h1, heq, hcard]
    exact Nat.add_sub_cancel _ _

/-- **The all-minimal tied stratum is the minimal set.** -/
theorem eq_minimalSet_of_all_minimal (i : ι) (I : Finset (Fin d)) (hI : I ⊆ (Ps i).e.support)
    (hne : I.Nonempty) (hall : ∀ j ∈ I, (Ps i).ratio j = R.coverLam Ps hact)
    (hdeg : I.card - 1 = R.coverDeg Ps hact) : I = (Ps i).minimalSet (R.coverLam Ps hact) := by
  have hIsub : I ⊆ (Ps i).minimalSet (R.coverLam Ps hact) :=
    fun j hj => Finset.mem_filter.2 ⟨hI hj, hall j hj⟩
  have htied := (R.tied_iff Ps hact i I hI hne).1 ⟨(Ps i).pieceLam_eq_of_forall hne hall, by
    rw [(Ps i).pieceMult_eq_card_of_forall hne hall]; exact hdeg⟩
  exact Finset.Subset.antisymm hIsub htied.1

variable (hK0 : ∀ x, 0 ≤ K x) {ε : ℝ} (hε : 0 < ε) (hεb : ∀ i, ε ≤ (Ps i).b)
  {F : (Fin d → ℝ) → ℝ} {p : TubeWeight d}
  (hFc : ∀ i, ContinuousOn (fun y => F ((R.chart i).φ y)) (Ps i).W)
  (hpc : ∀ i, ContinuousOn (fun y => p.w ((R.chart i).φ y)) (Ps i).W) (hFm : Measurable F)
  (hF : Integrable (fun x => F x * p.w x) (volume.restrict (⋃ i, R.image i))) (hK : Measurable K)

include hK0 hε hεb hFc hpc hFm hF hK in
/-- An untied piece contributes nothing at `(λ₀, k₀)`. -/
theorem scalarAtlasPieceCoeff'_eq_zero_of_not_tied (lam₀ : ℝ) (k₀ : ℕ) (i : ι)
    (I : Finset (Fin d)) (hI : I ⊆ (Ps i).e.support) (hne : I.Nonempty)
    (h : ¬ ((Ps i).pieceLam I hne = lam₀ ∧ (Ps i).pieceMult I hne - 1 = k₀)) :
    scalarAtlasPieceCoeff' (R.productAtlasesD Ps hK0 hε hεb hFc hpc hFm hF hK) lam₀ k₀ i I = 0 := by
  rw [scalarAtlasPieceCoeff'_of_mem _ lam₀ k₀ i I hI hne]
  refine FiniteScalarUnitAtlas.sum_tied_eq_zero _ lam₀ k₀ fun σ hσ => h ?_
  have h1 := (Ps i).pieceAtlasD_cell_lam hK0 hε (hεb i) rfl (hFc i) (hpc i) hFm hF hK I hI hne σ
  have h2 := (Ps i).pieceAtlasD_cell_mult hK0 hε (hεb i) rfl (hFc i) (hpc i) hFm hF hK I hI hne σ
  exact ⟨h1.symm.trans hσ.1, by rw [← h2]; exact hσ.2⟩

include hK0 hε hεb hFc hpc hFm hF hK in
/-- **The total coefficient at the extremal pair is the sum over tied strata**: over the charts with
`|M_i| = k* + 1` and the strata `M_i ⊆ I ⊆ supp e_i`. -/
theorem productCoeffD_extremal_eq_sum_tied :
    R.productCoeffD Ps hK0 hε hεb hFc hpc hFm hF hK (R.coverLam Ps hact) (R.coverDeg Ps hact) =
      ∑ i, ∑ I ∈ ((Ps i).e.support.powerset.filter fun I => I.Nonempty).filter
          (fun I => (Ps i).minimalSet (R.coverLam Ps hact) ⊆ I ∧
            ((Ps i).minimalSet (R.coverLam Ps hact)).card = R.coverDeg Ps hact + 1),
        scalarAtlasPieceCoeff' (R.productAtlasesD Ps hK0 hε hεb hFc hpc hFm hF hK)
          (R.coverLam Ps hact) (R.coverDeg Ps hact) i I := by
  unfold productCoeffD
  refine Finset.sum_congr rfl fun i _ => (Finset.sum_filter_of_ne fun I hI hne0 => ?_).symm
  obtain ⟨hpow, hne⟩ := Finset.mem_filter.1 hI
  have hIsub := Finset.mem_powerset.1 hpow
  by_contra hnot
  exact hne0 (R.scalarAtlasPieceCoeff'_eq_zero_of_not_tied Ps hK0 hε hεb hFc hpc hFm hF hK _ _ i I
    hIsub hne fun htied => hnot ((R.tied_iff Ps hact i I hIsub hne).1 htied))

include hK0 hε hεb hFc hpc hFm hF hK in
/-- **The all-minimal piece coefficient in chart data**: for a chart with `|M_i| = k* + 1`, the
piece `I = M_i` contributes
`2^{|M_i|} · Γ(λ*)/k*! · ∏_{j∈M_i} 1/e_j · ∫_base β · scalarPhase^{−λ*} · pieceAmp(·, 0)`. -/
theorem scalarAtlasPieceCoeff'_minimalSet (i : ι)
    (hneM : ((Ps i).minimalSet (R.coverLam Ps hact)).Nonempty)
    (hM : ((Ps i).minimalSet (R.coverLam Ps hact)).card = R.coverDeg Ps hact + 1) :
    scalarAtlasPieceCoeff' (R.productAtlasesD Ps hK0 hε hεb hFc hpc hFm hF hK) (R.coverLam Ps hact)
        (R.coverDeg Ps hact) i ((Ps i).minimalSet (R.coverLam Ps hact)) =
      2 ^ ((Ps i).minimalSet (R.coverLam Ps hact)).card *
        ((Real.Gamma (R.coverLam Ps hact) /
            ((((Ps i).minimalSet (R.coverLam Ps hact)).card - 1).factorial : ℝ) *
          ∏ j ∈ (Ps i).minimalSet (R.coverLam Ps hact), 1 / ((Ps i).e j : ℝ)) *
        ∫ z in ((Ps i).pieceDensity (D := fun i => (Ps i).e.support) hε (hεb i) rfl
            ((Ps i).minimalSet (R.coverLam Ps hact)) ((Ps i).minimalSet_subset _) hneM p).base,
          ((Ps i).pieceDensity (D := fun i => (Ps i).e.support) hε (hεb i) rfl
            ((Ps i).minimalSet (R.coverLam Ps hact)) ((Ps i).minimalSet_subset _) hneM p).beta z *
            (scalarPhase _ hneM (Ps i).u (Ps i).e z ^ (-(R.coverLam Ps hact)) *
              R.pieceAmp i _ hneM (Ps i).h (Ps i).v (F := F) (p := p) z 0)) := by
  rw [scalarAtlasPieceCoeff'_of_mem _ _ _ i _ ((Ps i).minimalSet_subset _) hneM]
  exact (Ps i).tiedSum_of_all_minimal hK0 hε (hεb i) rfl hFm hF hK _ ((Ps i).minimalSet_subset _)
    hneM (fun _ hj => (Ps i).ratio_eq_of_mem_minimalSet hj)
    (by rw [hM]; exact Nat.add_sub_cancel _ _)
    ((Ps i).pieceAtlasD_data hK0 hε (hεb i) rfl (hFc i) (hpc i) hFm hF hK _ _ hneM)

include hK0 hε hεb hFc hpc hFm hF hK in
/-- **The total coefficient when every attaining chart is all-minimal on its active set**
(`M_i = supp e_i` whenever `|M_i| = k* + 1`): only the strata `I = M_i` survive, and the total is
the sum of the explicit all-minimal formulas. -/
theorem productCoeffD_extremal_eq_sum_minimal
    (hsupp : ∀ i, ((Ps i).minimalSet (R.coverLam Ps hact)).card = R.coverDeg Ps hact + 1 →
      (Ps i).minimalSet (R.coverLam Ps hact) = (Ps i).e.support) :
    R.productCoeffD Ps hK0 hε hεb hFc hpc hFm hF hK (R.coverLam Ps hact) (R.coverDeg Ps hact) =
      ∑ i, if hM : ((Ps i).minimalSet (R.coverLam Ps hact)).card = R.coverDeg Ps hact + 1 then
        2 ^ ((Ps i).minimalSet (R.coverLam Ps hact)).card *
          ((Real.Gamma (R.coverLam Ps hact) /
              ((((Ps i).minimalSet (R.coverLam Ps hact)).card - 1).factorial : ℝ) *
            ∏ j ∈ (Ps i).minimalSet (R.coverLam Ps hact), 1 / ((Ps i).e j : ℝ)) *
          ∫ z in ((Ps i).pieceDensity (D := fun i => (Ps i).e.support) hε (hεb i) rfl
              ((Ps i).minimalSet (R.coverLam Ps hact)) ((Ps i).minimalSet_subset _)
              (Finset.card_pos.1 (hM ▸ Nat.succ_pos _)) p).base,
            ((Ps i).pieceDensity (D := fun i => (Ps i).e.support) hε (hεb i) rfl
              ((Ps i).minimalSet (R.coverLam Ps hact)) ((Ps i).minimalSet_subset _)
              (Finset.card_pos.1 (hM ▸ Nat.succ_pos _)) p).beta z *
              (scalarPhase _ (Finset.card_pos.1 (hM ▸ Nat.succ_pos _)) (Ps i).u (Ps i).e z ^
                  (-(R.coverLam Ps hact)) *
                R.pieceAmp i _ (Finset.card_pos.1 (hM ▸ Nat.succ_pos _)) (Ps i).h (Ps i).v
                  (F := F) (p := p) z 0))
      else 0 := by
  rw [R.productCoeffD_extremal_eq_sum_tied Ps hact hK0 hε hεb hFc hpc hFm hF hK]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with hM
  · have hneM : ((Ps i).minimalSet (R.coverLam Ps hact)).Nonempty :=
      Finset.card_pos.1 (hM ▸ Nat.succ_pos _)
    have hset : ((Ps i).e.support.powerset.filter fun I => I.Nonempty).filter
        (fun I => (Ps i).minimalSet (R.coverLam Ps hact) ⊆ I ∧
          ((Ps i).minimalSet (R.coverLam Ps hact)).card = R.coverDeg Ps hact + 1) =
        {(Ps i).minimalSet (R.coverLam Ps hact)} := by
      ext I
      simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨hIsub, -⟩, hMsub, -⟩
        exact Finset.Subset.antisymm (hsupp i hM ▸ hIsub) hMsub
      · rintro rfl
        exact ⟨⟨(Ps i).minimalSet_subset _, hneM⟩, subset_rfl, hM⟩
    rw [hset, Finset.sum_singleton]
    exact R.scalarAtlasPieceCoeff'_minimalSet Ps hact hK0 hε hεb hFc hpc hFm hF hK i hneM hM
  · refine Finset.sum_eq_zero fun I hI => ?_
    exact absurd (Finset.mem_filter.1 hI).2.2 hM

end ResolutionCover

end Grammar
