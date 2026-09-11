/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.ProductChartPieceData

/-!
# The extremal pair of a cover of product charts

Unit 4 of consult #78 (`tide-log/gpt6_bigpicture_v78.md`). The cells of a piece atlas sit at the
pair `(minRatio (normalExp I h) (normalHalfExp I e), multCount … − 1)` in the normal coordinates of
the stratum; through the bijection `Fin |I| ≃ I` and the parity `e_j = 2k_j` this is the **divisor
pair** `(min_{j∈I} (h_j+1)/e_j, #{j ∈ I : (h_j+1)/e_j = min} − 1)` (`ratioExp_normal_eq`,
`minRatio_normal_eq`, `multCount_normal_eq`; for a product chart `productPieceLam_eq`,
`productPieceMult_eq`, the parity coming from the package). Over all chart–stratum pairs of a cover
the extremal pair is `λ* = min_{i, j ∈ J_i} (h_{ij}+1)/e_{ij}` and
`k* = max over charts attaining λ* of (#{j ∈ J_i : r_{ij} = λ*} − 1)` (`coverLam`, `coverDeg`),
  which
dominates every chart–stratum pair (`coverLam_le_pieceLam`, `pieceMult_le_coverDeg`), so the
end-to-end theorem holds at `(λ*, k*)`
  (`hasLeadingTerm_boltzmannIntegral_of_productCharts_extremal`);
with no active divisor coordinate at all, the integral is negligible at every power–log scale
(`hasLeadingTerm_boltzmannIntegral_of_no_active`).

Non-claims: `(λ*, k*)` is the GEOMETRIC extremal pair; it is the actual leading pair only if the
summed tied coefficient is nonzero (unit 5).
-/

open MeasureTheory Set Filter Topology Monomialize.Analytic Monomialize.VolumeScaling
open scoped ENNReal

namespace Grammar

/-! ### Pair identification through the stratum bijection -/

section Identify

variable {d : ℕ} (I : Finset (Fin d)) (hne : I.Nonempty) (e h : Fin d →₀ ℕ)
  (hpar : ∀ a, normalExp I hne e a = 2 * normalHalfExp I hne e a)

/-- The divisor ratio `(h_j+1)/e_j`. -/
noncomputable def divisorRatio (j : Fin d) : ℝ := ((h j : ℝ) + 1) / (e j : ℝ)

include hpar in
theorem ratioExp_normal_eq (a : Fin (I.card - 1 + 1)) :
    ratioExp (normalExp I hne h) (normalHalfExp I hne e) a =
      divisorRatio e h ((stratumSplit I hne).symm (Sum.inr a)) := by
  unfold ratioExp divisorRatio
  have h2 : (2 : ℝ) * (normalHalfExp I hne e a : ℝ) = (e ((stratumSplit I hne).symm (Sum.inr
    a)) : ℝ) := by
    have := hpar a
    unfold normalExp at this
    exact_mod_cast this.symm
  rw [h2]
  rfl

include hpar in
/-- **The exponent of a stratum is the minimal divisor ratio over `I`.** -/
theorem minRatio_normal_eq :
    minRatio (normalExp I hne h) (normalHalfExp I hne e) = I.inf' hne (divisorRatio e h) := by
  unfold minRatio
  refine le_antisymm ?_ ?_
  · refine Finset.le_inf' hne _ fun j hj => ?_
    obtain ⟨a, ha⟩ := exists_inr_of_mem I hne hj
    rw [ha, ← ratioExp_normal_eq I hne e h hpar a]
    exact Finset.inf'_le _ (Finset.mem_univ a)
  · refine Finset.le_inf' _ _ fun a _ => ?_
    rw [ratioExp_normal_eq I hne e h hpar a]
    exact Finset.inf'_le _ (stratumSplit_symm_inr_mem I hne a)

include hpar in
/-- **The multiplicity of a stratum is the number of minimising divisor coordinates.** -/
theorem multCount_normal_eq (l : ℝ) :
    multCount (ratioExp (normalExp I hne h) (normalHalfExp I hne e)) l =
      (I.filter fun j => divisorRatio e h j = l).card := by
  classical
  unfold multCount
  rw [Finset.sum_boole, Nat.cast_id]
  refine Finset.card_nbij (fun a => (stratumSplit I hne).symm (Sum.inr a)) ?_ ?_ ?_
  · intro a ha
    rw [Finset.mem_coe, Finset.mem_filter] at ha ⊢
    exact ⟨stratumSplit_symm_inr_mem I hne a, by
      rw [← ratioExp_normal_eq I hne e h hpar a]
      exact ha.2⟩
  · intro a _ b _ hab
    exact Sum.inr_injective ((stratumSplit I hne).symm.injective hab)
  · intro j hj
    rw [Finset.mem_coe, Finset.mem_filter] at hj
    obtain ⟨a, ha⟩ := exists_inr_of_mem I hne hj.1
    refine ⟨a, Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_univ a, ?_⟩), ha.symm⟩
    rw [ratioExp_normal_eq I hne e h hpar a, ← ha]
    exact hj.2

end Identify

/-! ### The parity and the divisor pair of a product chart -/

namespace ProductMonomialChart

variable {d : ℕ} {ι : Type*} [Fintype ι] {R : ResolutionCover d ι} {i : ι} {K : (Fin d → ℝ) → ℝ}
  (P : ProductMonomialChart R i K)

theorem ratio_eq (j : Fin d) : P.ratio j = divisorRatio P.e P.h j := rfl

/-- Parity of the normal exponents of every stratum of a product chart, from `K ≥ 0`. -/
theorem normalExp_eq_two_mul (hK0 : ∀ x, 0 ≤ K x) (I : Finset (Fin d)) (hI : I ⊆ P.e.support)
    (hne : I.Nonempty) (a : Fin (I.card - 1 + 1)) :
    normalExp I hne P.e a = 2 * normalHalfExp I hne P.e a := by
  obtain ⟨y₀, hy₀, hz⟩ := exists_zeroPoint P.e.support P.T P.b P.T_nonempty P.T_zero P.b_pos.le
  have hy₀W : y₀ ∈ P.W := P.dom_subset (P.mem_dom_of_mem_productDom hy₀)
  exact normalExp_eq_two_mul_halfExp I hne P.e P.W_open (K := fun y => K ((R.chart i).φ y))
    P.phase_eq (fun y _ => hK0 _) hy₀W (P.u_cont.continuousAt (P.W_open.mem_nhds hy₀W))
    (P.u_ne y₀ hy₀W) (fun j hj => hz j (hI hj)) a

theorem pieceLam_eq (hK0 : ∀ x, 0 ≤ K x) (I : Finset (Fin d)) (hI : I ⊆ P.e.support)
    (hne : I.Nonempty) :
    minRatio (normalExp I hne P.h) (normalHalfExp I hne P.e) = P.pieceLam I hne :=
  minRatio_normal_eq I hne P.e P.h (P.normalExp_eq_two_mul hK0 I hI hne)

theorem pieceMult_eq (hK0 : ∀ x, 0 ≤ K x) (I : Finset (Fin d)) (hI : I ⊆ P.e.support)
    (hne : I.Nonempty) :
    multCount (ratioExp (normalExp I hne P.h) (normalHalfExp I hne P.e))
      (minRatio (normalExp I hne P.h) (normalHalfExp I hne P.e)) = P.pieceMult I hne := by
  rw [multCount_normal_eq I hne P.e P.h (P.normalExp_eq_two_mul hK0 I hI hne),
    P.pieceLam_eq hK0 I hI hne]
  rfl

end ProductMonomialChart

namespace ResolutionCover

variable {d : ℕ} {ι : Type*} [Fintype ι] (R : ResolutionCover d ι) {K : (Fin d → ℝ) → ℝ}
  (Ps : ∀ i, ProductMonomialChart R i K) (hK0 : ∀ x, 0 ≤ K x)

include hK0 in
theorem productPieceLam_eq (i : ι) (I : Finset (Fin d)) (hI : I ⊆ (Ps i).e.support)
    (hne : I.Nonempty) : R.productPieceLam Ps i I hne = (Ps i).pieceLam I hne :=
  (Ps i).pieceLam_eq hK0 I hI hne

include hK0 in
theorem productPieceMult_eq (i : ι) (I : Finset (Fin d)) (hI : I ⊆ (Ps i).e.support)
    (hne : I.Nonempty) : R.productPieceMult Ps i I hne = (Ps i).pieceMult I hne :=
  (Ps i).pieceMult_eq hK0 I hI hne

/-! ### The extremal pair over chart–stratum pairs -/

/-- The active coordinates of the cover: pairs `(i, j)` with `j ∈ supp e_i`. -/
def activeCoords : Finset (Σ _ : ι, Fin d) := Finset.univ.sigma fun i => (Ps i).e.support

/-- **The extremal exponent** `λ* = min_{i, j ∈ J_i} (h_{ij}+1)/e_{ij}`. -/
noncomputable def coverLam (hact : (R.activeCoords Ps).Nonempty) : ℝ :=
  (R.activeCoords Ps).inf' hact fun x => (Ps x.1).ratio x.2

/-- **The extremal log degree** `k* = max over charts attaining λ* of (#{j ∈ J_i : r_ij = λ*} −
  1)`. -/
noncomputable def coverDeg (hact : (R.activeCoords Ps).Nonempty) : ℕ :=
  (Finset.univ.filter fun i => ∃ j ∈ (Ps i).e.support, (Ps i).ratio j = R.coverLam Ps hact).sup
    fun i => ((Ps i).e.support.filter fun j => (Ps i).ratio j = R.coverLam Ps hact).card - 1

theorem mem_activeCoords {i : ι} {j : Fin d} (hj : j ∈ (Ps i).e.support) :
    (⟨i, j⟩ : Σ _ : ι, Fin d) ∈ R.activeCoords Ps :=
  Finset.mem_sigma.2 ⟨Finset.mem_univ i, hj⟩

theorem coverLam_le_ratio (hact) {i : ι} {j : Fin d} (hj : j ∈ (Ps i).e.support) :
    R.coverLam Ps hact ≤ (Ps i).ratio j :=
  Finset.inf'_le (fun x : Σ _ : ι, Fin d => (Ps x.1).ratio x.2) (R.mem_activeCoords Ps hj)

/-- The extremal exponent is below every chart–stratum exponent. -/
theorem coverLam_le_pieceLam (hact) (i : ι) (I : Finset (Fin d)) (hI : I ⊆ (Ps i).e.support)
    (hne : I.Nonempty) : R.coverLam Ps hact ≤ (Ps i).pieceLam I hne :=
  Finset.le_inf' hne _ fun _ hj => R.coverLam_le_ratio Ps hact (hI hj)

/-- At the extremal exponent, the chart–stratum multiplicity minus one is at most `k*`. -/
theorem pieceMult_le_coverDeg (hact) (i : ι) (I : Finset (Fin d)) (hI : I ⊆ (Ps i).e.support)
    (hne : I.Nonempty) (hlam : (Ps i).pieceLam I hne = R.coverLam Ps hact) :
    (Ps i).pieceMult I hne - 1 ≤ R.coverDeg Ps hact := by
  classical
  obtain ⟨j₀, hj₀, hmin⟩ := Finset.exists_mem_eq_inf' hne (Ps i).ratio
  have hattains : i ∈ Finset.univ.filter fun i => ∃ j ∈ (Ps i).e.support,
      (Ps i).ratio j = R.coverLam Ps hact :=
    Finset.mem_filter.2 ⟨Finset.mem_univ i, j₀, hI hj₀, by
      unfold ProductMonomialChart.pieceLam at hlam
      rw [← hmin]
      exact hlam⟩
  refine le_trans ?_ (Finset.le_sup (f := fun i =>
    ((Ps i).e.support.filter fun j => (Ps i).ratio j = R.coverLam Ps hact).card - 1) hattains)
  unfold ProductMonomialChart.pieceMult
  rw [hlam]
  exact Nat.sub_le_sub_right (Finset.card_le_card fun j hj => by
    rw [Finset.mem_filter] at hj ⊢
    exact ⟨hI hj.1, hj.2⟩) 1

variable {ε : ℝ} (hε : 0 < ε) (hεb : ∀ i, ε ≤ (Ps i).b) {F : (Fin d → ℝ) → ℝ} {p : TubeWeight d}
  (hFc : ∀ i, ContinuousOn (fun y => F ((R.chart i).φ y)) (Ps i).W)
  (hpc : ∀ i, ContinuousOn (fun y => p.w ((R.chart i).φ y)) (Ps i).W) (hFm : Measurable F)
  (hF : Integrable (fun x => F x * p.w x) (volume.restrict (⋃ i, R.image i))) (hK : Measurable K)

include hK0 hε hεb hFc hpc hFm hF hK in
/-- **The end-to-end theorem at the extremal pair**: with at least one active divisor coordinate,
the resolved Boltzmann integral of a cover of product charts has the leading-term certificate at
`(λ*, k*)`, with coefficient the sum of the tied cell coefficients. -/
theorem hasLeadingTerm_boltzmannIntegral_of_productCharts_extremal
    (hact : (R.activeCoords Ps).Nonempty) :
    HasLeadingTerm (R.boltzmannIntegral F K p)
      (∑ i, ∑ I ∈ (Ps i).e.support.powerset.filter (fun I => I.Nonempty),
        scalarAtlasPieceCoeff' (R.productAtlases Ps hK0 hε hεb hFc hpc hFm hF hK)
          (R.coverLam Ps hact) (R.coverDeg Ps hact) i I)
      (R.coverLam Ps hact) (R.coverDeg Ps hact) :=
  R.hasLeadingTerm_boltzmannIntegral_of_productCharts Ps hK0 hε hεb hFc hpc hFm hF hK
    (R.coverLam Ps hact) (R.coverDeg Ps hact)
    (fun i I hI hne => by
      rw [R.productPieceLam_eq Ps hK0 i I hI hne]
      exact R.coverLam_le_pieceLam Ps hact i I hI hne)
    (fun i I hI hne hlam => by
      rw [R.productPieceLam_eq Ps hK0 i I hI hne] at hlam
      rw [R.productPieceMult_eq Ps hK0 i I hI hne]
      exact R.pieceMult_le_coverDeg Ps hact i I hI hne hlam)

include hK0 hε hFm hF hK in
/-- **No active divisor coordinate**: the integral is negligible at every power–log scale. -/
theorem hasLeadingTerm_boltzmannIntegral_of_no_active (hno : ∀ i, (Ps i).e.support = ∅)
    (lam : ℝ) (k : ℕ) : HasLeadingTerm (R.boltzmannIntegral F K p) 0 lam k := by
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

end Grammar
