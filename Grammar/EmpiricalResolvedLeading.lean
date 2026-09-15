/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.EmpiricalPieceIntegral

/-!
# The empirical leading theorem on the resolved manifold

For a root field `ξ` (continuous branch representatives on the pieces, `|ψ| ≤ M`) and a
chart-leading pair `(λ, m)` of the resolved chart transport, the **empirical partition function**
`Z^{emp}_N[F; ξ] = ∫_U e^{−N K∘π + √N √(K∘π) ψ} F dμ_U` has the leading term
`N^{−λ}(log N)^{m−1} · Σ_{pieces} ∫_{Base} boxFaceLimit_p(s) dν_p(s)`
(`hasLeadingTerm_empZ`): the tail is exponentially small (`hasLeadingTerm_tail_zero`), the cores
are the empirical piece integrals. For a test `F` supported in `X = U ∖ D_{m+1}` the limit is the
integral of `F` against the **empirical stratum measure** `ν^λ_m(ξ)` of `EmpiricalStratumMeasure`
(`integral_empiricalStratumMeasure_eq_sum`, `hasLeadingTerm_empZ_eq_integral`): the leading term
of the empirical partition function is the population residue measure weighted by the fluctuation
density `S_λ(ξ̂)/Γ(λ)` of the branch trace of the field. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff Manifold
open Monomialize.VolumeScaling Monomialize.Transport Monomialize.Manifold
open Grammar.NormalCrossing Grammar.NormalCrossing.EvenChartBoxDepth

namespace Grammar

namespace SmoothEngine

namespace ResolvedData

variable {d : ℕ} (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)

/-- The empirical partition function `∫_U e^{−N K∘π + √N √(K∘π) ψ} F dμ_U`. -/
noncomputable def empZ (ξ : Ξ.RootField Y) (N : ℝ) : ℝ := ∫ P, Ξ.empIntegrand Y ξ N P ∂Ξ.μU

theorem tailU_le_μU : Y.tailU ≤ Ξ.μU := (Ξ.decomp Y).tail_le

/-- **The core decomposition of the empirical partition function**. -/
theorem empZ_eq_sum (ξ : Ξ.RootField Y) {N : ℝ} (hN : 0 ≤ N) {M : ℝ} (hM : ∀ P, |ξ.ψ P| ≤ M) :
    Ξ.empZ Y ξ N = ∑ p, Ξ.empPieceInt Y p ξ N + ∫ P, Ξ.empIntegrand Y ξ N P ∂Y.tailU := by
  have hint := Ξ.integrable_empIntegrand Y ξ hN hM
  unfold empZ
  have hcores : ∑ p, Ξ.coreMeasure Y p ≤ Ξ.μU := by
    rw [← Ξ.sum_coreMeasure Y]
    exact Measure.le_add_right le_rfl
  rw [← Ξ.sum_coreMeasure Y, integral_add_measure (hint.mono_measure hcores)
    (hint.mono_measure (Ξ.tailU_le_μU Y)),
    integral_finsetSum_measure fun p _ => hint.mono_measure (Ξ.coreMeasure_le_μU Y p)]
  congr 1
  exact Finset.sum_congr rfl fun p _ => Ξ.integral_coreMeasure_empIntegrand Y p ξ hN hM

/-! ### The tail -/

/-- The empirical tail integral is exponentially small: `|∫_tail| ≤ e^{M²/2}(∫|F|) e^{−δN/2}`. -/
theorem abs_integral_tail_le (ξ : Ξ.RootField Y) {N : ℝ} (hN : 0 ≤ N) {M : ℝ}
    (hM : ∀ P, |ξ.ψ P| ≤ M) :
    |∫ P, Ξ.empIntegrand Y ξ N P ∂Y.tailU| ≤
      (Real.exp (M ^ 2 / 2) * ∫ P, |Ξ.F P| ∂Y.tailU) * Real.exp (-(Y.T.δ / 2) * N) := by
  have hF : Integrable Ξ.F Y.tailU := Ξ.F_int.mono_measure (Ξ.tailU_le_μU Y)
  have hbound : ∀ᵐ P ∂Y.tailU, ‖Ξ.empIntegrand Y ξ N P‖ ≤
      Real.exp (M ^ 2 / 2) * Real.exp (-(Y.T.δ / 2) * N) * |Ξ.F P| := by
    filter_upwards [Y.ae_tailU_gap Ξ.hK0 Ξ.prior_compact Ξ.prior_W] with P hP
    have hK : Y.T.δ ≤ Ξ.phaseU P := hP
    have hK0 := Ξ.phaseU_nonneg P
    unfold empIntegrand
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have hs : 0 ≤ Real.sqrt N * Real.sqrt (Ξ.phaseU P) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have h1 : Real.sqrt N * Real.sqrt (Ξ.phaseU P) * ξ.ψ P ≤
        Real.sqrt N * Real.sqrt (Ξ.phaseU P) * M :=
      mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hM P)) hs
    have hsq : (Real.sqrt N * Real.sqrt (Ξ.phaseU P)) ^ 2 = N * Ξ.phaseU P := by
      rw [mul_pow, Real.sq_sqrt hN, Real.sq_sqrt hK0]
    nlinarith [sq_nonneg (Real.sqrt N * Real.sqrt (Ξ.phaseU P) - M),
      mul_le_mul_of_nonneg_left hK hN]
  have := norm_integral_le_of_norm_le ((hF.abs.const_mul _)) hbound
  rw [Real.norm_eq_abs] at this
  refine this.trans (le_of_eq ?_)
  rw [integral_const_mul]
  ring

/-- The tail contributes nothing at any power–log scale. -/
theorem hasLeadingTerm_tail_zero (ξ : Ξ.RootField Y) {M : ℝ} (hM : ∀ P, |ξ.ψ P| ≤ M) (lam : ℝ)
    (q : ℕ) :
    HasLeadingTerm (fun N => ∫ P, Ξ.empIntegrand Y ξ N P ∂Y.tailU) 0 lam q := by
  unfold HasLeadingTerm
  set C := Real.exp (M ^ 2 / 2) * ∫ P, |Ξ.F P| ∂Y.tailU with hC
  have hexp : Tendsto (fun N : ℝ => N ^ lam * Real.exp (-(Y.T.δ / 2) * N)) atTop (𝓝 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero lam (Y.T.δ / 2) (by linarith [Y.T.δ_pos])
  have h1 := hexp.const_mul C
  rw [mul_zero] at h1
  have h0 := h1.zero_mul_isBoundedUnder_le (SmoothEngine.isBoundedUnder_inv_log_pow q)
  refine squeeze_zero_norm' ?_ h0
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
  have hN0 : 0 < N := by linarith
  have hlog : 0 < Real.log N := Real.log_pos hN
  have hscale : 0 < powLogScale lam q N := powLogScale_pos _ _ hN
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hscale, div_le_iff₀ hscale]
  calc |∫ P, Ξ.empIntegrand Y ξ N P ∂Y.tailU|
      ≤ C * Real.exp (-(Y.T.δ / 2) * N) := Ξ.abs_integral_tail_le Y ξ hN0.le hM
    _ = C * (N ^ lam * Real.exp (-(Y.T.δ / 2) * N)) * (Real.log N ^ q)⁻¹ * powLogScale lam q N := by
        unfold powLogScale
        rw [Real.rpow_neg hN0.le]
        field_simp

/-! ### The leading term -/

/-- ★★★ **The empirical leading theorem**: at a chart-leading pair `(λ, m)` and for a bounded root
field, `Z^{emp}_N[F; ξ] / (N^{−λ}(log N)^{m−1}) → Σ_p ∫_{Base} boxFaceLimit_p dν_p`. -/
theorem hasLeadingTerm_empZ (ξ : Ξ.RootField Y) {lam : ℝ} {m : ℕ} (hm : 1 ≤ m)
    (hlead : Ξ.ChartLeading Y lam m) {M : ℝ} (hM : ∀ P, |ξ.ψ P| ≤ M) :
    HasLeadingTerm (Ξ.empZ Y ξ)
      (∑ p, ∫ s, Ξ.pieceFaceLimit Y p ξ lam m s ∂(Ξ.piecePresentation Y p).ν) lam (m - 1) := by
  have hsum := HasLeadingTerm.sum (lam := lam) (k := m - 1) Finset.univ
    (Z := fun p N => Ξ.empPieceInt Y p ξ N)
    (c := fun p => ∫ s, Ξ.pieceFaceLimit Y p ξ lam m s ∂(Ξ.piecePresentation Y p).ν)
    fun p _ => Ξ.hasLeadingTerm_empPieceInt Y p ξ hm (hlead p)
  have hall := hsum.add (Ξ.hasLeadingTerm_tail_zero Y ξ hM lam (m - 1))
  rw [add_zero] at hall
  refine hall.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with N hN
  exact (Ξ.empZ_eq_sum Y ξ hN hM).symm

/-! ### Identification with the empirical stratum measure -/

theorem mem_simpleFaces_iff (p : (Ξ.X Y).PIdx) (lam : ℝ) (m : ℕ)
    {J : Finset (Fin ((Ξ.X Y).da p))} :
    J ∈ Ξ.simpleFaces Y p lam m ↔ J.card = m ∧ J ⊆ resSet ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) lam := by
  unfold simpleFaces
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  refine and_congr Iff.rfl (forall₂_congr fun j _ => ?_)
  rw [mem_resSet]
  unfold ratioExp
  have hk : (0 : ℝ) < 2 * (Ξ.X Y).kA p j := by
    have := Nat.cast_pos (α := ℝ) |>.2 ((Ξ.X Y).kA_pos p j)
    positivity
  rw [div_eq_iff hk.ne']
  constructor <;> intro h <;> linarith

theorem simpleFaces_eq_singleton (p : (Ξ.X Y).PIdx) {lam : ℝ} {m : ℕ}
    (hmc : multCount (ratioExp ((Ξ.X Y).hA p) ((Ξ.X Y).kA p)) lam = m) :
    Ξ.simpleFaces Y p lam m = {resSet ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) lam} := by
  ext J
  rw [Ξ.mem_simpleFaces_iff, Finset.mem_singleton]
  constructor
  · rintro ⟨hJ, hsub⟩
    exact Finset.eq_of_subset_of_card_le hsub (by rw [card_resSet, hmc, hJ])
  · rintro rfl
    exact ⟨by rw [card_resSet, hmc], subset_rfl⟩

theorem simpleFaces_eq_empty (p : (Ξ.X Y).PIdx) {lam : ℝ} {m : ℕ}
    (hmc : multCount (ratioExp ((Ξ.X Y).hA p) ((Ξ.X Y).kA p)) lam < m) :
    Ξ.simpleFaces Y p lam m = ∅ := by
  ext J
  rw [Ξ.mem_simpleFaces_iff]
  simp only [Finset.notMem_empty, iff_false, not_and]
  intro hJ hsub
  have := Finset.card_le_card hsub
  rw [card_resSet, hJ] at this
  omega

theorem faceNorm'_eq_inv_prod (p : (Ξ.X Y).PIdx) (J : Finset (Fin ((Ξ.X Y).da p))) :
    Ξ.faceNorm' Y p J = (∏ i ∈ J, (2 * ((Ξ.X Y).kA p i : ℝ)))⁻¹ := by
  unfold faceNorm'
  rw [← Finset.prod_inv_distrib]
  exact (Finset.prod_subtype J (fun _ => inJ_iff.symm) fun i => (2 * ((Ξ.X Y).kA p i : ℝ))⁻¹).symm

/-- ★★ **The piece face limit is the empirical face integral**: for a test `F` and a chart-leading
piece, `∫_{Base} boxFaceLimit_p dν_p = Σ_{J simple} residueConst · ∫ F dempFaceMeasure_{p,J}`. -/
theorem integral_pieceFaceLimit_eq (p : (Ξ.X Y).PIdx) (ξ : Ξ.RootField Y) {lam : ℝ} (hμ : 0 < lam)
    {m : ℕ} (hlead : BoxLeading ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) lam m) (hFt : Ξ.IsTest m Ξ.F) :
    ∫ s, Ξ.pieceFaceLimit Y p ξ lam m s ∂(Ξ.piecePresentation Y p).ν =
      ∑ J ∈ Ξ.simpleFaces Y p lam m,
        residueConst lam m * ∫ x, Ξ.F x.1 ∂(Ξ.empFaceMeasure Y p J ξ lam m) := by
  by_cases hmc : multCount (ratioExp ((Ξ.X Y).hA p) ((Ξ.X Y).kA p)) lam = m
  · rw [Ξ.simpleFaces_eq_singleton Y p hmc, Finset.sum_singleton]
    have hJc : (resSet ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) lam).card = m := by
      rw [card_resSet, hmc]
    rw [Ξ.integral_empFaceMeasure_eq Y p _ ξ hμ Ξ.F_smooth.continuous hFt.2, ← integral_const_mul]
    unfold faceRef
    rw [integral_prod _ ((Ξ.integrable_empFaceDensity_mul Y p _ ξ hμ hJc Ξ.F_smooth
      hFt).const_mul (residueConst lam m))]
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    simp only [pieceFaceLimit, boxFaceLimit, if_pos hmc, faceFunctional]
    rw [← integral_const_mul]
    set J := resSet ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) lam with hJ
    refine setIntegral_congr_fun (measurableSet_box _) fun w hw => ?_
    have hface := Ξ.faceDensity_mul_eq Y p J Ξ.F_smooth lam (z := (s, w)) hw
    have hamp : (Ξ.ampObs Y p Ξ.F_smooth).amp s (glue J 0 w) =
      (Ξ.amp Y p).amp s (glue J 0 w) := rfl
    rw [hamp] at hface
    unfold empFaceDensity
    rw [show Ξ.faceDensity Y p J lam (s, w) * fluctDensity lam (Ξ.faceTrace Y p J ξ (s, w)) *
        Ξ.F (Ξ.faceMap Y p J (s, w)) =
        fluctDensity lam (Ξ.faceTrace Y p J ξ (s, w)) *
          (Ξ.faceDensity Y p J lam (s, w) * Ξ.F (Ξ.faceMap Y p J (s, w))) by ring, hface,
      Ξ.faceNorm'_eq_inv_prod Y p J]
    unfold faceTrace fluctDensity residueConst
    dsimp only
    rw [hmc]
    have hΓ : Real.Gamma lam ≠ 0 := (Real.Gamma_pos_of_pos hμ).ne'
    have hfact : ((m - 1).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
    have hprod : (∏ i ∈ J, (2 * ((Ξ.X Y).kA p i : ℝ))) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun i _ => by
        have := Nat.cast_pos (α := ℝ) |>.2 ((Ξ.X Y).kA_pos p i)
        positivity
    field_simp
  · have hlt : multCount (ratioExp ((Ξ.X Y).hA p) ((Ξ.X Y).kA p)) lam < m :=
      lt_of_le_of_ne hlead.2 hmc
    rw [Ξ.simpleFaces_eq_empty Y p hlt, Finset.sum_empty]
    refine integral_eq_zero_of_ae (Eventually.of_forall fun s => ?_)
    simp only [pieceFaceLimit, boxFaceLimit, if_neg hmc, Pi.zero_apply]

/-- ★★★ **The limit is the integral against the empirical stratum measure**: for a test `F`,
`Σ_p ∫_{Base} boxFaceLimit_p dν_p = ∫_X F dν^λ_m(ξ)`. -/
theorem integral_empiricalStratumMeasure_eq_sum (ξ : Ξ.RootField Y) {lam : ℝ} (hμ : 0 < lam)
    {m : ℕ} (hlead : Ξ.ChartLeading Y lam m) (hFt : Ξ.IsTest m Ξ.F) :
    ∫ x, Ξ.F x.1 ∂(Ξ.empiricalStratumMeasure Y ξ lam m) =
      ∑ p, ∫ s, Ξ.pieceFaceLimit Y p ξ lam m s ∂(Ξ.piecePresentation Y p).ν := by
  unfold empiricalStratumMeasure empiricalChartMeasure
  have hIf : ∀ (I : Fin (Fintype.card (Ξ.X Y).PIdx)), ∀ J ∈ Ξ.simpleFaces Y ((Ξ.X Y).en I) lam m,
      Integrable (fun x => Ξ.F x.1) (Ξ.empFaceMeasure Y ((Ξ.X Y).en I) J ξ lam m) :=
    fun I J hJ => Ξ.integrable_empFaceMeasure_test Y ξ hμ _ (Finset.mem_filter.1 hJ).2.1 Ξ.F_smooth
      hFt
  rw [integral_smul_measure, ENNReal.toReal_ofReal (residueConst_pos hμ m).le, smul_eq_mul,
    integral_finsetSum_measure fun I _ => integrable_finsetSum_measure.2 (hIf I), Finset.mul_sum]
  rw [← Equiv.sum_comp (Ξ.X Y).en fun p => ∫ s, Ξ.pieceFaceLimit Y p ξ lam m s
    ∂(Ξ.piecePresentation Y p).ν]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [integral_finsetSum_measure (hIf I), Finset.mul_sum,
    Ξ.integral_pieceFaceLimit_eq Y _ ξ hμ (hlead _) hFt]

/-- ★★★ **The empirical leading theorem, in the form of the empirical stratum measure**: for a
test `F` supported in `X = U ∖ D_{m+1}`, a bounded root field `ξ` and a chart-leading pair
`(λ, m)`, `N^{λ}(log N)^{−(m−1)} Z^{emp}_N[F; ξ] → ∫_X F dν^λ_m(ξ)`. -/
theorem hasLeadingTerm_empZ_eq_integral (ξ : Ξ.RootField Y) {lam : ℝ} (hμ : 0 < lam) {m : ℕ}
    (hm : 1 ≤ m) (hlead : Ξ.ChartLeading Y lam m) {M : ℝ} (hM : ∀ P, |ξ.ψ P| ≤ M)
    (hFt : Ξ.IsTest m Ξ.F) :
    HasLeadingTerm (Ξ.empZ Y ξ) (∫ x, Ξ.F x.1 ∂(Ξ.empiricalStratumMeasure Y ξ lam m)) lam
      (m - 1) := by
  rw [Ξ.integral_empiricalStratumMeasure_eq_sum Y ξ hμ hlead hFt]
  exact Ξ.hasLeadingTerm_empZ Y ξ hm hlead hM

end ResolvedData

end SmoothEngine

end Grammar
