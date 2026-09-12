/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.VariableResidualFormula
import Grammar.VariableUnitSquareExample
import Grammar.VariableUnitCellRegressions
import Grammar.MixedExponentPosterior

/-!
# The residual example with a unit depending on all coordinates, end to end (CCLXVIII)

`K(y) = (1 + y₀² + y₁²) y₀² y₁⁴` on `[−1,1]²` through the variable-unit product-chart theorem: the
extremal pair is `(1/4, 0)`, the minimal set is `{1}`, the `{1}`-piece has a null base at the cutoff
`ε = b = 1`, and the `{0,1}`-piece is tied but NOT all-minimal: its residual coordinate `y₀` is
kept, and the unit restricted to the minimal face `y₁ = 0` is `1 + y₀²`. The residual face formula
(CCLXVII) gives

* ★ `∫_{[−1,1]²} e^{−N K} dy ~ Γ(1/4) · I · N^{−1/4}` with `I = ∫₀¹ t^{−1/2} (1+t²)^{−1/4} dt`
  (`integral_isEquivalent`; `I ≈ 1.9234`, so the constant `≈ 6.97` differs from the origin-frozen
  value `2Γ(1/4) ≈ 7.25` — this is the end-to-end version of CCLVII's direct-cell regression);
* ★ `E_N[y₀²] → J / I` with `J = ∫₀¹ t^{3/2} (1+t²)^{−1/4} dt` (`tendsto_posteriorExpectation_sq`;
  `J ≈ 0.3600`, `J/I ≈ 0.1872 ∈ (0, 1]`, `J_pos`, `J_le_I`): the limiting posterior density along
  the face `y₁ = 0` is `∝ |y₀|^{−1/2} (1+y₀²)^{−1/4}` — the unit shapes the limiting posterior.
-/

open MeasureTheory Set Filter Topology Asymptotics Monomialize.Analytic Monomialize.VolumeScaling
open scoped ENNReal

namespace Grammar

/-! ### A piece with a null base contributes nothing (variable-unit version) -/

namespace ProductMonomialChartVar

variable {d : ℕ} {ι : Type*} [Fintype ι] {R : ResolutionCover d ι} {i : ι} {K : (Fin d → ℝ) → ℝ}
  (P : ProductMonomialChartVar R i K) (hK0 : ∀ x, 0 ≤ K x) {ε : ℝ} (hε : 0 < ε) (hεb : ε ≤ P.b)
  {D : ι → Finset (Fin d)} (hD : D i = P.e.support) {F : (Fin d → ℝ) → ℝ} {p : TubeWeight d}
  (hFm : Measurable F)
  (hF : Integrable (fun x => F x * p.w x) (volume.restrict (⋃ i, R.image i)))
  (hK : Measurable K) (I : Finset (Fin d)) (hI : I ⊆ P.e.support) (hne : I.Nonempty)

theorem tiedSum_eq_zero_of_null (lam₀ : ℝ) (k₀ : ℕ)
    (hnull : volume (P.pieceDensity hε hεb hD I hI hne p).base = 0)
    {At : FiniteVarUnitAtlas (d - (I.card - 1 + 1)) (R.pieceIntegral D ε i I F K p)}
    (hAt : P.IsVarPieceAtlasData hK0 hε hεb hD hFm hF hK I hI hne At) :
    ∑ σ ∈ At.tied lam₀ k₀, (At.cell σ).coeff = 0 := by
  obtain ⟨qv, A', hqv, hqv_pos, hA'c, hk, hbase, hβ, hamp', hphase', -, -, rfl⟩ := hAt
  refine Finset.sum_eq_zero fun σ _ => ?_
  unfold VarUnitCell.coeff
  exact setIntegral_measure_zero _ hnull

end ProductMonomialChartVar

namespace VarMixedExample

open MixedExample (ex ex_zero ex_one ex_support box_eq_productDom' Fsq continuous_Fsq)

/-- The phase `K(y) = (1 + y₀² + y₁²) y₀² y₁⁴`. -/
noncomputable def K (y : Fin 2 → ℝ) : ℝ := VarSquareExample.unit y * monomialEval y ex

theorem K_eq (y : Fin 2 → ℝ) : K y = (1 + y 0 ^ 2 + y 1 ^ 2) * (y 0 ^ 2 * y 1 ^ 4) := by
  unfold K
  rw [← MixedExample.K_eq]
  rfl

theorem K_nonneg (y : Fin 2 → ℝ) : 0 ≤ K y := by
  rw [K_eq]
  positivity

theorem continuous_K : Continuous K := by
  have : K = fun y => (1 + y 0 ^ 2 + y 1 ^ 2) * (y 0 ^ 2 * y 1 ^ 4) := funext K_eq
  rw [this]
  fun_prop

theorem isMonomialChart :
    IsMonomialChart K SquareExample.chart.φ SquareExample.chart.dom ex 0 univ where
  isOpen := isOpen_univ
  subset := subset_univ _
  analyticOnNhd := analyticOnNhd_id
  injOn := injOn_id _
  exists_unit := ⟨VarSquareExample.unit, VarSquareExample.continuous_unit.continuousOn,
    fun y _ => (VarSquareExample.unit_pos y).ne', fun _ _ => rfl⟩
  exists_jacUnit := ⟨fun _ => 1, continuousOn_const, fun _ _ => one_ne_zero, fun y _ => by
    change (fderiv ℝ (id : (Fin 2 → ℝ) → (Fin 2 → ℝ)) y).det = 1 * monomialEval y 0
    rw [SquareExample.det_id_eq, monomialEval_zero, one_mul]⟩

/-- **The variable-unit package.** -/
noncomputable def package :
    ProductMonomialChartVar (ResolutionCover.ofChart SquareExample.chart) () K where
  e := ex
  h := 0
  W := univ
  W_open := isOpen_univ
  dom_subset := subset_univ _
  monomial := isMonomialChart
  u := VarSquareExample.unit
  u_cont := VarSquareExample.continuous_unit.continuousOn
  u_ne := fun y _ => (VarSquareExample.unit_pos y).ne'
  phase_eq := fun _ _ => rfl
  v := fun _ => 1
  v_cont := continuousOn_const
  det_eq := fun y _ => by
    change (fderiv ℝ (id : (Fin 2 → ℝ) → (Fin 2 → ℝ)) y).det = 1 * monomialEval y 0
    rw [SquareExample.det_id_eq, monomialEval_zero, one_mul]
  T := {0}
  T_compact := isCompact_singleton
  T_nonempty := singleton_nonempty _
  T_zero := fun x hx j _ => by rw [mem_singleton_iff.1 hx]; rfl
  b := 1
  b_pos := one_pos
  dom_eq := box_eq_productDom'
  r := fun _ => 1
  r_meas := measurable_const
  Cr := 1
  r_bound := fun _ => by simp
  weight_eq := fun y hy => ResolutionCover.ofChart_weight_Φ SquareExample.chart hy

noncomputable def Qs :
    ∀ i : Unit, ProductMonomialChartVar (ResolutionCover.ofChart SquareExample.chart) i K :=
  fun _ => package

theorem e_eq : (Qs ()).e = ex := rfl

theorem h_eq : (Qs ()).h = 0 := rfl

theorem hεb : ∀ i, (1 : ℝ) ≤ (Qs i).b := fun _ => le_rfl

theorem hFc : ∀ i, ContinuousOn (fun y => (fun _ : Fin 2 → ℝ => (1 : ℝ))
    (((ResolutionCover.ofChart SquareExample.chart).chart i).φ y)) (Qs i).W :=
  fun _ => continuousOn_const

theorem hpc : ∀ i, ContinuousOn (fun y => SquareExample.one.w
    (((ResolutionCover.ofChart SquareExample.chart).chart i).φ y)) (Qs i).W :=
  fun _ => continuousOn_const

theorem hK : Measurable K := continuous_K.measurable

theorem hFc_sq : ∀ i, ContinuousOn (fun y => Fsq
    (((ResolutionCover.ofChart SquareExample.chart).chart i).φ y)) (Qs i).W :=
  fun _ => continuous_Fsq.continuousOn

/-! #### Exponents -/

theorem ratio_zero : (Qs ()).ratio 0 = 1 / 2 := by
  change ((((0 : Fin 2 →₀ ℕ) 0 : ℕ) : ℝ) + 1) / ((ex 0 : ℕ) : ℝ) = 1 / 2
  rw [ex_zero]
  simp

theorem ratio_one : (Qs ()).ratio 1 = 1 / 4 := by
  change ((((0 : Fin 2 →₀ ℕ) 1 : ℕ) : ℝ) + 1) / ((ex 1 : ℕ) : ℝ) = 1 / 4
  rw [ex_one]
  simp

theorem one_mem_support : (1 : Fin 2) ∈ (Qs ()).e.support := by
  rw [e_eq, ex_support]
  exact Finset.mem_univ _

theorem zero_mem_support : (0 : Fin 2) ∈ (Qs ()).e.support := by
  rw [e_eq, ex_support]
  exact Finset.mem_univ _

theorem one_subset_support : ({1} : Finset (Fin 2)) ⊆ (Qs ()).e.support := by
  rw [e_eq, ex_support]
  exact Finset.subset_univ _

theorem univ_subset_support : (Finset.univ : Finset (Fin 2)) ⊆ (Qs ()).e.support := by
  rw [e_eq, ex_support]

theorem hact : ((ResolutionCover.ofChart SquareExample.chart).activeCoordsV Qs).Nonempty :=
  ⟨⟨(), 1⟩, (ResolutionCover.ofChart SquareExample.chart).mem_activeCoordsV Qs one_mem_support⟩

theorem hjr : ∀ j : Fin 2, (Qs ()).ratio j = 1 / 2 ∨ (Qs ()).ratio j = 1 / 4 :=
  Fin.forall_fin_two.2 ⟨Or.inl ratio_zero, Or.inr ratio_one⟩

theorem hlow : ∀ j : Fin 2, (1 / 4 : ℝ) ≤ (Qs ()).ratio j := fun j => by
  rcases hjr j with h | h
  · rw [h]; norm_num
  · rw [h]

theorem coverLamV_eq : (ResolutionCover.ofChart SquareExample.chart).coverLamV Qs hact = 1 / 4 := by
  unfold ResolutionCover.coverLamV
  exact le_antisymm ((Finset.inf'_le _
    ((ResolutionCover.ofChart SquareExample.chart).mem_activeCoordsV Qs one_mem_support)).trans_eq
      ratio_one) (Finset.le_inf' _ _ fun x _ => hlow x.2)

theorem minimalSet_eq :
    (Qs ()).minimalSet ((ResolutionCover.ofChart SquareExample.chart).coverLamV Qs hact) = {1} := by
  unfold ProductMonomialChartVar.minimalSet
  rw [coverLamV_eq, e_eq, ex_support]
  ext j
  fin_cases j
  · simp [ratio_zero]
  · simp [ratio_one]

theorem coverDegV_eq : (ResolutionCover.ofChart SquareExample.chart).coverDegV Qs hact = 0 := by
  unfold ResolutionCover.coverDegV
  have hfilt : (Finset.univ.filter fun i : Unit => ∃ j ∈ (Qs i).e.support,
      (Qs i).ratio j = (ResolutionCover.ofChart SquareExample.chart).coverLamV Qs hact) =
      Finset.univ :=
    Finset.filter_true_of_mem fun i _ => ⟨1, one_mem_support, ratio_one.trans coverLamV_eq.symm⟩
  rw [hfilt, Finset.univ_unique, Finset.sup_singleton]
  have hM : ((Qs default).e.support.filter fun j =>
      (Qs default).ratio j = (ResolutionCover.ofChart SquareExample.chart).coverLamV Qs hact) =
      {1} := minimalSet_eq
  rw [hM, Finset.card_singleton]

/-! #### The `{1}`-piece has a null base -/

theorem base_singleton_null :
    volume ((Qs ()).pieceDensity (D := fun i => (Qs i).e.support) one_pos (hεb ()) rfl {1}
      one_subset_support (Finset.singleton_nonempty 1) SquareExample.one).base = 0 := by
  obtain ⟨i₀, hi₀⟩ := MixedExample.exists_inl_zero
  have hsub : ((Qs ()).pieceDensity (D := fun i => (Qs i).e.support) one_pos (hεb ()) rfl {1}
      one_subset_support (Finset.singleton_nonempty 1) SquareExample.one).base ⊆
      (fun z => planeReindex (stratumSplit ({1} : Finset (Fin 2)) (Finset.singleton_nonempty 1))
        z i₀) ⁻¹' ({1, -1} : Set ℝ) := by
    intro z hz
    unfold ProductMonomialChartVar.pieceDensity at hz
    rw [ResolutionCover.chartPieceDensity_base] at hz
    obtain ⟨⟨hfoot, -⟩, hT'⟩ := hz
    have h1 := hfoot 0 zero_mem_support (by decide)
    have h2 := hT'.2.2 0 zero_mem_support (by decide)
    have heq : planeSplit (stratumSplit ({1} : Finset (Fin 2)) (Finset.singleton_nonempty 1))
        (z, 0) 0 = planeReindex (stratumSplit ({1} : Finset (Fin 2)) (Finset.singleton_nonempty 1))
          z i₀ := by
      rw [hi₀, planeSplit_apply, coordCLE_apply_inl]
    rw [heq] at h1 h2
    have habs : |planeReindex (stratumSplit ({1} : Finset (Fin 2)) (Finset.singleton_nonempty 1))
        z i₀| = 1 := le_antisymm h2 (not_lt.1 h1)
    rcases (abs_eq zero_le_one).1 habs with h | h
    · exact Or.inl h
    · exact Or.inr h
  refine measure_mono_null hsub (Set.Finite.measure_zero ?_ _)
  refine Set.Finite.preimage ?_ (Set.toFinite _)
  intro z₁ _ z₂ _ h
  refine (planeReindex (stratumSplit ({1} : Finset (Fin 2))
    (Finset.singleton_nonempty 1))).injective (funext fun j => ?_)
  rw [Subsingleton.elim j i₀]
  exact h

/-! #### The `{0,1}`-piece -/

theorem tangentialMonomial_univ_h
    (z : Fin (2 - ((Finset.univ : Finset (Fin 2)).card - 1 + 1)) → ℝ) :
    tangentialMonomial (Finset.univ : Finset (Fin 2)) Finset.univ_nonempty (Qs ()).h z = 1 := by
  unfold tangentialMonomial
  rw [h_eq, Finsupp.support_zero, Finset.filter_empty, Finset.prod_empty]

theorem tangentialMonomial_univ_e
    (z : Fin (2 - ((Finset.univ : Finset (Fin 2)).card - 1 + 1)) → ℝ) :
    tangentialMonomial (Finset.univ : Finset (Fin 2)) Finset.univ_nonempty (Qs ()).e z = 1 := by
  unfold tangentialMonomial
  rw [Finset.filter_eq_empty_iff.2 fun j _ hj => hj (Finset.mem_univ j), Finset.prod_empty]

theorem zero_mem_pieceFootSet : (0 : Fin 2 → ℝ) ∈ (Qs ()).pieceFootSet Finset.univ := by
  refine ⟨?_, fun _ _ => rfl, fun j _ hj => absurd (Finset.mem_univ j) hj⟩
  change zeroOn (Qs ()).e.support (0 : Fin 2 → ℝ) ∈ ({0} : Set (Fin 2 → ℝ))
  rw [mem_singleton_iff]
  funext j
  by_cases hj : j ∈ (Qs ()).e.support
  · exact zeroOn_apply_of_mem _ hj _
  · exact zeroOn_apply_of_notMem _ hj _

theorem dominantFace_eq_univ :
    (Qs ()).dominantFace (fun i => (Qs i).e.support) 1 Finset.univ Finset.univ_nonempty
      (fun _ => (1 : ℝ)) SquareExample.one = univ := by
  refine eq_univ_of_forall fun z => ?_
  refine ⟨fun j _ hj => absurd (Finset.mem_univ j) hj, ?_, one_pos, one_pos, one_pos, one_ne_zero,
    ?_⟩
  · rw [SquareExample.planeSplit_univ_zero]
    exact SquareExample.zero_mem_box
  · rw [tangentialMonomial_univ_h]
    exact one_ne_zero

theorem base_univ_eq :
    ((Qs ()).pieceDensity (D := fun i => (Qs i).e.support) one_pos (hεb ()) rfl Finset.univ
      univ_subset_support Finset.univ_nonempty SquareExample.one).base = univ :=
  eq_univ_of_forall fun z => (Qs ()).mem_pieceDensity_base_of_mem_dominantFace one_pos (hεb ())
    rfl Finset.univ univ_subset_support Finset.univ_nonempty SquareExample.one
    (by rw [dominantFace_eq_univ]; exact mem_univ z)

theorem pieceLam_univ : (Qs ()).pieceLam Finset.univ Finset.univ_nonempty = 1 / 4 :=
  le_antisymm ((Finset.inf'_le _ (Finset.mem_univ 1)).trans_eq ratio_one)
    (Finset.le_inf' _ _ fun j _ => hlow j)

theorem pieceMult_univ : (Qs ()).pieceMult Finset.univ Finset.univ_nonempty = 1 := by
  rw [(Qs ()).pieceMult_eq_card_inter Finset.univ univ_subset_support Finset.univ_nonempty
    pieceLam_univ, ← coverLamV_eq, minimalSet_eq, Finset.univ_inter, Finset.card_singleton]

theorem normalExp_h (a : Fin ((Finset.univ : Finset (Fin 2)).card - 1 + 1)) :
    normalExp Finset.univ Finset.univ_nonempty (Qs ()).h a = 0 := rfl

theorem ratioExp_normal (a : Fin ((Finset.univ : Finset (Fin 2)).card - 1 + 1)) :
    ratioExp (normalExp Finset.univ Finset.univ_nonempty (Qs ()).h)
        (normalHalfExp Finset.univ Finset.univ_nonempty (Qs ()).e) a =
      (Qs ()).ratio ((stratumSplit Finset.univ Finset.univ_nonempty).symm (Sum.inr a)) :=
  ratioExp_normal_eq Finset.univ Finset.univ_nonempty (Qs ()).e (Qs ()).h
    ((Qs ()).normalExp_eq_two_mul K_nonneg Finset.univ univ_subset_support Finset.univ_nonempty) a

theorem minRatio_normal :
    minRatio (normalExp Finset.univ Finset.univ_nonempty (Qs ()).h)
      (normalHalfExp Finset.univ Finset.univ_nonempty (Qs ()).e) = 1 / 4 :=
  ((Qs ()).pieceLam_eq K_nonneg Finset.univ univ_subset_support Finset.univ_nonempty).trans
    pieceLam_univ

theorem multCount_normal :
    multCount (ratioExp (normalExp Finset.univ Finset.univ_nonempty (Qs ()).h)
        (normalHalfExp Finset.univ Finset.univ_nonempty (Qs ()).e))
      (minRatio (normalExp Finset.univ Finset.univ_nonempty (Qs ()).h)
        (normalHalfExp Finset.univ Finset.univ_nonempty (Qs ()).e)) = 1 :=
  ((Qs ()).pieceMult_eq K_nonneg Finset.univ univ_subset_support Finset.univ_nonempty).trans
    pieceMult_univ

theorem hk : ∀ a, 0 < normalHalfExp Finset.univ Finset.univ_nonempty (Qs ()).e a :=
  normalHalfExp_pos Finset.univ Finset.univ_nonempty (Qs ()).e
    (fun j _ => Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 (univ_subset_support
      (Finset.mem_univ j))))
    ((Qs ()).normalExp_eq_two_mul K_nonneg Finset.univ univ_subset_support Finset.univ_nonempty)

/-- The normal half-exponent is `2` on the minimal coordinate and `1` on the other. -/
theorem normalHalfExp_of_min {a : Fin ((Finset.univ : Finset (Fin 2)).card - 1 + 1)}
    (h : ratioExp (normalExp Finset.univ Finset.univ_nonempty (Qs ()).h)
      (normalHalfExp Finset.univ Finset.univ_nonempty (Qs ()).e) a = 1 / 4) :
    (normalHalfExp Finset.univ Finset.univ_nonempty (Qs ()).e a : ℝ) = 2 := by
  unfold ratioExp at h
  rw [normalExp_h] at h
  have hk' : (0 : ℝ) < 2 * (normalHalfExp Finset.univ Finset.univ_nonempty (Qs ()).e a : ℝ) := by
    have : (0 : ℝ) < normalHalfExp Finset.univ Finset.univ_nonempty (Qs ()).e a := by
      exact_mod_cast hk a
    linarith
  rw [div_eq_div_iff hk'.ne' (by norm_num)] at h
  push_cast at h
  linarith

theorem normalHalfExp_of_nonmin {a : Fin ((Finset.univ : Finset (Fin 2)).card - 1 + 1)}
    (h : ¬ ratioExp (normalExp Finset.univ Finset.univ_nonempty (Qs ()).h)
      (normalHalfExp Finset.univ Finset.univ_nonempty (Qs ()).e) a = 1 / 4) :
    (normalHalfExp Finset.univ Finset.univ_nonempty (Qs ()).e a : ℝ) = 1 := by
  have h2 : ratioExp (normalExp Finset.univ Finset.univ_nonempty (Qs ()).h)
      (normalHalfExp Finset.univ Finset.univ_nonempty (Qs ()).e) a = 1 / 2 := by
    rw [ratioExp_normal] at h ⊢
    rcases hjr _ with h' | h'
    · exact h'
    · exact absurd h' h
  unfold ratioExp at h2
  rw [normalExp_h] at h2
  have hk' : (0 : ℝ) < 2 * (normalHalfExp Finset.univ Finset.univ_nonempty (Qs ()).e a : ℝ) := by
    have : (0 : ℝ) < normalHalfExp Finset.univ Finset.univ_nonempty (Qs ()).e a := by
      exact_mod_cast hk a
    linarith
  rw [div_eq_div_iff hk'.ne' (by norm_num)] at h2
  push_cast at h2
  linarith

/-- The face constant `Γ(1/4)/0! · 1/(2·2) = Γ(1/4)/4`. -/
theorem faceLeadConst_eq :
    faceLeadConst (normalExp Finset.univ Finset.univ_nonempty (Qs ()).h)
      (normalHalfExp Finset.univ Finset.univ_nonempty (Qs ()).e) (1 / 4) 1 =
      Real.Gamma (1 / 4) / 4 := by
  rw [faceLeadConst_one_eq]
  have hJ : (minimalCoords (normalExp Finset.univ Finset.univ_nonempty (Qs ()).h)
      (normalHalfExp Finset.univ Finset.univ_nonempty (Qs ()).e) (1 / 4)).card = 1 := by
    rw [← minRatio_normal, ← multCount_eq_card_minimalCoords]
    exact multCount_normal
  rw [Finset.prod_congr rfl fun a ha => by
    rw [normalHalfExp_of_min ((mem_minimalCoords _ _ _).1 ha)], Finset.prod_const, hJ]
  norm_num
  ring

/-! #### The face: the normal indices of `y₀` and `y₁` -/

theorem exists_inr_zero : ∃ a₀, (0 : Fin 2) =
    (stratumSplit (Finset.univ : Finset (Fin 2)) Finset.univ_nonempty).symm (Sum.inr a₀) :=
  exists_inr_of_mem Finset.univ Finset.univ_nonempty (Finset.mem_univ 0)

theorem exists_inr_one : ∃ a₁, (1 : Fin 2) =
    (stratumSplit (Finset.univ : Finset (Fin 2)) Finset.univ_nonempty).symm (Sum.inr a₁) :=
  exists_inr_of_mem Finset.univ Finset.univ_nonempty (Finset.mem_univ 1)

theorem ratioExp_ne_of_zero {a₀ : Fin ((Finset.univ : Finset (Fin 2)).card - 1 + 1)}
    (ha₀ : (0 : Fin 2) =
      (stratumSplit (Finset.univ : Finset (Fin 2)) Finset.univ_nonempty).symm (Sum.inr a₀)) :
    ¬ ratioExp (normalExp Finset.univ Finset.univ_nonempty (Qs ()).h)
      (normalHalfExp Finset.univ Finset.univ_nonempty (Qs ()).e) a₀ = 1 / 4 := by
  rw [ratioExp_normal, ← ha₀, ratio_zero]
  norm_num

theorem ratioExp_eq_of_one {a₁ : Fin ((Finset.univ : Finset (Fin 2)).card - 1 + 1)}
    (ha₁ : (1 : Fin 2) =
      (stratumSplit (Finset.univ : Finset (Fin 2)) Finset.univ_nonempty).symm (Sum.inr a₁)) :
    ratioExp (normalExp Finset.univ Finset.univ_nonempty (Qs ()).h)
      (normalHalfExp Finset.univ Finset.univ_nonempty (Qs ()).e) a₁ = 1 / 4 := by
  rw [ratioExp_normal, ← ha₁, ratio_one]

theorem eq_of_nonmin {a₀ a : Fin ((Finset.univ : Finset (Fin 2)).card - 1 + 1)}
    (ha₀ : (0 : Fin 2) =
      (stratumSplit (Finset.univ : Finset (Fin 2)) Finset.univ_nonempty).symm (Sum.inr a₀))
    (h : ¬ ratioExp (normalExp Finset.univ Finset.univ_nonempty (Qs ()).h)
      (normalHalfExp Finset.univ Finset.univ_nonempty (Qs ()).e) a = 1 / 4) : a = a₀ := by
  rw [ratioExp_normal] at h
  rcases MixedExample.fin_two_eq ((stratumSplit (Finset.univ : Finset (Fin 2))
    Finset.univ_nonempty).symm (Sum.inr a)) with hj | hj
  · exact Sum.inr_injective ((stratumSplit (Finset.univ : Finset (Fin 2))
      Finset.univ_nonempty).symm.injective (hj.trans ha₀))
  · rw [hj, ratio_one] at h
    exact absurd rfl h

/-- **The variable phase on the minimal face** `y₁ = 0` is `1 + y₀²`. -/
theorem varPhase_face {a₀ : Fin ((Finset.univ : Finset (Fin 2)).card - 1 + 1)}
    (ha₀ : (0 : Fin 2) =
      (stratumSplit (Finset.univ : Finset (Fin 2)) Finset.univ_nonempty).symm (Sum.inr a₀))
    (z : Fin (2 - ((Finset.univ : Finset (Fin 2)).card - 1 + 1)) → ℝ)
    (σ : Fin ((Finset.univ : Finset (Fin 2)).card - 1 + 1) → Bool)
    (u : Fin ((Finset.univ : Finset (Fin 2)).card - 1 + 1) → ℝ) :
    varPhase Finset.univ Finset.univ_nonempty (Qs ()).u (Qs ()).e z
      (reflect σ ((1 : ℝ) • faceProj (normalExp Finset.univ Finset.univ_nonempty (Qs ()).h)
        (normalHalfExp Finset.univ Finset.univ_nonempty (Qs ()).e) (1 / 4) u)) =
      1 + u a₀ ^ 2 := by
  obtain ⟨a₁, ha₁⟩ := exists_inr_one
  unfold varPhase
  rw [tangentialMonomial_univ_e, mul_one]
  change VarSquareExample.unit (planeSplit (stratumSplit Finset.univ Finset.univ_nonempty)
    (z, _)) = _
  unfold VarSquareExample.unit
  rw [ha₀, ha₁, planeSplit_stratum_inr, planeSplit_stratum_inr, one_smul]
  simp only [reflect, faceProj, if_neg (ratioExp_ne_of_zero ha₀), if_pos (ratioExp_eq_of_one ha₁),
    mul_zero, mul_pow, sgn_sq, one_mul]
  ring

/-- The amplitude of the observable `1` on the piece is `1`. -/
theorem pieceAmp_one (z : Fin (2 - ((Finset.univ : Finset (Fin 2)).card - 1 + 1)) → ℝ)
    (w : Fin ((Finset.univ : Finset (Fin 2)).card - 1 + 1) → ℝ) :
    (ResolutionCover.ofChart SquareExample.chart).pieceAmp () Finset.univ Finset.univ_nonempty
      (Qs ()).h (Qs ()).v (F := fun _ => (1 : ℝ)) (p := SquareExample.one) z w = 1 := by
  unfold ResolutionCover.pieceAmp
  rw [tangentialMonomial_univ_h]
  change |(1 : ℝ)| * |(1 : ℝ)| * 1 * 1 = 1
  simp

/-- The amplitude of the observable `y₀²` on the piece is `(w a₀)²`. -/
theorem pieceAmp_sq {a₀ : Fin ((Finset.univ : Finset (Fin 2)).card - 1 + 1)}
    (ha₀ : (0 : Fin 2) =
      (stratumSplit (Finset.univ : Finset (Fin 2)) Finset.univ_nonempty).symm (Sum.inr a₀))
    (z : Fin (2 - ((Finset.univ : Finset (Fin 2)).card - 1 + 1)) → ℝ)
    (w : Fin ((Finset.univ : Finset (Fin 2)).card - 1 + 1) → ℝ) :
    (ResolutionCover.ofChart SquareExample.chart).pieceAmp () Finset.univ Finset.univ_nonempty
      (Qs ()).h (Qs ()).v (F := Fsq) (p := SquareExample.one) z w = w a₀ ^ 2 := by
  unfold ResolutionCover.pieceAmp
  rw [tangentialMonomial_univ_h]
  change |(1 : ℝ)| * |(1 : ℝ)| * 1 * Fsq (planeSplit (stratumSplit Finset.univ
    Finset.univ_nonempty) (z, w)) = w a₀ ^ 2
  unfold Fsq
  rw [ha₀, planeSplit_stratum_inr]
  simp

/-! #### The face integrals -/

/-- The residual face integral for the observable `1`: `I = ∫₀¹ t^{−1/2} (1+t²)^{−1/4} dt`. -/
noncomputable def I : ℝ := VarRegression.B.I

theorem I_pos : 0 < I := VarRegression.B.I_pos

/-- The residual face integral for the observable `y₀²`:
`J = ∫₀¹ t² · t^{−1/2} (1+t²)^{−1/4} dt`. -/
noncomputable def J : ℝ :=
  ∫ t in Ioc (0 : ℝ) 1, t ^ 2 * (t ^ (-(1 / 2 : ℝ)) * (1 + t ^ 2) ^ (-(1 / 4 : ℝ)))

theorem J_pos : 0 < J := by
  have hint : IntegrableOn (fun t : ℝ => t ^ (3 / 2 : ℝ)) (Ioc 0 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
      (intervalIntegral.intervalIntegrable_rpow' (by norm_num))
  have hle : ∀ t ∈ Ioc (0 : ℝ) 1, (2 : ℝ) ^ (-(1 / 4 : ℝ)) * t ^ (3 / 2 : ℝ) ≤
      t ^ 2 * (t ^ (-(1 / 2 : ℝ)) * (1 + t ^ 2) ^ (-(1 / 4 : ℝ))) := by
    intro t ht
    have h32 : t ^ 2 * t ^ (-(1 / 2 : ℝ)) = t ^ (3 / 2 : ℝ) := by
      rw [← Real.rpow_natCast t 2, ← Real.rpow_add ht.1]
      norm_num
    rw [← mul_assoc, h32, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg ht.1.le _)
    exact Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith [ht.2, ht.1]) (by norm_num)
  have hint2 : IntegrableOn
      (fun t : ℝ => t ^ 2 * (t ^ (-(1 / 2 : ℝ)) * (1 + t ^ 2) ^ (-(1 / 4 : ℝ)))) (Ioc 0 1) := by
    refine Integrable.mono' (VarRegression.B.integrableOn_integrand) ?_
      (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_)
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
      refine (continuousOn_id.pow 2).mul ?_
      refine (continuousOn_id.rpow_const fun t ht => Or.inl ht.1.ne').mul ?_
      exact (continuousOn_const.add (continuousOn_id.pow 2)).rpow_const fun t _ =>
        Or.inl (ne_of_gt (by change (0 : ℝ) < 1 + t ^ 2; positivity))
    · have hnn : 0 ≤ t ^ (-(1 / 2 : ℝ)) * (1 + t ^ 2) ^ (-(1 / 4 : ℝ)) :=
        mul_nonneg (Real.rpow_nonneg ht.1.le _) (Real.rpow_nonneg (by positivity) _)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) hnn)]
      exact mul_le_of_le_one_left hnn (by nlinarith [ht.1, ht.2])
  have hlow : ∫ t in Ioc (0 : ℝ) 1, (2 : ℝ) ^ (-(1 / 4 : ℝ)) * t ^ (3 / 2 : ℝ) =
      (2 : ℝ) ^ (-(1 / 4 : ℝ)) * (2 / 5) := by
    rw [integral_const_mul, integral_Ioc_rpow (by norm_num)]
    norm_num
  calc (0 : ℝ) < (2 : ℝ) ^ (-(1 / 4 : ℝ)) * (2 / 5) := by positivity
    _ = ∫ t in Ioc (0 : ℝ) 1, (2 : ℝ) ^ (-(1 / 4 : ℝ)) * t ^ (3 / 2 : ℝ) := hlow.symm
    _ ≤ J := setIntegral_mono_on (hint.const_mul _) hint2 measurableSet_Ioc hle

theorem J_le_I : J ≤ I := by
  have hint2 : IntegrableOn
      (fun t : ℝ => t ^ 2 * (t ^ (-(1 / 2 : ℝ)) * (1 + t ^ 2) ^ (-(1 / 4 : ℝ)))) (Ioc 0 1) := by
    refine Integrable.mono' (VarRegression.B.integrableOn_integrand) ?_
      (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_)
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
      refine (continuousOn_id.pow 2).mul ?_
      refine (continuousOn_id.rpow_const fun t ht => Or.inl ht.1.ne').mul ?_
      exact (continuousOn_const.add (continuousOn_id.pow 2)).rpow_const fun t _ =>
        Or.inl (ne_of_gt (by change (0 : ℝ) < 1 + t ^ 2; positivity))
    · have hnn : 0 ≤ t ^ (-(1 / 2 : ℝ)) * (1 + t ^ 2) ^ (-(1 / 4 : ℝ)) :=
        mul_nonneg (Real.rpow_nonneg ht.1.le _) (Real.rpow_nonneg (by positivity) _)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) hnn)]
      exact mul_le_of_le_one_left hnn (by nlinarith [ht.1, ht.2])
  refine setIntegral_mono_on hint2 VarRegression.B.integrableOn_integrand measurableSet_Ioc
    fun t ht => ?_
  have hnn : 0 ≤ t ^ (-(1 / 2 : ℝ)) * (1 + t ^ 2) ^ (-(1 / 4 : ℝ)) :=
    mul_nonneg (Real.rpow_nonneg ht.1.le _) (Real.rpow_nonneg (by positivity) _)
  exact mul_le_of_le_one_left hnn (by nlinarith [ht.1, ht.2])

/-- **The face integral of a product observable**: for a face amplitude `g (w a₀)` at the residual
coordinate, the face integral is `∫₀¹ g(t) · t^{−1/2} (1+t²)^{−1/4} dt`. -/
theorem inner_of_amp {a₀ : Fin ((Finset.univ : Finset (Fin 2)).card - 1 + 1)}
    (ha₀ : (0 : Fin 2) =
      (stratumSplit (Finset.univ : Finset (Fin 2)) Finset.univ_nonempty).symm (Sum.inr a₀))
    {F : (Fin 2 → ℝ) → ℝ} (g : ℝ → ℝ)
    (hamp : ∀ (z : Fin (2 - ((Finset.univ : Finset (Fin 2)).card - 1 + 1)) → ℝ)
      (w : Fin ((Finset.univ : Finset (Fin 2)).card - 1 + 1) → ℝ),
      (ResolutionCover.ofChart SquareExample.chart).pieceAmp () Finset.univ Finset.univ_nonempty
        (Qs ()).h (Qs ()).v (F := F) (p := SquareExample.one) z w = g (w a₀))
    (hg : ∀ s : Bool, ∀ t, g (sgn s * t) = g t)
    (z : Fin (2 - ((Finset.univ : Finset (Fin 2)).card - 1 + 1)) → ℝ)
    (σ : Fin ((Finset.univ : Finset (Fin 2)).card - 1 + 1) → Bool) :
    ∫ u in unitBox ((Finset.univ : Finset (Fin 2)).card - 1 + 1),
      (ResolutionCover.ofChart SquareExample.chart).pieceAmp () Finset.univ Finset.univ_nonempty
          (Qs ()).h (Qs ()).v (F := F) (p := SquareExample.one) z
          (reflect σ ((1 : ℝ) • faceProj (normalExp Finset.univ Finset.univ_nonempty (Qs ()).h)
            (normalHalfExp Finset.univ Finset.univ_nonempty (Qs ()).e) (1 / 4) u)) *
        varPhase Finset.univ Finset.univ_nonempty (Qs ()).u (Qs ()).e z
            (reflect σ ((1 : ℝ) • faceProj (normalExp Finset.univ Finset.univ_nonempty (Qs ()).h)
              (normalHalfExp Finset.univ Finset.univ_nonempty (Qs ()).e) (1 / 4) u)) ^
          (-(1 / 4 : ℝ)) *
        residualWeight (normalExp Finset.univ Finset.univ_nonempty (Qs ()).h)
          (normalHalfExp Finset.univ Finset.univ_nonempty (Qs ()).e) (1 / 4) u =
      ∫ t in Ioc (0 : ℝ) 1, g t * (t ^ (-(1 / 2 : ℝ)) * (1 + t ^ 2) ^ (-(1 / 4 : ℝ))) := by
  have hna₀ := ratioExp_ne_of_zero ha₀
  have hpt : ∀ u : Fin ((Finset.univ : Finset (Fin 2)).card - 1 + 1) → ℝ,
      (ResolutionCover.ofChart SquareExample.chart).pieceAmp () Finset.univ Finset.univ_nonempty
          (Qs ()).h (Qs ()).v (F := F) (p := SquareExample.one) z
          (reflect σ ((1 : ℝ) • faceProj (normalExp Finset.univ Finset.univ_nonempty (Qs ()).h)
            (normalHalfExp Finset.univ Finset.univ_nonempty (Qs ()).e) (1 / 4) u)) *
        varPhase Finset.univ Finset.univ_nonempty (Qs ()).u (Qs ()).e z
            (reflect σ ((1 : ℝ) • faceProj (normalExp Finset.univ Finset.univ_nonempty (Qs ()).h)
              (normalHalfExp Finset.univ Finset.univ_nonempty (Qs ()).e) (1 / 4) u)) ^
          (-(1 / 4 : ℝ)) *
        residualWeight (normalExp Finset.univ Finset.univ_nonempty (Qs ()).h)
          (normalHalfExp Finset.univ Finset.univ_nonempty (Qs ()).e) (1 / 4) u =
      ∏ a, ((if a = a₀ then g (u a) * (1 + u a ^ 2) ^ (-(1 / 4 : ℝ)) else 1) *
        (if ratioExp (normalExp Finset.univ Finset.univ_nonempty (Qs ()).h)
            (normalHalfExp Finset.univ Finset.univ_nonempty (Qs ()).e) a = 1 / 4 then (1 : ℝ)
          else u a ^ ((normalExp Finset.univ Finset.univ_nonempty (Qs ()).h a : ℝ) -
            2 * (normalHalfExp Finset.univ Finset.univ_nonempty (Qs ()).e a : ℝ) * (1 / 4)))) :=
    fun u => by
    rw [hamp, varPhase_face ha₀, Finset.prod_mul_distrib, Finset.prod_ite_eq',
      if_pos (Finset.mem_univ _)]
    unfold residualWeight
    congr 1
    rw [one_smul, reflect, faceProj]
    simp only [if_neg hna₀, hg]
  rw [setIntegral_congr_fun (measurableSet_unitBox _) fun u _ => hpt u,
    integral_unitBox_prod (fun a t =>
      (if a = a₀ then g t * (1 + t ^ 2) ^ (-(1 / 4 : ℝ)) else 1) *
      (if ratioExp (normalExp Finset.univ Finset.univ_nonempty (Qs ()).h)
          (normalHalfExp Finset.univ Finset.univ_nonempty (Qs ()).e) a = 1 / 4 then (1 : ℝ)
        else t ^ ((normalExp Finset.univ Finset.univ_nonempty (Qs ()).h a : ℝ) -
          2 * (normalHalfExp Finset.univ Finset.univ_nonempty (Qs ()).e a : ℝ) * (1 / 4))))]
  have hval : (∫ t in Ioc (0 : ℝ) 1, (fun a t =>
      (if a = a₀ then g t * (1 + t ^ 2) ^ (-(1 / 4 : ℝ)) else 1) *
      (if ratioExp (normalExp Finset.univ Finset.univ_nonempty (Qs ()).h)
          (normalHalfExp Finset.univ Finset.univ_nonempty (Qs ()).e) a = 1 / 4 then (1 : ℝ)
        else t ^ ((normalExp Finset.univ Finset.univ_nonempty (Qs ()).h a : ℝ) -
          2 * (normalHalfExp Finset.univ Finset.univ_nonempty (Qs ()).e a : ℝ) * (1 / 4))))
        a₀ t) =
      ∫ t in Ioc (0 : ℝ) 1, g t * (t ^ (-(1 / 2 : ℝ)) * (1 + t ^ 2) ^ (-(1 / 4 : ℝ))) := by
    have hexp : ((normalExp Finset.univ Finset.univ_nonempty (Qs ()).h a₀ : ℝ) -
        2 * (normalHalfExp Finset.univ Finset.univ_nonempty (Qs ()).e a₀ : ℝ) * (1 / 4)) =
        -(1 / 2) := by
      rw [normalExp_h, normalHalfExp_of_nonmin hna₀]
      norm_num
    simp only [if_true, if_neg hna₀, hexp]
    refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
    ring
  have hother : ∀ a ∈ (Finset.univ : Finset (Fin ((Finset.univ : Finset (Fin 2)).card - 1 + 1))),
      a ≠ a₀ → (∫ t in Ioc (0 : ℝ) 1, (fun a t =>
      (if a = a₀ then g t * (1 + t ^ 2) ^ (-(1 / 4 : ℝ)) else 1) *
      (if ratioExp (normalExp Finset.univ Finset.univ_nonempty (Qs ()).h)
          (normalHalfExp Finset.univ Finset.univ_nonempty (Qs ()).e) a = 1 / 4 then (1 : ℝ)
        else t ^ ((normalExp Finset.univ Finset.univ_nonempty (Qs ()).h a : ℝ) -
          2 * (normalHalfExp Finset.univ Finset.univ_nonempty (Qs ()).e a : ℝ) * (1 / 4))))
        a t) = 1 := fun a _ ha => by
    have hmin : ratioExp (normalExp Finset.univ Finset.univ_nonempty (Qs ()).h)
        (normalHalfExp Finset.univ Finset.univ_nonempty (Qs ()).e) a = 1 / 4 := by
      by_contra hn
      exact ha (eq_of_nonmin ha₀ hn)
    simp only [if_neg ha, if_pos hmin, one_mul]
    simp
  rw [Finset.prod_eq_single a₀ hother (fun h => absurd (Finset.mem_univ _) h), hval]

/-! #### The total coefficient -/

/-- **The total coefficient for an observable with residual face integral `R`** is `Γ(1/4) · R`:
the `{1}`-piece is null and the `{0,1}`-piece gives `Γ(1/4) · R` by the residual face formula. -/
theorem productCoeffV_eq_of_inner {F : (Fin 2 → ℝ) → ℝ}
    (hFc : ∀ i, ContinuousOn (fun y => F (((ResolutionCover.ofChart SquareExample.chart).chart i).φ
      y)) (Qs i).W) (hFm : Measurable F)
    (hF : Integrable (fun x => F x * SquareExample.one.w x)
      (volume.restrict (⋃ i, (ResolutionCover.ofChart SquareExample.chart).image i))) (R : ℝ)
    (hinner : ∀ (z : Fin (2 - ((Finset.univ : Finset (Fin 2)).card - 1 + 1)) → ℝ)
        (σ : Fin ((Finset.univ : Finset (Fin 2)).card - 1 + 1) → Bool),
        ∫ u in unitBox ((Finset.univ : Finset (Fin 2)).card - 1 + 1),
          (ResolutionCover.ofChart SquareExample.chart).pieceAmp () Finset.univ
              Finset.univ_nonempty (Qs ()).h (Qs ()).v (F := F) (p := SquareExample.one) z
              (reflect σ ((1 : ℝ) • faceProj (normalExp Finset.univ Finset.univ_nonempty (Qs ()).h)
                (normalHalfExp Finset.univ Finset.univ_nonempty (Qs ()).e) (1 / 4) u)) *
            varPhase Finset.univ Finset.univ_nonempty (Qs ()).u (Qs ()).e z
                (reflect σ ((1 : ℝ) • faceProj (normalExp Finset.univ Finset.univ_nonempty
                  (Qs ()).h) (normalHalfExp Finset.univ Finset.univ_nonempty (Qs ()).e) (1 / 4) u))
                ^ (-(1 / 4 : ℝ)) *
            residualWeight (normalExp Finset.univ Finset.univ_nonempty (Qs ()).h)
              (normalHalfExp Finset.univ Finset.univ_nonempty (Qs ()).e) (1 / 4) u = R) :
    (ResolutionCover.ofChart SquareExample.chart).productCoeffV Qs K_nonneg one_pos hεb hFc hpc hFm
      hF hK ((ResolutionCover.ofChart SquareExample.chart).coverLamV Qs hact)
      ((ResolutionCover.ofChart SquareExample.chart).coverDegV Qs hact) =
      Real.Gamma (1 / 4) * R := by
  have hsum : ∀ f : Unit → ℝ, ∑ i, f i = f () := fun f => Fintype.sum_unique f
  rw [(ResolutionCover.ofChart SquareExample.chart).productCoeffV_extremal_eq_sum_tied Qs hact
    K_nonneg one_pos hεb hFc hpc hFm hF hK, hsum]
  have hS : (((Qs ()).e.support.powerset.filter fun I => I.Nonempty).filter
      (fun I => (Qs ()).minimalSet ((ResolutionCover.ofChart SquareExample.chart).coverLamV Qs
        hact) ⊆ I ∧
        ((Qs ()).minimalSet ((ResolutionCover.ofChart SquareExample.chart).coverLamV Qs
          hact)).card = (ResolutionCover.ofChart SquareExample.chart).coverDegV Qs hact + 1)) =
      {{1}, Finset.univ} := by
    rw [minimalSet_eq, coverDegV_eq, e_eq, ex_support]
    decide
  have hzero : ResolutionCover.leadingAtlasPieceCoeff (fun i I hI hne =>
      ((ResolutionCover.ofChart SquareExample.chart).productAtlasesV Qs K_nonneg one_pos hεb hFc hpc
        hFm hF hK i I hI hne).toLeading)
      ((ResolutionCover.ofChart SquareExample.chart).coverLamV Qs hact)
      ((ResolutionCover.ofChart SquareExample.chart).coverDegV Qs hact) () {1} = 0 := by
    rw [ResolutionCover.leadingAtlasPieceCoeff_of_mem _ _ _ () {1} one_subset_support
      (Finset.singleton_nonempty 1)]
    exact (Qs ()).tiedSum_eq_zero_of_null K_nonneg one_pos (hεb ()) rfl hFm hF hK {1}
      one_subset_support (Finset.singleton_nonempty 1) _ _ base_singleton_null
      ((Qs ()).pieceAtlasV_data K_nonneg one_pos (hεb ()) rfl (hFc ()) (hpc ()) hFm hF hK {1}
        one_subset_support (Finset.singleton_nonempty 1))
  have huniv : ResolutionCover.leadingAtlasPieceCoeff (fun i I hI hne =>
      ((ResolutionCover.ofChart SquareExample.chart).productAtlasesV Qs K_nonneg one_pos hεb hFc hpc
        hFm hF hK i I hI hne).toLeading)
      ((ResolutionCover.ofChart SquareExample.chart).coverLamV Qs hact)
      ((ResolutionCover.ofChart SquareExample.chart).coverDegV Qs hact) () Finset.univ =
      Real.Gamma (1 / 4) * R := by
    rw [ResolutionCover.leadingAtlasPieceCoeff_of_mem _ _ _ () Finset.univ univ_subset_support
      Finset.univ_nonempty, coverLamV_eq, coverDegV_eq]
    refine ((Qs ()).tiedSum_residual_of_inner Finset.univ Finset.univ_nonempty K_nonneg one_pos
      (hεb ()) (D := fun i => (Qs i).e.support) rfl hFm hF hK univ_subset_support pieceLam_univ
      (by rw [pieceMult_univ])
      ((Qs ()).pieceAtlasV_data K_nonneg one_pos (hεb ()) (D := fun i => (Qs i).e.support) rfl
        (hFc ()) (hpc ()) hFm hF hK Finset.univ univ_subset_support Finset.univ_nonempty)
      (fun _ => R) (fun z _ τ => by rw [minRatio_normal]; exact hinner z _)).trans ?_
    have hJ : ((Qs ()).minimalNormal Finset.univ Finset.univ_nonempty).card = 1 := by
      rw [(Qs ()).card_minimalNormal Finset.univ Finset.univ_nonempty K_nonneg univ_subset_support,
        pieceMult_univ]
    have hcardτ : (Fintype.card ({a : Fin ((Finset.univ : Finset (Fin 2)).card - 1 + 1) //
        a ∉ (Qs ()).minimalNormal Finset.univ Finset.univ_nonempty} → Bool) : ℝ) = 2 := by
      rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_subtype]
      have h1 := Finset.card_filter_add_card_filter_not (s := Finset.univ)
        (fun a => a ∈ (Qs ()).minimalNormal Finset.univ Finset.univ_nonempty)
      have h2 : (Finset.univ.filter fun a =>
          a ∈ (Qs ()).minimalNormal Finset.univ Finset.univ_nonempty).card = 1 := by
        rw [Finset.filter_mem_eq_inter, Finset.univ_inter, hJ]
      have h3 : (Finset.univ : Finset (Fin ((Finset.univ : Finset (Fin 2)).card - 1 + 1))).card =
          2 := by decide
      have h4 : (Finset.univ.filter fun a =>
          a ∉ (Qs ()).minimalNormal Finset.univ Finset.univ_nonempty).card = 1 := by omega
      rw [h4]
      norm_num
    have hbase : ∫ z in ((Qs ()).pieceDensity (D := fun i => (Qs i).e.support) one_pos (hεb ())
        rfl Finset.univ univ_subset_support Finset.univ_nonempty SquareExample.one).base,
        ((Qs ()).pieceDensity (D := fun i => (Qs i).e.support) one_pos (hεb ()) rfl Finset.univ
          univ_subset_support Finset.univ_nonempty SquareExample.one).beta z * R = R := by
      have hone : ∀ z, ((Qs ()).pieceDensity (D := fun i => (Qs i).e.support) one_pos (hεb ()) rfl
          Finset.univ univ_subset_support Finset.univ_nonempty SquareExample.one).beta z * R =
          R := fun z => by
        rw [ProductMonomialChartVar.pieceDensity_beta, SquareExample.planeSplit_univ_zero,
          Set.indicator_of_mem zero_mem_pieceFootSet]
        change (1 : ℝ) * R = R
        ring
      rw [setIntegral_congr_fun (base_univ_eq ▸ MeasurableSet.univ) fun z _ => hone z, base_univ_eq,
        Measure.restrict_univ, integral_const, measureReal_def, SquareExample.volume_univ_base]
      simp
    rw [hJ, hcardτ, minRatio_normal, faceLeadConst_eq, Real.one_rpow, hbase]
    ring
  rw [hS, Finset.sum_pair (by decide : ({1} : Finset (Fin 2)) ≠ Finset.univ), hzero, huniv,
    zero_add]

/-- **The normaliser coefficient is `Γ(1/4) · I`.** -/
theorem productCoeffV_one :
    (ResolutionCover.ofChart SquareExample.chart).productCoeffV Qs K_nonneg one_pos hεb hFc hpc
      SquareExample.hFm SquareExample.hF hK
      ((ResolutionCover.ofChart SquareExample.chart).coverLamV Qs hact)
      ((ResolutionCover.ofChart SquareExample.chart).coverDegV Qs hact) =
      Real.Gamma (1 / 4) * I := by
  obtain ⟨a₀, ha₀⟩ := exists_inr_zero
  refine productCoeffV_eq_of_inner hFc SquareExample.hFm SquareExample.hF I fun z σ => ?_
  rw [inner_of_amp ha₀ (fun _ => (1 : ℝ)) (fun z w => pieceAmp_one z w) (fun _ _ => rfl) z σ]
  unfold I VarRegression.B.I
  refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
  ring

/-- **The coefficient of `Z_N[y₀²]` is `Γ(1/4) · J`.** -/
theorem productCoeffV_sq :
    (ResolutionCover.ofChart SquareExample.chart).productCoeffV Qs K_nonneg one_pos hεb hFc_sq hpc
      MixedExample.hFm_sq MixedExample.hF_sq hK
      ((ResolutionCover.ofChart SquareExample.chart).coverLamV Qs hact)
      ((ResolutionCover.ofChart SquareExample.chart).coverDegV Qs hact) =
      Real.Gamma (1 / 4) * J := by
  obtain ⟨a₀, ha₀⟩ := exists_inr_zero
  refine productCoeffV_eq_of_inner hFc_sq MixedExample.hFm_sq MixedExample.hF_sq J fun z σ => ?_
  rw [inner_of_amp ha₀ (fun t => t ^ 2) (fun z w => pieceAmp_sq ha₀ z w)
    (fun s t => by rw [mul_pow, sgn_sq, one_mul]) z σ]
  rfl

/-- ★ **The residual regression, end to end**:
`∫_{[−1,1]²} e^{−N (1+y₀²+y₁²) y₀² y₁⁴} dy ~ Γ(1/4) · (∫₀¹ t^{−1/2}(1+t²)^{−1/4} dt) · N^{−1/4}`. -/
theorem integral_isEquivalent :
    (fun N : ℝ => ∫ y in SquareExample.box, Real.exp (-N * K y)) ~[atTop]
      fun N => Real.Gamma (1 / 4) * I * N ^ (-(1 / 4 : ℝ)) := by
  have hc : (ResolutionCover.ofChart SquareExample.chart).productCoeffV Qs K_nonneg one_pos hεb hFc
      hpc SquareExample.hFm SquareExample.hF hK
      ((ResolutionCover.ofChart SquareExample.chart).coverLamV Qs hact)
      ((ResolutionCover.ofChart SquareExample.chart).coverDegV Qs hact) ≠ 0 := by
    rw [productCoeffV_one]
    exact (mul_pos (Real.Gamma_pos_of_pos (by norm_num)) I_pos).ne'
  have h := ((ResolutionCover.ofChart
      SquareExample.chart).hasLeadingTerm_boltzmannIntegral_of_productChartsV_extremal Qs K_nonneg
    one_pos hεb hFc hpc SquareExample.hFm SquareExample.hF hK hact).isEquivalent hc
  rw [productCoeffV_one, coverLamV_eq, coverDegV_eq] at h
  have hZ : (ResolutionCover.ofChart SquareExample.chart).boltzmannIntegral (fun _ => (1 : ℝ)) K
      SquareExample.one = fun N => ∫ y in SquareExample.box, Real.exp (-N * K y) := by
    funext N
    rw [ResolutionCover.boltzmannIntegral_eq, ResolutionCover.ofChart_iUnion_image]
    change ∫ y in id '' SquareExample.box, (1 : ℝ) * SquareExample.one.w y * Real.exp (-N * K y) = _
    rw [Set.image_id]
    simp only [SquareExample.one_w, one_mul]
  rw [hZ] at h
  refine h.congr_right (Eventually.of_forall fun N => ?_)
  simp [powLogScale]

/-- ★ **The posterior expectation of `y₀²` converges to `J / I`** — the limiting posterior along
the face `y₁ = 0` has density `∝ |y₀|^{−1/2} (1+y₀²)^{−1/4}`, shaped by the unit. -/
theorem tendsto_posteriorExpectation_sq :
    Tendsto ((ResolutionCover.ofChart SquareExample.chart).posteriorExpectation K SquareExample.one
      Fsq) atTop (𝓝 (J / I)) := by
  have hc₁ : 0 < (ResolutionCover.ofChart SquareExample.chart).productCoeffV Qs K_nonneg one_pos hεb
      hFc hpc SquareExample.hFm SquareExample.hF hK
      ((ResolutionCover.ofChart SquareExample.chart).coverLamV Qs hact)
      ((ResolutionCover.ofChart SquareExample.chart).coverDegV Qs hact) := by
    rw [productCoeffV_one]
    exact mul_pos (Real.Gamma_pos_of_pos (by norm_num)) I_pos
  have h := ((ResolutionCover.ofChart
      SquareExample.chart).tendsto_posteriorExpectation_of_hasLeadingTerm
    ((ResolutionCover.ofChart
      SquareExample.chart).hasLeadingTerm_boltzmannIntegral_of_productChartsV_extremal Qs K_nonneg
      one_pos hεb hFc_sq hpc MixedExample.hFm_sq MixedExample.hF_sq hK hact)
    ((ResolutionCover.ofChart
      SquareExample.chart).hasLeadingTerm_boltzmannIntegral_of_productChartsV_extremal Qs K_nonneg
      one_pos hεb hFc hpc SquareExample.hFm SquareExample.hF hK hact) hc₁).2
  rw [productCoeffV_sq, productCoeffV_one] at h
  have hΓ : Real.Gamma (1 / 4) ≠ 0 := (Real.Gamma_pos_of_pos (by norm_num)).ne'
  have : Real.Gamma (1 / 4) * J / (Real.Gamma (1 / 4) * I) = J / I := by
    rw [mul_div_mul_left _ _ hΓ]
  rwa [this] at h

theorem ratio_pos : 0 < J / I := div_pos J_pos I_pos

theorem ratio_le_one : J / I ≤ 1 := (div_le_one I_pos).2 J_le_I

end VarMixedExample

end Grammar
