/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.ResidualFaceCoefficient
import Grammar.OneChartProductExample

/-!
# The unequal-exponent example `∫_{[−1,1]²} e^{−N x²y⁴} ~ 2Γ(1/4) N^{−1/4}`

Unit 2 of consult #80 (`tide-log/gpt6_bigpicture_v80.md`). For `K(y) = y₀² y₁⁴` on the square the
ratios are `1/2` and `1/4`, so `(λ*, k*) = (1/4, 0)`, the minimal set is `{1}` and the tied strata
are `{1}` and `{0, 1}`; the second is NOT all-minimal and exercises the residual-face formula of
CCL: the residual exponent of the `y₀`-direction is `0 − 2·1·(1/4) = −1/2 > −1`.

* **General helpers.** A piece whose base is null contributes nothing (`tiedSum_eq_zero_of_null`);
  the unit-box integral of a product is the product of the interval integrals
  (`integral_unitBox_prod`, from `restrict_unitBox` and `integral_fintype_prod_eq_prod`); and
  `∫_{(0,1]} t^r dt = 1/(r+1)` for `r > −1` (`integral_Ioc_rpow`).
* **The example.** With the cutoff `ε = 1` equal to the box radius the `{1}`-piece has its base in
  `{|y₀| = 1}` (null, `base_singleton_null`), and the `{0,1}`-piece contributes
  `2^{|J|} · Σ_{τ} Γ(1/4)/4 · ∫_{(0,1]²} u₀^{−1/2} du = 2 · 2 · Γ(1/4)/4 · 2 = 2Γ(1/4)`
  (`productCoeffD_eq`), hence ★ `integral_isEquivalent`:
  `∫_{[−1,1]²} e^{−N y₀² y₁⁴} dy ~ 2Γ(1/4) N^{−1/4}`.
-/

open MeasureTheory Set Filter Topology Asymptotics Monomialize.Analytic Monomialize.VolumeScaling
open scoped ENNReal

namespace Grammar

/-! ### General helpers -/

/-- `∫_{(0,1]} t^r dt = 1/(r+1)` for `r > −1`. -/
theorem integral_Ioc_rpow {r : ℝ} (hr : -1 < r) :
    ∫ t in Ioc (0 : ℝ) 1, t ^ r = 1 / (r + 1) := by
  rw [← intervalIntegral.integral_of_le zero_le_one, integral_rpow (Or.inl hr), Real.one_rpow,
    Real.zero_rpow (by linarith), sub_zero]

/-- The unit-box integral of a product of one-variable functions. -/
theorem integral_unitBox_prod {r : ℕ} (g : Fin r → ℝ → ℝ) :
    ∫ u in unitBox r, ∏ a, g a (u a) = ∏ a, ∫ t in Ioc (0 : ℝ) 1, g a t := by
  rw [restrict_unitBox]
  exact integral_fintype_prod_eq_prod g

namespace ProductMonomialChart

variable {d : ℕ} {ι : Type*} [Fintype ι] {R : ResolutionCover d ι} {i : ι} {K : (Fin d → ℝ) → ℝ}
  (P : ProductMonomialChart R i K) (hK0 : ∀ x, 0 ≤ K x) {ε : ℝ} (hε : 0 < ε) (hεb : ε ≤ P.b)
  {D : ι → Finset (Fin d)} (hD : D i = P.e.support) {F : (Fin d → ℝ) → ℝ} {p : TubeWeight d}
  (hFm : Measurable F)
  (hF : Integrable (fun x => F x * p.w x) (volume.restrict (⋃ i, R.image i)))
  (hK : Measurable K) (I : Finset (Fin d)) (hI : I ⊆ P.e.support) (hne : I.Nonempty)

/-- A piece whose base is null contributes nothing at any pair. -/
theorem tiedSum_eq_zero_of_null (lam₀ : ℝ) (k₀ : ℕ)
    (hnull : volume (P.pieceDensity hε hεb hD I hI hne p).base = 0)
    {At : FiniteScalarUnitAtlas (d - (I.card - 1 + 1)) (R.pieceIntegral D ε i I F K p)}
    (hAt : P.IsPieceAtlasData hK0 hε hεb hD hFm hF hK I hI hne At) :
    ∑ σ ∈ At.tied lam₀ k₀, (At.cell σ).coeff = 0 := by
  obtain ⟨q', A', hq'c, hq'pos, hA'c, hk, hbase, hβ, hamp', hphase', -, -, rfl⟩ := hAt
  refine Finset.sum_eq_zero fun σ _ => ?_
  unfold ScalarUnitCell.coeff
  exact setIntegral_measure_zero _ hnull

end ProductMonomialChart

/-! ### The example -/

namespace MixedExample

open SquareExample

/-- The exponents `(2, 4)`. -/
noncomputable def ex : Fin 2 →₀ ℕ := Finsupp.equivFunOnFinite.symm ![2, 4]

theorem ex_zero : ex 0 = 2 := rfl

theorem ex_one : ex 1 = 4 := rfl

theorem ex_support : ex.support = Finset.univ := by
  ext j
  fin_cases j <;> simp [Finsupp.mem_support_iff, ex_zero, ex_one]

/-- The phase `K(y) = y₀² y₁⁴`. -/
noncomputable def K (y : Fin 2 → ℝ) : ℝ := monomialEval y ex

theorem K_eq (y : Fin 2 → ℝ) : K y = y 0 ^ 2 * y 1 ^ 4 := by
  unfold K monomialEval
  rw [Finsupp.prod, ex_support, Fin.prod_univ_two, ex_zero, ex_one]

theorem K_nonneg (y : Fin 2 → ℝ) : 0 ≤ K y := by
  rw [K_eq]
  positivity

theorem continuous_K : Continuous K := by
  have : K = fun y => y 0 ^ 2 * y 1 ^ 4 := funext K_eq
  rw [this]
  fun_prop

theorem box_eq_productDom' :
    SquareExample.box = productDom ex.support ({0} : Set (Fin 2 → ℝ)) 1 := by
  rw [ex_support, ← SquareExample.expo_support]
  exact SquareExample.box_eq_productDom

/-- The monomial-chart certificate. -/
theorem isMonomialChart : IsMonomialChart K chart.φ chart.dom ex 0 univ where
  isOpen := isOpen_univ
  subset := subset_univ _
  analyticOnNhd := analyticOnNhd_id
  injOn := injOn_id _
  exists_unit := ⟨fun _ => 1, continuousOn_const, fun _ _ => one_ne_zero, fun y _ => by
    change K y = 1 * monomialEval y ex
    rw [one_mul]
    rfl⟩
  exists_jacUnit := ⟨fun _ => 1, continuousOn_const, fun _ _ => one_ne_zero, fun y _ => by
    change (fderiv ℝ (id : (Fin 2 → ℝ) → (Fin 2 → ℝ)) y).det = 1 * monomialEval y 0
    rw [det_id_eq, monomialEval_zero, one_mul]⟩

/-- **The product-chart package.** -/
noncomputable def package : ProductMonomialChart (ResolutionCover.ofChart chart) () K :=
  ProductMonomialChart.ofUnit chart ex 0 univ isOpen_univ (subset_univ _) isMonomialChart
    (fun _ => 1) continuousOn_const (fun _ _ => one_ne_zero)
    (fun y _ => by
      change K y = 1 * monomialEval y ex
      rw [one_mul]
      rfl)
    (fun _ => 1) continuousOn_const
    (fun y _ => by
      change (fderiv ℝ (id : (Fin 2 → ℝ) → (Fin 2 → ℝ)) y).det = 1 * monomialEval y 0
      rw [det_id_eq, monomialEval_zero, one_mul])
    {0} isCompact_singleton (singleton_nonempty _)
    (fun x hx j _ => by rw [mem_singleton_iff.1 hx]; rfl)
    1 one_pos box_eq_productDom' (fun _ _ => rfl)

noncomputable def Ps : ∀ i : Unit, ProductMonomialChart (ResolutionCover.ofChart chart) i K :=
  fun _ => package

theorem hεb' : ∀ i, (1 : ℝ) ≤ (Ps i).b := fun _ => le_rfl

theorem hFc' : ∀ i, ContinuousOn (fun y => (fun _ : Fin 2 → ℝ => (1 : ℝ))
    (((ResolutionCover.ofChart chart).chart i).φ y)) (Ps i).W :=
  fun _ => continuousOn_const

theorem hpc' : ∀ i, ContinuousOn (fun y => one.w (((ResolutionCover.ofChart chart).chart i).φ y))
    (Ps i).W :=
  fun _ => continuousOn_const

theorem hK' : Measurable K := continuous_K.measurable

theorem ratio_zero : (Ps ()).ratio 0 = 1 / 2 := by
  change ((((0 : Fin 2 →₀ ℕ) 0 : ℕ) : ℝ) + 1) / ((ex 0 : ℕ) : ℝ) = 1 / 2
  rw [ex_zero]
  simp

theorem ratio_one : (Ps ()).ratio 1 = 1 / 4 := by
  change ((((0 : Fin 2 →₀ ℕ) 1 : ℕ) : ℝ) + 1) / ((ex 1 : ℕ) : ℝ) = 1 / 4
  rw [ex_one]
  simp

theorem one_mem_support : (1 : Fin 2) ∈ (Ps ()).e.support := by
  rw [show (Ps ()).e = ex from rfl, ex_support]
  exact Finset.mem_univ _

theorem hact : ((ResolutionCover.ofChart chart).activeCoords Ps).Nonempty :=
  ⟨⟨(), 1⟩, (ResolutionCover.ofChart chart).mem_activeCoords Ps one_mem_support⟩

theorem coverLam_eq : (ResolutionCover.ofChart chart).coverLam Ps hact = 1 / 4 := by
  unfold ResolutionCover.coverLam
  have hj : ∀ j : Fin 2, (1 / 4 : ℝ) ≤ (Ps ()).ratio j :=
    Fin.forall_fin_two.2 ⟨by rw [ratio_zero]; norm_num, ratio_one.ge⟩
  exact le_antisymm ((Finset.inf'_le _ ((ResolutionCover.ofChart chart).mem_activeCoords Ps
    one_mem_support)).trans_eq ratio_one) (Finset.le_inf' _ _ fun x _ => hj x.2)

theorem minimalSet_eq :
    (Ps ()).minimalSet ((ResolutionCover.ofChart chart).coverLam Ps hact) = {1} := by
  unfold ProductMonomialChart.minimalSet
  rw [coverLam_eq, show (Ps ()).e = ex from rfl, ex_support]
  ext j
  fin_cases j
  · simp [ratio_zero]
  · simp [ratio_one]

theorem coverDeg_eq : (ResolutionCover.ofChart chart).coverDeg Ps hact = 0 := by
  unfold ResolutionCover.coverDeg
  have hfilt : (Finset.univ.filter fun i : Unit => ∃ j ∈ (Ps i).e.support,
      (Ps i).ratio j = (ResolutionCover.ofChart chart).coverLam Ps hact) = Finset.univ :=
    Finset.filter_true_of_mem fun i _ => ⟨1, one_mem_support, ratio_one.trans coverLam_eq.symm⟩
  rw [hfilt, Finset.univ_unique, Finset.sup_singleton]
  have hM : ((Ps default).e.support.filter fun j =>
      (Ps default).ratio j = (ResolutionCover.ofChart chart).coverLam Ps hact) = {1} :=
    minimalSet_eq
  rw [hM, Finset.card_singleton]

/-! #### The `{1}`-piece has a null base -/

theorem zero_mem_support : (0 : Fin 2) ∈ (Ps ()).e.support := by
  rw [show (Ps ()).e = ex from rfl, ex_support]
  exact Finset.mem_univ _

theorem one_subset_support : ({1} : Finset (Fin 2)) ⊆ (Ps ()).e.support := by
  rw [show (Ps ()).e = ex from rfl, ex_support]
  exact Finset.subset_univ _

theorem univ_subset_support : (Finset.univ : Finset (Fin 2)) ⊆ (Ps ()).e.support := by
  rw [show (Ps ()).e = ex from rfl, ex_support]

/-- The coordinate `0 ∉ {1}` is a tangential coordinate of the stratum `{1}`. -/
theorem exists_inl_zero : ∃ i₀, (0 : Fin 2) =
    (stratumSplit ({1} : Finset (Fin 2)) (Finset.singleton_nonempty 1)).symm (Sum.inl i₀) := by
  rcases h : stratumSplit ({1} : Finset (Fin 2)) (Finset.singleton_nonempty 1) 0 with i | a
  · exact ⟨i, by rw [← h, Equiv.symm_apply_apply]⟩
  · exfalso
    have := stratumSplit_symm_inr_mem ({1} : Finset (Fin 2)) (Finset.singleton_nonempty 1) a
    rw [← h, Equiv.symm_apply_apply] at this
    exact absurd (Finset.mem_singleton.1 this) (by decide)

instance : Subsingleton (Fin (2 - ({1} : Finset (Fin 2)).card)) :=
  inferInstanceAs (Subsingleton (Fin 1))

instance : Nonempty (Fin (2 - (({1} : Finset (Fin 2)).card - 1 + 1))) :=
  inferInstanceAs (Nonempty (Fin 1))

/-- **With the cutoff equal to the box radius, the `{1}`-piece has a null base**: its foot points
have `|y₀| = 1`. -/
theorem base_singleton_null :
    volume ((Ps ()).pieceDensity (D := fun i => (Ps i).e.support) one_pos (hεb' ()) rfl {1}
      one_subset_support (Finset.singleton_nonempty 1) one).base = 0 := by
  obtain ⟨i₀, hi₀⟩ := exists_inl_zero
  have hsub : ((Ps ()).pieceDensity (D := fun i => (Ps i).e.support) one_pos (hεb' ()) rfl {1}
      one_subset_support (Finset.singleton_nonempty 1) one).base ⊆
      (fun z => planeReindex (stratumSplit ({1} : Finset (Fin 2)) (Finset.singleton_nonempty 1))
        z i₀) ⁻¹' ({1, -1} : Set ℝ) := by
    intro z hz
    unfold ProductMonomialChart.pieceDensity at hz
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
    tangentialMonomial (Finset.univ : Finset (Fin 2)) Finset.univ_nonempty (Ps ()).h z = 1 := by
  unfold tangentialMonomial
  rw [show (Ps ()).h = 0 from rfl, Finsupp.support_zero, Finset.filter_empty, Finset.prod_empty]

theorem tangentialMonomial_univ_e
    (z : Fin (2 - ((Finset.univ : Finset (Fin 2)).card - 1 + 1)) → ℝ) :
    tangentialMonomial (Finset.univ : Finset (Fin 2)) Finset.univ_nonempty (Ps ()).e z = 1 := by
  unfold tangentialMonomial
  rw [Finset.filter_eq_empty_iff.2 fun j _ hj => hj (Finset.mem_univ j), Finset.prod_empty]

theorem zero_mem_pieceFootSet : (0 : Fin 2 → ℝ) ∈ (Ps ()).pieceFootSet Finset.univ := by
  refine ⟨?_, fun _ _ => rfl, fun j _ hj => absurd (Finset.mem_univ j) hj⟩
  change zeroOn (Ps ()).e.support (0 : Fin 2 → ℝ) ∈ ({0} : Set (Fin 2 → ℝ))
  rw [mem_singleton_iff]
  funext j
  by_cases hj : j ∈ (Ps ()).e.support
  · exact zeroOn_apply_of_mem _ hj _
  · exact zeroOn_apply_of_notMem _ hj _

theorem dominantFace_eq_univ :
    (Ps ()).dominantFace (fun i => (Ps i).e.support) 1 Finset.univ Finset.univ_nonempty
      (fun _ => (1 : ℝ)) one = univ := by
  refine eq_univ_of_forall fun z => ?_
  refine ⟨fun j _ hj => absurd (Finset.mem_univ j) hj, ?_, one_pos, one_pos, one_pos, one_ne_zero,
    ?_⟩
  · rw [planeSplit_univ_zero]
    exact zero_mem_box
  · rw [tangentialMonomial_univ_h]
    exact one_ne_zero

theorem base_univ_eq :
    ((Ps ()).pieceDensity (D := fun i => (Ps i).e.support) one_pos (hεb' ()) rfl Finset.univ
      univ_subset_support Finset.univ_nonempty one).base = univ :=
  eq_univ_of_forall fun z => (Ps ()).mem_pieceDensity_base_of_mem_dominantFace one_pos (hεb' ())
    rfl Finset.univ univ_subset_support Finset.univ_nonempty one
    (by rw [dominantFace_eq_univ]; exact mem_univ z)

/-! #### The residual coefficient of the `{0,1}`-piece -/

theorem hjr : ∀ j : Fin 2, (Ps ()).ratio j = 1 / 2 ∨ (Ps ()).ratio j = 1 / 4 :=
  Fin.forall_fin_two.2 ⟨Or.inl ratio_zero, Or.inr ratio_one⟩

theorem hlow : ∀ j ∈ (Ps ()).e.support, (1 / 4 : ℝ) ≤ (Ps ()).ratio j := fun j _ => by
  rcases hjr j with h | h
  · rw [h]; norm_num
  · rw [h]

theorem pieceLam_univ : (Ps ()).pieceLam Finset.univ Finset.univ_nonempty = 1 / 4 :=
  le_antisymm ((Finset.inf'_le _ (Finset.mem_univ 1)).trans_eq ratio_one)
    (Finset.le_inf' _ _ fun j _ => hlow j (univ_subset_support (Finset.mem_univ j)))

theorem pieceMult_univ : (Ps ()).pieceMult Finset.univ Finset.univ_nonempty = 1 := by
  rw [(Ps ()).pieceMult_eq_card_inter Finset.univ univ_subset_support Finset.univ_nonempty
    pieceLam_univ, ← coverLam_eq, minimalSet_eq, Finset.univ_inter, Finset.card_singleton]

theorem normalExp_h (a : Fin ((Finset.univ : Finset (Fin 2)).card - 1 + 1)) :
    normalExp Finset.univ Finset.univ_nonempty (Ps ()).h a = 0 := rfl

theorem ratioExp_normal (a : Fin ((Finset.univ : Finset (Fin 2)).card - 1 + 1)) :
    ratioExp (normalExp Finset.univ Finset.univ_nonempty (Ps ()).h)
        (normalHalfExp Finset.univ Finset.univ_nonempty (Ps ()).e) a =
      (Ps ()).ratio ((stratumSplit Finset.univ Finset.univ_nonempty).symm (Sum.inr a)) :=
  ratioExp_normal_eq Finset.univ Finset.univ_nonempty (Ps ()).e (Ps ()).h
    ((Ps ()).normalExp_eq_two_mul K_nonneg Finset.univ univ_subset_support Finset.univ_nonempty) a

theorem minRatio_normal :
    minRatio (normalExp Finset.univ Finset.univ_nonempty (Ps ()).h)
      (normalHalfExp Finset.univ Finset.univ_nonempty (Ps ()).e) = 1 / 4 :=
  ((Ps ()).pieceLam_eq K_nonneg Finset.univ univ_subset_support Finset.univ_nonempty).trans
    pieceLam_univ

theorem multCount_normal :
    multCount (ratioExp (normalExp Finset.univ Finset.univ_nonempty (Ps ()).h)
        (normalHalfExp Finset.univ Finset.univ_nonempty (Ps ()).e))
      (minRatio (normalExp Finset.univ Finset.univ_nonempty (Ps ()).h)
        (normalHalfExp Finset.univ Finset.univ_nonempty (Ps ()).e)) = 1 :=
  ((Ps ()).pieceMult_eq K_nonneg Finset.univ univ_subset_support Finset.univ_nonempty).trans
    pieceMult_univ

/-- The normal half-exponent is `2` on the minimal coordinate and `1` on the other. -/
theorem normalHalfExp_of_min {a : Fin ((Finset.univ : Finset (Fin 2)).card - 1 + 1)}
    (hk : 0 < normalHalfExp Finset.univ Finset.univ_nonempty (Ps ()).e a)
    (h : ratioExp (normalExp Finset.univ Finset.univ_nonempty (Ps ()).h)
      (normalHalfExp Finset.univ Finset.univ_nonempty (Ps ()).e) a = 1 / 4) :
    (normalHalfExp Finset.univ Finset.univ_nonempty (Ps ()).e a : ℝ) = 2 := by
  unfold ratioExp at h
  rw [normalExp_h] at h
  have hk' : (0 : ℝ) < 2 * (normalHalfExp Finset.univ Finset.univ_nonempty (Ps ()).e a : ℝ) := by
    have : (0 : ℝ) < normalHalfExp Finset.univ Finset.univ_nonempty (Ps ()).e a := by
      exact_mod_cast hk
    linarith
  rw [div_eq_div_iff hk'.ne' (by norm_num)] at h
  push_cast at h
  linarith

theorem normalHalfExp_of_nonmin {a : Fin ((Finset.univ : Finset (Fin 2)).card - 1 + 1)}
    (hk : 0 < normalHalfExp Finset.univ Finset.univ_nonempty (Ps ()).e a)
    (h : ¬ ratioExp (normalExp Finset.univ Finset.univ_nonempty (Ps ()).h)
      (normalHalfExp Finset.univ Finset.univ_nonempty (Ps ()).e) a = 1 / 4) :
    (normalHalfExp Finset.univ Finset.univ_nonempty (Ps ()).e a : ℝ) = 1 := by
  have h2 : ratioExp (normalExp Finset.univ Finset.univ_nonempty (Ps ()).h)
      (normalHalfExp Finset.univ Finset.univ_nonempty (Ps ()).e) a = 1 / 2 := by
    rw [ratioExp_normal] at h ⊢
    rcases hjr _ with h' | h'
    · exact h'
    · exact absurd h' h
  unfold ratioExp at h2
  rw [normalExp_h] at h2
  have hk' : (0 : ℝ) < 2 * (normalHalfExp Finset.univ Finset.univ_nonempty (Ps ()).e a : ℝ) := by
    have : (0 : ℝ) < normalHalfExp Finset.univ Finset.univ_nonempty (Ps ()).e a := by
      exact_mod_cast hk
    linarith
  rw [div_eq_div_iff hk'.ne' (by norm_num)] at h2
  push_cast at h2
  linarith

/-- The residual-weight integral over the unit box: `∫_{(0,1]²} u₀^{−1/2} du = 2`. -/
theorem integral_residualWeight
    (hk : ∀ a, 0 < normalHalfExp Finset.univ Finset.univ_nonempty (Ps ()).e a) :
    ∫ u in unitBox ((Finset.univ : Finset (Fin 2)).card - 1 + 1),
      residualWeight (normalExp Finset.univ Finset.univ_nonempty (Ps ()).h)
        (normalHalfExp Finset.univ Finset.univ_nonempty (Ps ()).e) (1 / 4) u = 2 := by
  unfold residualWeight
  rw [integral_unitBox_prod (fun a t => if ratioExp (normalExp Finset.univ Finset.univ_nonempty
    (Ps ()).h) (normalHalfExp Finset.univ Finset.univ_nonempty (Ps ()).e) a = 1 / 4 then (1 : ℝ)
    else t ^ ((normalExp Finset.univ Finset.univ_nonempty (Ps ()).h a : ℝ) -
      2 * (normalHalfExp Finset.univ Finset.univ_nonempty (Ps ()).e a : ℝ) * (1 / 4)))]
  have hterm : ∀ a, (∫ t in Ioc (0 : ℝ) 1, if ratioExp (normalExp Finset.univ Finset.univ_nonempty
      (Ps ()).h) (normalHalfExp Finset.univ Finset.univ_nonempty (Ps ()).e) a = 1 / 4 then (1 : ℝ)
      else t ^ ((normalExp Finset.univ Finset.univ_nonempty (Ps ()).h a : ℝ) -
        2 * (normalHalfExp Finset.univ Finset.univ_nonempty (Ps ()).e a : ℝ) * (1 / 4))) =
      if ratioExp (normalExp Finset.univ Finset.univ_nonempty (Ps ()).h)
        (normalHalfExp Finset.univ Finset.univ_nonempty (Ps ()).e) a = 1 / 4 then (1 : ℝ)
      else 2 := fun a => by
    split_ifs with hp
    · simp
    · have hexp : ((normalExp Finset.univ Finset.univ_nonempty (Ps ()).h a : ℝ) -
          2 * (normalHalfExp Finset.univ Finset.univ_nonempty (Ps ()).e a : ℝ) * (1 / 4)) =
          -(1 / 2) := by
        rw [normalExp_h, normalHalfExp_of_nonmin (hk a) hp]
        norm_num
      rw [hexp, integral_Ioc_rpow (by norm_num)]
      norm_num
  rw [Finset.prod_congr rfl fun a _ => hterm a, Finset.prod_ite, Finset.prod_const_one, one_mul,
    Finset.prod_const]
  have hcard : (Finset.univ.filter fun a => ¬ ratioExp (normalExp Finset.univ
      Finset.univ_nonempty (Ps ()).h) (normalHalfExp Finset.univ Finset.univ_nonempty (Ps ()).e)
      a = 1 / 4).card = 1 := by
    have h1 := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun a => ratioExp (normalExp Finset.univ Finset.univ_nonempty (Ps ()).h)
        (normalHalfExp Finset.univ Finset.univ_nonempty (Ps ()).e) a = 1 / 4)
    have h2 : (Finset.univ.filter fun a => ratioExp (normalExp Finset.univ Finset.univ_nonempty
        (Ps ()).h) (normalHalfExp Finset.univ Finset.univ_nonempty (Ps ()).e) a = 1 / 4).card =
        1 := by
      rw [← minRatio_normal]
      exact (multCount_eq_card_minimalCoords _ _ _).symm.trans multCount_normal
    have h3 : (Finset.univ : Finset (Fin ((Finset.univ : Finset (Fin 2)).card - 1 + 1))).card =
        2 := by decide
    omega
  rw [hcard, pow_one]

/-- The face constant `Γ(1/4)/0! · 1/(2·2) = Γ(1/4)/4`. -/
theorem faceLeadConst_eq
    (hk : ∀ a, 0 < normalHalfExp Finset.univ Finset.univ_nonempty (Ps ()).e a) :
    faceLeadConst (normalExp Finset.univ Finset.univ_nonempty (Ps ()).h)
      (normalHalfExp Finset.univ Finset.univ_nonempty (Ps ()).e) (1 / 4) 1 =
      Real.Gamma (1 / 4) / 4 := by
  rw [faceLeadConst_one_eq]
  have hJ : (minimalCoords (normalExp Finset.univ Finset.univ_nonempty (Ps ()).h)
      (normalHalfExp Finset.univ Finset.univ_nonempty (Ps ()).e) (1 / 4)).card = 1 := by
    rw [← minRatio_normal, ← multCount_eq_card_minimalCoords]
    exact multCount_normal
  rw [Finset.prod_congr rfl fun a ha => by
    rw [normalHalfExp_of_min (hk a) ((mem_minimalCoords _ _ _).1 ha)], Finset.prod_const, hJ]
  norm_num
  ring


/-! #### The tied sum of the `{0,1}`-piece and the total coefficient -/

theorem v_eq (x : Fin 2 → ℝ) : (Ps ()).v x = 1 := rfl

theorem pieceAmp_eq_one (z : Fin (2 - ((Finset.univ : Finset (Fin 2)).card - 1 + 1)) → ℝ)
    (w : Fin ((Finset.univ : Finset (Fin 2)).card - 1 + 1) → ℝ) :
    (ResolutionCover.ofChart chart).pieceAmp () Finset.univ Finset.univ_nonempty (Ps ()).h (Ps ()).v
      (F := fun _ => (1 : ℝ)) (p := one) z w = 1 := by
  unfold ResolutionCover.pieceAmp
  rw [v_eq, tangentialMonomial_univ_h]
  simp

theorem scalarPhase_eq_one (z : Fin (2 - ((Finset.univ : Finset (Fin 2)).card - 1 + 1)) → ℝ) :
    scalarPhase Finset.univ Finset.univ_nonempty (Ps ()).u (Ps ()).e z = 1 := by
  unfold scalarPhase tangentialUnit
  rw [tangentialMonomial_univ_e]
  change (1 : ℝ) * 1 = 1
  norm_num

theorem reflect_faceProj_mem_closedBall {r : ℕ} (h k : Fin r → ℕ) (l : ℝ) (σ : Fin r → Bool)
    {u : Fin r → ℝ} (hu : u ∈ unitBox r) :
    reflect σ ((1 : ℝ) • faceProj h k l u) ∈ Metric.closedBall (0 : Fin r → ℝ) 1 := by
  rw [mem_closedBall_zero_iff, one_smul]
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun a => ?_
  rw [Real.norm_eq_abs, reflect, abs_mul, abs_sgn', one_mul, faceProj]
  split_ifs
  · simp
  · have hua := hu a (mem_univ a)
    rw [abs_of_pos hua.1]
    exact hua.2

/-- The minimal normal coordinates of the `{0,1}`-piece at its exponent. -/
noncomputable def Jmin : Finset (Fin ((Finset.univ : Finset (Fin 2)).card - 1 + 1)) :=
  minimalCoords (normalExp Finset.univ Finset.univ_nonempty (Ps ()).h)
    (normalHalfExp Finset.univ Finset.univ_nonempty (Ps ()).e)
    (minRatio (normalExp Finset.univ Finset.univ_nonempty (Ps ()).h)
      (normalHalfExp Finset.univ Finset.univ_nonempty (Ps ()).e))

/-- **The tied sum of the `{0,1}`-piece is `2Γ(1/4)`** (residual formula:
`2^{|J|} · Σ_{τ} Γ(1/4)/4 · ∫_{(0,1]²} u₀^{−1/2} du = 2 · 2 · Γ(1/4)/4 · 2`). -/
theorem tiedSum_univ
    {At : FiniteScalarUnitAtlas (2 - ((Finset.univ : Finset (Fin 2)).card - 1 + 1))
      ((ResolutionCover.ofChart chart).pieceIntegral (fun i => (Ps i).e.support) 1 () Finset.univ
        (fun _ => (1 : ℝ)) K one)}
    (hAt : (Ps ()).IsPieceAtlasData K_nonneg one_pos (hεb' ()) rfl hFm hF hK' Finset.univ
      univ_subset_support Finset.univ_nonempty At) :
    ∑ σ ∈ At.tied (1 / 4) 0, (At.cell σ).coeff = 2 * Real.Gamma (1 / 4) := by
  obtain ⟨q', A', hq'c, hq'pos, hA'c, hk, hbase, hβ, hamp', hphase', hq', hA', rfl⟩ := hAt
  rw [(ResolutionCover.ofChart chart).pieceAtlas_sum_tied_residual () (fun i => (Ps i).e.support)
    one_pos Finset.univ Finset.univ_nonempty _ hbase hβ rfl _ _ hk q' hq'c hq'pos A' hA'c hamp'
    hphase' hFm hF hK' K_nonneg minRatio_normal (by rw [multCount_normal])]
  have hJ : Jmin.card = 1 :=
    (multCount_eq_card_minimalCoords _ _ _).symm.trans multCount_normal
  have hterm : ∀ σ : Fin ((Finset.univ : Finset (Fin 2)).card - 1 + 1) → Bool,
      (((ResolutionCover.ofChart chart).pieceCell () (fun i => (Ps i).e.support)
      one_pos Finset.univ Finset.univ_nonempty _ hbase hβ
      (normalExp Finset.univ Finset.univ_nonempty (Ps ()).h)
      (normalHalfExp Finset.univ Finset.univ_nonempty (Ps ()).e) hk q' hq'c hq'pos A'
      hA'c).reflected σ).coeff = Real.Gamma (1 / 4) / 2 := fun σ => by
    refine (ScalarUnitCell.reflected_coeff_eq ((ResolutionCover.ofChart chart).pieceCell ()
      (fun i => (Ps i).e.support) one_pos Finset.univ Finset.univ_nonempty
      ((Ps ()).pieceDensity (D := fun i => (Ps i).e.support) one_pos (hεb' ()) rfl Finset.univ
        univ_subset_support Finset.univ_nonempty one) hbase hβ
      (normalExp Finset.univ Finset.univ_nonempty (Ps ()).h)
      (normalHalfExp Finset.univ Finset.univ_nonempty (Ps ()).e) hk q' hq'c hq'pos A' hA'c)
      σ).trans ?_
    change ∫ z in ((Ps ()).pieceDensity (D := fun i => (Ps i).e.support) one_pos (hεb' ()) rfl
        Finset.univ univ_subset_support Finset.univ_nonempty one).base,
      ((Ps ()).pieceDensity (D := fun i => (Ps i).e.support) one_pos (hεb' ()) rfl Finset.univ
        univ_subset_support Finset.univ_nonempty one).beta z *
      (q' z ^ (-(minRatio (normalExp Finset.univ Finset.univ_nonempty (Ps ()).h)
          (normalHalfExp Finset.univ Finset.univ_nonempty (Ps ()).e))) *
        ((1 : ℝ) ^ (∑ a ∈ Finset.univ.filter (fun a => ¬ ratioExp
            (normalExp Finset.univ Finset.univ_nonempty (Ps ()).h)
            (normalHalfExp Finset.univ Finset.univ_nonempty (Ps ()).e) a =
              minRatio (normalExp Finset.univ Finset.univ_nonempty (Ps ()).h)
                (normalHalfExp Finset.univ Finset.univ_nonempty (Ps ()).e)),
            (residualExponent (normalExp Finset.univ Finset.univ_nonempty (Ps ()).h)
              (normalHalfExp Finset.univ Finset.univ_nonempty (Ps ()).e)
              (minRatio (normalExp Finset.univ Finset.univ_nonempty (Ps ()).h)
                (normalHalfExp Finset.univ Finset.univ_nonempty (Ps ()).e)) a + 1)) *
          (faceLeadConst (normalExp Finset.univ Finset.univ_nonempty (Ps ()).h)
              (normalHalfExp Finset.univ Finset.univ_nonempty (Ps ()).e)
              (minRatio (normalExp Finset.univ Finset.univ_nonempty (Ps ()).h)
                (normalHalfExp Finset.univ Finset.univ_nonempty (Ps ()).e)) 1 *
            ∫ u in unitBox ((Finset.univ : Finset (Fin 2)).card - 1 + 1),
              A' z (reflect σ ((1 : ℝ) • faceProj (normalExp Finset.univ Finset.univ_nonempty
                (Ps ()).h) (normalHalfExp Finset.univ Finset.univ_nonempty (Ps ()).e)
                (minRatio (normalExp Finset.univ Finset.univ_nonempty (Ps ()).h)
                  (normalHalfExp Finset.univ Finset.univ_nonempty (Ps ()).e)) u)) *
                residualWeight (normalExp Finset.univ Finset.univ_nonempty (Ps ()).h)
                  (normalHalfExp Finset.univ Finset.univ_nonempty (Ps ()).e)
                  (minRatio (normalExp Finset.univ Finset.univ_nonempty (Ps ()).h)
                    (normalHalfExp Finset.univ Finset.univ_nonempty (Ps ()).e)) u))) = _
    rw [minRatio_normal, faceLeadConst_eq hk, Real.one_rpow]
    have hint : ∀ z, ((Ps ()).pieceDensity (D := fun i => (Ps i).e.support) one_pos (hεb' ()) rfl
        Finset.univ univ_subset_support Finset.univ_nonempty one).beta z *
        (q' z ^ (-(1 / 4 : ℝ)) * (1 * (Real.Gamma (1 / 4) / 4 *
          ∫ u in unitBox ((Finset.univ : Finset (Fin 2)).card - 1 + 1),
            A' z (reflect σ ((1 : ℝ) • faceProj (normalExp Finset.univ Finset.univ_nonempty
              (Ps ()).h) (normalHalfExp Finset.univ Finset.univ_nonempty (Ps ()).e) (1 / 4) u)) *
              residualWeight (normalExp Finset.univ Finset.univ_nonempty (Ps ()).h)
                (normalHalfExp Finset.univ Finset.univ_nonempty (Ps ()).e) (1 / 4) u))) =
        Real.Gamma (1 / 4) / 2 := fun z => by
      have hz : z ∈ ((Ps ()).pieceDensity (D := fun i => (Ps i).e.support) one_pos (hεb' ()) rfl
          Finset.univ univ_subset_support Finset.univ_nonempty one).base := by
        rw [base_univ_eq]; exact mem_univ z
      have hinner : ∫ u in unitBox ((Finset.univ : Finset (Fin 2)).card - 1 + 1),
          A' z (reflect σ ((1 : ℝ) • faceProj (normalExp Finset.univ Finset.univ_nonempty
            (Ps ()).h) (normalHalfExp Finset.univ Finset.univ_nonempty (Ps ()).e) (1 / 4) u)) *
            residualWeight (normalExp Finset.univ Finset.univ_nonempty (Ps ()).h)
              (normalHalfExp Finset.univ Finset.univ_nonempty (Ps ()).e) (1 / 4) u = 2 := by
        rw [← integral_residualWeight hk]
        refine setIntegral_congr_fun (measurableSet_unitBox _) fun u hu => ?_
        rw [hA' z hz _ (reflect_faceProj_mem_closedBall _ _ _ σ hu), pieceAmp_eq_one, one_mul]
      rw [ProductMonomialChart.pieceDensity_beta, planeSplit_univ_zero,
        Set.indicator_of_mem zero_mem_pieceFootSet, hq' z hz, scalarPhase_eq_one, Real.one_rpow,
        hinner]
      change (1 : ℝ) * (1 * (1 * (Real.Gamma (1 / 4) / 4 * 2))) = _
      ring
    rw [setIntegral_congr_fun (base_univ_eq ▸ MeasurableSet.univ) fun z _ => hint z, base_univ_eq,
      Measure.restrict_univ, integral_const, measureReal_def, volume_univ_base]
    simp
  have hL : (Finset.univ : Finset (Fin ((Finset.univ : Finset (Fin 2)).card - 1 + 1) → Bool)).card =
      4 := by decide
  have hcount := sum_reduce_of_indep Jmin (fun _ => (1 : ℝ)) (fun _ _ _ => rfl)
  rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, mul_one, mul_one, hJ, pow_one,
    hL] at hcount
  have hterm' : ∀ τ : {a // a ∉ Jmin} → Bool,
      (((ResolutionCover.ofChart chart).pieceCell () (fun i => (Ps i).e.support)
      one_pos Finset.univ Finset.univ_nonempty _ hbase hβ
      (normalExp Finset.univ Finset.univ_nonempty (Ps ()).h)
      (normalHalfExp Finset.univ Finset.univ_nonempty (Ps ()).e) hk q' hq'c hq'pos A'
      hA'c).reflected (extendFalse Jmin τ)).coeff = Real.Gamma (1 / 4) / 2 :=
    fun τ => hterm _
  have hsum : ∑ τ : {a // a ∉ Jmin} → Bool,
      (((ResolutionCover.ofChart chart).pieceCell () (fun i => (Ps i).e.support)
      one_pos Finset.univ Finset.univ_nonempty _ hbase hβ
      (normalExp Finset.univ Finset.univ_nonempty (Ps ()).h)
      (normalHalfExp Finset.univ Finset.univ_nonempty (Ps ()).e) hk q' hq'c hq'pos A'
      hA'c).reflected (extendFalse Jmin τ)).coeff =
      ∑ _τ : {a // a ∉ Jmin} → Bool, Real.Gamma (1 / 4) / 2 :=
    Finset.sum_congr rfl fun τ _ => hterm' τ
  have hfinal : (2 : ℝ) ^ (Jmin).card *
      ∑ _τ : {a // a ∉ Jmin} → Bool, Real.Gamma (1 / 4) / 2 =
        2 * Real.Gamma (1 / 4) := by
    rw [Finset.sum_const, nsmul_eq_mul, hJ, pow_one]
    push_cast at hcount ⊢
    linear_combination (-(Real.Gamma (1 / 4) / 2)) * hcount
  exact (congrArg (fun x => (2 : ℝ) ^ (Jmin).card * x) hsum).trans hfinal

/-- **The leading coefficient of the mixed-exponent example is `2Γ(1/4)`.** -/
theorem productCoeffD_eq :
    (ResolutionCover.ofChart chart).productCoeffD Ps K_nonneg one_pos hεb' hFc' hpc' hFm hF hK'
      ((ResolutionCover.ofChart chart).coverLam Ps hact)
      ((ResolutionCover.ofChart chart).coverDeg Ps hact) = 2 * Real.Gamma (1 / 4) := by
  have hsum : ∀ f : Unit → ℝ, ∑ i, f i = f () := fun f => Fintype.sum_unique f
  rw [(ResolutionCover.ofChart chart).productCoeffD_extremal_eq_sum_tied Ps hact K_nonneg one_pos
    hεb' hFc' hpc' hFm hF hK', hsum]
  have hS : (((Ps ()).e.support.powerset.filter fun I => I.Nonempty).filter
      (fun I => (Ps ()).minimalSet ((ResolutionCover.ofChart chart).coverLam Ps hact) ⊆ I ∧
        ((Ps ()).minimalSet ((ResolutionCover.ofChart chart).coverLam Ps hact)).card =
          (ResolutionCover.ofChart chart).coverDeg Ps hact + 1)) =
      {{1}, Finset.univ} := by
    rw [minimalSet_eq, coverDeg_eq, show (Ps ()).e = ex from rfl, ex_support]
    decide
  have hzero : ResolutionCover.scalarAtlasPieceCoeff'
      ((ResolutionCover.ofChart chart).productAtlasesD Ps K_nonneg one_pos hεb' hFc' hpc' hFm hF
        hK')
      ((ResolutionCover.ofChart chart).coverLam Ps hact)
      ((ResolutionCover.ofChart chart).coverDeg Ps hact) () {1} = 0 := by
    rw [ResolutionCover.scalarAtlasPieceCoeff'_of_mem _ _ _ () {1} one_subset_support
      (Finset.singleton_nonempty 1)]
    exact (Ps ()).tiedSum_eq_zero_of_null K_nonneg one_pos (hεb' ()) rfl hFm hF hK' {1}
      one_subset_support (Finset.singleton_nonempty 1) _ _ base_singleton_null
      ((Ps ()).pieceAtlasD_data K_nonneg one_pos (hεb' ()) rfl (hFc' ()) (hpc' ()) hFm hF hK' {1}
        one_subset_support (Finset.singleton_nonempty 1))
  have huniv : ResolutionCover.scalarAtlasPieceCoeff'
      ((ResolutionCover.ofChart chart).productAtlasesD Ps K_nonneg one_pos hεb' hFc' hpc' hFm hF
        hK')
      ((ResolutionCover.ofChart chart).coverLam Ps hact)
      ((ResolutionCover.ofChart chart).coverDeg Ps hact) () Finset.univ =
      2 * Real.Gamma (1 / 4) := by
    rw [ResolutionCover.scalarAtlasPieceCoeff'_of_mem _ _ _ () Finset.univ univ_subset_support
      Finset.univ_nonempty, coverLam_eq, coverDeg_eq]
    exact tiedSum_univ ((Ps ()).pieceAtlasD_data K_nonneg one_pos (hεb' ()) rfl (hFc' ()) (hpc' ())
      hFm hF hK' Finset.univ univ_subset_support Finset.univ_nonempty)
  rw [hS, Finset.sum_pair (by decide : ({1} : Finset (Fin 2)) ≠ Finset.univ), hzero, huniv,
    zero_add]

/-- ★ **The unequal-exponent regression example**:
`∫_{[−1,1]²} e^{−N y₀² y₁⁴} dy ~ 2Γ(1/4) · N^{−1/4}`. -/
theorem integral_isEquivalent :
    (fun N : ℝ => ∫ y in SquareExample.box, Real.exp (-N * K y)) ~[atTop]
      fun N => 2 * Real.Gamma (1 / 4) * N ^ (-(1 / 4 : ℝ)) := by
  have hc : (ResolutionCover.ofChart chart).productCoeffD Ps K_nonneg one_pos hεb' hFc' hpc' hFm hF
      hK' ((ResolutionCover.ofChart chart).coverLam Ps hact)
      ((ResolutionCover.ofChart chart).coverDeg Ps hact) ≠ 0 := by
    rw [productCoeffD_eq]
    exact (mul_pos two_pos (Real.Gamma_pos_of_pos (by norm_num))).ne'
  have h := ((ResolutionCover.ofChart
      chart).hasLeadingTerm_boltzmannIntegral_of_productChartsD_extremal Ps K_nonneg one_pos hεb'
    hpc' hK' hFc' hFm hF hact).isEquivalent hc
  rw [productCoeffD_eq, coverLam_eq, coverDeg_eq] at h
  have hZ : (ResolutionCover.ofChart chart).boltzmannIntegral (fun _ => (1 : ℝ)) K one =
      fun N => ∫ y in SquareExample.box, Real.exp (-N * K y) := by
    funext N
    rw [ResolutionCover.boltzmannIntegral_eq, ResolutionCover.ofChart_iUnion_image]
    change ∫ y in id '' SquareExample.box, (1 : ℝ) * one.w y * Real.exp (-N * K y) = _
    rw [Set.image_id]
    simp only [one_w, one_mul]
  rw [hZ] at h
  refine h.congr_right (Eventually.of_forall fun N => ?_)
  simp [powLogScale]


end MixedExample

end Grammar
