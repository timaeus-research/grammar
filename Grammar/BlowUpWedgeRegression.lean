/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.CertifiedResolutionExplicitCoefficient
import Monomialize.Analytic.BlowUpChart

/-!
# The blow-up square regression (CCLXXX)

The Gaussian integral `∫_{[−1,1]²} e^{−N(a²+b²)}` computed through the a.e.-disjoint assembly of
CCLXXVIII with the two standard blow-up charts of the origin (hironaka's `blowUpChart`):
`φ₀(s,t) = (s, st)`, `φ₁(s,t) = (st, t)` on `[−1,1]²`, with images the wedges `{|b| ≤ |a| ≤ 1}` and
`{|a| ≤ |b| ≤ 1}` — a genuine multi-chart, non-identity-chart test (consult #85 unit 7, checked in
consult #86):

* `K ∘ φ_β = y_β² (1 + y_{rev β}²)`, `det Dφ_β = y_β` (hironaka's `det_fderiv_blowUpChart`), so each
  chart carries the one-chart variable-unit product package with `e = 2·δ_β`, `h = δ_β`, unit
  `1 + y_{rev β}²`, tangential base `{x_β = 0, |x_{rev β}| ≤ 1}`;
* the images cover the square exactly and meet only on the diagonals, which are null
  (`Measure.addHaar_submodule`);
* each chart has pair `(1, 0)` and coefficient `2 · Γ(1)/0! · (1/2) · ∫_{−1}^{1} dt/(1+t²) = π/2`
  (the face integral transported from `Fin 1 → ℝ` to `ℝ`), the two tied charts sum to `π`;
* ★ `integral_isEquivalent : ∫_{[−1,1]²} e^{−N(a²+b²)} ~ π N^{−1}` — the classical value
  `(√π N^{−1/2})²`, recovered by the certified assembly.
-/

open MeasureTheory Set Filter Topology Asymptotics Monomialize.Analytic Monomialize.VolumeScaling

namespace Grammar

namespace BlowUpWedge

/-! ### Coordinates and the stratum splitting for a singleton stratum in the plane -/

theorem rev_ne (β : Fin 2) : Fin.rev β ≠ β := by fin_cases β <;> decide

theorem eq_or_eq_rev (β j : Fin 2) : j = β ∨ j = Fin.rev β := by
  fin_cases β <;> fin_cases j <;> simp

theorem rev_zero' : Fin.rev (0 : Fin 2) = 1 := by decide

theorem rev_one : Fin.rev (1 : Fin 2) = 0 := by decide

/-- The tangential index type of a singleton stratum in the plane is a point. -/
instance uniqueTang (β : Fin 2) : Unique (Fin (2 - (({β} : Finset (Fin 2)).card - 1 + 1))) :=
  inferInstanceAs (Unique (Fin 1))

/-- The normal index type of a singleton stratum is a point. -/
instance uniqueNorm (β : Fin 2) : Unique (Fin (({β} : Finset (Fin 2)).card - 1 + 1)) :=
  inferInstanceAs (Unique (Fin 1))

theorem planeSplit_rev (β : Fin 2) (z : Fin (2 - (({β} : Finset (Fin 2)).card - 1 + 1)) → ℝ)
    (n : Fin (({β} : Finset (Fin 2)).card - 1 + 1) → ℝ)
    (i : Fin (2 - (({β} : Finset (Fin 2)).card - 1 + 1))) :
    planeSplit (stratumSplit ({β} : Finset (Fin 2)) (Finset.singleton_nonempty β)) (z, n)
      (Fin.rev β) = z i := by
  rcases h : stratumSplit ({β} : Finset (Fin 2)) (Finset.singleton_nonempty β) (Fin.rev β)
    with i' | a
  · rw [planeSplit_apply, coordCLE_apply, h, Sum.elim_inl]
    simp only [planeReindex, LinearEquiv.coe_toContinuousLinearEquiv',
      LinearEquiv.funCongrLeft_apply]
    exact congrArg z (Subsingleton.elim _ _)
  · exfalso
    have hmem := stratumSplit_symm_inr_mem ({β} : Finset (Fin 2)) (Finset.singleton_nonempty β) a
    rw [← h, Equiv.symm_apply_apply, Finset.mem_singleton] at hmem
    exact rev_ne β hmem

theorem planeSplit_self (β : Fin 2) (z : Fin (2 - (({β} : Finset (Fin 2)).card - 1 + 1)) → ℝ)
    (n : Fin (({β} : Finset (Fin 2)).card - 1 + 1) → ℝ)
    (a : Fin (({β} : Finset (Fin 2)).card - 1 + 1)) :
    planeSplit (stratumSplit ({β} : Finset (Fin 2)) (Finset.singleton_nonempty β)) (z, n) β =
      n a := by
  obtain ⟨a', ha⟩ := exists_inr_of_mem ({β} : Finset (Fin 2)) (Finset.singleton_nonempty β)
    (Finset.mem_singleton_self β)
  have := planeSplit_stratum_inr ({β} : Finset (Fin 2)) (Finset.singleton_nonempty β) z n a'
  rw [← ha] at this
  rw [this]
  exact congrArg n (Subsingleton.elim _ _)

theorem monomialEval_single (y : Fin 2 → ℝ) (β : Fin 2) (k : ℕ) :
    monomialEval y (Finsupp.single β k) = y β ^ k := by
  unfold monomialEval
  exact Finsupp.prod_single_index (pow_zero _)

/-! ### The blow-up charts -/

/-- The block: both coordinates. -/
def B : Fin 2 ↪ Fin 2 := Function.Embedding.refl (Fin 2)

/-- The chart map of pivot `β`: `y ↦ (y_β, y_β y_{rev β})` in the coordinate order `(β, rev β)`. -/
noncomputable def φ (β : Fin 2) : (Fin 2 → ℝ) → (Fin 2 → ℝ) := blowUpChart B β

theorem φ_self (β : Fin 2) (y : Fin 2 → ℝ) : φ β y β = y β := blowUpChart_apply_scaling B y

theorem φ_rev (β : Fin 2) (y : Fin 2 → ℝ) : φ β y (Fin.rev β) = y β * y (Fin.rev β) :=
  blowUpChart_apply_ratio B y (rev_ne β)

theorem det_φ (β : Fin 2) (y : Fin 2 → ℝ) : (fderiv ℝ (φ β) y).det = y β := by
  unfold φ
  rw [det_fderiv_blowUpChart]
  simp [Fintype.card_fin, B]

theorem analyticOnNhd_φ (β : Fin 2) : AnalyticOnNhd ℝ (φ β) univ := by
  classical
  have hproj : ∀ j : Fin 2, AnalyticOnNhd ℝ (fun x : Fin 2 → ℝ => x j) univ := fun j =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) j).analyticOnNhd univ
  unfold φ blowUpChart
  refine AnalyticOnNhd.pi fun j => ?_
  by_cases hj : ∃ γ, γ ≠ β ∧ B γ = j
  · simp only [if_pos hj]
    exact (hproj (B β)).mul (hproj j)
  · simp only [if_neg hj]
    exact hproj j

theorem contDiffOn_φ (β : Fin 2) : ContDiffOn ℝ 1 (φ β) univ :=
  ((contDiff_blowUpChart B β (n := ⊤)).contDiffOn).of_le (by exact_mod_cast le_top)

theorem continuous_φ (β : Fin 2) : Continuous (φ β) := continuous_blowUpChart B β

/-- The square `[−1, 1]²`. -/
def square : Set (Fin 2 → ℝ) := Set.pi univ fun _ => Icc (-1) 1

theorem mem_square {x : Fin 2 → ℝ} : x ∈ square ↔ ∀ j, |x j| ≤ 1 := by
  simp only [square, Set.mem_pi, mem_univ, true_implies, mem_Icc, abs_le]

theorem isCompact_square : IsCompact square := isCompact_univ_pi fun _ => isCompact_Icc

theorem zero_mem_square : (0 : Fin 2 → ℝ) ∈ square :=
  mem_square.2 fun _ => by simp

/-- The blow-up chart of pivot `β` on the square, exceptional set the pivot hyperplane. -/
noncomputable def chart (β : Fin 2) : ResolutionChart 2 where
  dom := square
  dom_compact := isCompact_square
  φ := φ β
  U := univ
  U_open := isOpen_univ
  dom_subset := subset_univ _
  smooth := contDiffOn_φ β
  E := square ∩ {y | y β = 0}
  E_subset := inter_subset_left
  E_closed := isCompact_square.isClosed.inter (isClosed_eq (continuous_apply β) continuous_const)
  E_null := measure_mono_null inter_subset_right (pivotHyperplane_null B β)
  inj := fun a ha b hb hab =>
    blowUpChart_injOn_compl_pivotHyperplane B β (fun h0 => ha.2 ⟨ha.1, h0⟩)
      (fun h0 => hb.2 ⟨hb.1, h0⟩) hab

theorem chart_dom (β : Fin 2) : (chart β).dom = square := rfl

theorem chart_φ (β : Fin 2) : (chart β).φ = φ β := rfl

/-! ### The phase and the monomial data -/

/-- The phase `K(a, b) = a² + b²`. -/
noncomputable def K (x : Fin 2 → ℝ) : ℝ := x 0 ^ 2 + x 1 ^ 2

theorem K_nonneg (x : Fin 2 → ℝ) : 0 ≤ K x := add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem continuous_K : Continuous K := by
  unfold K
  fun_prop

theorem K_eq_rev (β : Fin 2) (x : Fin 2 → ℝ) : K x = x β ^ 2 + x (Fin.rev β) ^ 2 := by
  fin_cases β
  · simp only [Fin.isValue, Fin.zero_eta, rev_zero']
    rfl
  · simp only [Fin.isValue, Fin.mk_one, rev_one]
    unfold K
    ring

theorem K_φ (β : Fin 2) (y : Fin 2 → ℝ) : K (φ β y) = (1 + y (Fin.rev β) ^ 2) * y β ^ 2 := by
  rw [K_eq_rev β, φ_self, φ_rev]
  ring

/-- The unit `1 + y_{rev β}²`. -/
noncomputable def unit (β : Fin 2) (y : Fin 2 → ℝ) : ℝ := 1 + y (Fin.rev β) ^ 2

theorem unit_pos (β : Fin 2) (y : Fin 2 → ℝ) : 0 < unit β y := by
  unfold unit
  positivity

theorem continuous_unit (β : Fin 2) : Continuous (unit β) := by
  unfold unit
  fun_prop

/-- The phase exponents `2·δ_β`. -/
noncomputable def expo (β : Fin 2) : Fin 2 →₀ ℕ := Finsupp.single β 2

/-- The Jacobian exponents `δ_β`. -/
noncomputable def jexp (β : Fin 2) : Fin 2 →₀ ℕ := Finsupp.single β 1

theorem expo_support (β : Fin 2) : (expo β).support = {β} := by
  unfold expo
  exact Finsupp.support_single_ne_zero β two_ne_zero

theorem jexp_support (β : Fin 2) : (jexp β).support = {β} := by
  unfold jexp
  exact Finsupp.support_single_ne_zero β one_ne_zero

theorem expo_apply_self (β : Fin 2) : expo β β = 2 := by
  unfold expo
  exact Finsupp.single_eq_same

theorem jexp_apply_self (β : Fin 2) : jexp β β = 1 := by
  unfold jexp
  exact Finsupp.single_eq_same

theorem monomialEval_expo (β : Fin 2) (y : Fin 2 → ℝ) : monomialEval y (expo β) = y β ^ 2 :=
  monomialEval_single y β 2

theorem monomialEval_jexp (β : Fin 2) (y : Fin 2 → ℝ) : monomialEval y (jexp β) = y β := by
  rw [jexp, monomialEval_single, pow_one]

/-- **The blow-up chart is a monomial chart for the quadratic phase.** -/
theorem isMonomialChart (β : Fin 2) : IsMonomialChart K (φ β) square (expo β) (jexp β) univ where
  isOpen := isOpen_univ
  subset := subset_univ _
  analyticOnNhd := analyticOnNhd_φ β
  injOn := fun a ha b hb hab => by
    have ha' : monomialEval a (jexp β) ≠ 0 := ha.2
    have hb' : monomialEval b (jexp β) ≠ 0 := hb.2
    rw [monomialEval_jexp] at ha' hb'
    exact blowUpChart_injOn_compl_pivotHyperplane B β ha' hb' hab
  exists_unit := ⟨unit β, (continuous_unit β).continuousOn, fun y _ => (unit_pos β y).ne',
    fun y _ => by rw [K_φ, monomialEval_expo]; rfl⟩
  exists_jacUnit := ⟨fun _ => 1, continuousOn_const, fun _ _ => one_ne_zero,
    fun y _ => by rw [det_φ, monomialEval_jexp, one_mul]⟩

/-! ### The product package -/

/-- The tangential base `{x_β = 0, |x_{rev β}| ≤ 1}`. -/
def base (β : Fin 2) : Set (Fin 2 → ℝ) := square ∩ {x | x β = 0}

theorem isCompact_base (β : Fin 2) : IsCompact (base β) :=
  isCompact_square.inter_right (isClosed_eq (continuous_apply β) continuous_const)

theorem zero_mem_base (β : Fin 2) : (0 : Fin 2 → ℝ) ∈ base β := ⟨zero_mem_square, rfl⟩

theorem zeroOn_singleton_apply (β : Fin 2) (y : Fin 2 → ℝ) (j : Fin 2) :
    zeroOn ({β} : Finset (Fin 2)) y j = if j = β then 0 else y j := by
  unfold zeroOn
  simp only [Finset.mem_singleton]

/-- **The square is the product domain** over the tangential base with normal radius `1`. -/
theorem square_eq_productDom (β : Fin 2) :
    square = productDom (expo β).support (base β) 1 := by
  rw [expo_support]
  ext y
  simp only [productDom, Set.mem_ofPred_eq, base, mem_inter_iff, Finset.mem_singleton,
    forall_eq, mem_square, zeroOn_singleton_apply, if_true]
  constructor
  · intro hy
    refine ⟨⟨fun j => ?_, trivial⟩, hy β⟩
    split_ifs with hj
    · simp
    · exact hy j
  · rintro ⟨⟨h1, -⟩, h2⟩ j
    rcases eq_or_eq_rev β j with rfl | rfl
    · exact h2
    · have := h1 (Fin.rev β)
      rwa [if_neg (rev_ne β)] at this

/-- **The one-chart variable-unit product package of the blow-up chart.** -/
noncomputable def pkg (β : Fin 2) :
    ProductMonomialChartVar (ResolutionCover.ofChart (chart β)) () K where
  e := expo β
  h := jexp β
  W := univ
  W_open := isOpen_univ
  dom_subset := subset_univ _
  monomial := isMonomialChart β
  u := unit β
  u_cont := (continuous_unit β).continuousOn
  u_ne := fun y _ => (unit_pos β y).ne'
  phase_eq := fun y _ => by
    change K (φ β y) = unit β y * monomialEval y (expo β)
    rw [K_φ, monomialEval_expo]
    rfl
  v := fun _ => 1
  v_cont := continuousOn_const
  det_eq := fun y _ => by
    change (fderiv ℝ (φ β) y).det = 1 * monomialEval y (jexp β)
    rw [det_φ, monomialEval_jexp, one_mul]
  T := base β
  T_compact := isCompact_base β
  T_nonempty := ⟨0, zero_mem_base β⟩
  T_zero := fun x hx j hj => by
    rw [expo_support, Finset.mem_singleton] at hj
    rw [hj]
    exact hx.2
  b := 1
  b_pos := one_pos
  dom_eq := square_eq_productDom β
  r := fun _ => 1
  r_meas := measurable_const
  Cr := 1
  r_bound := fun _ => by simp
  weight_eq := fun y hy => ResolutionCover.ofChart_weight_Φ _ hy

theorem pkg_e (β : Fin 2) : (pkg β).e = expo β := rfl

theorem pkg_h (β : Fin 2) : (pkg β).h = jexp β := rfl

theorem pkg_W (β : Fin 2) : (pkg β).W = univ := rfl

theorem pkg_b (β : Fin 2) : (pkg β).b = 1 := rfl

theorem pkg_isActive (β : Fin 2) : (pkg β).IsActive := by
  unfold ProductMonomialChartVar.IsActive
  rw [pkg_e, expo_support]
  exact Finset.singleton_nonempty β

/-! ### The images: wedges covering the square, meeting on the null diagonals -/

/-- The wedge `{|x_{rev β}| ≤ |x_β| ≤ 1}`. -/
def wedge (β : Fin 2) : Set (Fin 2 → ℝ) := {x | |x β| ≤ 1 ∧ |x (Fin.rev β)| ≤ |x β|}

/-- A point of the plane from its `β` and `rev β` coordinates. -/
noncomputable def mk (β : Fin 2) (a c : ℝ) : Fin 2 → ℝ := fun j => if j = β then a else c

theorem mk_self (β : Fin 2) (a c : ℝ) : mk β a c β = a := by simp [mk]

theorem mk_rev (β : Fin 2) (a c : ℝ) : mk β a c (Fin.rev β) = c := by simp [mk, rev_ne β]

theorem funext_two (β : Fin 2) {x y : Fin 2 → ℝ} (h1 : x β = y β)
    (h2 : x (Fin.rev β) = y (Fin.rev β)) : x = y := by
  funext j
  rcases eq_or_eq_rev β j with rfl | rfl
  · exact h1
  · exact h2

theorem image_eq (β : Fin 2) : φ β '' square = wedge β := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [mem_square] at hy
    refine ⟨?_, ?_⟩
    · rw [φ_self]
      exact hy β
    · rw [φ_self, φ_rev, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (hy _)
  · rintro ⟨h1, h2⟩
    by_cases h0 : x β = 0
    · have hrev : x (Fin.rev β) = 0 := by
        rw [h0, abs_zero] at h2
        exact abs_nonpos_iff.1 h2
      refine ⟨0, zero_mem_square, funext_two β ?_ ?_⟩
      · rw [φ_self, h0]
        rfl
      · rw [φ_rev, hrev]
        simp
    · refine ⟨mk β (x β) (x (Fin.rev β) / x β), mem_square.2 fun j => ?_, funext_two β ?_ ?_⟩
      · rcases eq_or_eq_rev β j with rfl | rfl
        · rw [mk_self]
          exact h1
        · rw [mk_rev, abs_div, div_le_one (abs_pos.2 h0)]
          exact h2
      · rw [φ_self, mk_self]
      · rw [φ_rev, mk_self, mk_rev, mul_div_cancel₀ _ h0]

theorem wedge_subset_square (β : Fin 2) : wedge β ⊆ square := fun x ⟨h1, h2⟩ =>
  mem_square.2 fun j => by
    rcases eq_or_eq_rev β j with rfl | rfl
    · exact h1
    · exact h2.trans h1

/-- The union of the two wedges is the square. -/
theorem iUnion_wedge : ⋃ β, wedge β = square := by
  refine subset_antisymm (iUnion_subset wedge_subset_square) fun x hx => ?_
  rw [mem_square] at hx
  rcases le_total |x 1| |x 0| with h | h
  · exact mem_iUnion.2 ⟨0, hx 0, by simpa using h⟩
  · exact mem_iUnion.2 ⟨1, hx 1, by simpa using h⟩

/-- The diagonal `{x_0 = c · x_1}` is a proper subspace. -/
noncomputable def diagonal (c : ℝ) : Submodule ℝ (Fin 2 → ℝ) :=
  LinearMap.ker (LinearMap.proj 0 - c • LinearMap.proj 1 : (Fin 2 → ℝ) →ₗ[ℝ] ℝ)

theorem mem_diagonal {c : ℝ} {x : Fin 2 → ℝ} : x ∈ diagonal c ↔ x 0 = c * x 1 := by
  simp only [diagonal, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.proj_apply, smul_eq_mul, sub_eq_zero]

theorem diagonal_ne_top (c : ℝ) : diagonal c ≠ ⊤ := by
  intro h
  have : (fun j : Fin 2 => if j = 0 then (1 : ℝ) else 0) ∈ diagonal c := h ▸ Submodule.mem_top
  rw [mem_diagonal] at this
  simp at this

theorem volume_diagonal (c : ℝ) : volume {x : Fin 2 → ℝ | x 0 = c * x 1} = 0 := by
  have h := Measure.addHaar_submodule (volume : Measure (Fin 2 → ℝ)) (diagonal c)
    (diagonal_ne_top c)
  refine measure_mono_null (fun x hx => ?_) h
  exact mem_diagonal.2 hx

/-- The two wedges meet only on the diagonals, a null set. -/
theorem volume_wedge_inter : volume (wedge 0 ∩ wedge 1) = 0 := by
  refine measure_mono_null (fun x ⟨⟨_, h0⟩, ⟨_, h1⟩⟩ => ?_)
    (measure_union_null (volume_diagonal 1) (volume_diagonal (-1)))
  rw [rev_zero'] at h0
  rw [rev_one] at h1
  have habs : |x 0| = |x 1| := le_antisymm h1 h0
  rcases abs_eq_abs.1 habs with h | h
  · exact Or.inl (by simpa using h)
  · exact Or.inr (by simpa using h)


/-! ### The one-chart data: pair `(1, 0)`, minimal set `{β}` -/

/-- The one-chart family of the blow-up chart `β`. -/
noncomputable def Qs (β : Fin 2) :
    ∀ i : Unit, ProductMonomialChartVar (ResolutionCover.ofChart (chart β)) i K :=
  fun _ => pkg β

theorem ratio_eq (β : Fin 2) : (pkg β).ratio β = 1 := by
  change ((((jexp β) β : ℕ) : ℝ) + 1) / (((expo β) β : ℕ) : ℝ) = 1
  rw [jexp_apply_self, expo_apply_self]
  norm_num

theorem mem_support (β : Fin 2) : β ∈ (Qs β ()).e.support := by
  change β ∈ (pkg β).e.support
  rw [pkg_e, expo_support]
  exact Finset.mem_singleton_self β

theorem eq_of_mem_support (β : Fin 2) {j : Fin 2} (hj : j ∈ (pkg β).e.support) : j = β := by
  rw [pkg_e, expo_support, Finset.mem_singleton] at hj
  exact hj

theorem hact (β : Fin 2) : ((ResolutionCover.ofChart (chart β)).activeCoordsV (Qs β)).Nonempty :=
  ⟨⟨(), β⟩, (ResolutionCover.ofChart (chart β)).mem_activeCoordsV (Qs β) (mem_support β)⟩

theorem coverLamV_eq (β : Fin 2) :
    (ResolutionCover.ofChart (chart β)).coverLamV (Qs β) (hact β) = 1 := by
  unfold ResolutionCover.coverLamV
  refine le_antisymm ((Finset.inf'_le _
    ((ResolutionCover.ofChart (chart β)).mem_activeCoordsV (Qs β) (mem_support β))).trans_eq
      (ratio_eq β)) (Finset.le_inf' _ _ fun x hx => ?_)
  obtain ⟨i, j⟩ := x
  have hj : j = β := eq_of_mem_support β (Finset.mem_sigma.1 hx).2
  subst hj
  exact (ratio_eq j).ge

theorem filter_ratio_eq (β : Fin 2) :
    ((pkg β).e.support.filter fun j => (pkg β).ratio j = 1) = {β} := by
  rw [pkg_e, expo_support]
  exact Finset.filter_true_of_mem fun j hj => by
    rw [Finset.mem_singleton] at hj
    rw [hj]
    exact ratio_eq β

theorem coverDegV_eq (β : Fin 2) :
    (ResolutionCover.ofChart (chart β)).coverDegV (Qs β) (hact β) = 0 := by
  unfold ResolutionCover.coverDegV
  rw [coverLamV_eq]
  have hfilt : (Finset.univ.filter fun i : Unit => ∃ j ∈ (Qs β i).e.support,
      (Qs β i).ratio j = 1) = Finset.univ :=
    Finset.filter_true_of_mem fun i _ => ⟨β, mem_support β, ratio_eq β⟩
  rw [hfilt, Finset.univ_unique, Finset.sup_singleton]
  change ((pkg β).e.support.filter fun j => (pkg β).ratio j = 1).card - 1 = 0
  rw [filter_ratio_eq, Finset.card_singleton]

theorem minimalSet_eq (β : Fin 2) :
    (Qs β ()).minimalSet ((ResolutionCover.ofChart (chart β)).coverLamV (Qs β) (hact β)) =
      {β} := by
  unfold ProductMonomialChartVar.minimalSet
  rw [coverLamV_eq]
  exact filter_ratio_eq β

theorem singleton_subset_support (β : Fin 2) : ({β} : Finset (Fin 2)) ⊆ (Qs β ()).e.support := by
  change ({β} : Finset (Fin 2)) ⊆ (pkg β).e.support
  rw [pkg_e, expo_support]

/-! ### The face: tangential monomials, the foot set and the base -/

theorem tangentialMonomial_h (β : Fin 2) (z : Fin (2 - (({β} : Finset (Fin 2)).card - 1 + 1)) → ℝ) :
    tangentialMonomial ({β} : Finset (Fin 2)) (Finset.singleton_nonempty β) (Qs β ()).h z = 1 := by
  unfold tangentialMonomial
  change ∏ j ∈ (pkg β).h.support.filter (fun j => j ∉ ({β} : Finset (Fin 2))), _ = 1
  rw [pkg_h, jexp_support, Finset.filter_eq_empty_iff.2 fun j hj hj' => hj' hj, Finset.prod_empty]

theorem tangentialMonomial_e (β : Fin 2) (z : Fin (2 - (({β} : Finset (Fin 2)).card - 1 + 1)) → ℝ) :
    tangentialMonomial ({β} : Finset (Fin 2)) (Finset.singleton_nonempty β) (Qs β ()).e z = 1 := by
  unfold tangentialMonomial
  change ∏ j ∈ (pkg β).e.support.filter (fun j => j ∉ ({β} : Finset (Fin 2))), _ = 1
  rw [pkg_e, expo_support, Finset.filter_eq_empty_iff.2 fun j hj hj' => hj' hj, Finset.prod_empty]

/-- The foot of a tangential point `z`: coordinate `β` is `0`, coordinate `rev β` is `z`. -/
theorem foot_self (β : Fin 2) (z : Fin (2 - (({β} : Finset (Fin 2)).card - 1 + 1)) → ℝ) :
    planeSplit (stratumSplit ({β} : Finset (Fin 2)) (Finset.singleton_nonempty β)) (z, 0) β = 0 :=
  planeSplit_self β z 0 default

theorem foot_rev (β : Fin 2) (z : Fin (2 - (({β} : Finset (Fin 2)).card - 1 + 1)) → ℝ) :
    planeSplit (stratumSplit ({β} : Finset (Fin 2)) (Finset.singleton_nonempty β)) (z, 0)
      (Fin.rev β) = z default :=
  planeSplit_rev β z 0 default

/-- The tangential interval `{|z| ≤ 1}`. -/
def tangInterval (β : Fin 2) : Set (Fin (2 - (({β} : Finset (Fin 2)).card - 1 + 1)) → ℝ) :=
  {z | |z default| ≤ 1}

theorem foot_mem_square (β : Fin 2) {z : Fin (2 - (({β} : Finset (Fin 2)).card - 1 + 1)) → ℝ}
    (hz : z ∈ tangInterval β) :
    planeSplit (stratumSplit ({β} : Finset (Fin 2)) (Finset.singleton_nonempty β)) (z, 0) ∈
      square := by
  rw [mem_square]
  intro j
  rcases eq_or_eq_rev β j with rfl | rfl
  · rw [foot_self, abs_zero]
    exact zero_le_one
  · rw [foot_rev]
    exact hz

theorem foot_mem_pieceFootSet (β : Fin 2)
    {z : Fin (2 - (({β} : Finset (Fin 2)).card - 1 + 1)) → ℝ} (hz : z ∈ tangInterval β) :
    planeSplit (stratumSplit ({β} : Finset (Fin 2)) (Finset.singleton_nonempty β)) (z, 0) ∈
      (Qs β ()).pieceFootSet {β} := by
  change planeSplit (stratumSplit ({β} : Finset (Fin 2)) (Finset.singleton_nonempty β)) (z, 0) ∈
    footSet (pkg β).e.support (base β) 1 {β}
  rw [pkg_e, expo_support]
  refine ⟨⟨?_, ?_⟩, fun j hj => ?_, fun j hj hj' => absurd hj hj'⟩
  · rw [mem_square]
    intro j
    rw [zeroOn_singleton_apply]
    split_ifs with hj
    · simp
    · rcases eq_or_eq_rev β j with rfl | rfl
      · exact absurd rfl hj
      · rw [foot_rev]
        exact hz
  · show zeroOn ({β} : Finset (Fin 2)) _ β = 0
    rw [zeroOn_singleton_apply, if_pos rfl]
  · rw [Finset.mem_singleton] at hj
    rw [hj, foot_self]

theorem tangInterval_of_foot_mem_pieceFootSet (β : Fin 2)
    {z : Fin (2 - (({β} : Finset (Fin 2)).card - 1 + 1)) → ℝ}
    (hz : planeSplit (stratumSplit ({β} : Finset (Fin 2)) (Finset.singleton_nonempty β)) (z, 0) ∈
      (Qs β ()).pieceFootSet {β}) : z ∈ tangInterval β := by
  change planeSplit (stratumSplit ({β} : Finset (Fin 2)) (Finset.singleton_nonempty β)) (z, 0) ∈
    footSet (pkg β).e.support (base β) 1 {β} at hz
  rw [pkg_e, expo_support] at hz
  have h := (mem_square.1 hz.1.1) (Fin.rev β)
  rw [zeroOn_singleton_apply, if_neg (rev_ne β), foot_rev] at h
  exact h

/-! ### The analytic hypotheses for `F = 1`, `p = one 2` -/

theorem hK0 : ∀ x, 0 ≤ K x := K_nonneg

theorem hK : Measurable K := continuous_K.measurable

theorem hεb (β : Fin 2) : ∀ i, (1 : ℝ) ≤ (Qs β i).b := fun _ => le_rfl

theorem hFc (β : Fin 2) : ∀ i, ContinuousOn (fun y => (fun _ : Fin 2 → ℝ => (1 : ℝ))
    (((ResolutionCover.ofChart (chart β)).chart i).φ y)) (Qs β i).W :=
  fun _ => continuousOn_const

theorem hpc (β : Fin 2) : ∀ i, ContinuousOn (fun y => (TubeWeight.one 2).w
    (((ResolutionCover.ofChart (chart β)).chart i).φ y)) (Qs β i).W :=
  fun _ => continuousOn_const

theorem isClosed_wedge (β : Fin 2) : IsClosed (wedge β) :=
  (isClosed_le (continuous_apply β).abs continuous_const).inter
    (isClosed_le (continuous_apply _).abs (continuous_apply β).abs)

theorem isCompact_wedge (β : Fin 2) : IsCompact (wedge β) :=
  isCompact_square.of_isClosed_subset (isClosed_wedge β) (wedge_subset_square β)

theorem hF (β : Fin 2) :
    Integrable (fun x => (fun _ : Fin 2 → ℝ => (1 : ℝ)) x * (TubeWeight.one 2).w x)
      (volume.restrict (⋃ i, (ResolutionCover.ofChart (chart β)).image i)) := by
  rw [ResolutionCover.ofChart_iUnion_image, chart_dom, chart_φ, image_eq]
  exact (integrableOn_const (C := (1 : ℝ)) (isCompact_wedge β).measure_lt_top.ne).congr
    (Eventually.of_forall fun x => by simp)

/-! ### The base of the piece density and the face integral -/

theorem base_eq (β : Fin 2) :
    ((Qs β ()).pieceDensity (D := fun i => (Qs β i).e.support) one_pos (hεb β ()) rfl {β}
      (singleton_subset_support β) (Finset.singleton_nonempty β) (TubeWeight.one 2)).base =
      tangInterval β := by
  ext z
  constructor
  · intro hz
    exact tangInterval_of_foot_mem_pieceFootSet β
      ((Qs β ()).foot_mem_pieceFootSet_of_mem_base one_pos (hεb β ()) rfl {β}
        (singleton_subset_support β) (Finset.singleton_nonempty β) (TubeWeight.one 2) hz)
  · intro hz
    unfold ProductMonomialChartVar.pieceDensity
    rw [ResolutionCover.chartPieceDensity_base]
    refine ⟨⟨fun j hj hj' => ?_, mem_tangentialCarrier_of_mem _ (foot_mem_square β hz)⟩,
      foot_mem_pieceFootSet β hz⟩
    exact absurd (eq_of_mem_support β hj) (by rwa [Finset.mem_singleton] at hj')

/-- The face integrand is `(1 + z²)⁻¹`. -/
theorem face_integrand (β : Fin 2) {z : Fin (2 - (({β} : Finset (Fin 2)).card - 1 + 1)) → ℝ}
    (hz : z ∈ tangInterval β) :
    ((Qs β ()).pieceDensity (D := fun i => (Qs β i).e.support) one_pos (hεb β ()) rfl {β}
        (singleton_subset_support β) (Finset.singleton_nonempty β) (TubeWeight.one 2)).beta z *
      (scalarPhase ({β} : Finset (Fin 2)) (Finset.singleton_nonempty β) (Qs β ()).u (Qs β ()).e z ^
          (-((ResolutionCover.ofChart (chart β)).coverLamV (Qs β) (hact β))) *
        (ResolutionCover.ofChart (chart β)).pieceAmp () {β} (Finset.singleton_nonempty β)
          (Qs β ()).h (Qs β ()).v (F := fun _ => (1 : ℝ)) (p := TubeWeight.one 2) z 0) =
      (1 + z default ^ 2)⁻¹ := by
  rw [ProductMonomialChartVar.pieceDensity_beta, Set.indicator_of_mem (foot_mem_pieceFootSet β hz),
    coverLamV_eq]
  unfold scalarPhase tangentialUnit ResolutionCover.pieceAmp
  rw [tangentialMonomial_e, tangentialMonomial_h]
  change (1 : ℝ) * ((unit β (planeSplit (stratumSplit ({β} : Finset (Fin 2))
    (Finset.singleton_nonempty β)) (z, 0)) * 1) ^ (-(1 : ℝ)) *
    (|(1 : ℝ)| * |(1 : ℝ)| * 1 * 1)) = (1 + z default ^ 2)⁻¹
  unfold unit
  rw [foot_rev, Real.rpow_neg (by positivity), Real.rpow_one, abs_one]
  ring

/-- The tangential interval is the preimage of `[−1, 1]` under the coordinate equivalence. -/
theorem tangInterval_eq (β : Fin 2) :
    tangInterval β =
      MeasurableEquiv.funUnique (Fin (2 - (({β} : Finset (Fin 2)).card - 1 + 1))) ℝ ⁻¹'
        Icc (-1) 1 := by
  ext z
  simp only [tangInterval, Set.mem_ofPred_eq, mem_preimage, MeasurableEquiv.funUnique_apply,
    mem_Icc, abs_le]

theorem integral_arctan : ∫ t in Icc (-1 : ℝ) 1, (1 + t ^ 2)⁻¹ = Real.pi / 2 := by
  have h := integral_inv_one_add_sq (a := (-1 : ℝ)) (b := 1)
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num), h,
    Real.arctan_neg, Real.arctan_one]
  ring

/-- **The face integral** `∫_{−1}^{1} dt/(1+t²) = π/2`. -/
theorem integral_face (β : Fin 2) :
    ∫ z in ((Qs β ()).pieceDensity (D := fun i => (Qs β i).e.support) one_pos (hεb β ()) rfl {β}
        (singleton_subset_support β) (Finset.singleton_nonempty β) (TubeWeight.one 2)).base,
      ((Qs β ()).pieceDensity (D := fun i => (Qs β i).e.support) one_pos (hεb β ()) rfl {β}
        (singleton_subset_support β) (Finset.singleton_nonempty β) (TubeWeight.one 2)).beta z *
        (scalarPhase ({β} : Finset (Fin 2)) (Finset.singleton_nonempty β) (Qs β ()).u (Qs β ()).e
            z ^ (-((ResolutionCover.ofChart (chart β)).coverLamV (Qs β) (hact β))) *
          (ResolutionCover.ofChart (chart β)).pieceAmp () {β} (Finset.singleton_nonempty β)
            (Qs β ()).h (Qs β ()).v (F := fun _ => (1 : ℝ)) (p := TubeWeight.one 2) z 0) =
      Real.pi / 2 := by
  have hmeas : MeasurableSet (tangInterval β) := by
    rw [tangInterval_eq]
    exact (MeasurableEquiv.funUnique _ _).measurable measurableSet_Icc
  rw [base_eq, setIntegral_congr_fun hmeas fun z hz => face_integrand β hz, tangInterval_eq]
  have h := (volume_preserving_funUnique (Fin (2 - (({β} : Finset (Fin 2)).card - 1 + 1)))
    ℝ).setIntegral_preimage_emb (MeasurableEquiv.funUnique _ _).measurableEmbedding
    (fun t : ℝ => (1 + t ^ 2)⁻¹) (Icc (-1) 1)
  rw [← integral_arctan, ← h]
  rfl


/-! ### The per-chart coefficient `π/2` -/

theorem card_minimalSet_eq_succ (β : Fin 2) :
    ((Qs β ()).minimalSet ((ResolutionCover.ofChart (chart β)).coverLamV (Qs β) (hact β))).card =
      (ResolutionCover.ofChart (chart β)).coverDegV (Qs β) (hact β) + 1 := by
  rw [minimalSet_eq, Finset.card_singleton, coverDegV_eq]

theorem prod_minimalSet (β : Fin 2) :
    ∏ j ∈ (Qs β ()).minimalSet ((ResolutionCover.ofChart (chart β)).coverLamV (Qs β) (hact β)),
      1 / ((Qs β ()).e j : ℝ) = 1 / 2 := by
  rw [minimalSet_eq, Finset.prod_singleton]
  change 1 / (((expo β) β : ℕ) : ℝ) = 1 / 2
  rw [expo_apply_self]
  norm_num

/-- The face integral for any stratum equal to `{β}`. -/
theorem integral_face' (β : Fin 2) (I : Finset (Fin 2)) (hI : I = {β})
    (hIsub : I ⊆ (Qs β ()).e.support) (hne : I.Nonempty) :
    ∫ z in ((Qs β ()).pieceDensity (D := fun i => (Qs β i).e.support) one_pos (hεb β ()) rfl I
        hIsub hne (TubeWeight.one 2)).base,
      ((Qs β ()).pieceDensity (D := fun i => (Qs β i).e.support) one_pos (hεb β ()) rfl I hIsub
        hne (TubeWeight.one 2)).beta z *
        (scalarPhase I hne (Qs β ()).u (Qs β ()).e z ^
            (-((ResolutionCover.ofChart (chart β)).coverLamV (Qs β) (hact β))) *
          (ResolutionCover.ofChart (chart β)).pieceAmp () I hne (Qs β ()).h (Qs β ()).v
            (F := fun _ => (1 : ℝ)) (p := TubeWeight.one 2) z 0) = Real.pi / 2 := by
  subst hI
  exact integral_face β

/-- **The coefficient of one blow-up chart is `π/2`.** -/
theorem productCoeffV_eq (β : Fin 2) :
    (ResolutionCover.ofChart (chart β)).productCoeffV (Qs β) hK0 one_pos (hεb β) (hFc β) (hpc β)
      measurable_const (hF β) hK ((ResolutionCover.ofChart (chart β)).coverLamV (Qs β) (hact β))
      ((ResolutionCover.ofChart (chart β)).coverDegV (Qs β) (hact β)) = Real.pi / 2 := by
  have hsupp : ∀ i, ((Qs β i).minimalSet
      ((ResolutionCover.ofChart (chart β)).coverLamV (Qs β) (hact β))).card =
      (ResolutionCover.ofChart (chart β)).coverDegV (Qs β) (hact β) + 1 →
      (Qs β i).minimalSet ((ResolutionCover.ofChart (chart β)).coverLamV (Qs β) (hact β)) =
        (Qs β i).e.support := by
    intro i _
    cases i
    rw [minimalSet_eq]
    change ({β} : Finset (Fin 2)) = (pkg β).e.support
    rw [pkg_e, expo_support]
  have hsum : ∀ f : Unit → ℝ, ∑ i, f i = f () := fun f => Fintype.sum_unique f
  rw [(ResolutionCover.ofChart (chart β)).productCoeffV_extremal_eq_sum_minimal (Qs β) (hact β)
    hK0 one_pos (hεb β) (hFc β) (hpc β) measurable_const (hF β) hK hsupp, hsum,
    dif_pos (card_minimalSet_eq_succ β)]
  rw [integral_face' β _ (minimalSet_eq β), prod_minimalSet, minimalSet_eq, Finset.card_singleton,
    coverLamV_eq, Real.Gamma_one]
  norm_num [Nat.factorial]
  ring

/-! ### The two-chart assembly -/

/-- The cover of the two blow-up charts. -/
noncomputable def R : ResolutionCover 2 (Fin 2) := ⟨chart⟩

theorem R_chart (β : Fin 2) : R.chart β = chart β := rfl

/-- The packages. -/
noncomputable def Ps :
    ∀ β : Fin 2, ProductMonomialChartVar (ResolutionCover.ofChart (R.chart β)) () K :=
  pkg

theorem R_image (β : Fin 2) : R.image β = wedge β := image_eq β

theorem hdisj : R.AEDisjointImages := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · rw [R_image, R_image]
    exact volume_wedge_inter
  · rw [R_image, R_image, inter_comm]
    exact volume_wedge_inter
  · exact absurd rfl hij

theorem iUnion_image_eq : ⋃ β, R.image β = square := by
  rw [show (fun β => R.image β) = wedge from funext R_image]
  exact iUnion_wedge

theorem hFR : Integrable (fun x => (fun _ : Fin 2 → ℝ => (1 : ℝ)) x * (TubeWeight.one 2).w x)
    (volume.restrict (⋃ i, R.image i)) := by
  rw [iUnion_image_eq]
  exact (integrableOn_const (C := (1 : ℝ)) isCompact_square.measure_lt_top.ne).congr
    (Eventually.of_forall fun x => by simp)

theorem hεbR : ∀ i, (1 : ℝ) ≤ (Ps i).b := fun _ => le_rfl

theorem hpcR : ∀ i, ContinuousOn (fun y => (TubeWeight.one 2).w ((R.chart i).φ y)) (Ps i).W :=
  fun _ => continuousOn_const

theorem hFcR : ∀ i, ContinuousOn (fun y => (fun _ : Fin 2 → ℝ => (1 : ℝ)) ((R.chart i).φ y))
    (Ps i).W :=
  fun _ => continuousOn_const

theorem Ps_isActive (β : Fin 2) : (Ps β).IsActive := pkg_isActive β

theorem activeCharts_eq : R.activeCharts Ps = Finset.univ := by
  classical
  exact Finset.filter_true_of_mem fun i _ => Ps_isActive i

theorem hne : (R.activeCharts Ps).Nonempty := ⟨0, (R.mem_activeCharts Ps).2 (Ps_isActive 0)⟩

theorem chartLam'_eq (β : Fin 2) : R.chartLam' Ps β = 1 := by
  rw [R.chartLam'_of_active Ps (Ps_isActive β)]
  exact coverLamV_eq β

theorem chartDeg'_eq (β : Fin 2) : R.chartDeg' Ps β = 0 := by
  rw [R.chartDeg'_of_active Ps (Ps_isActive β)]
  exact coverDegV_eq β

theorem partitionLam'_eq : R.partitionLam' Ps hne = 1 := by
  unfold ResolutionCover.partitionLam' extremalExponent
  refine le_antisymm ((Finset.inf'_le _ ((R.mem_activeCharts Ps).2 (Ps_isActive 0))).trans_eq
    (chartLam'_eq 0)) (Finset.le_inf' _ _ fun i _ => (chartLam'_eq i).ge)

theorem partitionDeg'_eq : R.partitionDeg' Ps hne = 0 := by
  unfold ResolutionCover.partitionDeg' extremalDegree
  exact le_antisymm (Finset.sup'_le _ _ fun i _ => (chartDeg'_eq i).le) (Nat.zero_le _)

theorem tiedCharts'_eq : R.tiedCharts' Ps hne = Finset.univ := by
  classical
  unfold ResolutionCover.tiedCharts'
  rw [activeCharts_eq]
  exact Finset.filter_true_of_mem fun i _ =>
    ⟨(chartLam'_eq i).trans partitionLam'_eq.symm, (chartDeg'_eq i).trans partitionDeg'_eq.symm⟩

theorem hlam (β : Fin 2) : ∀ I, I ⊆ (Ps β).e.support → ∀ hne : I.Nonempty,
    R.chartLam' Ps β ≤ (Ps β).pieceLam I hne := fun I hI hne => by
  rw [chartLam'_eq, ← coverLamV_eq β]
  exact (ResolutionCover.ofChart (chart β)).coverLamV_le_pieceLam (Qs β) (hact β) () I hI hne

theorem hk (β : Fin 2) : ∀ I, I ⊆ (Ps β).e.support → ∀ hne : I.Nonempty,
    (Ps β).pieceLam I hne = R.chartLam' Ps β → (Ps β).pieceMult I hne - 1 ≤ R.chartDeg' Ps β :=
  fun I hI hne hl => by
  rw [chartLam'_eq, ← coverLamV_eq β] at hl
  rw [chartDeg'_eq, ← coverDegV_eq β]
  exact (ResolutionCover.ofChart (chart β)).pieceMult_le_coverDegV (Qs β) (hact β) () I hI hne hl

/-- **Each blow-up chart contributes `π/2`.** -/
theorem sourceChartCoeff'_eq (β : Fin 2) :
    R.sourceChartCoeff' Ps (fun i y => (fun _ : Fin 2 → ℝ => (1 : ℝ)) ((R.chart i).Φ y)) hK0
      one_pos hεbR hpcR (fun i => measurable_const.comp (R.chart i).measurable_Φ)
      (fun i => ResolutionCover.continuousOn_pullback_Φ (R.chart i) (F := fun _ => (1 : ℝ))
        (hFcR i) (Ps i).dom_subset) hK β = Real.pi / 2 := by
  unfold ResolutionCover.sourceChartCoeff'
  rw [dif_pos (Ps_isActive β), (Ps β).sourceCoeff_pullback hK0 one_pos (hεbR β) (hpcR β) hK (hFcR β)
    measurable_const (hF β) (R.chartLam' Ps β) (R.chartDeg' Ps β) (hlam β) (hk β)]
  have h := productCoeffV_eq β
  rw [coverLamV_eq, coverDegV_eq] at h
  rw [chartLam'_eq, chartDeg'_eq]
  exact h

/-- **The two tied charts sum to `π`.** -/
theorem aeDisjointCoeff_eq :
    R.aeDisjointCoeff Ps hK0 one_pos hεbR hpcR hFcR measurable_const hK hne = Real.pi := by
  unfold ResolutionCover.aeDisjointCoeff ResolutionCover.sourceDecompCoeff
  rw [tiedCharts'_eq, Fin.sum_univ_two, sourceChartCoeff'_eq, sourceChartCoeff'_eq]
  ring

/-- The tangential interval has positive volume. -/
theorem volume_tangInterval_pos (β : Fin 2) : 0 < volume (tangInterval β) := by
  refine lt_of_lt_of_le (Metric.isOpen_ball.measure_pos volume ⟨0, Metric.mem_ball_self one_pos⟩)
    (measure_mono fun z hz => ?_)
  rw [Metric.mem_ball, dist_zero_right] at hz
  exact ((norm_le_pi_norm z default).trans hz.le)

/-- The source dominant face of the stratum `{0}` of the first chart contains the tangential
interval, hence has positive measure. -/
theorem volume_sourceDominantFace_pos :
    0 < volume ((Ps 0).sourceDominantFace (fun _ => (Ps 0).e.support) 1 {0}
      (Finset.singleton_nonempty 0)
      (fun y => (fun _ : Fin 2 → ℝ => (1 : ℝ)) ((R.chart 0).Φ y)) (TubeWeight.one 2)) := by
  refine lt_of_lt_of_le (volume_tangInterval_pos 0) (measure_mono fun z hz => ?_)
  refine ⟨fun j hj hj' => absurd (eq_of_mem_support 0 hj) (by rwa [Finset.mem_singleton] at hj'),
    foot_mem_square 0 hz, zero_lt_one, zero_lt_one, zero_lt_one, one_ne_zero, ?_⟩
  change tangentialMonomial ({0} : Finset (Fin 2)) _ (Qs 0 ()).h z ≠ 0
  rw [tangentialMonomial_h]
  exact one_ne_zero

/-- ★ **The blow-up square regression**: `∫_{[−1,1]²} e^{−N(a²+b²)} da db ~ π · N^{−1}`, obtained
through the a.e.-disjoint assembly of the two blow-up charts with the explicit tied coefficients
`π/2 + π/2`. -/
theorem integral_isEquivalent :
    (fun N : ℝ => ∫ x in square, Real.exp (-N * K x)) ~[atTop]
      fun N => Real.pi * N ^ (-(1 : ℝ)) := by
  have h₁ : volume (square \ ⋃ i, R.image i) = 0 := by
    simp only [iUnion_image_eq, sdiff_self, measure_empty]
  have h₂ : volume ((⋃ i, R.image i) \ square) = 0 := by
    simp only [iUnion_image_eq, sdiff_self, measure_empty]
  have h := (R.targetIntegral_isEquivalent_of_aeDisjoint Ps hK0 one_pos hεbR hpcR hFcR
    measurable_const hK hne hdisj h₁ h₂ hFR (fun _ => zero_le_one) (fun _ => zero_le_one)
    (fun _ _ => zero_le_one) 0 (Ps_isActive 0)
    ⟨(chartLam'_eq 0).trans partitionLam'_eq.symm, (chartDeg'_eq 0).trans partitionDeg'_eq.symm⟩
    {0} (singleton_subset_support 0) (Finset.singleton_nonempty 0)
    (fun j hj => by
      rw [Finset.mem_singleton] at hj
      rw [hj, chartLam'_eq]
      exact ratio_eq 0)
    (by rw [Finset.card_singleton, chartDeg'_eq]) volume_sourceDominantFace_pos).2
  rw [aeDisjointCoeff_eq, partitionLam'_eq, partitionDeg'_eq] at h
  have hZ : targetIntegral square (fun _ => (1 : ℝ)) K (TubeWeight.one 2) =
      fun N : ℝ => ∫ x in square, Real.exp (-N * K x) := by
    funext N
    unfold targetIntegral
    refine setIntegral_congr_fun isCompact_square.isClosed.measurableSet fun x _ => ?_
    simp
  rw [hZ] at h
  refine h.congr_right (Eventually.of_forall fun N => ?_)
  simp [powLogScale]

end BlowUpWedge

end Grammar
