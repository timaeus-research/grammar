/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.VariableNoActiveAssembly

/-!
# The local product box of a monomial chart at a divisor point (CCLXX)

Two constructions on a monomial chart `(φ, dom, e, h, W)` (hironaka's `IsMonomialChart`):

* **Phase-support restriction** (`IsMonomialChart.restrictPhase`): for a set `J` of coordinates,
  on the open set `restrictNhd e J W = W ∩ {y | y_j ≠ 0 for j ∈ supp e ∖ J}` the active factors off
  `J` are units, so `K ∘ φ = (u · ∏_{j∉J} y_j^{e_j}) · y^{e|_J}` is a monomial chart with phase
  exponents `restrictExp e J = e|_J` and the SAME Jacobian data `h, v` (Astra #84: a coordinate
  with `e_j = 0`, `h_j > 0`, `(y₀)_j = 0` cannot be absorbed into a unit, so `h` is kept). The
  Jacobian-support restriction `restrictJac` is the analogous separate lemma.
* **The product box at a point** (`IsMonomialChart.boxChart`, `boxPackage`): at `y₀ ∈ W` with
  divisor set `J₀ = {j ∈ supp e : (y₀)_j = 0}` and a closed ball `closedBall y₀ ρ ⊆ restrictNhd e J₀
  W`, the centred product domain `productBox = productDom J₀ (boxBase e y₀ ρ) ρ` (tangential
  rectangle `boxBase = ∏_j ({0} if j ∈ J₀ else [y₀_j − ρ, y₀_j + ρ])`, normal radius `ρ`) lies in
  the closed ball; the same chart map on this box, with exceptional set
  `productBox ∩ {monomialEval · h = 0}` (closed, null: contained in the coordinate hyperplanes),
  is a `ResolutionChart`, and the restricted phase data make it a one-chart **variable-unit product
  package** `ProductMonomialChartVar (ofChart boxChart) () K` with `r = 1`. At a divisor point
  (`monomialEval y₀ e = 0`) the package is active (`boxPackage_isActive`). This is the constructor
  feeding CCLX/CCLXVII with a chart of a resolution; the box lies in the monomial neighbourhood
  `W`, not necessarily in the original compact domain.
-/

open MeasureTheory Set Filter Topology Monomialize.Analytic Monomialize.VolumeScaling

namespace Grammar

/-! ### Restricting the exponent support -/

section Restrict

variable {d : ℕ}

/-- The exponents restricted to `J`. -/
noncomputable def restrictExp (e : Fin d →₀ ℕ) (J : Finset (Fin d)) : Fin d →₀ ℕ :=
  e.filter (· ∈ J)

/-- The exponents off `J`. -/
noncomputable def removedExp (e : Fin d →₀ ℕ) (J : Finset (Fin d)) : Fin d →₀ ℕ :=
  e.filter (· ∉ J)

theorem restrictExp_add_removedExp (e : Fin d →₀ ℕ) (J : Finset (Fin d)) :
    restrictExp e J + removedExp e J = e := by
  ext j
  simp only [restrictExp, removedExp, Finsupp.add_apply, Finsupp.filter_apply]
  split_ifs <;> simp

theorem support_restrictExp (e : Fin d →₀ ℕ) (J : Finset (Fin d)) :
    (restrictExp e J).support = e.support.filter (· ∈ J) := Finsupp.support_filter _ _

theorem support_restrictExp_subset (e : Fin d →₀ ℕ) (J : Finset (Fin d)) :
    (restrictExp e J).support ⊆ J := by
  rw [support_restrictExp]
  exact fun j hj => (Finset.mem_filter.1 hj).2

theorem support_restrictExp_of_subset (e : Fin d →₀ ℕ) {J : Finset (Fin d)} (hJ : J ⊆ e.support) :
    (restrictExp e J).support = J := by
  rw [support_restrictExp, Finset.filter_mem_eq_inter]
  exact Finset.inter_eq_right.2 hJ

/-- The monomial factors along a finitely supported exponent are continuous. -/
theorem continuous_monomialEval (ν : Fin d →₀ ℕ) :
    Continuous fun y : Fin d → ℝ => monomialEval y ν := by
  unfold monomialEval Finsupp.prod
  exact continuous_finsetProd _ fun k _ => (continuous_apply k).pow _

theorem monomialEval_restrict_mul (e : Fin d →₀ ℕ) (J : Finset (Fin d)) (y : Fin d → ℝ) :
    monomialEval y e = monomialEval y (restrictExp e J) * monomialEval y (removedExp e J) := by
  conv_lhs => rw [← restrictExp_add_removedExp e J]
  exact monomialEval_add y _ _

theorem monomialEval_removedExp_ne_zero (e : Fin d →₀ ℕ) (J : Finset (Fin d)) {y : Fin d → ℝ}
    (hy : ∀ j ∈ e.support, j ∉ J → y j ≠ 0) : monomialEval y (removedExp e J) ≠ 0 := by
  unfold monomialEval Finsupp.prod
  refine Finset.prod_ne_zero_iff.2 fun j hj => ?_
  rw [removedExp, Finsupp.support_filter, Finset.mem_filter] at hj
  exact pow_ne_zero _ (hy j hj.1 hj.2)

/-- A vanishing monomial has a vanishing coordinate in its support. -/
theorem exists_eq_zero_of_monomialEval_eq_zero {ν : Fin d →₀ ℕ} {y : Fin d → ℝ}
    (h0 : monomialEval y ν = 0) : ∃ j ∈ ν.support, y j = 0 := by
  unfold monomialEval Finsupp.prod at h0
  obtain ⟨j, hj, hpow⟩ := Finset.prod_eq_zero_iff.1 h0
  exact ⟨j, hj, (pow_eq_zero_iff (Finsupp.mem_support_iff.1 hj)).1 hpow⟩

/-- **The restricted monomial neighbourhood**: the active coordinates off `J` do not vanish. -/
def restrictNhd (e : Fin d →₀ ℕ) (J : Finset (Fin d)) (W : Set (Fin d → ℝ)) : Set (Fin d → ℝ) :=
  W ∩ ⋂ j ∈ e.support.filter (· ∉ J), {y : Fin d → ℝ | y j ≠ 0}

theorem mem_restrictNhd {e : Fin d →₀ ℕ} {J : Finset (Fin d)} {W : Set (Fin d → ℝ)}
    {y : Fin d → ℝ} :
    y ∈ restrictNhd e J W ↔ y ∈ W ∧ ∀ j ∈ e.support, j ∉ J → y j ≠ 0 := by
  unfold restrictNhd
  simp only [mem_inter_iff, mem_iInter, Finset.mem_filter, mem_ofPred_eq, and_imp]

theorem restrictNhd_subset (e : Fin d →₀ ℕ) (J : Finset (Fin d)) (W : Set (Fin d → ℝ)) :
    restrictNhd e J W ⊆ W := inter_subset_left

theorem isOpen_restrictNhd (e : Fin d →₀ ℕ) (J : Finset (Fin d)) {W : Set (Fin d → ℝ)}
    (hW : IsOpen W) : IsOpen (restrictNhd e J W) :=
  hW.inter (isOpen_biInter_finset fun j _ => isOpen_ne_fun (continuous_apply j) continuous_const)

variable {K : (Fin d → ℝ) → ℝ} {φ : (Fin d → ℝ) → (Fin d → ℝ)} {dom W : Set (Fin d → ℝ)}
  {e h : Fin d →₀ ℕ}

/-- **Phase-support restriction**: on the restricted neighbourhood the active factors off `J` are
absorbed into the phase unit; the Jacobian data are unchanged. -/
theorem IsMonomialChart.restrictPhase (hc : IsMonomialChart K φ dom e h W) (J : Finset (Fin d))
    {dom' : Set (Fin d → ℝ)} (hdom : dom' ⊆ restrictNhd e J W) :
    IsMonomialChart K φ dom' (restrictExp e J) h (restrictNhd e J W) where
  isOpen := isOpen_restrictNhd e J hc.isOpen
  subset := hdom
  analyticOnNhd := hc.analyticOnNhd.mono (restrictNhd_subset e J W)
  injOn := hc.injOn.mono fun y hy => And.intro (restrictNhd_subset e J W hy.1) hy.2
  exists_unit := by
    obtain ⟨u, hu, hu0, hKu⟩ := hc.exists_unit
    refine ⟨fun y => u y * monomialEval y (removedExp e J), ?_, ?_, ?_⟩
    · exact (hu.mono (restrictNhd_subset e J W)).mul (continuous_monomialEval _).continuousOn
    · intro y hy
      exact mul_ne_zero (hu0 y (mem_restrictNhd.1 hy).1)
        (monomialEval_removedExp_ne_zero e J (mem_restrictNhd.1 hy).2)
    · intro y hy
      rw [hKu y (mem_restrictNhd.1 hy).1, monomialEval_restrict_mul e J y]
      ring
  exists_jacUnit := by
    obtain ⟨v, hv, hv0, hdet⟩ := hc.exists_jacUnit
    exact ⟨v, hv.mono (restrictNhd_subset e J W), fun y hy => hv0 y (restrictNhd_subset e J W hy),
      fun y hy => hdet y (restrictNhd_subset e J W hy)⟩

/-- **Jacobian-support restriction**: on `restrictNhd h J W` the Jacobian factors off `J` are
absorbed into the Jacobian unit. -/
theorem IsMonomialChart.restrictJac (hc : IsMonomialChart K φ dom e h W) (J : Finset (Fin d))
    {dom' : Set (Fin d → ℝ)} (hdom : dom' ⊆ restrictNhd h J W) :
    IsMonomialChart K φ dom' e (restrictExp h J) (restrictNhd h J W) where
  isOpen := isOpen_restrictNhd h J hc.isOpen
  subset := hdom
  analyticOnNhd := hc.analyticOnNhd.mono (restrictNhd_subset h J W)
  injOn := hc.injOn.mono fun y hy => And.intro (restrictNhd_subset h J W hy.1) (by
    rw [monomialEval_restrict_mul h J y]
    exact mul_ne_zero hy.2 (monomialEval_removedExp_ne_zero h J (mem_restrictNhd.1 hy.1).2))
  exists_unit := by
    obtain ⟨u, hu, hu0, hKu⟩ := hc.exists_unit
    exact ⟨u, hu.mono (restrictNhd_subset h J W), fun y hy => hu0 y (restrictNhd_subset h J W hy),
      fun y hy => hKu y (restrictNhd_subset h J W hy)⟩
  exists_jacUnit := by
    obtain ⟨v, hv, hv0, hdet⟩ := hc.exists_jacUnit
    refine ⟨fun y => v y * monomialEval y (removedExp h J), ?_, ?_, ?_⟩
    · exact (hv.mono (restrictNhd_subset h J W)).mul (continuous_monomialEval _).continuousOn
    · intro y hy
      exact mul_ne_zero (hv0 y (mem_restrictNhd.1 hy).1)
        (monomialEval_removedExp_ne_zero h J (mem_restrictNhd.1 hy).2)
    · intro y hy
      rw [hdet y (mem_restrictNhd.1 hy).1, monomialEval_restrict_mul h J y]
      ring

/-! ### The divisor set of a point -/

/-- The active coordinates vanishing at `y₀`. -/
noncomputable def divisorSet (e : Fin d →₀ ℕ) (y₀ : Fin d → ℝ) : Finset (Fin d) :=
  e.support.filter fun j => y₀ j = 0

theorem divisorSet_subset (e : Fin d →₀ ℕ) (y₀ : Fin d → ℝ) : divisorSet e y₀ ⊆ e.support :=
  Finset.filter_subset _ _

theorem mem_divisorSet {e : Fin d →₀ ℕ} {y₀ : Fin d → ℝ} {j : Fin d} :
    j ∈ divisorSet e y₀ ↔ j ∈ e.support ∧ y₀ j = 0 := Finset.mem_filter

theorem support_restrictExp_divisor (e : Fin d →₀ ℕ) (y₀ : Fin d → ℝ) :
    (restrictExp e (divisorSet e y₀)).support = divisorSet e y₀ :=
  support_restrictExp_of_subset e (divisorSet_subset e y₀)

/-- A point of `W` lies in the neighbourhood restricted to its own divisor set. -/
theorem mem_restrictNhd_divisor (e : Fin d →₀ ℕ) {y₀ : Fin d → ℝ} {W : Set (Fin d → ℝ)}
    (hy₀ : y₀ ∈ W) : y₀ ∈ restrictNhd e (divisorSet e y₀) W :=
  mem_restrictNhd.2 ⟨hy₀, fun _ hj hjD h0 => hjD (mem_divisorSet.2 ⟨hj, h0⟩)⟩

/-- At a divisor point the divisor set is nonempty. -/
theorem divisorSet_nonempty_of_monomialEval_eq_zero {e : Fin d →₀ ℕ} {y₀ : Fin d → ℝ}
    (h0 : monomialEval y₀ e = 0) : (divisorSet e y₀).Nonempty := by
  obtain ⟨j, hj, hz⟩ := exists_eq_zero_of_monomialEval_eq_zero h0
  exact ⟨j, mem_divisorSet.2 ⟨hj, hz⟩⟩

end Restrict

/-! ### The product box at a point -/

section Box

variable {d : ℕ} {K : (Fin d → ℝ) → ℝ} {φ : (Fin d → ℝ) → (Fin d → ℝ)} {dom W : Set (Fin d → ℝ)}
  {e h : Fin d →₀ ℕ} (hc : IsMonomialChart K φ dom e h W) {y₀ : Fin d → ℝ} (hy₀ : y₀ ∈ W)
  {ρ : ℝ} (hρ : 0 < ρ) (hball : Metric.closedBall y₀ ρ ⊆ restrictNhd e (divisorSet e y₀) W)

/-- **The tangential rectangle** at `y₀`: `x_j = 0` on the divisor set, `|x_j − (y₀)_j| ≤ ρ`
elsewhere. -/
def boxBase (e : Fin d →₀ ℕ) (y₀ : Fin d → ℝ) (ρ : ℝ) : Set (Fin d → ℝ) :=
  Set.pi univ fun j => if j ∈ divisorSet e y₀ then ({0} : Set ℝ) else Icc (y₀ j - ρ) (y₀ j + ρ)

theorem isCompact_productBoxBase (e : Fin d →₀ ℕ) (y₀ : Fin d → ℝ) (ρ : ℝ) :
    IsCompact (boxBase e y₀ ρ) :=
  isCompact_univ_pi fun j => by
    split_ifs
    · exact isCompact_singleton
    · exact isCompact_Icc

theorem boxBase_zero {x : Fin d → ℝ} (hx : x ∈ boxBase e y₀ ρ) {j : Fin d}
    (hj : j ∈ divisorSet e y₀) : x j = 0 := by
  have := hx j (mem_univ j)
  simp only [if_pos hj, mem_singleton_iff] at this
  exact this

theorem boxBase_abs_le {x : Fin d → ℝ} (hx : x ∈ boxBase e y₀ ρ) {j : Fin d}
    (hj : j ∉ divisorSet e y₀) : |x j - y₀ j| ≤ ρ := by
  have := hx j (mem_univ j)
  simp only [if_neg hj, mem_Icc] at this
  rw [abs_le]
  constructor <;> linarith [this.1, this.2]

include hρ in
theorem y₀_mem_boxBase : y₀ ∈ boxBase e y₀ ρ := fun j _ => by
  by_cases hj : j ∈ divisorSet e y₀
  · simp only [if_pos hj, mem_singleton_iff]
    exact (mem_divisorSet.1 hj).2
  · simp only [if_neg hj, mem_Icc]
    constructor <;> linarith

/-- **The product box**: the centred product domain over the tangential rectangle with normal
radius `ρ`. -/
def productBox (e : Fin d →₀ ℕ) (y₀ : Fin d → ℝ) (ρ : ℝ) : Set (Fin d → ℝ) :=
  productDom (restrictExp e (divisorSet e y₀)).support (boxBase e y₀ ρ) ρ

include hρ in
theorem productBox_subset_closedBall : productBox e y₀ ρ ⊆ Metric.closedBall y₀ ρ := by
  intro y hy
  obtain ⟨hT, hb⟩ := hy
  rw [support_restrictExp_divisor] at hT hb
  rw [Metric.mem_closedBall, dist_pi_le_iff hρ.le]
  intro j
  rw [Real.dist_eq]
  by_cases hj : j ∈ divisorSet e y₀
  · rw [(mem_divisorSet.1 hj).2, sub_zero]
    exact hb j hj
  · have := boxBase_abs_le hT hj
    rwa [zeroOn_apply_of_notMem _ hj] at this

include hρ hball in
theorem productBox_subset_restrictNhd : productBox e y₀ ρ ⊆ restrictNhd e (divisorSet e y₀) W :=
  (productBox_subset_closedBall hρ).trans hball

include hρ in
theorem y₀_mem_productBox : y₀ ∈ productBox e y₀ ρ := by
  have h1 : zeroOn (restrictExp e (divisorSet e y₀)).support y₀ ∈ boxBase e y₀ ρ := by
    rw [support_restrictExp_divisor, zeroOn_of_forall_eq_zero _ fun j hj => (mem_divisorSet.1 hj).2]
    exact y₀_mem_boxBase hρ
  have h2 : ∀ j ∈ (restrictExp e (divisorSet e y₀)).support, |y₀ j| ≤ ρ := fun j hj => by
    rw [support_restrictExp_divisor] at hj
    rw [(mem_divisorSet.1 hj).2, abs_zero]
    exact hρ.le
  exact And.intro h1 h2

theorem isCompact_productBox (e : Fin d →₀ ℕ) (y₀ : Fin d → ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    IsCompact (productBox e y₀ ρ) :=
  isCompact_productDom _ _ _ (isCompact_productBoxBase e y₀ ρ) hρ.le

/-- The zero set of a monomial lies in the coordinate hyperplanes of its support and is null. -/
theorem volume_monomialEval_zero_set (ν : Fin d →₀ ℕ) :
    volume {y : Fin d → ℝ | monomialEval y ν = 0} = 0 := by
  have hnull : volume (⋃ j ∈ (ν.support : Set (Fin d)), {y : Fin d → ℝ | y j = 0}) = 0 :=
    (measure_biUnion_null_iff (Finset.countable_toSet ν.support)).2 fun j _ => by
      rw [volume_pi]
      exact Measure.pi_hyperplane _ j 0
  refine measure_mono_null (fun y (hy : monomialEval y ν = 0) => ?_) hnull
  obtain ⟨j, hj, hz⟩ := exists_eq_zero_of_monomialEval_eq_zero hy
  exact mem_biUnion (Finset.mem_coe.2 hj) hz

include hc hρ hball in
/-- **The product box as a resolution chart**: the chart map on the box, with exceptional set the
zero set of the Jacobian monomial. -/
noncomputable def IsMonomialChart.boxChart : ResolutionChart d where
  dom := productBox e y₀ ρ
  dom_compact := isCompact_productBox e y₀ hρ
  φ := φ
  U := restrictNhd e (divisorSet e y₀) W
  U_open := isOpen_restrictNhd _ _ hc.isOpen
  dom_subset := productBox_subset_restrictNhd hρ hball
  smooth := (hc.analyticOnNhd.mono (restrictNhd_subset _ _ _)).contDiffOn_of_completeSpace
  E := productBox e y₀ ρ ∩ {y | monomialEval y h = 0}
  E_subset := inter_subset_left
  E_closed := (isCompact_productBox e y₀ hρ).isClosed.inter
    (isClosed_eq (continuous_monomialEval h) continuous_const)
  E_null := measure_mono_null inter_subset_right (volume_monomialEval_zero_set h)
  inj := hc.injOn.mono fun _ hy =>
    And.intro (restrictNhd_subset _ _ _ (productBox_subset_restrictNhd hρ hball hy.1))
      fun h0 => hy.2 (And.intro hy.1 h0)

include hc hρ hball in
/-- **The one-chart variable-unit product package of the box.** -/
noncomputable def IsMonomialChart.boxPackage :
    ProductMonomialChartVar (ResolutionCover.ofChart (IsMonomialChart.boxChart hc hρ hball)) ()
      K where
  e := restrictExp e (divisorSet e y₀)
  h := h
  W := restrictNhd e (divisorSet e y₀) W
  W_open := isOpen_restrictNhd _ _ hc.isOpen
  dom_subset := productBox_subset_restrictNhd hρ hball
  monomial := IsMonomialChart.restrictPhase hc (divisorSet e y₀)
    (productBox_subset_restrictNhd hρ hball)
  u := fun y => hc.exists_unit.choose y * monomialEval y (removedExp e (divisorSet e y₀))
  u_cont := (hc.exists_unit.choose_spec.1.mono (restrictNhd_subset _ _ _)).mul
    (continuous_monomialEval _).continuousOn
  u_ne := fun y hy => mul_ne_zero (hc.exists_unit.choose_spec.2.1 y (mem_restrictNhd.1 hy).1)
    (monomialEval_removedExp_ne_zero e _ (mem_restrictNhd.1 hy).2)
  phase_eq := fun y hy => by
    change K (φ y) = _
    rw [hc.exists_unit.choose_spec.2.2 y (mem_restrictNhd.1 hy).1,
      monomialEval_restrict_mul e (divisorSet e y₀) y]
    ring
  v := hc.exists_jacUnit.choose
  v_cont := hc.exists_jacUnit.choose_spec.1.mono (restrictNhd_subset _ _ _)
  det_eq := fun y hy => hc.exists_jacUnit.choose_spec.2.2 y (restrictNhd_subset _ _ _ hy)
  T := boxBase e y₀ ρ
  T_compact := isCompact_productBoxBase e y₀ ρ
  T_nonempty := ⟨y₀, y₀_mem_boxBase hρ⟩
  T_zero := fun x hx j hj => boxBase_zero hx (support_restrictExp_subset e _ hj)
  b := ρ
  b_pos := hρ
  dom_eq := rfl
  r := fun _ => 1
  r_meas := measurable_const
  Cr := 1
  r_bound := fun _ => by simp
  weight_eq := fun y hy => ResolutionCover.ofChart_weight_Φ _ hy

include hc hρ hball in
theorem IsMonomialChart.boxPackage_e :
    (IsMonomialChart.boxPackage hc hρ hball).e = restrictExp e (divisorSet e y₀) := rfl

include hc hρ hball in
theorem IsMonomialChart.boxPackage_e_support :
    (IsMonomialChart.boxPackage hc hρ hball).e.support = divisorSet e y₀ :=
  support_restrictExp_divisor e y₀

include hc hρ hball in
/-- At a divisor point the box package is active. -/
theorem IsMonomialChart.boxPackage_isActive (h0 : monomialEval y₀ e = 0) :
    (IsMonomialChart.boxPackage hc hρ hball).IsActive := by
  unfold ProductMonomialChartVar.IsActive
  rw [IsMonomialChart.boxPackage_e_support hc hρ hball]
  exact divisorSet_nonempty_of_monomialEval_eq_zero h0

/-- A closed ball around a point of an open set lies in it: the radius for the box. -/
theorem exists_closedBall_subset_restrictNhd {W : Set (Fin d → ℝ)} (hW : IsOpen W) (e : Fin d →₀ ℕ)
    {y₀ : Fin d → ℝ} (hy₀ : y₀ ∈ W) :
    ∃ ρ : ℝ, 0 < ρ ∧ Metric.closedBall y₀ ρ ⊆ restrictNhd e (divisorSet e y₀) W := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (isOpen_restrictNhd e (divisorSet e y₀) hW) y₀
    (mem_restrictNhd_divisor e hy₀)
  exact ⟨ε / 2, half_pos hε, (Metric.closedBall_subset_ball (half_lt_self hε)).trans hball⟩

end Box

end Grammar
