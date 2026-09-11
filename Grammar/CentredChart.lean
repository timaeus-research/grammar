/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SplitReflection
import Grammar.AnalyticJacobian

/-!
# The centred normal form of a hironaka chart at a divisor point (towards the chart theorem)

At a point `y₀` of a hironaka monomial chart `φ` where the phase vanishes, the chart is put into
the **centred split normal form** used by the strip and box machinery: after translating `y₀` to
the origin and splitting the coordinates into the normal ones
`S = {j | y₀_j = 0 ∧ e_j > 0}` (indexed by `Fin (n+1)` through a splitting `σ`) and the tangential
ones, the phase reads `K(φ(y + y₀)) = unit₀(y) · ∏_j y_{n_j}^{2k_j}` with `unit₀` analytic and
positive, and the Jacobian reads `|det Dφ(y + y₀)| = jac₀(y) · ∏_j |y_{n_j}|^{h_j}` with `jac₀`
analytic and positive (`CentredChartData`, `exists_centredChartData`). The exponents come from the
parity theorem (`even_positive_form_halfExp`, the reduced form with `k = e/2` made explicit) and the
Jacobian exponents at the coordinates vanishing at `y₀` are supported on `S` because `supp h ⊆
supp e` (hypothesis `hhe`). Off the divisor of the box the Jacobian monomial `y^h` does not vanish,
so the chart is injective there (`monomialEval_ne_zero`).

Non-claims: no strip normalisation or expansion yet; `y₀` is a point with `K(φ y₀) = 0`.
-/

open Set Filter Topology Monomialize.Analytic Monomialize.VolumeScaling

namespace Grammar

variable {d : ℕ}

/-! ### The even positive form with explicit half exponents -/

/-- `exists_even_positive_form` with the witnesses made explicit: the reduced unit and the half
exponents `halfExp e y₀ = e/2` at the coordinates vanishing at the centre. -/
theorem even_positive_form_halfExp {W : Set (Fin d → ℝ)} (hW : IsOpen W) {K u : (Fin d → ℝ) → ℝ}
    {e : Fin d →₀ ℕ} (hu : AnalyticOnNhd ℝ u W) (hu0 : ∀ y ∈ W, u y ≠ 0)
    (hK : ∀ y ∈ W, K y = u y * monomialEval y e) (hK0 : ∀ y ∈ W, 0 ≤ K y) {y₀ : Fin d → ℝ}
    (hy₀ : y₀ ∈ W) :
    ∃ W' : Set (Fin d → ℝ), IsOpen W' ∧ y₀ ∈ W' ∧ W' ⊆ W ∧
      AnalyticOnNhd ℝ (reducedUnit u e y₀) W' ∧ (∀ y ∈ W', 0 < reducedUnit u e y₀ y) ∧
      ∀ y ∈ W', K y = reducedUnit u e y₀ y * ∏ j, y j ^ (2 * halfExp e y₀ j) := by
  have hcont : ContinuousAt u y₀ := (hu y₀ hy₀).continuousAt
  have heven : ∀ j, y₀ j = 0 → Even (e j) := fun j hj =>
    even_exponent_of_nonneg hW hK hK0 hy₀ hcont (hu0 y₀ hy₀) hj
  refine ⟨W ∩ (reducedUnit u e y₀) ⁻¹' Ioi 0, ?_, ⟨hy₀, reducedUnit_pos hW hK hK0 hy₀ hcont
    (hu0 y₀ hy₀)⟩, inter_subset_left, ?_, fun y hy => hy.2, fun y hy => ?_⟩
  · exact (continuousOn_reducedUnit e y₀ hu.continuousOn).isOpen_inter_preimage hW isOpen_Ioi
  · exact fun y hy => analyticAt_reducedUnit e y₀ (hu y hy.1)
  · rw [hK y hy.1, ← reducedUnit_mul_monomialEval u e y₀ y,
      monomialEval_reducedExp_eq_pow_two_mul heven]

theorem two_mul_halfExp_of_eq_zero {e : Fin d →₀ ℕ} {y₀ : Fin d → ℝ}
    (heven : ∀ j, y₀ j = 0 → Even (e j)) {j : Fin d} (hj : y₀ j = 0) :
    2 * halfExp e y₀ j = e j := by
  simp only [halfExp, Finsupp.mapRange_apply, reducedExp_apply_of_eq hj]
  exact Nat.two_mul_div_two_of_even (heven j hj)

/-! ### The splitting attached to a set of normal coordinates -/

/-- The splitting of `Fin d` into the complement of `S` and `S`, indexed by `Fin t ⊕ Fin (n+1)`. -/
noncomputable def splittingOf (S : Finset (Fin d)) {t n : ℕ}
    (hT : Fintype.card {j : Fin d // j ∉ S} = t) (hN : Fintype.card {j : Fin d // j ∈ S} = n + 1) :
    Fin t ⊕ Fin (n + 1) ≃ Fin d :=
  (Equiv.sumCongr (Fintype.equivFinOfCardEq hT).symm (Fintype.equivFinOfCardEq hN).symm).trans
    ((Equiv.sumComm _ _).trans (Equiv.sumCompl fun j : Fin d => j ∈ S))

theorem nIdx_splittingOf_mem (S : Finset (Fin d)) {t n : ℕ}
    (hT : Fintype.card {j : Fin d // j ∉ S} = t) (hN : Fintype.card {j : Fin d // j ∈ S} = n + 1)
    (j : Fin (n + 1)) : nIdx (splittingOf S hT hN) j ∈ S := by
  unfold nIdx splittingOf
  simp only [Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr, Equiv.sumComm_apply,
    Sum.swap_inr, Equiv.sumCompl_apply_inl]
  exact ((Fintype.equivFinOfCardEq hN).symm j).2

theorem tIdx_splittingOf_notMem (S : Finset (Fin d)) {t n : ℕ}
    (hT : Fintype.card {j : Fin d // j ∉ S} = t) (hN : Fintype.card {j : Fin d // j ∈ S} = n + 1)
    (i : Fin t) : tIdx (splittingOf S hT hN) i ∉ S := by
  unfold tIdx splittingOf
  simp only [Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Equiv.sumComm_apply,
    Sum.swap_inl, Equiv.sumCompl_apply_inr]
  exact ((Fintype.equivFinOfCardEq hT).symm i).2

/-- A product over all coordinates whose tangential factors are `1` is the product over the normal
coordinates. -/
theorem prod_eq_prod_nIdx {t n : ℕ} (σ : Fin t ⊕ Fin (n + 1) ≃ Fin d) (f : Fin d → ℝ)
    (hf : ∀ i, f (tIdx σ i) = 1) : ∏ x, f x = ∏ j, f (nIdx σ j) := by
  rw [← Equiv.prod_comp σ f, Fintype.prod_sum_type]
  simp only [show ∀ i, σ (Sum.inl i) = tIdx σ i from fun _ => rfl, hf, Finset.prod_const_one,
    one_mul]
  rfl

/-- A product over all coordinates splits into the tangential and the normal factors. -/
theorem prod_eq_prod_tIdx_mul_prod_nIdx {t n : ℕ} (σ : Fin t ⊕ Fin (n + 1) ≃ Fin d)
    (f : Fin d → ℝ) : ∏ x, f x = (∏ i, f (tIdx σ i)) * ∏ j, f (nIdx σ j) := by
  rw [← Equiv.prod_comp σ f, Fintype.prod_sum_type]
  rfl

/-- The reduced Jacobian is positive at points where the unit and the absorbed coordinates do not
vanish. -/
theorem reducedJac_pos' {v : (Fin d → ℝ) → ℝ} (h : Fin d →₀ ℕ) {y₀ y : Fin d → ℝ} (hv0 : v y ≠ 0)
    (hy : ∀ x, y₀ x ≠ 0 → y x ≠ 0) : 0 < reducedJac v h y₀ y := by
  classical
  exact mul_pos (abs_pos.2 hv0)
    (Finset.prod_pos fun x hx => pow_pos (abs_pos.2 (hy x (Finset.mem_filter.1 hx).2)) _)

/-- The reduced Jacobian is analytic at such points. -/
theorem analyticAt_reducedJac' {v : (Fin d → ℝ) → ℝ} (h : Fin d →₀ ℕ) {y₀ y : Fin d → ℝ}
    (hv : AnalyticAt ℝ v y) (hv0 : v y ≠ 0) (hy : ∀ x, y₀ x ≠ 0 → y x ≠ 0) :
    AnalyticAt ℝ (reducedJac v h y₀) y := by
  classical
  have hprod : AnalyticAt ℝ (∏ x ∈ Finset.univ.filter (fun x => y₀ x ≠ 0),
      fun y : Fin d → ℝ => |y x| ^ h x) y := by
    refine Finset.analyticAt_prod _ fun x hx => ?_
    exact (analyticAt_abs_of_ne_zero
      ((ContinuousLinearMap.proj x : (Fin d → ℝ) →L[ℝ] ℝ).analyticAt y)
      (hy x (Finset.mem_filter.1 hx).2)).pow _
  have h2 : AnalyticAt ℝ (fun y : Fin d → ℝ =>
      ∏ x ∈ Finset.univ.filter (fun x => y₀ x ≠ 0), |y x| ^ h x) y :=
    hprod.congr (Filter.Eventually.of_forall fun y => by simp [Finset.prod_apply])
  exact (analyticAt_abs_of_ne_zero hv hv0).mul h2

/-! ### The centred chart data -/

/-- **The centred split normal form of a chart at a divisor point.** -/
structure CentredChartData (K : (Fin d → ℝ) → ℝ) (φ : (Fin d → ℝ) → (Fin d → ℝ))
    (h : Fin d →₀ ℕ) (y₀ : Fin d → ℝ) where
  /-- the tangential dimension -/
  t : ℕ
  /-- the normal dimension minus one -/
  n : ℕ
  /-- the splitting into tangential and normal coordinates -/
  σ : Fin t ⊕ Fin (n + 1) ≃ Fin d
  /-- the phase exponents -/
  k : Fin (n + 1) → ℕ
  k_pos : ∀ j, 0 < k j
  /-- the centre has vanishing normal coordinates -/
  y₀_nIdx : ∀ j, y₀ (nIdx σ j) = 0
  /-- an open neighbourhood of the origin (translated coordinates) -/
  V₀ : Set (Fin d → ℝ)
  V₀_open : IsOpen V₀
  zero_mem : (0 : Fin d → ℝ) ∈ V₀
  /-- the analytic positive phase unit -/
  unit₀ : (Fin d → ℝ) → ℝ
  unit₀_analytic : AnalyticOnNhd ℝ unit₀ V₀
  unit₀_pos : ∀ y ∈ V₀, 0 < unit₀ y
  phase_eq : ∀ y ∈ V₀, K (φ (y + y₀)) = unit₀ y * ∏ j, y (nIdx σ j) ^ (2 * k j)
  /-- the analytic positive Jacobian unit -/
  jac₀ : (Fin d → ℝ) → ℝ
  jac₀_analytic : AnalyticOnNhd ℝ jac₀ V₀
  jac₀_pos : ∀ y ∈ V₀, 0 < jac₀ y
  /-- the tangential Jacobian weights (the Jacobian exponents of the tangential coordinates
  vanishing at the centre, whose phase exponent is zero) -/
  hT : Fin t → ℕ
  det_eq : ∀ y ∈ V₀, |(fderiv ℝ φ (y + y₀)).det| =
    jac₀ y * (∏ j, |y (nIdx σ j)| ^ h (nIdx σ j)) * ∏ i, |y (tIdx σ i)| ^ hT i
  /-- the Jacobian monomial does not vanish off the normal and weight hyperplanes -/
  monomialEval_ne_zero : ∀ y ∈ V₀, (∀ j, y (nIdx σ j) ≠ 0) →
    (∀ i, 0 < hT i → y (tIdx σ i) ≠ 0) → monomialEval (y + y₀) h ≠ 0

/-- **Every divisor point of a hironaka monomial chart has centred chart data**, with tangential
weights `hT i = h_{t_i}` at the tangential coordinates vanishing at the centre (no support
condition on the Jacobian exponents). -/
theorem exists_centredChartData {K : (Fin d → ℝ) → ℝ} {φ : (Fin d → ℝ) → (Fin d → ℝ)}
    {dom : Set (Fin d → ℝ)} {e h : Fin d →₀ ℕ} {W : Set (Fin d → ℝ)}
    (hc : IsMonomialChart K φ dom e h W) {U : Set (Fin d → ℝ)} (hU : IsOpen U)
    (hK : AnalyticOnNhd ℝ K U) (hK0 : ∀ x ∈ U, 0 ≤ K x)
    {y₀ : Fin d → ℝ} (hy₀W : y₀ ∈ W) (hy₀U : φ y₀ ∈ U) (hKy₀ : K (φ y₀) = 0) :
    ∃ C : CentredChartData K φ h y₀, (∀ y ∈ C.V₀, y + y₀ ∈ W ∧ φ (y + y₀) ∈ U) ∧
      ∀ i, C.hT i = reducedExp h y₀ (tIdx C.σ i) := by
  classical
  -- the analytic units
  set W' := W ∩ φ ⁻¹' U with hW'
  have hW'o : IsOpen W' := MonomialChart.isOpen_inter_preimage hc hU
  have hy₀W' : y₀ ∈ W' := ⟨hy₀W, hy₀U⟩
  obtain ⟨u, hu, hu0, hKu⟩ := MonomialChart.exists_analytic_unit hc hU hK
  obtain ⟨v, hv, hv0, hdet⟩ := MonomialChart.exists_analytic_jacUnit hc
  -- the even positive form at `y₀`
  have hK0' : ∀ y ∈ W', 0 ≤ K (φ y) := fun y hy => hK0 _ hy.2
  obtain ⟨W'', hW''o, hy₀W'', hW''W', hu'an, hu'pos, hK'⟩ :=
    even_positive_form_halfExp hW'o hu hu0 hKu hK0' hy₀W'
  have heven : ∀ j, y₀ j = 0 → Even (e j) := fun j hj =>
    even_exponent_of_nonneg hW'o hKu hK0' hy₀W' (hu y₀ hy₀W').continuousAt (hu0 y₀ hy₀W') hj
  set k := halfExp e y₀ with hkdef
  -- the normal set
  set S : Finset (Fin d) := Finset.univ.filter fun j => 0 < k j with hS
  have hS_zero : ∀ j ∈ S, y₀ j = 0 := by
    intro j hj
    by_contra hne
    have := halfExp_apply_of_ne (e := e) hne
    have hpos := (Finset.mem_filter.1 hj).2
    rw [hkdef] at hpos
    omega
  have hS_ne : ∃ j, j ∈ S := by
    by_contra hnone
    push Not at hnone
    have hK0y := hK' y₀ hy₀W''
    rw [hKy₀] at hK0y
    have hprod : ∏ j, y₀ j ^ (2 * k j) = 1 := by
      refine Finset.prod_eq_one fun j _ => ?_
      have : k j = 0 := by
        by_contra hk
        exact hnone j (Finset.mem_filter.2 ⟨Finset.mem_univ _, Nat.pos_of_ne_zero hk⟩)
      rw [this]
      simp
    rw [hprod, mul_one] at hK0y
    exact (hu'pos y₀ hy₀W'').ne' hK0y.symm
  obtain ⟨n, hn⟩ : ∃ n, Fintype.card {j : Fin d // j ∈ S} = n + 1 := by
    obtain ⟨j₁, hj₁⟩ := hS_ne
    have : Nonempty {j : Fin d // j ∈ S} := ⟨⟨j₁, hj₁⟩⟩
    obtain ⟨m, hm⟩ :=
      Nat.exists_eq_succ_of_ne_zero (Fintype.card_ne_zero (α := {j : Fin d // j ∈ S}))
    exact ⟨m, hm⟩
  set σ := splittingOf S rfl hn with hσ
  have hnIdx : ∀ j, nIdx σ j ∈ S := fun j => nIdx_splittingOf_mem S rfl hn j
  have htIdx : ∀ i, tIdx σ i ∉ S := fun i => tIdx_splittingOf_notMem S rfl hn i
  have hk_tIdx : ∀ i, k (tIdx σ i) = 0 := fun i => by
    have := htIdx i
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at this
    omega
  have hk_nIdx : ∀ j, 0 < k (nIdx σ j) := fun j => (Finset.mem_filter.1 (hnIdx j)).2
  have hy₀_nIdx : ∀ j, y₀ (nIdx σ j) = 0 := fun j => hS_zero _ (hnIdx j)
  -- the neighbourhood of the origin
  have hopen2 : IsOpen {y : Fin d → ℝ | ∀ x, y₀ x ≠ 0 → y x ≠ 0} := by
    have : {y : Fin d → ℝ | ∀ x, y₀ x ≠ 0 → y x ≠ 0} =
        ⋂ x ∈ (Finset.univ.filter fun x => y₀ x ≠ 0), {y : Fin d → ℝ | y x ≠ 0} := by
      ext y
      simp
    rw [this]
    exact isOpen_biInter_finset fun x _ => isOpen_ne_fun (continuous_apply x) continuous_const
  set V₀ : Set (Fin d → ℝ) := (fun y => y + y₀) ⁻¹' W'' ∩
    (fun y => y + y₀) ⁻¹' {y | ∀ x, y₀ x ≠ 0 → y x ≠ 0} with hV₀
  have hV₀o : IsOpen V₀ :=
    (hW''o.preimage (continuous_id.add continuous_const)).inter
      (hopen2.preimage (continuous_id.add continuous_const))
  have hzero_mem : (0 : Fin d → ℝ) ∈ V₀ := ⟨by simpa using hy₀W'', by simp⟩
  have hmemW'' : ∀ y ∈ V₀, y + y₀ ∈ W'' := fun y hy => hy.1
  have hmemW : ∀ y ∈ V₀, y + y₀ ∈ W := fun y hy => (hW''W' hy.1).1
  have hne : ∀ y ∈ V₀, ∀ x, y₀ x ≠ 0 → (y + y₀) x ≠ 0 := fun y hy => hy.2
  -- the exponents at the normal coordinates
  have hred_nIdx : ∀ j, reducedExp h y₀ (nIdx σ j) = h (nIdx σ j) := fun j =>
    reducedExp_apply_of_eq (hy₀_nIdx j)
  refine ⟨⟨_, n, σ, fun j => k (nIdx σ j), hk_nIdx, hy₀_nIdx, V₀, hV₀o, hzero_mem,
    fun y => reducedUnit u e y₀ (y + y₀), ?_, ?_, ?_, fun y => reducedJac v h y₀ (y + y₀),
    ?_, ?_, fun i => reducedExp h y₀ (tIdx σ i), ?_, ?_⟩,
    fun y hy => ⟨hmemW y hy, (hW''W' hy.1).2⟩, fun i => rfl⟩
  · intro y hy
    exact AnalyticAt.comp (g := reducedUnit u e y₀) (f := fun y => y + y₀) (hu'an _ (hmemW'' y hy))
      (analyticAt_id.add analyticAt_const)
  · intro y hy
    exact hu'pos _ (hmemW'' y hy)
  · intro y hy
    rw [hK' _ (hmemW'' y hy), prod_eq_prod_nIdx σ _ (fun i => by simp [hk_tIdx i])]
    congr 1
    refine Finset.prod_congr rfl fun j _ => ?_
    simp [hy₀_nIdx j]
  · intro y hy
    exact AnalyticAt.comp (g := reducedJac v h y₀) (f := fun y => y + y₀)
      (analyticAt_reducedJac' h (hv _ (hmemW y hy)) (hv0 _ (hmemW y hy)) (hne y hy))
      (analyticAt_id.add analyticAt_const)
  · intro y hy
    exact reducedJac_pos' h (hv0 _ (hmemW y hy)) (hne y hy)
  · intro y hy
    have hnor : ∏ j, |(y + y₀) (nIdx σ j)| ^ reducedExp h y₀ (nIdx σ j) =
        ∏ j, |y (nIdx σ j)| ^ h (nIdx σ j) := by
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [hred_nIdx j]
      simp [hy₀_nIdx j]
    have htan : ∏ i, |(y + y₀) (tIdx σ i)| ^ reducedExp h y₀ (tIdx σ i) =
        ∏ i, |y (tIdx σ i)| ^ reducedExp h y₀ (tIdx σ i) := by
      refine Finset.prod_congr rfl fun i _ => ?_
      by_cases hx : y₀ (tIdx σ i) = 0
      · simp [hx]
      · rw [reducedExp_apply_of_ne hx, pow_zero, pow_zero]
    rw [absDet_eq_reducedJac_mul (hdet _ (hmemW y hy)), prod_eq_prod_tIdx_mul_prod_nIdx σ, hnor,
      htan]
    ring
  · intro y hy hyn hyt
    rw [monomialEval_eq_prod]
    refine Finset.prod_ne_zero_iff.2 fun x _ => ?_
    by_cases hx : y₀ x = 0
    · obtain ⟨z, rfl⟩ := σ.surjective x
      rcases z with i | j
      · by_cases hh : h (σ (Sum.inl i)) = 0
        · rw [hh, pow_zero]
          exact one_ne_zero
        · refine pow_ne_zero _ ?_
          have hpos : 0 < reducedExp h y₀ (tIdx σ i) := by
            rw [show tIdx σ i = σ (Sum.inl i) from rfl, reducedExp_apply_of_eq hx]
            exact Nat.pos_of_ne_zero hh
          have := hyt i hpos
          rw [show tIdx σ i = σ (Sum.inl i) from rfl] at this
          simpa [hx] using this
      · refine pow_ne_zero _ ?_
        rw [show σ (Sum.inr j) = nIdx σ j from rfl]
        simpa [hy₀_nIdx j] using hyn j
    · exact pow_ne_zero _ (hne y hy x hx)

end Grammar
