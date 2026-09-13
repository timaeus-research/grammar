/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.CoordinateResolvedGeometry

/-!
# The chart model: a partial-active coordinate geometry (CCCXLIII; phase E, unit E1)

Consult #102 §2–3. The coordinate model (CCCXIII) declares every coordinate hyperplane a divisor
component. A chart of a resolution has an ACTIVE set `A ⊆ Fin d` of divisor coordinates and
inactive tangential coordinates on which the phase does not vanish, and a positive unit depending
on the inactive coordinates. The **chart model** is `ℝ^d` with `π = id`, components `↥A`,
`E_i = {y_i = 0}` for `i ∈ A`, orders `(k_i, h_i)`, the phase `u₀(y) · ∏_{i∈A} y_i^{2k_i}`
(`phase`; `isResolutionOf` for a positive unit), strata `S_I = {y : y_i = 0 ⇔ i ∈ I}` for
`I ⊆ A` (the deepest stratum is `{y_i = 0, i ∈ A} ≅ ℝ^{d−|A|}`, not a point:
`mem_stratumSet_univ_iff`, `exists_mem_stratumSet_univ_ne_zero`), and the normal data built from the
coordinate constructions on the ambient index set `amb A I ⊆ Fin d` of a component finset
(`normalSpace d (amb A I)`, coordinate conormal differentials, `Φ_s(v) = s + v`). The full-active
model recovers the coordinate phase (`phase_univ`). Zero `sorry`/`axiom`.
-/

open Set Filter Topology

namespace Grammar

namespace ChartModel

variable (d : ℕ) (A : Finset (Fin d)) (k h : Fin d → ℕ) (hk : ∀ i ∈ A, 0 < k i)

/-- The active monomial `∏_{i∈A} y_i^{2k_i}`. -/
def monoPhase (y : Fin d → ℝ) : ℝ := ∏ i ∈ A, y i ^ (2 * k i)

/-- The chart phase `u₀(y) · ∏_{i∈A} y_i^{2k_i}`. -/
def phase (u₀ : (Fin d → ℝ) → ℝ) (y : Fin d → ℝ) : ℝ := u₀ y * monoPhase d A k y

omit h hk in
theorem monoPhase_nonneg (y : Fin d → ℝ) : 0 ≤ monoPhase d A k y :=
  Finset.prod_nonneg fun i _ => by rw [pow_mul]; exact pow_nonneg (sq_nonneg _) _

omit h hk in
theorem phase_nonneg (u₀ : (Fin d → ℝ) → ℝ) (hu : ∀ y, 0 ≤ u₀ y) (y : Fin d → ℝ) :
    0 ≤ phase d A k u₀ y :=
  mul_nonneg (hu y) (monoPhase_nonneg d A k y)

omit h hk in
theorem measurable_monoPhase : Measurable (monoPhase d A k) :=
  Finset.measurable_prod _ fun i _ => (measurable_pi_apply i).pow_const _

omit h hk in
theorem continuous_monoPhase : Continuous (monoPhase d A k) :=
  continuous_finsetProd _ fun i _ => (continuous_apply i).pow _

omit A h hk in
/-- The full-active chart model with unit `1` is the coordinate model. -/
theorem phase_univ : phase d Finset.univ k (fun _ => 1) = CoordModel.phase d k := by
  funext y
  unfold phase monoPhase CoordModel.phase
  rw [one_mul]

/-- **The chart model geometry**: `ℝ^d`, `π = id`, components the active coordinates. -/
noncomputable def geometry : ResolvedGeometry d (Fin d → ℝ) where
  π := id
  continuous_π := continuous_id
  proper_π := isProperMap_id
  Component := ↥A
  E := fun i => {u : Fin d → ℝ | u i.1 = 0}
  isClosed_E := fun i => isClosed_eq (continuous_apply i.1) continuous_const
  k := fun i => k i.1
  h := fun i => h i.1
  k_pos := fun i => hk i.1 i.2

theorem geometry_π (u : Fin d → ℝ) : (geometry d A k h hk).π u = u := rfl

theorem mem_E_iff (i : ↥A) (u : Fin d → ℝ) : u ∈ (geometry d A k h hk).E i ↔ u i.1 = 0 := Iff.rfl

theorem mem_stratumSet_iff (I : Finset ↥A) (u : Fin d → ℝ) :
    u ∈ (geometry d A k h hk).stratumSet I ↔ ∀ i : ↥A, u i.1 = 0 ↔ i ∈ I := Iff.rfl

/-- The geometry resolves the chart phase for a positive unit. -/
theorem isResolutionOf (u₀ : (Fin d → ℝ) → ℝ) (hu : ∀ y, 0 < u₀ y) :
    (geometry d A k h hk).IsResolutionOf (phase d A k u₀) := by
  intro u
  rw [ResolvedGeometry.divisor, Set.mem_iUnion, geometry_π]
  unfold phase monoPhase
  rw [mul_eq_zero, Finset.prod_eq_zero_iff]
  constructor
  · rintro (h0 | ⟨i, hi, hi0⟩)
    · exact absurd h0 (hu u).ne'
    · exact ⟨⟨i, hi⟩, (pow_eq_zero_iff (by have := hk i hi; omega)).1 hi0⟩
  · rintro ⟨i, hi⟩
    refine Or.inr ⟨i.1, i.2, ?_⟩
    rw [(mem_E_iff d A k h hk i u).1 hi]
    exact zero_pow (by have := hk i.1 i.2; omega)

/-- **The deepest stratum** `{y : y_i = 0 for all i ∈ A}`. -/
theorem mem_stratumSet_univ_iff (u : Fin d → ℝ) :
    u ∈ (geometry d A k h hk).stratumSet Finset.univ ↔ ∀ i ∈ A, u i = 0 := by
  change (∀ i : ↥A, u i.1 = 0 ↔ i ∈ (Finset.univ : Finset ↥A)) ↔ ∀ i ∈ A, u i = 0
  constructor
  · intro hu i hi
    exact (hu ⟨i, hi⟩).2 (Finset.mem_univ _)
  · intro hu i
    exact ⟨fun _ => Finset.mem_univ _, fun _ => hu i.1 i.2⟩

/-- With an inactive coordinate the deepest stratum is not a point. -/
theorem exists_mem_stratumSet_univ_ne_zero (hA : A ≠ Finset.univ) :
    ∃ u : Fin d → ℝ, u ≠ 0 ∧ u ∈ (geometry d A k h hk).stratumSet Finset.univ := by
  obtain ⟨j, hj⟩ : ∃ j, j ∉ A := by
    by_contra hcon
    push Not at hcon
    exact hA (Finset.eq_univ_iff_forall.2 hcon)
  refine ⟨Pi.single j 1, ?_, ?_⟩
  · intro h0
    have := congrFun h0 j
    simp at this
  · rw [mem_stratumSet_univ_iff]
    intro i hi
    rw [Pi.single_apply, if_neg]
    rintro rfl
    exact hj hi

/-! ### Normal data -/

/-- The ambient index set of a component finset. -/
def amb (I : Finset ↥A) : Finset (Fin d) := I.map (Function.Embedding.subtype _)

omit k h hk in
theorem mem_amb {I : Finset ↥A} {j : Fin d} : j ∈ amb d A I ↔ ∃ hj : j ∈ A, ⟨j, hj⟩ ∈ I := by
  unfold amb
  rw [Finset.mem_map]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i.2, hi⟩
  · rintro ⟨hj, hi⟩
    exact ⟨⟨j, hj⟩, hi, rfl⟩

omit k h hk in
theorem card_amb (I : Finset ↥A) : (amb d A I).card = I.card := Finset.card_map _

omit k h hk in
theorem mem_amb_of_mem {I : Finset ↥A} (i : ↥I) : (i.1.1 : Fin d) ∈ amb d A I :=
  (mem_amb d A).2 ⟨i.1.2, i.2⟩

/-- The component-indexed conormal differentials, through the ambient index set. -/
noncomputable def du (I : Finset ↥A) (i : ↥I) :
    Module.Dual ℝ (CoordModel.normalSpace d (amb d A I)) :=
  CoordModel.du d (amb d A I) ⟨i.1.1, mem_amb_of_mem d A i⟩

omit k h hk in
theorem linearIndependent_du (I : Finset ↥A) : LinearIndependent ℝ (du d A I) :=
  (CoordModel.linearIndependent_du d (amb d A I)).comp
    (fun i : ↥I => (⟨i.1.1, mem_amb_of_mem d A i⟩ : ↥(amb d A I)))
    fun i j hij => Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hij))

/-- **The normal data of the chart model**: `N_I = span{e_i : i ∈ I}` through the ambient index
set, coordinate conormal differentials, tubular germ `Φ_s(v) = s + v`. -/
noncomputable def normalData : ResolvedNormalData (geometry d A k h hk) (CoordModel.Amb d) where
  N := fun I _ => CoordModel.normalSpace d (amb d A I)
  finrank_N := fun I _ => (CoordModel.finrank_normalSpace d _).trans (card_amb d A I)
  finiteDimensional_N := fun _ _ => inferInstance
  du := fun I _ => du d A I
  du_linearIndependent := fun I _ => linearIndependent_du d A I
  Φ := fun _ s v => fun i => s.1 i + (v : CoordModel.Amb d) i
  Φ_zero := fun _ s => by
    funext i
    simp
  continuousAt_Φ := fun _ _ =>
    (continuous_pi fun i => continuous_const.add
      ((PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) i).comp continuous_subtype_val)).continuousAt

theorem normalData_Φ (I : Finset ↥A) (s : (geometry d A k h hk).Stratum I)
    (v : CoordModel.normalSpace d (amb d A I)) :
    (normalData d A k h hk).Φ I s v = fun i => s.1 i + (v : CoordModel.Amb d) i := rfl

end ChartModel

end Grammar
