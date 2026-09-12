/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Grammar.NormalDifferentialConvention

/-!
# Resolved geometry: the exceptional divisor and its strata (CCXCVIII)

Unit 2 of the coordinate-free programme (consult #92; `tide-log/plan_coordinate_free_expansion.md`).
The geometric data the final expansion formula refers to, with NO charts: a resolved space `U` with
a continuous proper map `π : U → ℝ^d` to the parameter space, finitely many closed divisor
components `E_i ⊆ U` carrying the numerical orders `(k_i, h_i)` (phase order `2k_i`, Jacobian
order `h_i`), and the derived stratification

`S_I = {u ∈ U | ∀ i, u ∈ E_i ↔ i ∈ I}` (`stratumSet`), the locus where exactly the components in
`I` pass. The strata are pairwise disjoint and cover `U` (`stratumSet_disjoint`,
`iUnion_stratumSet`), `S_∅` is the complement of the divisor, `S_I = ⋂_{i∈I} E_i \ ⋃_{j∉I} E_j`
(`stratumSet_eq`), `closure S_I ⊆ ⋂_{i∈I} E_i`, and every stratum is Borel. Each nonempty stratum
carries the paper's pair: `λ_I = min_{i∈I} (h_i+1)/(2k_i)` (`stratumLam`) with multiplicity
`m_I = #{i ∈ I : (h_i+1)/(2k_i) = λ_I}` (`stratumMult`), `1 ≤ m_I ≤ |I|`. A phase `K` is
resolved by the geometry when its zero set pulls back exactly to the divisor (`IsResolutionOf`).
No asymptotic statement lives here: those are theorems about certified resolved geometry (units
5–11), of which this structure is the chart-free part of the hypotheses.
-/

open Set Filter Topology

namespace Grammar

/-- **Resolved geometry over `ℝ^d`**: a proper continuous map from the resolved space, finitely
many closed divisor components with their numerical orders. -/
structure ResolvedGeometry (d : ℕ) (U : Type*) [TopologicalSpace U] where
  /-- The resolution map. -/
  π : U → (Fin d → ℝ)
  continuous_π : Continuous π
  proper_π : IsProperMap π
  /-- The index type of the divisor components. -/
  Component : Type
  [fintype : Fintype Component]
  [decEq : DecidableEq Component]
  /-- The divisor components. -/
  E : Component → Set U
  isClosed_E : ∀ i, IsClosed (E i)
  /-- The half phase orders `k_i` (the phase vanishes to order `2k_i` along `E_i`). -/
  k : Component → ℕ
  /-- The Jacobian orders `h_i`. -/
  h : Component → ℕ
  k_pos : ∀ i, 0 < k i

attribute [instance] ResolvedGeometry.fintype ResolvedGeometry.decEq

namespace ResolvedGeometry

variable {d : ℕ} {U : Type*} [TopologicalSpace U] (R : ResolvedGeometry d U)

/-! ### The divisor and the strata -/

/-- The exceptional divisor `E = ⋃ E_i`. -/
def divisor : Set U := ⋃ i, R.E i

theorem isClosed_divisor : IsClosed R.divisor := isClosed_iUnion_of_finite R.isClosed_E

/-- **The stratum of the index set `I`**: the points through which exactly the components in `I`
pass. -/
def stratumSet (I : Finset R.Component) : Set U := {u | ∀ i, u ∈ R.E i ↔ i ∈ I}

/-- The stratum as a type. -/
abbrev Stratum (I : Finset R.Component) : Type _ := ↥(R.stratumSet I)

/-- The incidence set of a point: the components passing through it. -/
noncomputable def incidence (u : U) : Finset R.Component :=
  open scoped Classical in Finset.univ.filter fun i => u ∈ R.E i

theorem mem_incidence {u : U} {i : R.Component} : i ∈ R.incidence u ↔ u ∈ R.E i := by
  unfold incidence
  classical
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem mem_stratumSet_iff {u : U} {I : Finset R.Component} :
    u ∈ R.stratumSet I ↔ R.incidence u = I := by
  constructor
  · intro hu
    ext i
    rw [R.mem_incidence]
    exact hu i
  · intro hu i
    rw [← hu, R.mem_incidence]

theorem mem_stratumSet_incidence (u : U) : u ∈ R.stratumSet (R.incidence u) :=
  R.mem_stratumSet_iff.2 rfl

/-- **The strata are pairwise disjoint.** -/
theorem stratumSet_disjoint {I J : Finset R.Component} (hIJ : I ≠ J) :
    Disjoint (R.stratumSet I) (R.stratumSet J) := by
  rw [Set.disjoint_left]
  intro u hI hJ
  exact hIJ ((R.mem_stratumSet_iff.1 hI).symm.trans (R.mem_stratumSet_iff.1 hJ))

/-- **The strata cover the resolved space.** -/
theorem iUnion_stratumSet : ⋃ I : Finset R.Component, R.stratumSet I = univ :=
  eq_univ_of_forall fun u => mem_iUnion.2 ⟨R.incidence u, R.mem_stratumSet_incidence u⟩

/-- `S_I = ⋂_{i∈I} E_i \ ⋃_{j∉I} E_j`. -/
theorem stratumSet_eq (I : Finset R.Component) :
    R.stratumSet I = (⋂ i ∈ I, R.E i) \ ⋃ j ∈ (Finset.univ \ I), R.E j := by
  ext u
  simp only [stratumSet, mem_ofPred_eq, Set.mem_sdiff, mem_iInter, mem_iUnion, Finset.mem_sdiff,
    Finset.mem_univ, true_and, not_exists]
  constructor
  · intro hu
    exact ⟨fun i hi => (hu i).2 hi, fun j hj hju => hj ((hu j).1 hju)⟩
  · rintro ⟨h1, h2⟩ i
    exact ⟨fun hi => by_contra fun hiI => h2 i hiI hi, h1 i⟩

/-- The empty stratum is the complement of the divisor. -/
theorem stratumSet_empty : R.stratumSet ∅ = R.divisorᶜ := by
  ext u
  simp only [stratumSet, mem_ofPred_eq, Finset.notMem_empty, iff_false, divisor, mem_compl_iff,
    mem_iUnion, not_exists]

theorem stratumSet_subset_biInter (I : Finset R.Component) :
    R.stratumSet I ⊆ ⋂ i ∈ I, R.E i := by
  rw [stratumSet_eq]; exact sdiff_subset

/-- The closure of a stratum stays inside the intersection of its components. -/
theorem closure_stratumSet_subset (I : Finset R.Component) :
    closure (R.stratumSet I) ⊆ ⋂ i ∈ I, R.E i :=
  closure_minimal (R.stratumSet_subset_biInter I)
    (isClosed_biInter fun i _ => R.isClosed_E i)

/-- A stratum is relatively open in the intersection of its components: it is the intersection
with the open complement of the other components. -/
theorem stratumSet_eq_inter_compl (I : Finset R.Component) :
    R.stratumSet I = (⋂ i ∈ I, R.E i) ∩ (⋃ j ∈ (Finset.univ \ I), R.E j)ᶜ := by
  rw [stratumSet_eq]; rfl

theorem isOpen_compl_others (I : Finset R.Component) :
    IsOpen (⋃ j ∈ (Finset.univ \ I), R.E j)ᶜ :=
  (isClosed_biUnion_finset fun j _ => R.isClosed_E j).isOpen_compl

/-- The strata are Borel. -/
theorem measurableSet_stratumSet [MeasurableSpace U] [OpensMeasurableSpace U]
    (I : Finset R.Component) : MeasurableSet (R.stratumSet I) := by
  rw [stratumSet_eq]
  exact (MeasurableSet.biInter I.countable_toSet fun i _ => (R.isClosed_E i).measurableSet).diff
    (MeasurableSet.biUnion (Finset.univ \ I).countable_toSet fun j _ =>
      (R.isClosed_E j).measurableSet)

/-! ### The numerical pair of a stratum -/

/-- The ratio `(h_i + 1)/(2k_i)` of a component. -/
noncomputable def ratio (i : R.Component) : ℝ := ((R.h i : ℝ) + 1) / (2 * (R.k i : ℝ))

theorem ratio_pos (i : R.Component) : 0 < R.ratio i := by
  unfold ratio
  have := R.k_pos i
  positivity

/-- **The exponent of a stratum** `λ_I = min_{i∈I} (h_i+1)/(2k_i)`. -/
noncomputable def stratumLam (I : Finset R.Component) (hne : I.Nonempty) : ℝ :=
  I.inf' hne R.ratio

/-- **The multiplicity of a stratum** `m_I = #{i ∈ I : (h_i+1)/(2k_i) = λ_I}`. -/
noncomputable def stratumMult (I : Finset R.Component) (hne : I.Nonempty) : ℕ :=
  (I.filter fun i => R.ratio i = R.stratumLam I hne).card

theorem stratumLam_le {I : Finset R.Component} (hne : I.Nonempty) {i : R.Component} (hi : i ∈ I) :
    R.stratumLam I hne ≤ R.ratio i :=
  Finset.inf'_le _ hi

theorem exists_ratio_eq_stratumLam (I : Finset R.Component) (hne : I.Nonempty) :
    ∃ i ∈ I, R.ratio i = R.stratumLam I hne := by
  obtain ⟨i, hi, h⟩ := Finset.exists_mem_eq_inf' hne R.ratio
  exact ⟨i, hi, h.symm⟩

theorem stratumLam_pos (I : Finset R.Component) (hne : I.Nonempty) : 0 < R.stratumLam I hne := by
  obtain ⟨i, -, hi⟩ := R.exists_ratio_eq_stratumLam I hne
  rw [← hi]; exact R.ratio_pos i

theorem stratumMult_pos (I : Finset R.Component) (hne : I.Nonempty) :
    0 < R.stratumMult I hne := by
  obtain ⟨i, hi, h⟩ := R.exists_ratio_eq_stratumLam I hne
  exact Finset.card_pos.2 ⟨i, Finset.mem_filter.2 ⟨hi, h⟩⟩

theorem stratumMult_le_card (I : Finset R.Component) (hne : I.Nonempty) :
    R.stratumMult I hne ≤ I.card :=
  Finset.card_filter_le _ _

/-- Adding a component with a larger ratio does not change the exponent. -/
theorem stratumLam_insert_of_lt {I : Finset R.Component} (hne : I.Nonempty) {j : R.Component}
    (hj : R.stratumLam I hne < R.ratio j) :
    R.stratumLam (insert j I) (Finset.insert_nonempty j I) = R.stratumLam I hne := by
  unfold stratumLam
  rw [Finset.inf'_insert]
  exact min_eq_right hj.le

/-! ### Properness and the resolved phase -/

theorem isCompact_preimage {S : Set (Fin d → ℝ)} (hS : IsCompact S) : IsCompact (R.π ⁻¹' S) :=
  R.proper_π.isCompact_preimage hS

theorem isClosedMap_π : IsClosedMap R.π := R.proper_π.isClosedMap

/-- **A phase is resolved by the geometry** when its zero set pulls back exactly to the divisor. -/
def IsResolutionOf (K : (Fin d → ℝ) → ℝ) : Prop := ∀ u, K (R.π u) = 0 ↔ u ∈ R.divisor

theorem image_divisor_subset {K : (Fin d → ℝ) → ℝ} (hK : R.IsResolutionOf K) :
    R.π '' R.divisor ⊆ {w | K w = 0} := by
  rintro _ ⟨u, hu, rfl⟩
  exact (hK u).2 hu

theorem mem_divisor_of_phase_zero {K : (Fin d → ℝ) → ℝ} (hK : R.IsResolutionOf K) {u : U}
    (h : K (R.π u) = 0) : u ∈ R.divisor := (hK u).1 h

/-- Off the divisor the resolved phase is nonzero. -/
theorem phase_ne_zero_of_notMem_divisor {K : (Fin d → ℝ) → ℝ} (hK : R.IsResolutionOf K) {u : U}
    (h : u ∉ R.divisor) : K (R.π u) ≠ 0 := fun h0 => h ((hK u).1 h0)

/-- The image of the divisor is closed (properness) and contained in the zero set. -/
theorem isClosed_image_divisor : IsClosed (R.π '' R.divisor) :=
  R.isClosedMap_π _ R.isClosed_divisor

end ResolvedGeometry

end Grammar
