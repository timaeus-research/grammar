/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.ResolvedNormalData

/-!
# The one-dimensional resolved geometry (CCCV)

Plan unit 8, first step (consult #93 A): the cheapest complete instance of the certified resolved
geometry — the line `U = ℝ¹` resolving itself, `π = id`, the single divisor component `{x = 0}` of
phase order `k = 1` (`K = x²`) and Jacobian order `h = 0`. The strata are `S_∅ = {x ≠ 0}` and
`S_{•} = {0}`; the normal space of `S_{•}` is `ℝ` and that of `S_∅` is `0`; the conormal
differential is the identity functional and the tubular germ is `Φ_s(v) = s + v`.

* `geometry : ResolvedGeometry 1 (Fin 1 → ℝ)`, `isResolutionOf : geometry.IsResolutionOf (x ↦ x²)`;
* `normalData : ResolvedNormalData geometry ℝ` with `normalSpace I = if I = ∅ then ⊥ else ⊤`;
* the frames `frameUniv : (Fin 1 → ℝ) ≃L[ℝ] N_s` and `frameUnivNeg` (the reflected side) with
  `coe_frameUniv_apply : ↑(frameUniv u) = u 0`, and the tubular identity
  `Φ_frameUniv : Φ_s (frameUniv u) = fun _ => s 0 + u 0`.

Non-claims: no charts, measures or certificates yet (next units).
-/

open Set Filter Topology

namespace Grammar

namespace OneDim

/-- The parameter space `ℝ¹`. -/
abbrev Space := Fin 1 → ℝ

/-- The phase `K(x) = x²`. -/
def phase (w : Space) : ℝ := w 0 ^ 2

theorem phase_nonneg (w : Space) : 0 ≤ phase w := sq_nonneg _

theorem measurable_phase : Measurable phase := ((measurable_pi_apply 0).pow_const 2)

theorem continuous_phase : Continuous phase := (continuous_apply 0).pow 2

/-- **The one-dimensional resolved geometry**: `U = ℝ¹`, `π = id`, one component `{x = 0}`,
`k = 1`, `h = 0`. -/
noncomputable def geometry : ResolvedGeometry 1 Space where
  π := id
  continuous_π := continuous_id
  proper_π := isProperMap_id
  Component := Unit
  E := fun _ => {u : Space | u 0 = 0}
  isClosed_E := fun _ => isClosed_eq (continuous_apply 0) continuous_const
  k := fun _ => 1
  h := fun _ => 0
  k_pos := fun _ => one_pos

theorem geometry_π (u : Space) : geometry.π u = u := rfl

theorem mem_E_iff (i : geometry.Component) (u : Space) : u ∈ geometry.E i ↔ u 0 = 0 := Iff.rfl

theorem mem_stratumSet_univ {u : Space} :
    u ∈ geometry.stratumSet Finset.univ ↔ u 0 = 0 := by
  simp only [ResolvedGeometry.stratumSet, mem_E_iff, Finset.mem_univ, iff_true, Set.mem_ofPred_eq]
  exact ⟨fun h => h (), fun h _ => h⟩

theorem mem_stratumSet_empty {u : Space} :
    u ∈ geometry.stratumSet ∅ ↔ u 0 ≠ 0 := by
  simp only [ResolvedGeometry.stratumSet, mem_E_iff, Finset.notMem_empty, iff_false,
    Set.mem_ofPred_eq]
  exact ⟨fun h => h (), fun h _ => h⟩

/-- The geometry resolves the phase `x²`. -/
theorem isResolutionOf : geometry.IsResolutionOf phase := by
  intro u
  rw [ResolvedGeometry.divisor, Set.mem_iUnion]
  constructor
  · intro h
    exact ⟨(), (mem_E_iff _ u).2 ((pow_eq_zero_iff two_ne_zero).1 h)⟩
  · rintro ⟨i, hi⟩
    rw [mem_E_iff] at hi
    change (u 0) ^ 2 = 0
    rw [hi, zero_pow two_ne_zero]

/-- The unique point of the divisor stratum. -/
def origin : geometry.Stratum Finset.univ := ⟨fun _ => 0, mem_stratumSet_univ.2 rfl⟩

theorem Stratum_univ_eq (s : geometry.Stratum Finset.univ) : s = origin := by
  apply Subtype.ext
  funext i
  rw [Fin.fin_one_eq_zero i]
  exact mem_stratumSet_univ.1 s.2

instance : Subsingleton (geometry.Stratum Finset.univ) :=
  ⟨fun s t => (Stratum_univ_eq s).trans (Stratum_univ_eq t).symm⟩

instance : Nonempty (geometry.Stratum Finset.univ) := ⟨origin⟩

/-! ### Normal data -/

/-- The normal space of the stratum `S_I`: `ℝ` on the divisor point, `0` on the open stratum. -/
noncomputable def normalSpace (I : Finset Unit) : Submodule ℝ ℝ := if I = ∅ then ⊥ else ⊤

theorem univ_ne_empty : (Finset.univ : Finset Unit) ≠ ∅ := Finset.univ_nonempty.ne_empty

theorem normalSpace_univ : normalSpace Finset.univ = ⊤ := if_neg univ_ne_empty

theorem normalSpace_empty : normalSpace ∅ = ⊥ := if_pos rfl

theorem eq_univ_of_ne_empty {I : Finset Unit} (hI : I ≠ ∅) : I = Finset.univ := by
  obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.2 hI
  exact Finset.eq_univ_iff_forall.2 fun y => (Subsingleton.elim y x) ▸ hx

theorem finrank_normalSpace (I : Finset Unit) : Module.finrank ℝ (normalSpace I) = I.card := by
  unfold normalSpace
  by_cases h : I = ∅
  · subst h
    rw [if_pos rfl, finrank_bot, Finset.card_empty]
  · rw [if_neg h, finrank_top, Module.finrank_self, eq_univ_of_ne_empty h, Finset.card_univ,
      Fintype.card_unit]

/-- The element `1 ∈ N_{S_•} = ℝ`. -/
def oneUniv : normalSpace Finset.univ := ⟨1, by rw [normalSpace_univ]; exact Submodule.mem_top⟩

theorem linearIndependent_subtype (I : Finset Unit) :
    LinearIndependent ℝ fun _ : I => (normalSpace I).subtype := by
  by_cases hI : I = ∅
  · subst hI
    have : IsEmpty ↥(∅ : Finset Unit) := ⟨fun x => Finset.notMem_empty _ x.2⟩
    exact linearIndependent_empty_type
  · have hu := eq_univ_of_ne_empty hI
    subst hu
    have : Unique ↥(Finset.univ : Finset Unit) :=
      ⟨⟨⟨(), Finset.mem_univ _⟩⟩, fun x => Subtype.ext (Subsingleton.elim _ _)⟩
    rw [linearIndependent_unique_iff]
    intro h
    have h1 := congrArg (fun f : Module.Dual ℝ (normalSpace Finset.univ) => f oneUniv) h
    simp only [LinearMap.zero_apply, Submodule.subtype_apply] at h1
    exact one_ne_zero (show ((oneUniv : normalSpace Finset.univ) : ℝ) = 0 from h1)

/-- **The normal data**: normal spaces `normalSpace I ⊆ ℝ`, the inclusion as the conormal
differential, and the tubular germ `Φ_s(v) = s + v`. -/
noncomputable def normalData : ResolvedNormalData geometry ℝ where
  N := fun I _ => normalSpace I
  finrank_N := fun I _ => finrank_normalSpace I
  finiteDimensional_N := fun I _ => inferInstance
  du := fun I _ _ => (normalSpace I).subtype
  du_linearIndependent := fun I _ => linearIndependent_subtype I
  Φ := fun _ s v => fun _ => s.1 0 + (v : ℝ)
  Φ_zero := fun _ s => by
    funext i
    rw [Fin.fin_one_eq_zero i]
    simp
  continuousAt_Φ := fun _ _ =>
    (continuous_pi fun _ => continuous_const.add continuous_subtype_val).continuousAt

theorem normalData_Φ (I : Finset Unit) (s : geometry.Stratum I) (v : normalSpace I) :
    normalData.Φ I s v = fun _ => s.1 0 + (v : ℝ) := rfl

/-! ### Frames -/

/-- The frame `ℝ¹ ≃ N_{S_•} = ℝ`, `u ↦ u 0`. -/
noncomputable def frameUniv : Space ≃L[ℝ] normalSpace Finset.univ :=
  ((LinearEquiv.funUnique (Fin 1) ℝ ℝ).trans (Submodule.topEquiv.symm.trans
    (LinearEquiv.ofEq ⊤ (normalSpace Finset.univ) normalSpace_univ.symm))).toContinuousLinearEquiv

theorem coe_frameUniv_apply (u : Space) : ((frameUniv u : normalSpace Finset.univ) : ℝ) = u 0 := by
  simp [frameUniv, LinearEquiv.funUnique]

/-- The reflected frame `u ↦ −u 0`. -/
noncomputable def frameUnivNeg : Space ≃L[ℝ] normalSpace Finset.univ :=
  (ContinuousLinearEquiv.neg ℝ).trans frameUniv

theorem coe_frameUnivNeg_apply (u : Space) :
    ((frameUnivNeg u : normalSpace Finset.univ) : ℝ) = -u 0 := by
  simp [frameUnivNeg, coe_frameUniv_apply]

/-- The tubular identity along the frame: `Φ_s(frameUniv u) = fun _ => s 0 + u 0`. -/
theorem Φ_frameUniv (s : geometry.Stratum Finset.univ) (u : Space) :
    normalData.Φ Finset.univ s (frameUniv u) = fun _ => s.1 0 + u 0 := by
  change (fun _ : Fin 1 => s.1 0 + ((frameUniv u : normalSpace Finset.univ) : ℝ)) = _
  rw [coe_frameUniv_apply]

theorem Φ_frameUnivNeg (s : geometry.Stratum Finset.univ) (u : Space) :
    normalData.Φ Finset.univ s (frameUnivNeg u) = fun _ => s.1 0 + -u 0 := by
  change (fun _ : Fin 1 => s.1 0 + ((frameUnivNeg u : normalSpace Finset.univ) : ℝ)) = _
  rw [coe_frameUnivNeg_apply]

theorem origin_val_zero : (origin : Space) 0 = 0 := rfl

end OneDim

end Grammar
