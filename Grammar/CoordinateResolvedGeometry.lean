/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.ResolvedNormalData

/-!
# The coordinate model: `ℝ^d` resolving a monomial phase (CCCXIII)

The `d`-dimensional companion of CCCV, the geometry side of every monomial instance: `U = ℝ^d`
resolving itself (`π = id`), the coordinate hyperplanes `E_i = {u_i = 0}` as divisor components
with orders `(k_i, h_i)`, the monomial phase `K = ∏ u_i^{2k_i}` (`isResolutionOf`), the strata
`S_I = {u : u_i = 0 ⇔ i ∈ I}`, the normal spaces `N_I = span{e_i : i ∈ I} ⊆ ℝ^d` (Euclidean),
the coordinate functionals as conormal differentials, and the tubular germ `Φ_s(v) = s + v`.

* `geometry d k h hk : ResolvedGeometry d (Fin d → ℝ)`, `normalData : ResolvedNormalData …
(EuclideanSpace ℝ (Fin d))`;
* `normalSpace_univ : N_{univ} = ⊤` and the frame `frameUniv : (Fin d → ℝ) ≃L[ℝ] N_{univ}` with
  `coe_frameUniv_apply` and the tubular identity `Φ_frameUniv` at the deepest stratum.

Non-claims: no charts or certificates (the instances supply them); the strata other than the
deepest are not equipped with frames here.
-/

open Set Filter Topology

namespace Grammar

namespace CoordModel

variable (d : ℕ) (k h : Fin d → ℕ) (hk : ∀ i, 0 < k i)

/-- The monomial phase `K(u) = ∏ u_i^{2k_i}`. -/
def phase (w : Fin d → ℝ) : ℝ := ∏ i, w i ^ (2 * k i)

omit h hk in
theorem phase_nonneg (w : Fin d → ℝ) : 0 ≤ phase d k w :=
  Finset.prod_nonneg fun i _ => by rw [pow_mul]; exact pow_nonneg (sq_nonneg _) _

omit h hk in
theorem measurable_phase : Measurable (phase d k) :=
  Finset.measurable_prod _ fun i _ => (measurable_pi_apply i).pow_const _

omit h hk in
theorem continuous_phase : Continuous (phase d k) :=
  continuous_finsetProd _ fun i _ => (continuous_apply i).pow _

/-- **The coordinate model geometry**: `ℝ^d`, `π = id`, components `{u_i = 0}`, orders `k, h`. -/
noncomputable def geometry : ResolvedGeometry d (Fin d → ℝ) where
  π := id
  continuous_π := continuous_id
  proper_π := isProperMap_id
  Component := Fin d
  E := fun i => {u : Fin d → ℝ | u i = 0}
  isClosed_E := fun i => isClosed_eq (continuous_apply i) continuous_const
  k := k
  h := h
  k_pos := hk

theorem geometry_π (u : Fin d → ℝ) : (geometry d k h hk).π u = u := rfl

theorem mem_E_iff (i : Fin d) (u : Fin d → ℝ) : u ∈ (geometry d k h hk).E i ↔ u i = 0 := Iff.rfl

theorem mem_stratumSet_iff (I : Finset (Fin d)) (u : Fin d → ℝ) :
    u ∈ (geometry d k h hk).stratumSet I ↔ ∀ i, u i = 0 ↔ i ∈ I := Iff.rfl

/-- The geometry resolves the monomial phase. -/
theorem isResolutionOf : (geometry d k h hk).IsResolutionOf (phase d k) := by
  intro u
  rw [ResolvedGeometry.divisor, Set.mem_iUnion, geometry_π]
  unfold phase
  rw [Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨i, _, hi⟩
    exact ⟨i, (pow_eq_zero_iff (by have := hk i; omega)).1 hi⟩
  · rintro ⟨i, hi⟩
    refine ⟨i, Finset.mem_univ _, ?_⟩
    rw [(mem_E_iff d k h hk i u).1 hi]
    exact zero_pow (by have := hk i; omega)

theorem mem_stratumSet_univ_iff (u : Fin d → ℝ) :
    u ∈ (geometry d k h hk).stratumSet Finset.univ ↔ u = 0 := by
  change (∀ i, u i = 0 ↔ i ∈ Finset.univ) ↔ u = 0
  constructor
  · intro hu
    funext i
    exact (hu i).2 (Finset.mem_univ i)
  · intro hu i
    subst hu
    simp

/-- The origin, the unique point of the deepest stratum. -/
def origin : (geometry d k h hk).Stratum Finset.univ :=
  ⟨0, (mem_stratumSet_univ_iff d k h hk 0).2 rfl⟩

theorem Stratum_univ_eq (s : (geometry d k h hk).Stratum Finset.univ) : s = origin d k h hk :=
  Subtype.ext ((mem_stratumSet_univ_iff d k h hk s.1).1 s.2)

instance : Subsingleton ((geometry d k h hk).Stratum Finset.univ) :=
  ⟨fun s t => (Stratum_univ_eq d k h hk s).trans (Stratum_univ_eq d k h hk t).symm⟩

instance : Nonempty ((geometry d k h hk).Stratum Finset.univ) := ⟨origin d k h hk⟩

/-! ### Normal data -/

/-- The ambient Euclidean space. -/
abbrev Amb := EuclideanSpace ℝ (Fin d)

/-- The coordinate vector `e_i`. -/
noncomputable def basisVec (i : Fin d) : Amb d := EuclideanSpace.single i 1

omit k h hk in
theorem basisVec_eq : basisVec d = ⇑(EuclideanSpace.basisFun (Fin d) ℝ) := by
  funext i
  simp [basisVec, EuclideanSpace.basisFun_apply]

omit k h hk in
theorem linearIndependent_basisVec : LinearIndependent ℝ (basisVec d) := by
  rw [basisVec_eq]
  exact (EuclideanSpace.basisFun (Fin d) ℝ).orthonormal.linearIndependent

/-- The normal space of `S_I`: `span{e_i : i ∈ I}`. -/
noncomputable def normalSpace (I : Finset (Fin d)) : Submodule ℝ (Amb d) :=
  Submodule.span ℝ (Set.range fun i : I => basisVec d (i : Fin d))

omit k h hk in
theorem linearIndependent_basisVec_restrict (I : Finset (Fin d)) :
    LinearIndependent ℝ fun i : I => basisVec d (i : Fin d) :=
  (linearIndependent_basisVec d).comp _ Subtype.val_injective

omit k h hk in
theorem finrank_normalSpace (I : Finset (Fin d)) :
    Module.finrank ℝ (normalSpace d I) = I.card := by
  unfold normalSpace
  rw [finrank_span_eq_card (linearIndependent_basisVec_restrict d I), Fintype.card_coe]

omit k h hk in
theorem basisVec_mem (I : Finset (Fin d)) (i : I) : basisVec d (i : Fin d) ∈ normalSpace d I :=
  Submodule.subset_span ⟨i, rfl⟩

/-- The conormal differential `du_i` on `N_I`: the coordinate functional. -/
noncomputable def du (I : Finset (Fin d)) (i : I) : Module.Dual ℝ (normalSpace d I) :=
  (EuclideanSpace.projₗ (i : Fin d)).comp (normalSpace d I).subtype

omit k h hk in
theorem du_apply_basisVec (I : Finset (Fin d)) (i j : I) :
    du d I i ⟨basisVec d j, basisVec_mem d I j⟩ = if (i : Fin d) = j then 1 else 0 := by
  unfold du basisVec
  simp [PiLp.single_apply]

omit k h hk in
theorem linearIndependent_du (I : Finset (Fin d)) : LinearIndependent ℝ (du d I) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  have h := congrArg (fun f : Module.Dual ℝ (normalSpace d I) =>
    f ⟨basisVec d j, basisVec_mem d I j⟩) hg
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, du_apply_basisVec, smul_eq_mul,
    LinearMap.zero_apply] at h
  rw [Finset.sum_eq_single j] at h
  · simpa using h
  · intro i _ hij
    rw [if_neg (fun hc => hij (Subtype.ext hc)), mul_zero]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

/-- **The normal data of the coordinate model**: `N_I = span{e_i : i ∈ I}`, coordinate conormal
differentials, tubular germ `Φ_s(v) = s + v`. -/
noncomputable def normalData : ResolvedNormalData (geometry d k h hk) (Amb d) where
  N := fun I _ => normalSpace d I
  finrank_N := fun I _ => finrank_normalSpace d I
  finiteDimensional_N := fun _ _ => inferInstance
  du := fun I _ => du d I
  du_linearIndependent := fun I _ => linearIndependent_du d I
  Φ := fun _ s v => fun i => s.1 i + (v : Amb d) i
  Φ_zero := fun _ s => by
    funext i
    simp
  continuousAt_Φ := fun _ _ =>
    (continuous_pi fun i => continuous_const.add
      ((PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) i).comp continuous_subtype_val)).continuousAt

theorem normalData_Φ (I : Finset (Fin d)) (s : (geometry d k h hk).Stratum I)
    (v : normalSpace d I) : (normalData d k h hk).Φ I s v = fun i => s.1 i + (v : Amb d) i := rfl

/-! ### The frame at the deepest stratum -/

omit k h hk in
theorem normalSpace_univ : normalSpace d Finset.univ = ⊤ := by
  unfold normalSpace
  have hr : (Set.range fun i : (Finset.univ : Finset (Fin d)) => basisVec d (i : Fin d)) =
      Set.range (basisVec d) := by
    ext v
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨⟨i, Finset.mem_univ i⟩, rfl⟩
  rw [hr, basisVec_eq, ← OrthonormalBasis.coe_toBasis]
  exact (EuclideanSpace.basisFun (Fin d) ℝ).toBasis.span_eq

/-- The frame `ℝ^d ≃ N_{univ}`, `u ↦ (u_i)_i`. -/
noncomputable def frameUniv : (Fin d → ℝ) ≃L[ℝ] normalSpace d Finset.univ :=
  LinearEquiv.toContinuousLinearEquiv
    ((WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).symm.trans (Submodule.topEquiv.symm.trans
      (LinearEquiv.ofEq ⊤ (normalSpace d Finset.univ) (normalSpace_univ d).symm)))

omit k h hk in
theorem coe_frameUniv_apply (u : Fin d → ℝ) (i : Fin d) :
    ((frameUniv d u : normalSpace d Finset.univ) : Amb d) i = u i := by
  simp [frameUniv]

/-- The tubular identity along the frame at the deepest stratum. -/
theorem Φ_frameUniv (s : (geometry d k h hk).Stratum Finset.univ) (u : Fin d → ℝ) :
    (normalData d k h hk).Φ Finset.univ s (frameUniv d u) = fun i => s.1 i + u i := by
  change (fun i => s.1 i + ((frameUniv d u : normalSpace d Finset.univ) : Amb d) i) = _
  funext i
  rw [coe_frameUniv_apply]

theorem Φ_frameUniv_origin (u : Fin d → ℝ) :
    (normalData d k h hk).Φ Finset.univ (origin d k h hk) (frameUniv d u) = u := by
  rw [Φ_frameUniv]
  funext i
  change (0 : Fin d → ℝ) i + u i = u i
  rw [Pi.zero_apply, zero_add]

end CoordModel

end Grammar
