import Grammar.LabelledNormalBundle

/-!
# The labelled normal bundle as the Riesz image of the conormal splitting (Astra #65 units 2–3)

Astra's review (#65) asked two questions about CLXXVI: which labelled splitting the gradient frames
realise, and what geometric hypotheses identify the constructed bundle with the paper's normal
bundle. This file answers both without new geometry.

* **The splitting convention.** The paper's `eq:decomp_nx` is the *conormal* splitting
  `⊕ 𝓛_i ≅ N^*X` with `𝓛_i = ℝ·du_i` (CLXVII, pointwise). The Riesz map carries the gradient
  frame `c ↦ ∑ c_l ∇u_l` to the differential frame `c ↦ ∑ c_l du_l` (`toDual_frame_apply`), each
  gradient line to the labelled conormal line `ℝ·du_l` (`toDual_grad_mem_conormalLine`), and the
  normal space `(T x)ᗮ` onto the pointwise conormal space `(T x)^⊥ ⊆ E^*` of CLXVII
  (`mem_normal_iff_toDual_mem_conormalOf`); in fact the frame coordinates are exactly CLXVII's
  conormal coordinates (`toDual_frame_eq_conormalCoordEquiv`). So the labelled lines of CLXXVI are
  the Riesz images of the paper's `𝓛_i`, not the lines dual to them under the canonical pairing.
* **The geometric identification adapter.** `LabelledDefiningEquations` is algebraic data along a
  smooth map. `GeometricIdentification` records the hypotheses needed to read it geometrically:
  the equations vanish along the map, the map is injective, and its differential has image the
  kernel field `⋂ ker du_l`. Under them the kernel field is the image of the tangent spaces and
  the normal field is its orthogonal complement (`normal_eq_orthogonal_range_mfderiv`); the scalar
  overlap law follows from function-level unit changes (`unit_of_mul`).

Non-claims: the tangent-image equality is a hypothesis (no implicit-function construction of a
level-set manifold); no direct-sum bundle isomorphism beyond the frame-level statements.
-/

open scoped Manifold ContDiff InnerProductSpace
open Bundle Set Function Module

namespace Grammar

namespace LabelledDefiningEquations

variable {EB HB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB} {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {k : ℕ} {ι : Type*} (D : LabelledDefiningEquations IB B E k ι)

/-- **Riesz carries the gradient frame to the differential frame** `c ↦ ∑ c_l du_l`. -/
theorem toDual_frame_apply (i : ι) (x : B) (c : EuclideanSpace ℝ (Fin k)) :
    InnerProductSpace.toDual ℝ E (D.frame i x c) = ∑ l, c l • D.diff i l x := by
  rw [frame_apply, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [LinearIsometryEquiv.map_smulₛₗ, toDual_grad]
  simp

/-- Each gradient line is the Riesz image of the labelled conormal line `ℝ·du_l` of CLXVII. -/
theorem toDual_grad_mem_conormalLine (i : ι) (x : B) (l : Fin k) :
    ((InnerProductSpace.toDual ℝ E (D.grad i l x) : E →L[ℝ] ℝ) : Dual ℝ E) ∈
      conormalLine (fun l => (D.diff i l x : Dual ℝ E)) l := by
  rw [toDual_grad]
  exact Submodule.mem_span_singleton_self _

/-- **The normal space is the Riesz preimage of the pointwise conormal space** of CLXVII. -/
theorem mem_normal_iff_toDual_mem_conormalOf (i : ι) {x : B} (hx : x ∈ D.baseSet i) (e : E) :
    e ∈ D.normal x ↔
      ((InnerProductSpace.toDual ℝ E e : E →L[ℝ] ℝ) : Dual ℝ E) ∈
        conormalOf (fun l => (D.diff i l x : Dual ℝ E)) := by
  unfold normal conormalOf
  rw [← D.tangent_eq i hx]
  exact mem_orthogonal_iff_toDual_mem_dualAnnihilator _ e

/-- **The frame coordinates are the labelled conormal coordinates**: under Riesz, the gradient frame
is CLXVII's coordinate equivalence `ℝ^k ≃ N^*_pX`, `c ↦ ∑ c_l du_l`. -/
theorem toDual_frame_eq_conormalCoordEquiv (i : ι) {x : B} (hx : x ∈ D.baseSet i)
    (c : EuclideanSpace ℝ (Fin k)) :
    ((InnerProductSpace.toDual ℝ E (D.frame i x c) : E →L[ℝ] ℝ) : Dual ℝ E) =
      (conormalCoordEquiv (fun l => (D.diff i l x : Dual ℝ E))
        ((D.indep i x hx).map' (ContinuousLinearMap.coeLM ℝ) (LinearMap.ker_eq_bot.2
          fun _ _ h => ContinuousLinearMap.coe_injective h)) (WithLp.ofLp c) : Dual ℝ E) := by
  refine Eq.trans ?_ (conormalCoordEquiv_apply _ _ _).symm
  rw [toDual_frame_apply, ContinuousLinearMap.toLinearMap_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [ContinuousLinearMap.toLinearMap_smul]

/-- **The geometric identification hypotheses**: the labelled equations vanish along the map, the
map is injective, and its differential has image the kernel field `⋂ ker du_l`. -/
structure GeometricIdentification : Prop where
  u_zero : ∀ i, ∀ x ∈ D.baseSet i, ∀ l, D.u i l (D.emb x) = 0
  emb_injective : Injective D.emb
  range_mfderiv : ∀ x,
    LinearMap.range (mfderiv IB 𝓘(ℝ, E) D.emb x : TangentSpace IB x →L[ℝ] E).toLinearMap =
      D.tangent x

omit [CompleteSpace E] in
/-- Under the geometric identification the normal field is the orthogonal complement of the image
of the tangent spaces: the paper's normal bundle read through the metric. -/
theorem normal_eq_orthogonal_range_mfderiv (h : D.GeometricIdentification) (x : B) :
    D.normal x =
      (LinearMap.range
        (mfderiv IB 𝓘(ℝ, E) D.emb x : TangentSpace IB x →L[ℝ] E).toLinearMap)ᗮ := by
  unfold normal
  rw [h.range_mfderiv x]
  rfl

end LabelledDefiningEquations

/-- **The scalar overlap law from function-level units**: if `u' = g·u` near `p` with `u(p) = 0` and
`g(p) ≠ 0`, the differentials satisfy `du'(p) = g(p)·du(p)` — the form used by
`LabelledDefiningEquations.unit`. -/
theorem unit_of_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {u u' g : E → ℝ} {p : E}
    (h : ∀ y, u' y = g y * u y) (hg : DifferentiableAt ℝ g p) (hu : DifferentiableAt ℝ u p)
    (hu0 : u p = 0) (hg0 : g p ≠ 0) :
    ∃ a : ℝ, a ≠ 0 ∧ fderiv ℝ u' p = a • fderiv ℝ u p :=
  ⟨g p, hg0, fderiv_unit_mul_eq_smul h hg hu hu0⟩

end Grammar
