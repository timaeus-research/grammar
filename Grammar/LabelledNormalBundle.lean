import Grammar.FrameAtlasOfCoframes
import Grammar.ConormalSplitting

/-!
# The normal bundle of labelled defining equations (Astra #64 units 11–12)

The paper's strata are cut out by labelled defining equations `u₁, …, u_k` with `du_i` spanning the
conormal space, and different equations differ by units on overlaps. We realise this over an
**embedded base**: a manifold `B` with a smooth map `emb : B → E` into a finite-dimensional inner
product space, and on an open cover of `B` labelled equations `u i l : E → ℝ` whose differentials
along `emb` are independent and related on overlaps by nonzero scalars (`LabelledDefiningEquations`;
the scalar law follows from `u' = g·u` on the zero set, `fderiv_unit_mul_eq_smul`):

* the **tangent field** `T x = ⋂ ker du_l(emb x)` is chart independent (`tangent_eq`, from
  `tangentOf_smul` of CLXVII) and the **normal field** is `N x = (T x)ᗮ` (`normal`);
* the **gradient frames** `frame i x c = ∑ c_l ∇u_l(emb x)` (Riesz gradients `grad`) are smooth,
  injective, with range `N x` (`range_frame`, from `orthogonal_tangentOf_toDual` of CLXVII), so with
  the Moore–Penrose coframes of CLXXV they form a `NormalFrameAtlas` (`normalAtlas`) and hence a
  **`C^∞` normal bundle with fibre `ℝ^k`** (`contMDiffVectorBundle`) whose realisation lands in
  `N x` (CLXXIV);
* **the labelled lines are canonical (`eq:decomp_nx` at bundle level)**: the transition functions
  are diagonal in the labels, `coordChange i j x c = (a_l⁻¹ c_l)_l` where `du^j_l = a_l du^i_l`
  (`coordChange_diagonal`), so each coordinate line `ℝ e_l` is preserved
  (`coordChange_single`): the normal bundle is the direct sum of the labelled line bundles
  `𝓛_l`, and the dual lines `ℝ·du_l` split the conormal bundle.

Non-claims: the base manifold `B` and the embedding are inputs (no implicit-function construction of
the manifold structure on a level set); the normal bundle is realised through the metric as
`(TX)ᗮ`, its dual being the conormal bundle; no quotient bundle.
-/

open scoped Manifold ContDiff InnerProductSpace
open Bundle Set Function Module

namespace Grammar

section Riesz

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The Riesz isomorphism `E* → E` as a real continuous linear map. -/
noncomputable def rieszCLM : (E →L[ℝ] ℝ) →L[ℝ] E :=
  { toFun := (InnerProductSpace.toDual ℝ E).symm
    map_add' := fun f g => map_add _ f g
    map_smul' := fun c f => by
      rw [LinearIsometryEquiv.map_smulₛₗ]
      simp
    cont := (InnerProductSpace.toDual ℝ E).symm.continuous }

@[simp] theorem rieszCLM_apply (f : E →L[ℝ] ℝ) :
    rieszCLM f = (InnerProductSpace.toDual ℝ E).symm f := rfl

theorem toDual_rieszCLM (f : E →L[ℝ] ℝ) : InnerProductSpace.toDual ℝ E (rieszCLM f) = f :=
  (InnerProductSpace.toDual ℝ E).apply_symm_apply f

theorem rieszCLM_injective : Injective (rieszCLM : (E →L[ℝ] ℝ) → E) :=
  (InnerProductSpace.toDual ℝ E).symm.injective

end Riesz

/-- Injectivity of the linear-combination map of an independent family. -/
theorem injective_sum_smul_of_linearIndependent {k : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]
    {w : Fin k → E} (hw : LinearIndependent ℝ w) :
    Injective fun c : Fin k → ℝ => ∑ l, c l • w l := by
  intro c c' h
  have h0 : ∑ l, (c l - c' l) • w l = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib]
    exact sub_eq_zero.2 h
  funext l
  exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hw _ h0 l)

section Labelled

variable {EB HB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]

/-- **Labelled defining equations of an embedded base**: a smooth map `emb : B → E`, and on an open
cover labelled equations `u i l : E → ℝ` with independent differentials along `emb`, related on
overlaps by nonzero scalars (the differential form of `u^j_l = g_l u^i_l` on the zero set). -/
structure LabelledDefiningEquations (IB : ModelWithCorners ℝ EB HB) (B : Type*) [TopologicalSpace B]
    [ChartedSpace HB B] (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (k : ℕ)
    (ι : Type*) where
  emb : B → E
  contMDiff_emb : ContMDiff IB 𝓘(ℝ, E) ∞ emb
  baseSet : ι → Set B
  isOpen_baseSet : ∀ i, IsOpen (baseSet i)
  indexAt : B → ι
  mem_baseSet_at : ∀ x, x ∈ baseSet (indexAt x)
  u : ι → Fin k → E → ℝ
  contDiff_u : ∀ i l, ContDiff ℝ ∞ (u i l)
  indep : ∀ i, ∀ x ∈ baseSet i, LinearIndependent ℝ fun l => fderiv ℝ (u i l) (emb x)
  unit : ∀ i j, ∀ x ∈ baseSet i ∩ baseSet j, ∀ l,
    ∃ a : ℝ, a ≠ 0 ∧ fderiv ℝ (u j l) (emb x) = a • fderiv ℝ (u i l) (emb x)

/-- The differential form of a unit change of defining equation: on the zero set of `u`,
`d(g·u) = g · du`. -/
theorem fderiv_unit_mul_eq_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u u' g : E → ℝ} {p : E} (h : ∀ y, u' y = g y * u y)
    (hg : DifferentiableAt ℝ g p) (hu : DifferentiableAt ℝ u p) (hu0 : u p = 0) :
    fderiv ℝ u' p = g p • fderiv ℝ u p := by
  have : u' = fun y => g y * u y := funext h
  rw [this]
  exact fderiv_mul_of_eq_zero hg hu hu0

namespace LabelledDefiningEquations

variable {IB : ModelWithCorners ℝ EB HB} {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {k : ℕ} {ι : Type*} (D : LabelledDefiningEquations IB B E k ι)

/-- The differential `du^i_l` along the embedding. -/
noncomputable def diff (i : ι) (l : Fin k) (x : B) : E →L[ℝ] ℝ := fderiv ℝ (D.u i l) (D.emb x)

/-- The Riesz gradient `∇u^i_l`. -/
noncomputable def grad (i : ι) (l : Fin k) (x : B) : E := rieszCLM (D.diff i l x)

theorem toDual_grad (i : ι) (l : Fin k) (x : B) :
    InnerProductSpace.toDual ℝ E (D.grad i l x) = D.diff i l x :=
  toDual_rieszCLM _

/-- **The tangent field** `T x = ⋂ ker du_l(emb x)`, computed in the chosen chart. -/
noncomputable def tangent (x : B) : Submodule ℝ E :=
  tangentOf fun l => (D.diff (D.indexAt x) l x : Dual ℝ E)

omit [CompleteSpace E] in
/-- **Chart independence of the tangent field.** -/
theorem tangent_eq (i : ι) {x : B} (hx : x ∈ D.baseSet i) :
    tangentOf (fun l => (D.diff i l x : Dual ℝ E)) = D.tangent x := by
  choose a ha using D.unit (D.indexAt x) i x ⟨D.mem_baseSet_at x, hx⟩
  have h : (fun l => (D.diff i l x : Dual ℝ E)) =
      fun l => a l • (D.diff (D.indexAt x) l x : Dual ℝ E) := by
    funext l
    unfold diff
    rw [(ha l).2, ContinuousLinearMap.toLinearMap_smul]
  rw [h]
  exact tangentOf_smul _ a fun l => (ha l).1

/-- **The normal field** `N x = (T x)ᗮ`. -/
noncomputable def normal (x : B) : Submodule ℝ E := (D.tangent x)ᗮ

/-- **The gradient frame** `c ↦ ∑ c_l ∇u^i_l(emb x)`. -/
noncomputable def frame (i : ι) (x : B) : EuclideanSpace ℝ (Fin k) →L[ℝ] E :=
  ∑ l, ContinuousLinearMap.smulRightL ℝ (EuclideanSpace ℝ (Fin k)) E (EuclideanSpace.proj l)
    (D.grad i l x)

theorem frame_apply (i : ι) (x : B) (c : EuclideanSpace ℝ (Fin k)) :
    D.frame i x c = ∑ l, c l • D.grad i l x := by
  simp [frame, sum_apply]

theorem linearIndependent_grad (i : ι) {x : B} (hx : x ∈ D.baseSet i) :
    LinearIndependent ℝ fun l => D.grad i l x := by
  rw [Fintype.linearIndependent_iff]
  intro g hg l
  have h := congrArg (InnerProductSpace.toDual ℝ E) hg
  rw [map_sum, map_zero] at h
  simp only [LinearIsometryEquiv.map_smulₛₗ, starRingEnd_apply, star_trivial, toDual_grad] at h
  exact Fintype.linearIndependent_iff.1 (D.indep i x hx) g h l

theorem frame_injective (i : ι) {x : B} (hx : x ∈ D.baseSet i) : Injective (D.frame i x) := by
  intro c c' h
  rw [frame_apply, frame_apply] at h
  exact WithLp.ofLp_injective 2
    (injective_sum_smul_of_linearIndependent (D.linearIndependent_grad i hx) h)

/-- **The range of the gradient frame is the normal space.** -/
theorem range_frame [FiniteDimensional ℝ E] (i : ι) {x : B} (hx : x ∈ D.baseSet i) :
    LinearMap.range (D.frame i x : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] E) = D.normal x := by
  have h1 : LinearMap.range (D.frame i x : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] E) =
      Submodule.span ℝ (Set.range fun l => D.grad i l x) := by
    refine le_antisymm ?_ (Submodule.span_le.2 ?_)
    · rintro _ ⟨c, rfl⟩
      rw [ContinuousLinearMap.coe_coe, frame_apply]
      exact Submodule.sum_mem _ fun l _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
    · rintro _ ⟨l, rfl⟩
      refine ⟨EuclideanSpace.single l 1, ?_⟩
      rw [ContinuousLinearMap.coe_coe, frame_apply]
      simp
  rw [h1, ← orthogonal_tangentOf_toDual (fun l => D.grad i l x)]
  unfold normal
  congr 1
  rw [← D.tangent_eq i hx]
  congr 1
  funext l
  rw [D.toDual_grad]

theorem contMDiff_grad (i : ι) (l : Fin k) : ContMDiff IB 𝓘(ℝ, E) ∞ fun x => D.grad i l x :=
  ((rieszCLM (E := E)).contDiff.comp ((D.contDiff_u i l).fderiv_right (by simp))).contMDiff.comp
    D.contMDiff_emb

theorem contMDiff_frame (i : ι) :
    ContMDiff IB 𝓘(ℝ, EuclideanSpace ℝ (Fin k) →L[ℝ] E) ∞ (D.frame i) :=
  ContMDiff.sum fun l _ =>
    ((ContinuousLinearMap.smulRightL ℝ (EuclideanSpace ℝ (Fin k)) E
      (EuclideanSpace.proj l)).contDiff.contMDiff).comp (D.contMDiff_grad i l)

variable [FiniteDimensional ℝ E]

/-- **The normal frame atlas** of the labelled equations (Moore–Penrose coframes). -/
noncomputable def frameCoframeData : FrameCoframeData IB (EuclideanSpace ℝ (Fin k)) ∞ D.normal ι :=
  frameCoframeDataOfFrames (EuclideanSpace ℝ (Fin k)) IB D.baseSet D.isOpen_baseSet D.indexAt
    D.mem_baseSet_at D.frame (fun i _ hx => D.frame_injective i hx)
    (fun i _ hx => D.range_frame i hx) (fun i => (D.contMDiff_frame i).contMDiffOn)

/-- **The normal bundle of the labelled equations** as a frame atlas. -/
noncomputable def normalAtlas : NormalFrameAtlas IB (EuclideanSpace ℝ (Fin k)) ∞ D.normal ι :=
  D.frameCoframeData.toAtlas

/-- **The normal bundle is a `C^∞` vector bundle with fibre `ℝ^k`.** -/
theorem contMDiffVectorBundle :
    ContMDiffVectorBundle ∞ (EuclideanSpace ℝ (Fin k)) D.normalAtlas.toCore.Fiber IB :=
  D.normalAtlas.contMDiffVectorBundle

theorem normalAtlas_frame (i : ι) (x : B) : D.normalAtlas.frame i x = D.frame i x := rfl

theorem normalAtlas_coordChange (i j : ι) (x : B) :
    D.normalAtlas.coordChange i j x = pinv (D.frame j x) ∘L D.frame i x := rfl

/-- **The transition functions are diagonal in the labels** (`eq:decomp_nx` at bundle level): if
`du^j_l = a_l du^i_l` on the overlap then `coordChange i j x c = (a_l⁻¹ c_l)_l`. -/
theorem coordChange_diagonal (i j : ι) {x : B} (hx : x ∈ D.baseSet i ∩ D.baseSet j) :
    ∃ a : Fin k → ℝ, (∀ l, a l ≠ 0) ∧ ∀ c : EuclideanSpace ℝ (Fin k),
      D.normalAtlas.coordChange i j x c = WithLp.toLp 2 fun l => (a l)⁻¹ * c l := by
  choose a ha using D.unit i j x hx
  refine ⟨a, fun l => (ha l).1, fun c => ?_⟩
  have hgrad : ∀ l, D.grad i l x = (a l)⁻¹ • D.grad j l x := by
    intro l
    unfold grad diff
    rw [(ha l).2, map_smul, smul_smul, inv_mul_cancel₀ (ha l).1, one_smul]
  have hframe : D.frame i x c = D.frame j x (WithLp.toLp 2 fun l => (a l)⁻¹ * c l) := by
    rw [frame_apply, frame_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hgrad l, smul_smul]
    simp [mul_comm]
  rw [normalAtlas_coordChange, ContinuousLinearMap.comp_apply, hframe]
  exact pinv_apply (D.frame_injective j hx.2) _

/-- **Each labelled coordinate line is preserved** by the transition functions. -/
theorem coordChange_single (i j : ι) {x : B} (hx : x ∈ D.baseSet i ∩ D.baseSet j) (l : Fin k)
    (t : ℝ) :
    ∃ a : ℝ, a ≠ 0 ∧
      D.normalAtlas.coordChange i j x (EuclideanSpace.single l t) =
        EuclideanSpace.single l (a * t) := by
  obtain ⟨a, ha, h⟩ := D.coordChange_diagonal i j hx
  refine ⟨(a l)⁻¹, inv_ne_zero (ha l), ?_⟩
  rw [h]
  ext m
  by_cases hm : m = l
  · subst hm
    simp
  · simp [hm]

end LabelledDefiningEquations

end Labelled

end Grammar
