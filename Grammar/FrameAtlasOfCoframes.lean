import Grammar.NormalBundleOfFrames

/-!
# Frame atlases from frames and coframes (Astra #64 unit 10)

The transition functions of a `NormalFrameAtlas` need not be supplied: they are determined by the
frames once each frame has a smooth **left inverse** (a coframe). Two constructors:

* **frames with coframes** (`FrameCoframeData`, `NormalFrameAtlas.ofCoframes`): frames
  `frame i x : V →L E` onto `N x` together with `C^n` coframes `coframe i x : E →L V` satisfying
  `coframe i x ∘ frame i x = 1`; the transition functions are `coframe j x ∘ frame i x`, smooth by
  composition, and the frame identity holds because `frame i x v ∈ N x = range (frame j x)`
  (`coframe_frame_of_mem_range`). Jacobian frames `Jᵀ` with coframes `(JJᵀ)⁻¹J`, and dual frames of
  differentials, are instances;
* **frames alone over inner product spaces** (`NormalFrameAtlas.ofFrames`): the coframe is the
  Moore–Penrose left inverse `(f†f)⁻¹ f†` (`pinv`), which is a left inverse of any injective `f`
  (`pinv_apply`) and depends `C^n` on `f` through the frame (`contMDiffOn_pinv`: the adjoint is a
  continuous linear map on operators and the inverse is smooth on the group of units,
  `contDiffAt_map_inverse`).

Non-claims: no subbundle/quotient framework; the base is any manifold and the frames are data.
-/

open scoped Manifold ContDiff InnerProductSpace
open Bundle Set Function

namespace Grammar

section Coframes

variable {B EB HB : Type*} [TopologicalSpace B] [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [TopologicalSpace HB] (IB : ModelWithCorners ℝ EB HB) [ChartedSpace HB B]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **Frames with coframes**: local frames `frame i x : V →L E` onto `N x` with `C^n` left inverses
`coframe i x`. -/
structure FrameCoframeData (n : ℕ∞ω) (N : B → Submodule ℝ E) (ι : Type*) where
  baseSet : ι → Set B
  isOpen_baseSet : ∀ i, IsOpen (baseSet i)
  indexAt : B → ι
  mem_baseSet_at : ∀ x, x ∈ baseSet (indexAt x)
  frame : ι → B → V →L[ℝ] E
  range_frame : ∀ i, ∀ x ∈ baseSet i, LinearMap.range (frame i x : V →ₗ[ℝ] E) = N x
  contMDiffOn_frame : ∀ i, ContMDiffOn IB 𝓘(ℝ, V →L[ℝ] E) n (frame i) (baseSet i)
  coframe : ι → B → E →L[ℝ] V
  coframe_frame : ∀ i, ∀ x ∈ baseSet i, ∀ v, coframe i x (frame i x v) = v
  contMDiffOn_coframe : ∀ i, ContMDiffOn IB 𝓘(ℝ, E →L[ℝ] V) n (coframe i) (baseSet i)

namespace FrameCoframeData

variable {IB V} {n : ℕ∞ω} {N : B → Submodule ℝ E} {ι : Type*} (D : FrameCoframeData IB V n N ι)

theorem frame_injective (i : ι) {x : B} (hx : x ∈ D.baseSet i) : Injective (D.frame i x) :=
  fun v w h => by rw [← D.coframe_frame i x hx v, h, D.coframe_frame i x hx w]

/-- `frame ∘ coframe` is the identity on the range of the frame. -/
theorem frame_coframe_of_mem_range (i : ι) {x : B} (hx : x ∈ D.baseSet i) {e : E}
    (he : e ∈ LinearMap.range (D.frame i x : V →ₗ[ℝ] E)) :
    D.frame i x (D.coframe i x e) = e := by
  obtain ⟨v, rfl⟩ := he
  rw [ContinuousLinearMap.coe_coe, D.coframe_frame i x hx v]

/-- **The frame atlas** with transition functions `coframe j x ∘ frame i x`. -/
def toAtlas : NormalFrameAtlas IB V n N ι where
  baseSet := D.baseSet
  isOpen_baseSet := D.isOpen_baseSet
  indexAt := D.indexAt
  mem_baseSet_at := D.mem_baseSet_at
  frame := D.frame
  frame_injective := fun i x hx => D.frame_injective i hx
  range_frame := D.range_frame
  contMDiffOn_frame := D.contMDiffOn_frame
  coordChange := fun i j x => D.coframe j x ∘L D.frame i x
  frame_coordChange := fun i j x hx v => by
    rw [ContinuousLinearMap.comp_apply]
    refine D.frame_coframe_of_mem_range j hx.2 ?_
    rw [D.range_frame j x hx.2, ← D.range_frame i x hx.1]
    exact ⟨v, rfl⟩
  contMDiffOn_coordChange := fun i j =>
    ((D.contMDiffOn_coframe j).mono inter_subset_right).clm_comp
      ((D.contMDiffOn_frame i).mono inter_subset_left)

theorem toAtlas_coordChange (i j : ι) (x : B) :
    D.toAtlas.coordChange i j x = D.coframe j x ∘L D.frame i x := rfl

end FrameCoframeData

end Coframes

/-! ### Moore–Penrose coframes over inner product spaces -/

section Pinv

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [FiniteDimensional ℝ V]

/-- The adjoint as a real continuous linear map on operators. -/
noncomputable def adjointCLM : (V →L[ℝ] E) →L[ℝ] (E →L[ℝ] V) :=
  { toFun := fun f => ContinuousLinearMap.adjoint f
    map_add' := fun f g => map_add _ f g
    map_smul' := fun c f => by
      simp only [map_smul, RingHom.id_apply]
    cont := (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := V) (F := E)).continuous }

omit [FiniteDimensional ℝ V] in
@[simp] theorem adjointCLM_apply (f : V →L[ℝ] E) :
    adjointCLM f = ContinuousLinearMap.adjoint f := rfl

/-- The Gram operator `f†f`. -/
noncomputable def gram (f : V →L[ℝ] E) : V →L[ℝ] V := ContinuousLinearMap.adjoint f ∘L f

omit [FiniteDimensional ℝ V] in
theorem gram_injective {f : V →L[ℝ] E} (hf : Injective f) : Injective (gram f) := by
  intro v w h
  have h1 : ∀ z, ⟪f v - f w, f z⟫_ℝ = 0 := by
    intro z
    have := congrArg (fun y => ⟪y, z⟫_ℝ) h
    simp only [gram, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left]
      at this
    rw [inner_sub_left, this, sub_self]
  have := h1 (v - w)
  rw [map_sub] at this
  exact hf (sub_eq_zero.1 (inner_self_eq_zero.1 this))

/-- The Gram operator of an injective map is a continuous linear automorphism. -/
noncomputable def gramEquiv (f : V →L[ℝ] E) (hf : Injective f) : V ≃L[ℝ] V :=
  ContinuousLinearEquiv.ofBijective (gram f) (LinearMap.ker_eq_bot.2 (gram_injective hf))
    (LinearMap.range_eq_top.2
      ((LinearMap.injective_iff_surjective (f := (gram f : V →ₗ[ℝ] V))).1 (gram_injective hf)))

theorem coe_gramEquiv (f : V →L[ℝ] E) (hf : Injective f) : (gramEquiv f hf : V →L[ℝ] V) = gram f :=
  rfl

/-- **The Moore–Penrose left inverse** `(f†f)⁻¹ f†`. -/
noncomputable def pinv (f : V →L[ℝ] E) : E →L[ℝ] V :=
  (gram f).inverse ∘L ContinuousLinearMap.adjoint f

theorem pinv_apply {f : V →L[ℝ] E} (hf : Injective f) (v : V) : pinv f (f v) = v := by
  unfold pinv
  rw [← coe_gramEquiv f hf, ContinuousLinearMap.inverse_equiv, ContinuousLinearMap.comp_apply]
  have : ContinuousLinearMap.adjoint f (f v) = gramEquiv f hf v := rfl
  rw [this]
  exact (gramEquiv f hf).symm_apply_apply v

variable {B EB HB : Type*} [TopologicalSpace B] [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} [ChartedSpace HB B] {n : ℕ∞ω}

/-- **Smoothness of the Moore–Penrose coframe** in a smooth family of injective frames. -/
theorem contMDiffOn_pinv {f : B → V →L[ℝ] E} {s : Set B}
    (hf : ContMDiffOn IB 𝓘(ℝ, V →L[ℝ] E) n f s) (hinj : ∀ x ∈ s, Injective (f x)) :
    ContMDiffOn IB 𝓘(ℝ, E →L[ℝ] V) n (fun x => pinv (f x)) s := by
  have hadj : ContMDiffOn IB 𝓘(ℝ, E →L[ℝ] V) n (fun x => ContinuousLinearMap.adjoint (f x)) s :=
    fun x hx => (adjointCLM.contDiff.contDiffAt).comp_contMDiffWithinAt (hf x hx)
  have hgram : ContMDiffOn IB 𝓘(ℝ, V →L[ℝ] V) n (fun x => gram (f x)) s := hadj.clm_comp hf
  have hinv : ContMDiffOn IB 𝓘(ℝ, V →L[ℝ] V) n (fun x => (gram (f x)).inverse) s := by
    intro x hx
    have h : ContDiffAt ℝ n (ContinuousLinearMap.inverse : (V →L[ℝ] V) → (V →L[ℝ] V))
        (gram (f x)) := by
      have := contDiffAt_map_inverse (n := n) (gramEquiv (f x) (hinj x hx))
      rwa [coe_gramEquiv] at this
    exact ContDiffAt.comp_contMDiffWithinAt (f := fun x => gram (f x)) (x := x) h (hgram x hx)
  exact hinv.clm_comp hadj

variable (IB V)

/-- **Frames alone** (over inner product spaces) determine the atlas: the coframes are the
Moore–Penrose left inverses. -/
noncomputable def frameCoframeDataOfFrames {N : B → Submodule ℝ E} {ι : Type*} (baseSet : ι → Set B)
    (isOpen_baseSet : ∀ i, IsOpen (baseSet i)) (indexAt : B → ι)
    (mem_baseSet_at : ∀ x, x ∈ baseSet (indexAt x)) (frame : ι → B → V →L[ℝ] E)
    (frame_injective : ∀ i, ∀ x ∈ baseSet i, Injective (frame i x))
    (range_frame : ∀ i, ∀ x ∈ baseSet i, LinearMap.range (frame i x : V →ₗ[ℝ] E) = N x)
    (contMDiffOn_frame : ∀ i, ContMDiffOn IB 𝓘(ℝ, V →L[ℝ] E) n (frame i) (baseSet i)) :
    FrameCoframeData IB V n N ι where
  baseSet := baseSet
  isOpen_baseSet := isOpen_baseSet
  indexAt := indexAt
  mem_baseSet_at := mem_baseSet_at
  frame := frame
  range_frame := range_frame
  contMDiffOn_frame := contMDiffOn_frame
  coframe := fun i x => pinv (frame i x)
  coframe_frame := fun i x hx v => pinv_apply (frame_injective i x hx) v
  contMDiffOn_coframe := fun i => contMDiffOn_pinv (contMDiffOn_frame i) (frame_injective i)

end Pinv

end Grammar
