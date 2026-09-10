import Grammar.LabelledNormalBundle

/-!
# Global normal sections (Astra #64 unit 13)

The paper's `defn:normal_diff` and `lem:normal_deriv` assert that the normal Taylor forms
`D^r_⊥F(x) ∈ Sym^r(N^*_xX)` "define a global section". Without a symmetric-power bundle we make
this honest as a **compatible family**: for a frame atlas `A` of the normal field (CLXXIV), a family
of symmetric fibre forms `σ x : JetForm (N x) r` is a **global normal section** when its frame
coordinates `pullForm i x (σ x) = σ x ∘ (frame i x, …, frame i x)` are `C^n` on every frame domain
(`IsGlobalNormalSection`).

* the frame pullbacks transform by the transition functions,
  `pullForm j x σ = (pullForm i x σ) ∘ (coordChange j i x, …)` (`pullForm_eq_comp_coordChange`);
* composition with a smooth family of linear maps is smooth (`contMDiffOn_compCLM_family`, from
  Mathlib's analyticity of `(f, g) ↦ g ∘ f`), so smoothness in one frame gives smoothness in every
  other frame on the overlap (`contMDiffOn_pullForm_of_frame`): the predicate can be checked in
  any covering frames (`IsGlobalNormalSection.of_cover`);
* symmetry is frame independent (`isSymmForm_pullForm`), degree zero is the restriction of `F`
  (`pullForm_normalTaylorForm_zero`);
* **the global Taylor-section theorem** (`isGlobalNormalSection_normalTaylorForm`): over a base
  modelled on a normed space, if the frame realisations `G_i(x, v) = F(Φ_x(frame i x v))` are
  jointly `C^∞` and the fibre maps are analytic at `0`, then `x ↦ D^r_⊥F(x)` is a global normal
  section — the "global section" clauses of `defn:normal_diff` and `lem:normal_deriv`, relative to
  the chosen normal family.

Non-claims: no `Sym^r` bundle functor or multilinear-map bundle; no independence from the chosen
fibre maps `Φ` (nonlinear reparametrisations change higher jets).
-/

open scoped Manifold ContDiff
open Bundle Set Function

namespace Grammar

namespace NormalFrameAtlas

variable {B EB HB : Type*} [TopologicalSpace B] [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} [ChartedSpace HB B]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {n : ℕ∞ω} {N : B → Submodule ℝ E} {ι : Type*} (A : NormalFrameAtlas IB V n N ι)

open Classical in
/-- The frame as a map into the normal space (zero outside the frame domain). -/
noncomputable def frameToN (i : ι) (x : B) : V →L[ℝ] N x :=
  if hx : x ∈ A.baseSet i then
    (A.frame i x).codRestrict (N x) fun v => by
      rw [← A.range_frame i x hx]
      exact ⟨v, rfl⟩
  else 0

theorem coe_frameToN (i : ι) {x : B} (hx : x ∈ A.baseSet i) (v : V) :
    ((A.frameToN i x v : N x) : E) = A.frame i x v := by
  unfold frameToN
  rw [dif_pos hx]
  rfl

/-- **Frame change**: `frameToN j = frameToN i ∘ coordChange j i` on the overlap. -/
theorem frameToN_eq (i j : ι) {x : B} (hx : x ∈ A.baseSet i ∩ A.baseSet j) :
    A.frameToN j x = (A.frameToN i x).comp (A.coordChange j i x) := by
  ext v
  rw [ContinuousLinearMap.comp_apply, coe_frameToN _ _ hx.2, coe_frameToN _ _ hx.1]
  exact (A.frame_coordChange j i x ⟨hx.2, hx.1⟩ v).symm

/-- **The frame pullback** of a fibre form. -/
noncomputable def pullForm (i : ι) (x : B) {r : ℕ} (σ : JetForm (N x) r) : JetForm V r :=
  σ.compContinuousLinearMap fun _ => A.frameToN i x

theorem pullForm_apply (i : ι) (x : B) {r : ℕ} (σ : JetForm (N x) r) (v : Fin r → V) :
    A.pullForm i x σ v = σ fun k => A.frameToN i x (v k) := rfl

/-- **Transformation law of the frame coordinates.** -/
theorem pullForm_eq_comp_coordChange (i j : ι) {x : B} (hx : x ∈ A.baseSet i ∩ A.baseSet j) {r : ℕ}
    (σ : JetForm (N x) r) :
    A.pullForm j x σ = (A.pullForm i x σ).compContinuousLinearMap fun _ => A.coordChange j i x := by
  ext v
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply, pullForm_apply, pullForm_apply,
    A.frameToN_eq i j hx]
  rfl

theorem isSymmForm_pullForm (i : ι) (x : B) {r : ℕ} {σ : JetForm (N x) r} (hσ : IsSymmForm σ) :
    IsSymmForm (A.pullForm i x σ) := fun τ v => by
  rw [pullForm_apply, pullForm_apply]
  exact hσ τ fun k => A.frameToN i x (v k)

/-- **Composition with a smooth family of linear maps is smooth** (Mathlib: `(f, g) ↦ g ∘ f` is
polynomial, hence analytic). -/
theorem contMDiffOn_compCLM_family {r : ℕ} {P : B → JetForm V r} {L : B → V →L[ℝ] V} {s : Set B}
    (hP : ContMDiffOn IB 𝓘(ℝ, JetForm V r) n P s) (hL : ContMDiffOn IB 𝓘(ℝ, V →L[ℝ] V) n L s) :
    ContMDiffOn IB 𝓘(ℝ, JetForm V r) n
      (fun x => (P x).compContinuousLinearMap fun _ => L x) s := by
  intro x hx
  have h : ContDiffAt ℝ n (fun p : (Fin r → V →L[ℝ] V) × JetForm V r =>
      p.2.compContinuousLinearMap p.1) ((fun _ => L x), P x) :=
    (ContinuousMultilinearMap.analyticAt_uncurry_compContinuousLinearMap (𝕜 := ℝ)
      (Fm := fun _ : Fin r => V) (Em := fun _ : Fin r => V) (G := ℝ)).contDiffAt
  have hpair : ContMDiffWithinAt IB 𝓘(ℝ, (Fin r → V →L[ℝ] V) × JetForm V r) n
      (fun x => ((fun _ : Fin r => L x), P x)) s x :=
    (contMDiffWithinAt_pi_space.2 fun _ => hL x hx).prodMk_space (hP x hx)
  exact h.comp_contMDiffWithinAt (f := fun x => ((fun _ : Fin r => L x), P x)) (x := x) hpair

/-- **Smoothness in one frame gives smoothness in another** on a subset of the overlap. -/
theorem contMDiffOn_pullForm_of_frame (i j : ι) {r : ℕ} {σ : ∀ x, JetForm (N x) r} {s : Set B}
    (hs : s ⊆ A.baseSet i ∩ A.baseSet j)
    (hi : ContMDiffOn IB 𝓘(ℝ, JetForm V r) n (fun x => A.pullForm i x (σ x)) s) :
    ContMDiffOn IB 𝓘(ℝ, JetForm V r) n (fun x => A.pullForm j x (σ x)) s := by
  refine (contMDiffOn_compCLM_family hi ((A.contMDiffOn_coordChange j i).mono ?_)).congr
    fun x hx => A.pullForm_eq_comp_coordChange i j (hs hx) (σ x)
  intro x hx
  exact ⟨(hs hx).2, (hs hx).1⟩

/-- **A global normal section**: symmetric fibre forms whose frame coordinates are `C^n` on every
frame domain. -/
structure IsGlobalNormalSection (r : ℕ) (σ : ∀ x, JetForm (N x) r) : Prop where
  symm : ∀ x, IsSymmForm (σ x)
  smooth : ∀ i, ContMDiffOn IB 𝓘(ℝ, JetForm V r) n (fun x => A.pullForm i x (σ x)) (A.baseSet i)

/-- **The predicate can be checked in covering frames**: symmetric fibre forms whose coordinates in
some frame are smooth near every point are a global normal section. -/
theorem IsGlobalNormalSection.of_cover {r : ℕ} {σ : ∀ x, JetForm (N x) r}
    (hsymm : ∀ x, IsSymmForm (σ x))
    (hloc : ∀ x, ∃ (j : ι) (s : Set B), IsOpen s ∧ x ∈ s ∧ s ⊆ A.baseSet j ∧
      ContMDiffOn IB 𝓘(ℝ, JetForm V r) n (fun x => A.pullForm j x (σ x)) s) :
    A.IsGlobalNormalSection r σ where
  symm := hsymm
  smooth := by
    intro i x hx
    obtain ⟨j, s, hs, hxs, hsj, hsm⟩ := hloc x
    have h := A.contMDiffOn_pullForm_of_frame j i (s := s ∩ A.baseSet i)
      (fun y hy => ⟨hsj hy.1, hy.2⟩) (hsm.mono inter_subset_left)
    exact (h.contMDiffAt ((hs.inter (A.isOpen_baseSet i)).mem_nhds ⟨hxs, hx⟩)).contMDiffWithinAt

variable {M : Type*} (Φ : ∀ x, N x → M) (F : M → ℝ)

/-- Degree zero: the frame coordinates of `D^0_⊥F` are the restriction of `F` to the base. -/
theorem pullForm_normalTaylorForm_zero (i : ι) (x : B) (v : Fin 0 → V) :
    A.pullForm i x (normalTaylorForm N Φ F x 0) v = F (Φ x 0) := by
  rw [pullForm_apply, normalTaylorForm_zero_apply]

end NormalFrameAtlas

/-! ### The global Taylor-section theorem over a base modelled on a normed space -/

section TaylorSection

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {N : EB → Submodule ℝ E} {ι : Type*} (A : NormalFrameAtlas 𝓘(ℝ, EB) V ∞ N ι)
  {M : Type*} (Φ : ∀ x, N x → M) (F : M → ℝ)

namespace NormalFrameAtlas

/-- The frame as a continuous linear equivalence `V ≃L N x` on its domain. -/
noncomputable def frameEquiv (i : ι) {x : EB} (hx : x ∈ A.baseSet i) : V ≃L[ℝ] N x :=
  (LinearEquiv.ofBijective (A.frameToN i x : V →ₗ[ℝ] N x) ⟨fun v w h => by
      apply A.frame_injective i x hx
      rw [← A.coe_frameToN i hx, ← A.coe_frameToN i hx]
      exact congrArg Subtype.val h,
    fun ⟨e, he⟩ => by
      rw [← A.range_frame i x hx] at he
      obtain ⟨v, hv⟩ := he
      exact ⟨v, Subtype.ext ((A.coe_frameToN i hx v).trans hv)⟩⟩).toContinuousLinearEquiv

theorem coe_frameEquiv (i : ι) {x : EB} (hx : x ∈ A.baseSet i) :
    (A.frameEquiv i hx : V →L[ℝ] N x) = A.frameToN i x := by
  ext v
  rfl

/-- **The frame coordinates of the normal Taylor form** are the Taylor forms of the frame
realisation `v ↦ F(Φ_x(frame i x v))` (unconditionally, CLXXII). -/
theorem pullForm_normalTaylorForm (i : ι) {x : EB} (hx : x ∈ A.baseSet i) (r : ℕ) :
    A.pullForm i x (normalTaylorForm N Φ F x r) =
      (r.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ r (fun v : V => F (Φ x (A.frameToN i x v))) 0 := by
  have h := normalTaylorForm_comp_equiv N Φ F x (A.frameEquiv i hx) r
  rw [coe_frameEquiv] at h
  simp only [show ∀ v, A.frameEquiv i hx v = A.frameToN i x v from fun v => rfl] at h
  exact h.symm

/-- **The global Taylor-section theorem**: if the frame realisations
`G_i(x,v) = F(Φ_x(frame i x v))` are jointly `C^∞` and the fibre maps are analytic at `0`, then
`x ↦ D^r_⊥F(x)` is a global normal section (the "global section" clauses of `defn:normal_diff` and
`lem:normal_deriv`). -/
theorem isGlobalNormalSection_normalTaylorForm
    (hG : ∀ i, ContDiff ℝ ∞ fun p : EB × V => F (Φ p.1 (A.frameToN i p.1 p.2)))
    (hΦ : ∀ x, ContDiffAt ℝ ω (fun n : N x => F (Φ x n)) 0) (r : ℕ) :
    A.IsGlobalNormalSection r fun x => normalTaylorForm N Φ F x r where
  symm := fun x => by
    have h := isSymmForm_normalJet (r := r) (hΦ x)
    intro τ v
    unfold normalTaylorForm
    rw [smul_apply, smul_apply, rawNormalJet_eq_normalJet, h τ v]
  smooth := by
    intro i
    have h := contDiff_normalTaylorCoeff (hG i) r
    refine ((contMDiff_iff_contDiff.2 h).contMDiffOn).congr fun x hx => ?_
    exact A.pullForm_normalTaylorForm Φ F i hx r

end NormalFrameAtlas

end TaylorSection

end Grammar
