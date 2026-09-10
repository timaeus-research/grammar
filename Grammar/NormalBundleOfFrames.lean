import Grammar.StrucDualNormalFamily
import Mathlib.Geometry.Manifold.VectorBundle.Basic

/-!
# The normal bundle from local frames (Astra #64 unit 9)

Mathlib has no quotient bundles, so the normal bundle of the paper's strata is built here from
**construction data**: a family of subspaces `N x ⊆ E` of a fixed normed space over a manifold `B`,
covered by local **frames** `frame i x : V ≃ N x` (injective continuous linear maps `V →L E` with
range `N x`) whose transition functions `coordChange i j x = (frame i x)⁻¹ ∘ frame j x` are `C^n`
(`NormalFrameAtlas`, Mathlib's convention: `coordChange i j x` carries frame-`i` coordinates to
frame-`j` coordinates, `frame j x (coordChange i j x v) = frame i x v`). The transition functions
then satisfy the cocycle laws automatically
(`coordChange_self`, `coordChange_comp`), so they define a `VectorBundleCore` (`toCore`) whose
total space `Bundle.TotalSpace V A.toCore.Fiber` is a `C^n` vector bundle over `B` by Mathlib's
`VectorBundleCore.instContMDiffVectorBundle` (`contMDiffVectorBundle`), and a `C^n` manifold.

The **ambient realisation** `realise ⟨x, v⟩ = frame (indexAt x) x v` identifies the abstract fibre
with `N x` (`realise_mem`, `realise_injective_fibre`, `fibreEquiv : Fiber x ≃ₗ N x`), agrees with
every frame in its domain (`realise_eq_frame`), and is a `C^n` map on the total space
(`contMDiff_realise`): the fibre inclusion `NX ↪ B × E` as a smooth fibrewise-linear bundle map.
Sections are `C^n` iff their frame coordinates are (`contMDiffAt_section_iff_coord`).

Non-claims: no general subbundle or quotient-bundle framework — bundles of subspaces of a fixed
finite-dimensional `E` only; the frames and the smoothness of their transition functions are data
(units 10–11 supply them for embedded submanifolds and analytic LCI atlases).
-/

open scoped Manifold ContDiff Bundle
open Bundle Set

namespace Grammar

variable {B : Type*} [TopologicalSpace B] {EB HB : Type*} [NormedAddCommGroup EB]
  [NormedSpace ℝ EB] [TopologicalSpace HB] (IB : ModelWithCorners ℝ EB HB) [ChartedSpace HB B]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **A smooth frame atlas** for a family of subspaces `N x ⊆ E`: local frames `frame i x : V →L E`
onto `N x` on an open cover, with `C^n` transition functions `coordChange i j x`, characterised by
`frame j x (coordChange i j x v) = frame i x v`. -/
structure NormalFrameAtlas (n : ℕ∞ω) (N : B → Submodule ℝ E) (ι : Type*) where
  /-- the frame domains -/
  baseSet : ι → Set B
  isOpen_baseSet : ∀ i, IsOpen (baseSet i)
  /-- a chosen frame at every point -/
  indexAt : B → ι
  mem_baseSet_at : ∀ x, x ∈ baseSet (indexAt x)
  /-- the frames -/
  frame : ι → B → V →L[ℝ] E
  frame_injective : ∀ i, ∀ x ∈ baseSet i, Function.Injective (frame i x)
  range_frame : ∀ i, ∀ x ∈ baseSet i, LinearMap.range (frame i x : V →ₗ[ℝ] E) = N x
  contMDiffOn_frame : ∀ i, ContMDiffOn IB 𝓘(ℝ, V →L[ℝ] E) n (frame i) (baseSet i)
  /-- the transition functions `(frame j x)⁻¹ ∘ frame i x` (frame-`i` to frame-`j` coordinates) -/
  coordChange : ι → ι → B → V →L[ℝ] V
  frame_coordChange : ∀ i j, ∀ x ∈ baseSet i ∩ baseSet j, ∀ v,
    frame j x (coordChange i j x v) = frame i x v
  contMDiffOn_coordChange : ∀ i j,
    ContMDiffOn IB 𝓘(ℝ, V →L[ℝ] V) n (coordChange i j) (baseSet i ∩ baseSet j)

namespace NormalFrameAtlas

variable {IB V} {n : ℕ∞ω} {N : B → Submodule ℝ E} {ι : Type*} (A : NormalFrameAtlas IB V n N ι)

/-- The cocycle identity `t_ii = 1`. -/
theorem coordChange_self (i : ι) {x : B} (hx : x ∈ A.baseSet i) (v : V) :
    A.coordChange i i x v = v :=
  A.frame_injective i x hx (A.frame_coordChange i i x ⟨hx, hx⟩ v)

/-- The cocycle identity `t_jk ∘ t_ij = t_ik`. -/
theorem coordChange_comp (i j k : ι) {x : B} (hx : x ∈ A.baseSet i ∩ A.baseSet j ∩ A.baseSet k)
    (v : V) : A.coordChange j k x (A.coordChange i j x v) = A.coordChange i k x v :=
  A.frame_injective k x hx.2 (by
    rw [A.frame_coordChange j k x ⟨hx.1.2, hx.2⟩, A.frame_coordChange i j x hx.1,
      A.frame_coordChange i k x ⟨hx.1.1, hx.2⟩])

/-- **The vector bundle core** of the frame atlas. -/
def toCore : VectorBundleCore ℝ B V ι where
  baseSet := A.baseSet
  isOpen_baseSet := A.isOpen_baseSet
  indexAt := A.indexAt
  mem_baseSet_at := A.mem_baseSet_at
  coordChange := A.coordChange
  coordChange_self := fun i _ hx v => A.coordChange_self i hx v
  continuousOn_coordChange := fun i j => (A.contMDiffOn_coordChange i j).continuousOn
  coordChange_comp := fun i j k _ hx v => A.coordChange_comp i j k hx v

instance isContMDiff : A.toCore.IsContMDiff IB n := ⟨A.contMDiffOn_coordChange⟩

/-- **The normal bundle is a `C^n` vector bundle** (Mathlib's core construction). -/
theorem contMDiffVectorBundle : ContMDiffVectorBundle n V A.toCore.Fiber IB := inferInstance

/-- **The ambient realisation** of a fibre element through the chosen frame at its base point. -/
def realise (p : TotalSpace V A.toCore.Fiber) : E := A.frame (A.indexAt p.1) p.1 p.2

theorem realise_mk (x : B) (v : A.toCore.Fiber x) :
    A.realise ⟨x, v⟩ = A.frame (A.indexAt x) x v := rfl

/-- The realisation agrees with every frame on its domain, read through the local trivialisation. -/
theorem realise_eq_frame (i : ι) (p : TotalSpace V A.toCore.Fiber) (hp : p.1 ∈ A.baseSet i) :
    A.realise p = A.frame i p.1 (A.toCore.localTriv i p).2 := by
  rw [VectorBundleCore.localTriv_apply]
  exact (A.frame_coordChange (A.indexAt p.1) i p.1 ⟨A.mem_baseSet_at _, hp⟩ p.2).symm

theorem realise_mem (p : TotalSpace V A.toCore.Fiber) : A.realise p ∈ N p.1 := by
  rw [← A.range_frame _ _ (A.mem_baseSet_at p.1)]
  exact ⟨p.2, rfl⟩

theorem realise_injective_fibre (x : B) :
    Function.Injective fun v : A.toCore.Fiber x => A.realise ⟨x, v⟩ :=
  A.frame_injective _ x (A.mem_baseSet_at x)

theorem range_realise_fibre (x : B) :
    LinearMap.range (A.frame (A.indexAt x) x : V →ₗ[ℝ] E) = N x :=
  A.range_frame _ x (A.mem_baseSet_at x)

/-- **The fibre is the normal space**: `Fiber x ≃ₗ N x` through the realisation. -/
noncomputable def fibreEquiv (x : B) : A.toCore.Fiber x ≃ₗ[ℝ] N x :=
  (LinearEquiv.ofInjective (A.frame (A.indexAt x) x : V →ₗ[ℝ] E)
    (A.frame_injective _ x (A.mem_baseSet_at x))).trans
    (LinearEquiv.ofEq _ _ (A.range_realise_fibre x))

theorem fibreEquiv_apply (x : B) (v : A.toCore.Fiber x) :
    (A.fibreEquiv x v : E) = A.realise ⟨x, v⟩ := rfl

/-- **The realisation is `C^n` on the total space**: the fibre inclusion is a smooth
fibrewise-linear bundle map into the trivial bundle `B × E`. -/
theorem contMDiff_realise : ContMDiff (IB.prod 𝓘(ℝ, V)) 𝓘(ℝ, E) n A.realise := by
  intro p
  set i := A.indexAt p.1 with hi
  have hsrc : (trivializationAt V A.toCore.Fiber p.1).source ∈ nhds p :=
    (trivializationAt V A.toCore.Fiber p.1).open_source.mem_nhds
      (FiberBundle.mem_trivializationAt_proj_source)
  have h1 : ContMDiffOn (IB.prod 𝓘(ℝ, V)) (IB.prod 𝓘(ℝ, V)) n
      (trivializationAt V A.toCore.Fiber p.1) (trivializationAt V A.toCore.Fiber p.1).source :=
    Trivialization.contMDiffOn _
  have h2 : ContMDiffOn (IB.prod 𝓘(ℝ, V)) 𝓘(ℝ, E) n (fun q : B × V => A.frame i q.1 q.2)
      (A.baseSet i ×ˢ univ) :=
    ((A.contMDiffOn_frame i).comp contMDiffOn_fst fun q hq => hq.1).clm_apply contMDiffOn_snd
  refine ((h2.comp h1 fun q hq => ?_).congr fun q hq => ?_).contMDiffAt hsrc
  · exact ⟨hq, mem_univ _⟩
  · exact A.realise_eq_frame i q hq

/-- **Coordinate criterion for smooth sections**: a section is `C^n` at `x₀` iff its coordinates in
the frame at `x₀` are. -/
theorem contMDiffAt_section_iff_coord (s : ∀ x, A.toCore.Fiber x) (x₀ : B) :
    ContMDiffAt IB (IB.prod 𝓘(ℝ, V)) n (fun x => TotalSpace.mk' V x (s x)) x₀ ↔
      ContMDiffAt IB 𝓘(ℝ, V) n
        (fun x => A.coordChange (A.indexAt x) (A.indexAt x₀) x (s x)) x₀ := by
  rw [Bundle.contMDiffAt_section]
  rfl

end NormalFrameAtlas

end Grammar
