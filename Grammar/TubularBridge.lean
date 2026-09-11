import Grammar.StrucDualNormalFamily
import Grammar.FrameAtlasOfCoframes

/-!
# The conditional tubular equivalence (Astra #65 unit 4 = Astra #64 unit 14, conditional form)

Given a StrucDual normal tubular chart `T` of a set `S ⊆ ℝ^d`, a manifold `B` with an injective
smooth map `emb : B → ℝ^d` onto `S`, a frame–coframe atlas of the normal field `N (emb x)`, and a
**lifted foot** `P : ℝ^d → B` — a smooth map on the tube with `emb (P y) = T.proj y` — the map
`Ψ (x, n) = emb x + n` from the certified domain `{‖n‖ < ε}` of the normal bundle onto the tube is
a diffeomorphism with inverse `y ↦ (P y, T.ncoord y)`:

* `Ψ` lands in the tube, with foot `emb x` and normal coordinate `n` (`tubeMap_mem_tube`,
  `proj_tubeMap`, `ncoord_tubeMap`); it is injective on the domain (`tubeInv_tubeMap`) and onto
  the tube (`tubeMap_tubeInv`, `image_tubeMap`);
* `Ψ` is `C^∞` on the total space (`contMDiff_tubeMap`) and its inverse is `C^∞` on the tube: in the
  frame `j` the fibre coordinate of the inverse is the coframe applied to the normal coordinate,
  `coframe j (P y) (T.ncoord y)` (`snd_tubeInv_eq_coframe`, `contMDiffOn_tubeInv`);
* packaged as an open partial homeomorphism from the domain onto the tube (`tubeHomeomorph`).

What this closes: *given* a certified tube and a smooth identification of its foot with the manifold
base, the frame-built normal bundle realises the tube diffeomorphically. What it does **not** prove:
the existence of the lifted foot (a smooth left inverse of `emb` along the tube), an embedded
level-set manifold, or a tubular neighbourhood from the labelled equations alone.

All statements are at an arbitrary grade `n : ℕ∞ω` (`∞` smooth, `ω` real-analytic): the
`LiftedFoot` records, besides `emb` and `P`, the regularity of the tube's normal coordinate at that
grade (`contDiffAt_ncoord`; for `n = ∞` the chart's own field, for `n = ω` the analytic chart's
`analyticAt_ncoord`). `TubularLocalInstance` discharges the whole hypothesis locally, at every
grade, for compact analytic LCI strata.
-/

open scoped Manifold ContDiff
open Bundle Set Function StrucDual.Geometry

namespace Grammar

section Bridge

variable {d : ℕ} {B EB HB : Type*} [TopologicalSpace B] [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} [ChartedSpace HB B]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {n : ℕ∞ω}
  {N : (Fin d → ℝ) → Submodule ℝ (Fin d → ℝ)} {S : Set (Fin d → ℝ)}

/-- **A lifted foot**: a tube `T`, an injective smooth map `emb : B → ℝ^d` onto `S`, a frame–coframe
atlas of the normal field along `emb`, and a smooth map `P` on the tube with
`emb (P y) = proj y`. -/
structure LiftedFoot (T : NormalTubularChart N S) (emb : B → (Fin d → ℝ)) {ι : Type*}
    (D : FrameCoframeData IB V n (fun x => N (emb x)) ι) (P : (Fin d → ℝ) → B) : Prop where
  contMDiff_emb : ContMDiff IB 𝓘(ℝ, Fin d → ℝ) n emb
  emb_mem : ∀ x, emb x ∈ S
  emb_injective : Injective emb
  contMDiffOn_P : ContMDiffOn 𝓘(ℝ, Fin d → ℝ) IB n P T.U
  emb_P : ∀ y ∈ T.U, emb (P y) = T.proj y
  /-- The tube's normal coordinate has the grade of the bridge (for `n = ∞` this is the chart's own
  `contDiffAt_ncoord`; for `n = ω` the analytic chart's `analyticAt_ncoord`). -/
  contDiffAt_ncoord : ∀ y ∈ T.U, ContDiffAt ℝ n T.ncoord y

variable (T : NormalTubularChart N S) (emb : B → (Fin d → ℝ)) {ι : Type*}
  (D : FrameCoframeData IB V n (fun x => N (emb x)) ι) (P : (Fin d → ℝ) → B)

/-- **The tubular map** `Ψ (x, n) = emb x + n`. -/
noncomputable def tubeMap (p : TotalSpace V D.toAtlas.toCore.Fiber) : Fin d → ℝ :=
  emb p.1 + D.toAtlas.realise p

/-- **The certified domain** `{(x, n) : ‖n‖ < ε}`. -/
def tubeDom : Set (TotalSpace V D.toAtlas.toCore.Fiber) := {p | ‖D.toAtlas.realise p‖ < T.eps}

theorem isOpen_tubeDom : IsOpen (tubeDom T emb D) :=
  isOpen_lt (D.toAtlas.contMDiff_realise.continuous.norm) continuous_const

variable {T emb D P}

theorem tubeMap_mem_tube (h : LiftedFoot T emb D P) {p : TotalSpace V D.toAtlas.toCore.Fiber}
    (hp : p ∈ tubeDom T emb D) : tubeMap emb D p ∈ T.U :=
  (T.mem_U_iff _).2 ⟨emb p.1, h.emb_mem _, D.toAtlas.realise p, D.toAtlas.realise_mem p, hp, rfl⟩

theorem proj_tubeMap (h : LiftedFoot T emb D P) {p : TotalSpace V D.toAtlas.toCore.Fiber}
    (hp : p ∈ tubeDom T emb D) : T.proj (tubeMap emb D p) = emb p.1 :=
  (T.proj_eq_of_decomp (tubeMap_mem_tube h hp) (h.emb_mem _) (D.toAtlas.realise_mem p) hp rfl).1

theorem ncoord_tubeMap (h : LiftedFoot T emb D P) {p : TotalSpace V D.toAtlas.toCore.Fiber}
    (hp : p ∈ tubeDom T emb D) : T.ncoord (tubeMap emb D p) = D.toAtlas.realise p :=
  (T.proj_eq_of_decomp (tubeMap_mem_tube h hp) (h.emb_mem _) (D.toAtlas.realise_mem p) hp rfl).2

theorem P_tubeMap (h : LiftedFoot T emb D P) {p : TotalSpace V D.toAtlas.toCore.Fiber}
    (hp : p ∈ tubeDom T emb D) : P (tubeMap emb D p) = p.1 :=
  h.emb_injective (by rw [h.emb_P _ (tubeMap_mem_tube h hp), proj_tubeMap h hp])

variable (T D P)

/-- The normal coordinate of a tube point lies in the normal space at the lifted foot. -/
theorem ncoord_mem_of_liftedFoot (h : LiftedFoot T emb D P) {y : Fin d → ℝ} (hy : y ∈ T.U) :
    T.ncoord y ∈ N (emb (P y)) := by
  rw [h.emb_P y hy]
  exact T.ncoord_mem hy

open Classical in
/-- **The inverse tubular map** `y ↦ (P y, T.ncoord y)`, defined on the tube (and arbitrary
elsewhere). -/
noncomputable def tubeInv (h : LiftedFoot T emb D P) (y : Fin d → ℝ) :
    TotalSpace V D.toAtlas.toCore.Fiber :=
  if hy : y ∈ T.U then
    ⟨P y, (D.toAtlas.fibreEquiv (P y)).symm ⟨T.ncoord y, ncoord_mem_of_liftedFoot T D P h hy⟩⟩
  else ⟨P y, 0⟩

variable {T D P}

theorem tubeInv_proj (h : LiftedFoot T emb D P) (y : Fin d → ℝ) : (tubeInv T D P h y).1 = P y := by
  unfold tubeInv
  split_ifs <;> rfl

theorem realise_tubeInv (h : LiftedFoot T emb D P) {y : Fin d → ℝ} (hy : y ∈ T.U) :
    D.toAtlas.realise (tubeInv T D P h y) = T.ncoord y := by
  unfold tubeInv
  rw [dif_pos hy, ← NormalFrameAtlas.fibreEquiv_apply, LinearEquiv.apply_symm_apply]

theorem tubeMap_tubeInv (h : LiftedFoot T emb D P) {y : Fin d → ℝ} (hy : y ∈ T.U) :
    tubeMap emb D (tubeInv T D P h y) = y := by
  unfold tubeMap
  rw [realise_tubeInv h hy, tubeInv_proj, h.emb_P y hy]
  exact (T.decomp y).symm

theorem tubeInv_mem_tubeDom (h : LiftedFoot T emb D P) {y : Fin d → ℝ} (hy : y ∈ T.U) :
    tubeInv T D P h y ∈ tubeDom T emb D := by
  change ‖D.toAtlas.realise (tubeInv T D P h y)‖ < T.eps
  rw [realise_tubeInv h hy]
  exact T.ncoord_norm_lt hy

theorem tubeInv_tubeMap (h : LiftedFoot T emb D P) {p : TotalSpace V D.toAtlas.toCore.Fiber}
    (hp : p ∈ tubeDom T emb D) : tubeInv T D P h (tubeMap emb D p) = p := by
  have hy := tubeMap_mem_tube h hp
  set q := tubeInv T D P h (tubeMap emb D p) with hq
  have h1 : q.1 = p.1 := by rw [hq, tubeInv_proj, P_tubeMap h hp]
  have h2 : D.frame (D.indexAt q.1) q.1 q.2 = D.frame (D.indexAt p.1) p.1 p.2 := by
    have := realise_tubeInv h hy
    rw [ncoord_tubeMap h hp] at this
    exact this
  rw [h1] at h2
  have h3 : q.2 = p.2 := D.frame_injective _ (D.mem_baseSet_at p.1) h2
  exact Bundle.TotalSpace.ext h1 (heq_of_eq h3)

/-- **The image of the certified domain is the tube.** -/
theorem image_tubeMap (h : LiftedFoot T emb D P) : tubeMap emb D '' tubeDom T emb D = T.U := by
  ext y
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact tubeMap_mem_tube h hp
  · intro hy
    exact ⟨tubeInv T D P h y, tubeInv_mem_tubeDom h hy, tubeMap_tubeInv h hy⟩

/-- **`Ψ` is `C^∞`** on the whole total space. -/
theorem contMDiff_tubeMap (h : LiftedFoot T emb D P) :
    ContMDiff (IB.prod 𝓘(ℝ, V)) 𝓘(ℝ, Fin d → ℝ) n (tubeMap emb D) :=
  (h.contMDiff_emb.comp (Bundle.contMDiff_proj _)).add D.toAtlas.contMDiff_realise

/-- In the frame `j`, the fibre coordinate of the inverse is the coframe applied to the normal
coordinate. -/
theorem snd_tubeInv_eq_coframe (h : LiftedFoot T emb D P) (j : ι) {y : Fin d → ℝ} (hy : y ∈ T.U) :
    (D.toAtlas.toCore.localTriv j (tubeInv T D P h y)).2 = D.coframe j (P y) (T.ncoord y) := by
  rw [VectorBundleCore.localTriv_apply]
  change D.coframe j _ (D.toAtlas.realise (tubeInv T D P h y)) = _
  rw [realise_tubeInv h hy, tubeInv_proj]

/-- **The inverse is `C^∞` on the tube.** -/
theorem contMDiffOn_tubeInv (h : LiftedFoot T emb D P) :
    ContMDiffOn 𝓘(ℝ, Fin d → ℝ) (IB.prod 𝓘(ℝ, V)) n (tubeInv T D P h) T.U := by
  intro y₀ hy₀
  set j := D.indexAt (P y₀) with hj
  have hsrc : tubeInv T D P h y₀ ∈
      (trivializationAt V D.toAtlas.toCore.Fiber (P y₀)).source :=
    (Trivialization.mem_source _).2 (by rw [tubeInv_proj]; exact D.mem_baseSet_at (P y₀))
  rw [(trivializationAt V D.toAtlas.toCore.Fiber (P y₀)).contMDiffWithinAt_iff hsrc]
  refine ⟨(h.contMDiffOn_P y₀ hy₀).congr (fun y _ => tubeInv_proj h y) (tubeInv_proj h y₀), ?_⟩
  have hs' : T.U ∩ P ⁻¹' (D.baseSet j) ∈ nhdsWithin y₀ T.U :=
    Filter.inter_mem self_mem_nhdsWithin
      ((h.contMDiffOn_P.continuousOn.continuousWithinAt hy₀).preimage_mem_nhdsWithin
        ((D.isOpen_baseSet j).mem_nhds (D.mem_baseSet_at (P y₀))))
  have hnc : ContMDiffOn 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, Fin d → ℝ) n T.ncoord (T.U ∩ P ⁻¹' (D.baseSet j)) :=
    fun y hy => (h.contDiffAt_ncoord y hy.1).contMDiffAt.contMDiffWithinAt
  have hcof : ContMDiffOn 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, V) n
      (fun y => D.coframe j (P y) (T.ncoord y)) (T.U ∩ P ⁻¹' (D.baseSet j)) :=
    ((D.contMDiffOn_coframe j).comp (h.contMDiffOn_P.mono inter_subset_left)
      fun y hy => hy.2).clm_apply hnc
  refine ((hcof y₀ ⟨hy₀, D.mem_baseSet_at (P y₀)⟩).congr (fun y hy => ?_) ?_).mono_of_mem_nhdsWithin
    hs'
  · exact snd_tubeInv_eq_coframe h j hy.1
  · exact snd_tubeInv_eq_coframe h j hy₀

/-- **The conditional tubular equivalence**: an open partial homeomorphism from the certified domain
of the normal bundle onto the tube, `Ψ (x, n) = emb x + n` with inverse `y ↦ (P y, ncoord y)`. -/
noncomputable def tubeHomeomorph (h : LiftedFoot T emb D P) :
    OpenPartialHomeomorph (TotalSpace V D.toAtlas.toCore.Fiber) (Fin d → ℝ) where
  toFun := tubeMap emb D
  invFun := tubeInv T D P h
  source := tubeDom T emb D
  target := T.U
  map_source' := fun _ hp => tubeMap_mem_tube h hp
  map_target' := fun _ hy => tubeInv_mem_tubeDom h hy
  left_inv' := fun _ hp => tubeInv_tubeMap h hp
  right_inv' := fun _ hy => tubeMap_tubeInv h hy
  open_source := isOpen_tubeDom T emb D
  open_target := T.isOpen_U
  continuousOn_toFun := (contMDiff_tubeMap h).continuous.continuousOn
  continuousOn_invFun := (contMDiffOn_tubeInv h).continuousOn

end Bridge

end Grammar
