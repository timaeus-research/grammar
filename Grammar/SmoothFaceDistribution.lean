/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothPartitionDistribution

/-!
# The chart-face functionals and the reconstruction of the coefficient distribution
(consult #124 §4–§5, units C5c/C5e — algebraic part)

For a chart piece `P` of the resolution bridge, a face `J` of its active box (the active
coordinates set to zero) and a normal multi-index `a`, Theorem B (CDXI) writes the coefficient as
`Σ_{P,J,a} faceW J a · ∫_s renormFunctional (ρfam P s) … J a μ q (∂^a_J (obsfam P s)) dν(s)`. The
renormalised functional depends on its argument `U` only through the restriction of `U` to the face
`{v_J = 0}` (the complementary Taylor remainder and the face integral live there). This file
introduces the **face space** `FaceSpace P J = BaseSpace × TangSpace` (base coordinates and the
tangential active coordinates, an ambient Euclidean space), the **cylinder extension**
`cyl u s v = u (s, tangProj v)` of a function `u` on the face space, and the **face functional**

  `faceFunctional X P J a μ q u = ∫_s renormFunctional (ρfam P s) … J a μ q (cyl u s.1) dν(s)`,

a linear functional of `u`, and proves:

* face factorisation (`renormFunctional_eq_cyl`): the renormalised functional of `U` equals that of
  the cylinder extension of the face restriction of `U`, because coordinate derivatives in the
  tangential directions of two functions agreeing on the face agree on the face
  (`pdMulti_lK_eqOn_face`);
* the **face jet** `faceJet X P J a f (s, w) = ∂^a_J (f ∘ ψ ∘ T_P(s, ·)) (0_J, w)` of an observable,
  smooth on the face space;
* ★★★ **reconstruction** (`coeff_eq_sum_faceFunctional`, `coeffDistribution_eq_sum_faceFunctional`):
  for every test function `f`,
  `coeffDistribution X μ q f = Σ_{P,J,a} faceW J a · faceFunctional X P J a μ q (faceJetObs f)`

The chart-face functionals are presentation data (they depend on the charts and the weights); their
sum is the intrinsic coefficient distribution. Their continuity (finite tangential order) and the
resulting chart-face distributions are the analytic part (C5d), built on the parametric derivative
infrastructure.
-/

open MeasureTheory Set Real Filter Topology Finset
open scoped ContDiff Distributions
open Monomialize.VolumeScaling

namespace Grammar

namespace SmoothEngine

variable {d : ℕ}

/-! ### Tangential derivatives on a face -/

/-- The face `{v | ∀ i ∈ J, v i = 0}` of a coordinate box. -/
def face (J : Finset (Fin d)) : Set (Fin d → ℝ) := {v | ∀ i ∈ J, v i = 0}

theorem update_mem_face {J : Finset (Fin d)} {v : Fin d → ℝ} (hv : v ∈ face J) {i : Fin d}
    (hi : i ∉ J) (t : ℝ) : Function.update v i t ∈ face J := by
  intro j hj
  have hji : j ≠ i := fun h => hi (h ▸ hj)
  rw [Function.update_of_ne hji]
  exact hv j hj

theorem glue_zero_mem_face (J : Finset (Fin d)) (w : {i // ¬ inJ J i} → ℝ) :
    glue J 0 w ∈ face J := fun i hi => by rw [glue_apply_of_mem J _ _ hi]; rfl

/-- Tangential coordinate derivatives of functions agreeing on the face agree on the face. -/
theorem pd_eqOn_face {J : Finset (Fin d)} {F G : (Fin d → ℝ) → ℝ} (h : EqOn F G (face J))
    {i : Fin d} (hi : i ∉ J) : EqOn (pd i F) (pd i G) (face J) := by
  intro v hv
  unfold pd
  have : line F i v = line G i v := funext fun t => h (update_mem_face hv hi t)
  rw [this]

theorem pdPow_eqOn_face {J : Finset (Fin d)} {F G : (Fin d → ℝ) → ℝ} (h : EqOn F G (face J))
    {i : Fin d} (hi : i ∉ J) (n : ℕ) : EqOn (pdPow i n F) (pdPow i n G) (face J) := by
  induction n generalizing F G with
  | zero => exact h
  | succ n ih => rw [pdPow_succ, pdPow_succ]; exact ih (pd_eqOn_face h hi)

theorem pdMulti_eqOn_face {J : Finset (Fin d)} {F G : (Fin d → ℝ) → ℝ} (h : EqOn F G (face J))
    (m : Fin d → ℕ) {l : List (Fin d)} (hl : ∀ i ∈ l, i ∉ J) :
    EqOn (pdMulti m l F) (pdMulti m l G) (face J) := by
  induction l generalizing F G with
  | nil => exact h
  | cons i l ih =>
    exact pdPow_eqOn_face (ih h fun j hj => hl j (List.mem_cons_of_mem i hj))
      (hl i (List.mem_cons_self ..)) (m i)

theorem pdMulti_lK_eqOn_face {J : Finset (Fin d)} {F G : (Fin d → ℝ) → ℝ} (h : EqOn F G (face J))
    (m : Fin d → ℕ) : EqOn (pdMulti m (lK J) F) (pdMulti m (lK J) G) (face J) :=
  pdMulti_eqOn_face h m fun _ hi => (mem_lK J).1 hi

/-! ### The tangential projection and the cylinder extension -/

/-- The tangential projection `v ↦ (v_k)_{k ∉ J}`. -/
def tangProj (J : Finset (Fin d)) : (Fin d → ℝ) →L[ℝ] ({i // ¬ inJ J i} → ℝ) :=
  ContinuousLinearMap.pi fun k => ContinuousLinearMap.proj k.1

theorem tangProj_apply (J : Finset (Fin d)) (v : Fin d → ℝ) (k : {i // ¬ inJ J i}) :
    tangProj J v k = v k.1 := rfl

theorem tangProj_glue_zero (J : Finset (Fin d)) (w : {i // ¬ inJ J i} → ℝ) :
    tangProj J (glue J 0 w) = w := by
  funext k
  rw [tangProj_apply, glue_apply_of_not_mem J _ _ k.2]

theorem glue_zero_tangProj {J : Finset (Fin d)} {v : Fin d → ℝ} (hv : v ∈ face J) :
    glue J 0 (tangProj J v) = v := by
  funext i
  by_cases hi : i ∈ J
  · rw [glue_apply_of_mem J _ _ hi]; exact (hv i hi).symm
  · rw [glue_apply_of_not_mem J _ _ hi]; rfl

/-- The face space of a face `J` over a base space `B`: base coordinates and tangential
coordinates. -/
abbrev FaceSpace (B : Type*) (J : Finset (Fin d)) : Type _ := B × ({i // ¬ inJ J i} → ℝ)

/-- The cylinder extension of a function on the face space to the engine's coordinates. -/
def cyl {B : Type*} (J : Finset (Fin d)) (u : FaceSpace B J → ℝ) (s : B) : (Fin d → ℝ) → ℝ :=
  fun v => u (s, tangProj J v)

theorem cyl_apply {B : Type*} (J : Finset (Fin d)) (u : FaceSpace B J → ℝ) (s : B)
    (v : Fin d → ℝ) : cyl J u s v = u (s, tangProj J v) := rfl

theorem cyl_glue_zero {B : Type*} (J : Finset (Fin d)) (u : FaceSpace B J → ℝ) (s : B)
    (w : {i // ¬ inJ J i} → ℝ) : cyl J u s (glue J 0 w) = u (s, w) := by
  rw [cyl_apply, tangProj_glue_zero]

theorem contDiff_cyl {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] (J : Finset (Fin d))
    {u : FaceSpace B J → ℝ} (hu : ContDiff ℝ ∞ u) (s : B) : ContDiff ℝ ∞ (cyl J u s) :=
  hu.comp (contDiff_const.prodMk (tangProj J).contDiff)

/-- The face restriction of a function on the engine's coordinates, over a base parameter. -/
def faceResFam {B : Type*} (J : Finset (Fin d)) (U : B → (Fin d → ℝ) → ℝ) : FaceSpace B J → ℝ :=
  fun z => U z.1 (glue J 0 z.2)

theorem cyl_faceResFam_eqOn_face {B : Type*} (J : Finset (Fin d)) (U : B → (Fin d → ℝ) → ℝ) (s
    : B) :
    EqOn (cyl J (faceResFam J U) s) (U s) (face J) := fun v hv => by
  rw [cyl_apply, faceResFam, glue_zero_tangProj hv]

/-! ### Face factorisation of the renormalised functional -/

variable {h k p : Fin d → ℕ} {β b μ : ℝ}

/-- ★ **Face factorisation**: the renormalised functional depends on its argument only through
the restriction to the face. -/
theorem renormFunctional_eqOn_face {D U U' : (Fin d → ℝ) → ℝ} (hD : ContDiff ℝ ∞ D)
    (hU : ContDiff ℝ ∞ U) (hU' : ContDiff ℝ ∞ U') (hb : 0 < b) (J : Finset (Fin d))
    (a : Fin d → ℕ) (q : ℕ) (heq : EqOn U U' (face J)) :
    renormFunctional D h k p β b J a μ q U = renormFunctional D h k p β b J a μ q U' :=
  renormFunctional_congr hD hU hU' hb J a q fun α _ _ _ hvJ =>
    pdMulti_lK_eqOn_face heq α (fun i hi => hvJ i hi)

theorem renormFunctional_eq_cyl {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    {D : (Fin d → ℝ) → ℝ} (hD : ContDiff ℝ ∞ D) (J : Finset (Fin d)) {U : B → (Fin d → ℝ) → ℝ}
    (s : B) (hU : ContDiff ℝ ∞ (U s)) (hres : ContDiff ℝ ∞ (faceResFam J U)) (hb : 0 < b)
    (a : Fin d → ℕ) (q : ℕ) :
    renormFunctional D h k p β b J a μ q (U s) =
      renormFunctional D h k p β b J a μ q (cyl J (faceResFam J U) s) :=
  renormFunctional_eqOn_face hD hU (contDiff_cyl J hres s) hb J a q
    (cyl_faceResFam_eqOn_face J U s).symm

/-! ### Smoothness of the affine chart glue in both arguments -/

theorem contDiff_glue_zero (J : Finset (Fin d)) :
    ContDiff ℝ ∞ fun w : {i // ¬ inJ J i} → ℝ => glue J 0 w := by
  rw [contDiff_pi]
  intro i
  by_cases hi : i ∈ J
  · simp only [glue_apply_of_mem J _ _ hi]
    exact contDiff_const
  · simp only [glue_apply_of_not_mem J _ _ hi]
    exact contDiff_apply _ _ _

variable {da : ℕ}

theorem contDiff_affineMap_pair {J : Finset (Fin d)} (e : Fin da ≃ {i // inJ J i})
    (σ : WaterFilling.CoordSign d) :
    ContDiff ℝ ∞ fun z : ({i // ¬ inJ J i} → ℝ) × (Fin da → ℝ) => affineMap e σ z.1 z.2 := by
  rw [contDiff_pi]
  intro i
  by_cases hi : i ∈ J
  · simp only [affineMap_apply_of_mem e σ _ _ hi]
    exact contDiff_const.mul ((contDiff_apply _ _ _).comp contDiff_snd)
  · simp only [affineMap_apply_of_not_mem e σ _ _ hi]
    exact (contDiff_apply _ _ _).comp contDiff_fst

/-! ### The chart-face functionals of the resolution bridge -/

namespace BridgeInputs

variable (X : BridgeInputs d)

/-- The ambient base space of a piece: the inactive coordinates. -/
abbrev BaseSpace (P : X.PIdx) : Type := {j // ¬ inJ (X.act P.1) j} → ℝ

/-- The reflected inactive coordinates of an ambient base point (extends `sc`). -/
def scAmb (P : X.PIdx) (s : X.BaseSpace P) : {j // ¬ inJ (X.act P.1) j} → ℝ :=
  fun j => WaterFilling.sgn P.2 j.1 * s j

theorem scAmb_val (P : X.PIdx) (s : Base (X.act P.1) (X.T.a P.1)) : X.scAmb P s.1 = X.sc P s := rfl

/-- The chart coordinate of a piece over an ambient base point (extends `Tm`). -/
noncomputable def TmAmb (P : X.PIdx) (s : X.BaseSpace P) (v : Fin (X.da P) → ℝ) : Fin d → ℝ :=
  affineMap (X.eqv P) P.2 (X.scAmb P s) v

theorem TmAmb_val (P : X.PIdx) (s : Base (X.act P.1) (X.T.a P.1)) : X.TmAmb P s.1 = X.Tm P s := rfl

/-- The face space of a piece and a face: ambient base coordinates and tangential coordinates. -/
abbrev PieceFaceSpace (P : X.PIdx) (J : Finset (Fin (X.da P))) : Type :=
  FaceSpace (X.BaseSpace P) J

/-- ★ **The face jet of an observable**: `∂^a_J (obs ∘ ψ ∘ T_P(s, ·))` on the face `v_J = 0`, as a
function of the base point and the tangential coordinates. -/
noncomputable def faceJet (P : X.PIdx) (J : Finset (Fin (X.da P))) (a : Fin (X.da P) → ℕ)
    (z : X.PieceFaceSpace P J) : ℝ :=
  pdMulti a (lJ J) (fun v => X.obsExt P.1 (X.TmAmb P z.1 v)) (glue J 0 z.2)

/-- On the base, the cylinder extension of the face jet agrees on the face with the normal
derivative of the observable family. -/
theorem cyl_faceJet_eqOn_face (P : X.PIdx) (J : Finset (Fin (X.da P))) (a : Fin (X.da P) → ℕ)
    (s : Base (X.act P.1) (X.T.a P.1)) :
    EqOn (cyl J (X.faceJet P J a) s.1) (pdMulti a (lJ J) (X.obsfam P s)) (face J) := by
  intro v hv
  rw [cyl_apply, faceJet, glue_zero_tangProj hv]
  rfl

/-- The face jet is smooth on the face space. -/
theorem contDiff_faceJet (P : X.PIdx) (J : Finset (Fin (X.da P))) (a : Fin (X.da P) → ℕ) :
    ContDiff ℝ ∞ (X.faceJet P J a) := by
  have hfun : X.faceJet P J a = fun z : X.PieceFaceSpace P J =>
      ((lJ J).map fun j => WaterFilling.sgn P.2 ((X.eqv P) j).1 ^ a j).prod *
        pdMulti (extendIdx (X.eqv P) a) ((lJ J).map fun j => ((X.eqv P) j).1) (X.obsExt P.1)
          (affineMap (X.eqv P) P.2 (X.scAmb P z.1) (glue J 0 z.2)) := by
    funext z
    unfold faceJet TmAmb
    rw [pdMulti_comp_affineMap]
  rw [hfun]
  have hglue : ContDiff ℝ ∞ fun z : X.PieceFaceSpace P J =>
      ((fun j : {j // ¬ inJ (X.act P.1) j} => WaterFilling.sgn P.2 j.1 * z.1 j), glue J 0 z.2) := by
    refine ContDiff.prodMk ?_ ((contDiff_glue_zero J).comp contDiff_snd)
    rw [contDiff_pi]
    intro j
    exact contDiff_const.mul ((contDiff_apply _ _ _).comp contDiff_fst)
  have haff : ContDiff ℝ ∞ fun z : X.PieceFaceSpace P J =>
      affineMap (X.eqv P) P.2 (X.scAmb P z.1) (glue J 0 z.2) :=
    (contDiff_affineMap_pair (X.eqv P) P.2).comp hglue
  exact contDiff_const.mul
    ((contDiff_pdMulti (X.contDiff_obsExt P.1) (extendIdx (X.eqv P) a) _).comp haff)

/-- ★★ **The chart-face functional** of a piece, a face and a normal multi-index: the base
integral of the renormalised functional of the transport density applied to the cylinder extension
of a function on the face space. -/
noncomputable def faceFunctional (P : X.PIdx) (J : Finset (Fin (X.da P))) (a : Fin (X.da P) → ℕ)
    (μ : ℝ) (q : ℕ) (u : X.PieceFaceSpace P J → ℝ) : ℝ :=
  ∫ s, renormFunctional (X.ρfam P s) (X.hA P) (X.kA P) (X.pieceDepth P μ) (X.T.phaseConst P.1)
    (X.T.a P.1) J a μ q (cyl J u s.1) ∂(baseMeasure (X.act P.1) (X.T.a P.1) (X.T.h P.1))

/-- Face factorisation on a piece: the Theorem B integrand is the renormalised functional of the
cylinder extension of the face jet. -/
theorem renormFunctional_obsfam_eq_faceJet (P : X.PIdx) (J : Finset (Fin (X.da P)))
    (a : Fin (X.da P) → ℕ) (μ : ℝ) (q : ℕ) (s : Base (X.act P.1) (X.T.a P.1)) :
    renormFunctional (X.ρfam P s) (X.hA P) (X.kA P) (X.pieceDepth P μ) (X.T.phaseConst P.1)
        (X.T.a P.1) J a μ q (pdMulti a (lJ J) (X.obsfam P s)) =
      renormFunctional (X.ρfam P s) (X.hA P) (X.kA P) (X.pieceDepth P μ) (X.T.phaseConst P.1)
        (X.T.a P.1) J a μ q (cyl J (X.faceJet P J a) s.1) :=
  renormFunctional_eqOn_face ((X.ρfam P).smooth s)
    (contDiff_pdMulti ((X.obsfam P).smooth s) a (lJ J))
    (contDiff_cyl (B := X.BaseSpace P) J (X.contDiff_faceJet P J a) s.1) (X.T.a_pos P.1) J a q
    (X.cyl_faceJet_eqOn_face P J a s).symm

/-- ★★★ **The chart-face presentation of the intrinsic coefficient** (Theorem B in face form):
`coeff μ q = Σ_{P,J,a} faceW J a · faceFunctional P J a μ q (faceJet P J a)`. -/
theorem coeff_eq_sum_faceFunctional (μ : ℝ) (q : ℕ) :
    X.decomp.coeff μ q = ∑ I : Fin (Fintype.card X.PIdx), ∑ J : Finset (Fin (X.da (X.en I))),
      ∑ a ∈ idxL (X.pieceDepth (X.en I) μ) (lJ J), faceW J a *
        X.faceFunctional (X.en I) J a μ q (X.faceJet (X.en I) J a) := by
  rw [X.coeff_eq_renormSum μ q]
  refine Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun J _ =>
    Finset.sum_congr rfl fun a _ => ?_
  congr 1
  unfold faceFunctional
  exact integral_congr_ae (Eventually.of_forall fun s =>
    X.renormFunctional_obsfam_eq_faceJet (X.en I) J a μ q s)

/-- The face jet of a variable smooth observable. -/
noncomputable def faceJetObs (P : X.PIdx) (J : Finset (Fin (X.da P))) (a : Fin (X.da P) → ℕ)
    (f : (Fin d → ℝ) → ℝ) (hf : ContDiff ℝ ∞ f) : X.PieceFaceSpace P J → ℝ :=
  (X.withObs f hf).faceJet P J a

theorem contDiff_faceJetObs (P : X.PIdx) (J : Finset (Fin (X.da P))) (a : Fin (X.da P) → ℕ)
    (f : (Fin d → ℝ) → ℝ) (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (X.faceJetObs P J a f hf) :=
  (X.withObs f hf).contDiff_faceJet P J a

/-- ★★★ **The chart-face presentation of the coefficient distribution**: for every test function
`f`, `coeffDistribution X μ q f = Σ_{P,J,a} faceW J a · faceFunctional X P J a μ q (faceJetObs f)`.
The face functionals depend only on the transport data (not on `f`). -/
theorem coeffDistribution_eq_sum_faceFunctional (μ : ℝ) (q : ℕ)
    (f : 𝓓((⊤ : TopologicalSpace.Opens (Fin d → ℝ)), ℝ)) :
    X.coeffDistribution μ q f = ∑ I : Fin (Fintype.card X.PIdx),
      ∑ J : Finset (Fin (X.da (X.en I))), ∑ a ∈ idxL (X.pieceDepth (X.en I) μ) (lJ J),
        faceW J a * X.faceFunctional (X.en I) J a μ q (X.faceJetObs (X.en I) J a f f.contDiff) :=
  (X.withObs f f.contDiff).coeff_eq_sum_faceFunctional μ q

end BridgeInputs

end SmoothEngine

end Grammar
