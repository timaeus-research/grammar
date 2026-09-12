/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.HolomorphicBoxBuffer
import Grammar.AnalyticUniformSeries

/-!
# Face series from a holomorphic box extension (CCCXXXI; phase 3, unit P4)

Consult #98 §4. For a holomorphic box extension `A` (CCCXXX) with uniform buffer radius `R` and
uniform bound `M` on the tube, and a nonempty coordinate set `I`, the RECENTRED normal family
`G_s(z) = H (complexify s + complexInsert I z)` over the closed face `X_I` satisfies, in order:

* A. containment: `complexify s + complexInsert I z ∈ Ω` for `‖z‖ ≤ R` (the insertion is
  norm-nonincreasing; `recentred_mem`);
* B. holomorphicity in `z` on the open polydisc of radius `R` (`differentiableOn_recentred`);
* C. joint continuity on `X_I × closedPolydisc (R/2)` (`continuousOn_recentred`);
* D. the uniform bound `M` on the closed polydisc of radius `R/2` (`norm_recentred_le`);
* E. the uniform series family at radius `ρ = R/4` (`analyticUniformSeries`, CCCXXVIII);
* F. the evaluation identity for the ORIGINAL real functions on the real ball of radius `ρ`
  (reconstruction + `complexify_originalNormalMap` + the real-slice identity of `A`).

Hence ★★ `HolomorphicBoxExtension.faceSeries A I : OriginalFaceSeries a ϕ φ I` at the COMMON radius
`A.radius = R/4` (`faceSeries_ρ`), and ★★ `exists_originalFaceSeries_of_holomorphicBoxExtension`.
No differentiation in the face parameter and no compatibility across faces is needed.
Zero `sorry`/`axiom`.
-/

open Set Filter Topology

namespace Grammar

namespace WaterFilling

open CoeffFamily

variable {d : ℕ} (a : ℝ)

/-- The recentred normal family `G_s(z) = H (complexify s + complexInsert I z)` over the closed
face. -/
noncomputable def recentred (H : (Fin d → ℂ) → ℂ) (I : NonemptyIdx d) (s : ↥(faceSet a I.1))
    (z : Fin (nI I + 1) → ℂ) : ℂ :=
  H (complexify s.1 + complexInsert I z)

theorem norm_le_of_mem_closedPolydisc {m : ℕ} {r : ℝ} (hr : 0 ≤ r) {z : Fin m → ℂ}
    (hz : z ∈ closedPolydisc m r) : ‖z‖ ≤ r :=
  (pi_norm_le_iff_of_nonneg hr).2 (mem_closedPolydisc.1 hz)

theorem norm_lt_of_mem_openPolydisc {m : ℕ} {r : ℝ} (hr : 0 < r) {z : Fin m → ℂ}
    (hz : z ∈ openPolydisc m r) : ‖z‖ < r :=
  (pi_norm_lt_iff hr).2 (mem_openPolydisc.1 hz)

theorem norm_complexify_le (u : Fin d → ℝ) : ‖complexify u‖ ≤ ‖u‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg u)).2 fun i => by
    rw [complexify_apply, Complex.norm_real]
    exact norm_le_pi_norm u i

section Recentred

variable {Ω : Set (Fin d → ℂ)} {R : ℝ}
  (hbuf : ∀ w ∈ piBox d (Icc 0 a), ∀ z : Fin d → ℂ, ‖z‖ ≤ R → complexify w + z ∈ Ω)
  (I : NonemptyIdx d)

include hbuf in
/-- A. Containment of the recentred polydisc in `Ω`. -/
theorem recentred_mem (s : ↥(faceSet a I.1)) {z : Fin (nI I + 1) → ℂ} (hz : ‖z‖ ≤ R) :
    complexify s.1 + complexInsert I z ∈ Ω :=
  hbuf s.1 (mem_piBox_of_mem_faceSet a s.2) _ ((norm_complexInsert_le I z).trans hz)

include hbuf in
/-- B. Holomorphicity of the recentred family in the normal variable. -/
theorem differentiableOn_recentred (hR : 0 < R) {H : (Fin d → ℂ) → ℂ}
    (hH : DifferentiableOn ℂ H Ω) (s : ↥(faceSet a I.1)) :
    DifferentiableOn ℂ (recentred a H I s) (openPolydisc (nI I + 1) R) := by
  refine hH.comp ((differentiable_const _).add (complexInsert I).differentiable).differentiableOn
    fun z hz => ?_
  exact recentred_mem a hbuf I s (norm_lt_of_mem_openPolydisc hR hz).le

include hbuf in
/-- C. Joint continuity of the recentred family on the face times the closed polydisc. -/
theorem continuousOn_recentred {r : ℝ} (hrR : r ≤ R) {H : (Fin d → ℂ) → ℂ}
    (hH : DifferentiableOn ℂ H Ω) :
    ContinuousOn (fun p : ↥(faceSet a I.1) × (Fin (nI I + 1) → ℂ) => recentred a H I p.1 p.2)
      (univ ×ˢ closedPolydisc (nI I + 1) r) := by
  have hin : Continuous fun p : ↥(faceSet a I.1) × (Fin (nI I + 1) → ℂ) =>
      complexify p.1.1 + complexInsert I p.2 :=
    (continuous_complexify.comp (continuous_subtype_val.comp continuous_fst)).add
      ((complexInsert I).continuous.comp continuous_snd)
  refine hH.continuousOn.comp hin.continuousOn fun p hp => ?_
  have hr0 : 0 ≤ r := by
    rcases (mem_closedPolydisc.1 hp.2) with h
    by_cases hm : Nonempty (Fin (nI I + 1))
    · obtain ⟨i⟩ := hm
      exact (norm_nonneg _).trans (h i)
    · exact absurd ⟨0⟩ hm
  exact recentred_mem a hbuf I p.1 ((norm_le_of_mem_closedPolydisc hr0 hp.2).trans hrR)

omit hbuf in
/-- D. The uniform bound of the recentred family on the closed polydisc. -/
theorem norm_recentred_le {r M : ℝ} (hrR : r ≤ R) {H : (Fin d → ℂ) → ℂ}
    (hM : ∀ w ∈ piBox d (Icc 0 a), ∀ z : Fin d → ℂ, ‖z‖ ≤ R → ‖H (complexify w + z)‖ ≤ M)
    (s : ↥(faceSet a I.1)) {z : Fin (nI I + 1) → ℂ} (hz : ‖z‖ ≤ r) :
    ‖recentred a H I s z‖ ≤ M :=
  hM s.1 (mem_piBox_of_mem_faceSet a s.2) _ ((norm_complexInsert_le I z).trans (hz.trans hrR))

end Recentred

namespace HolomorphicBoxExtension

variable {ϕ φ : (Fin d → ℝ) → ℝ} (A : HolomorphicBoxExtension a ϕ φ)

/-- The buffer radius of the extension. -/
noncomputable def bufferRadius : ℝ := (A.exists_buffer a).choose

theorem bufferRadius_pos : 0 < A.bufferRadius a := (A.exists_buffer a).choose_spec.1

theorem buffer_mem : ∀ w ∈ piBox d (Icc 0 a), ∀ z : Fin d → ℂ, ‖z‖ ≤ A.bufferRadius a →
    complexify w + z ∈ A.Ω :=
  (A.exists_buffer a).choose_spec.2

/-- The common normal radius of the face series: a quarter of the buffer radius. -/
noncomputable def radius : ℝ := A.bufferRadius a / 4

theorem radius_pos : 0 < A.radius a := by
  have := A.bufferRadius_pos a
  unfold radius
  positivity

/-- The uniform bound of both extensions on the tube. -/
noncomputable def bound : ℝ := (A.exists_bounds a (A.buffer_mem a)).choose

theorem bound_ϕ : ∀ w ∈ piBox d (Icc 0 a), ∀ z : Fin d → ℂ, ‖z‖ ≤ A.bufferRadius a →
    ‖A.Hϕ (complexify w + z)‖ ≤ A.bound a :=
  (A.exists_bounds a (A.buffer_mem a)).choose_spec.2.1

theorem bound_φ : ∀ w ∈ piBox d (Icc 0 a), ∀ z : Fin d → ℂ, ‖z‖ ≤ A.bufferRadius a →
    ‖A.Hφ (complexify w + z)‖ ≤ A.bound a :=
  (A.exists_bounds a (A.buffer_mem a)).choose_spec.2.2

theorem radius_lt_half : A.radius a < A.bufferRadius a / 2 := by
  have := A.bufferRadius_pos a
  unfold radius
  linarith

theorem half_lt_buffer : A.bufferRadius a / 2 < A.bufferRadius a := by
  have := A.bufferRadius_pos a
  linarith

/-- E. The uniform series family of an extension over the face `I` at the common radius. -/
noncomputable def uniformSeries (H : (Fin d → ℂ) → ℂ) (hH : DifferentiableOn ℂ H A.Ω)
    (hM : ∀ w ∈ piBox d (Icc 0 a), ∀ z : Fin d → ℂ, ‖z‖ ≤ A.bufferRadius a →
      ‖H (complexify w + z)‖ ≤ A.bound a) (I : NonemptyIdx d) :
    UniformSeriesFamily (↥(faceSet a I.1)) (nI I + 1) (A.radius a) :=
  analyticUniformSeries (A.radius_pos a) (A.radius_lt_half a) (recentred a H I)
    (continuousOn_recentred a (A.buffer_mem a) I (by linarith [A.bufferRadius_pos a]) hH)
    fun s _ hz => norm_recentred_le a I (by linarith [A.bufferRadius_pos a]) hM s
      (norm_le_of_mem_closedPolydisc (by linarith [A.bufferRadius_pos a]) hz)

/-- F. The evaluation identity on the real ball of radius `A.radius`: the series reconstructs
`Re H` at the recentred point (the identification with the original real function is made in
`faceSeries`, through the packet's real-slice agreement). -/
theorem evalF_uniformSeries (H : (Fin d → ℂ) → ℂ) (hH : DifferentiableOn ℂ H A.Ω)
    (hM : ∀ w ∈ piBox d (Icc 0 a), ∀ z : Fin d → ℂ, ‖z‖ ≤ A.bufferRadius a →
      ‖H (complexify w + z)‖ ≤ A.bound a) (I : NonemptyIdx d) (s : ↥(faceSet a I.1))
    {u : Fin (nI I + 1) → ℝ} (hu : ‖u‖ < A.radius a) :
    evalF ((A.uniformSeries a H hH hM I).f s) u =
      (H (complexify (originalNormalMap I s.1 u))).re := by
  rw [complexify_originalNormalMap]
  change evalF (polyRealCoeff (nI I + 1) (A.bufferRadius a / 2) (recentred a H I s)) u = _
  refine evalF_polyRealCoeff_of_lt (by linarith [A.bufferRadius_pos a]) (A.half_lt_buffer a)
    (differentiableOn_recentred a (A.buffer_mem a) I (A.bufferRadius_pos a) hH s) fun i => ?_
  rw [Complex.norm_real]
  exact (norm_le_pi_norm u i).trans_lt (hu.trans (A.radius_lt_half a))

theorem complexify_originalNormalMap_mem (I : NonemptyIdx d) (s : ↥(faceSet a I.1))
    {u : Fin (nI I + 1) → ℝ} (hu : ‖u‖ < A.radius a) :
    complexify (originalNormalMap I s.1 u) ∈ A.Ω := by
  rw [complexify_originalNormalMap]
  refine recentred_mem a (A.buffer_mem a) I s ((norm_complexify_le u).trans ?_)
  have := A.bufferRadius_pos a
  unfold radius at hu
  linarith

/-- ★★ **The original face series of a holomorphic box extension** at the common radius
`A.radius`. -/
noncomputable def faceSeries (I : NonemptyIdx d) : OriginalFaceSeries a ϕ φ I where
  ρ := A.radius a
  hρ := A.radius_pos a
  Fϕ := A.uniformSeries a A.Hϕ A.holϕ (A.bound_ϕ a) I
  Fφ := A.uniformSeries a A.Hφ A.holφ (A.bound_φ a) I
  hϕ_eq := fun s _ hz =>
    (A.eqϕ _ (A.complexify_originalNormalMap_mem a I s hz)).trans
      (A.evalF_uniformSeries a A.Hϕ A.holϕ (A.bound_ϕ a) I s hz).symm
  hφ_eq := fun s _ hz =>
    (A.eqφ _ (A.complexify_originalNormalMap_mem a I s hz)).trans
      (A.evalF_uniformSeries a A.Hφ A.holφ (A.bound_φ a) I s hz).symm

theorem faceSeries_ρ (I : NonemptyIdx d) : (A.faceSeries a I).ρ = A.radius a := rfl

end HolomorphicBoxExtension

/-- ★★ **The bridge**: a holomorphic box extension yields original-variable face series at a
common positive radius for every nonempty coordinate set. -/
theorem exists_originalFaceSeries_of_holomorphicBoxExtension {ϕ φ : (Fin d → ℝ) → ℝ}
    (A : HolomorphicBoxExtension a ϕ φ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ O : ∀ I : NonemptyIdx d, OriginalFaceSeries a ϕ φ I, ∀ I, (O I).ρ = ρ :=
  ⟨A.radius a, A.radius_pos a, A.faceSeries a, fun _ => rfl⟩

end WaterFilling

end Grammar
