/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.ComplexNormalInsertion

/-!
# Holomorphic extensions near the box: the uniform buffer (CCCXXX; phase 3, unit P3)

Consult #98 §1.1, §3.3–3.4. The primary analytic hypothesis of the bridge is the packet
`HolomorphicBoxExtension a ϕ φ`: an open `Ω ⊆ ℂ^d` containing the complexified box `[0,a]^d`,
holomorphic `Hϕ Hφ` on `Ω`, and agreement `ϕ w = Re Hϕ (complexify w)` on the REAL SLICE of `Ω`
(the normal form of "agreement on a real neighbourhood of the box"; agreement only on the box would
be a different theorem, about chosen extensions).

Compactness of the embedded box gives a UNIFORM buffer `R > 0` with `complexify w + z ∈ Ω` for all
`w ∈ [0,a]^d` and `‖z‖ ≤ R` (`exists_uniform_complex_box_buffer`, from the closed thickening
`IsCompact.exists_cthickening_subset_open`), the compact tube `tube a R = {complexify w + z}`
lies in `Ω` (`isCompact_tube`, `tube_subset`), and a holomorphic function on `Ω` is uniformly
bounded on it (`exists_bound_on_tube`). One radius and one bound serve all faces.
Zero `sorry`/`axiom`.
-/

open Set Filter Topology

namespace Grammar

namespace WaterFilling

variable {d : ℕ} (a : ℝ)

/-- **Holomorphic box extension**: holomorphic extensions of the prior and the observable on a
complex neighbourhood of the box, agreeing with them on its real slice. Convention: the
extensions are holomorphic REPRESENTATIVES whose real parts agree
with `ϕ, φ` on the real slice of `Ω` (`ϕ w = Re Hϕ (complexify w)`), not complex-valued identities;
the imaginary parts on the real slice are unconstrained. -/
structure HolomorphicBoxExtension (ϕ φ : (Fin d → ℝ) → ℝ) where
  /-- the complex neighbourhood -/
  Ω : Set (Fin d → ℂ)
  isOpen_Ω : IsOpen Ω
  box_subset : ∀ w ∈ piBox d (Icc 0 a), complexify w ∈ Ω
  /-- the holomorphic extensions -/
  Hϕ : (Fin d → ℂ) → ℂ
  Hφ : (Fin d → ℂ) → ℂ
  holϕ : DifferentiableOn ℂ Hϕ Ω
  holφ : DifferentiableOn ℂ Hφ Ω
  eqϕ : ∀ w, complexify w ∈ Ω → ϕ w = (Hϕ (complexify w)).re
  eqφ : ∀ w, complexify w ∈ Ω → φ w = (Hφ (complexify w)).re

theorem isCompact_complexify_box : IsCompact (complexify '' piBox d (Icc 0 a)) :=
  (isCompact_univ_pi fun _ => isCompact_Icc).image continuous_complexify

/-- ★ **The uniform complex buffer**: an open set containing the complexified box contains all
`complexify w + z` with `w` in the box and `‖z‖ ≤ R`, for some `R > 0`. -/
theorem exists_uniform_complex_box_buffer {Ω : Set (Fin d → ℂ)} (hΩ : IsOpen Ω)
    (hWΩ : ∀ w ∈ piBox d (Icc 0 a), complexify w ∈ Ω) :
    ∃ R : ℝ, 0 < R ∧ ∀ w ∈ piBox d (Icc 0 a), ∀ z : Fin d → ℂ, ‖z‖ ≤ R →
      complexify w + z ∈ Ω := by
  obtain ⟨R, hR, hsub⟩ := (isCompact_complexify_box a).exists_cthickening_subset_open hΩ (by
    rintro _ ⟨w, hw, rfl⟩
    exact hWΩ w hw)
  refine ⟨R, hR, fun w hw z hz => hsub (Metric.mem_cthickening_of_dist_le _ _ _ _ ⟨w, hw, rfl⟩ ?_)⟩
  rw [dist_eq_norm, add_sub_cancel_left]
  exact hz

/-- The compact tube `{complexify w + z : w ∈ [0,a]^d, ‖z‖ ≤ R}` around the embedded box. -/
def tube (R : ℝ) : Set (Fin d → ℂ) :=
  (fun p : (Fin d → ℝ) × (Fin d → ℂ) => complexify p.1 + p.2) ''
    (piBox d (Icc 0 a) ×ˢ Metric.closedBall 0 R)

theorem isCompact_tube (R : ℝ) : IsCompact (tube (d := d) a R) := by
  have hK : IsCompact (piBox d (Icc 0 a)) := isCompact_univ_pi fun _ => isCompact_Icc
  exact (hK.prod (isCompact_closedBall 0 R)).image
    (show Continuous fun p : (Fin d → ℝ) × (Fin d → ℂ) => complexify p.1 + p.2 from
      (continuous_complexify.comp continuous_fst).add continuous_snd)

theorem mem_tube {R : ℝ} {w : Fin d → ℝ} (hw : w ∈ piBox d (Icc 0 a)) {z : Fin d → ℂ}
    (hz : ‖z‖ ≤ R) : complexify w + z ∈ tube a R :=
  ⟨(w, z), ⟨hw, mem_closedBall_zero_iff.2 hz⟩, rfl⟩

theorem tube_subset {Ω : Set (Fin d → ℂ)} {R : ℝ}
    (hbuf : ∀ w ∈ piBox d (Icc 0 a), ∀ z : Fin d → ℂ, ‖z‖ ≤ R → complexify w + z ∈ Ω) :
    tube a R ⊆ Ω := by
  rintro _ ⟨⟨w, z⟩, ⟨hw, hz⟩, rfl⟩
  exact hbuf w hw z (mem_closedBall_zero_iff.1 hz)

/-- ★ **Uniform bound on the tube**: a holomorphic function on `Ω` is bounded on the compact
tube. -/
theorem exists_bound_on_tube {Ω : Set (Fin d → ℂ)} {R : ℝ} {H : (Fin d → ℂ) → ℂ}
    (hH : DifferentiableOn ℂ H Ω)
    (hbuf : ∀ w ∈ piBox d (Icc 0 a), ∀ z : Fin d → ℂ, ‖z‖ ≤ R → complexify w + z ∈ Ω) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ w ∈ piBox d (Icc 0 a), ∀ z : Fin d → ℂ, ‖z‖ ≤ R →
      ‖H (complexify w + z)‖ ≤ M := by
  obtain ⟨C, hC⟩ := (isCompact_tube a R).exists_bound_of_continuousOn
    (hH.continuousOn.mono (tube_subset a hbuf))
  exact ⟨max C 0, le_max_right _ _, fun w hw z hz =>
    (hC _ (mem_tube a hw hz)).trans (le_max_left _ _)⟩

namespace HolomorphicBoxExtension

variable {ϕ φ : (Fin d → ℝ) → ℝ} (A : HolomorphicBoxExtension a ϕ φ)

/-- The buffer radius of the extension. -/
theorem exists_buffer : ∃ R : ℝ, 0 < R ∧ ∀ w ∈ piBox d (Icc 0 a), ∀ z : Fin d → ℂ, ‖z‖ ≤ R →
    complexify w + z ∈ A.Ω :=
  exists_uniform_complex_box_buffer a A.isOpen_Ω A.box_subset

/-- Uniform bounds for both extensions on a common tube. -/
theorem exists_bounds {R : ℝ}
    (hbuf : ∀ w ∈ piBox d (Icc 0 a), ∀ z : Fin d → ℂ, ‖z‖ ≤ R → complexify w + z ∈ A.Ω) :
    ∃ M : ℝ, 0 ≤ M ∧ (∀ w ∈ piBox d (Icc 0 a), ∀ z : Fin d → ℂ, ‖z‖ ≤ R →
      ‖A.Hϕ (complexify w + z)‖ ≤ M) ∧
      ∀ w ∈ piBox d (Icc 0 a), ∀ z : Fin d → ℂ, ‖z‖ ≤ R → ‖A.Hφ (complexify w + z)‖ ≤ M := by
  obtain ⟨M₁, hM₁, h₁⟩ := exists_bound_on_tube a A.holϕ hbuf
  obtain ⟨M₂, hM₂, h₂⟩ := exists_bound_on_tube a A.holφ hbuf
  exact ⟨max M₁ M₂, le_trans hM₁ (le_max_left _ _),
    fun w hw z hz => (h₁ w hw z hz).trans (le_max_left _ _),
    fun w hw z hz => (h₂ w hw z hz).trans (le_max_right _ _)⟩

end HolomorphicBoxExtension

end WaterFilling

end Grammar
