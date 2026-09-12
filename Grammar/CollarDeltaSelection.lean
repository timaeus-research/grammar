/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.CoordinateBoxInputs

/-!
# Small-level selection for the collar (CCCXXVII)

Consult #97 §3.2: the collar level `δ` should be chosen AFTER the face series, so that the collar
fits their radii. For every radius `ρ > 0` there is `δ > 0` with `δ^{1/d} < a^{2k_i}` (the collar
lies in the box) and `2 δ^{1/(2k_i d)} < ρ` (the rescaled normal ball lies in the series ball) for
every `i` (`exists_delta`: every `δ ↦ δ^c`, `c > 0`, tends to `0` at `0⁺`, and there are finitely
many constraints). Hence the compact-box expansion from original-variable face series holds for
SOME collar level, with no smallness hypothesis left to the user
(`hasCoordFreeExpansion_collar_of_face_exists`): the certificate and its coefficient field are
exhibited for the chosen `δ`. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Grammar

namespace WaterFilling

open CoordModel

variable {d : ℕ} (k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (a : ℝ)

omit k hk a in
/-- `δ ↦ δ^c` tends to `0` at `0` for `c > 0`. -/
theorem tendsto_rpow_const_zero {c : ℝ} (hc : 0 < c) :
    Tendsto (fun δ : ℝ => δ ^ c) (𝓝 0) (𝓝 0) := by
  have h := (Real.continuousAt_rpow_const 0 c (Or.inr hc.le)).tendsto
  rwa [Real.zero_rpow hc.ne'] at h

include hk in
/-- ★ **Small-level selection**: for every radius `ρ > 0` there is a collar level `δ > 0` with
`δ^{1/d} < a^{2k_i}` and `2 δ^{1/(2k_i d)} < ρ` for every `i`. -/
theorem exists_delta (hd : 0 < d) (ha : 0 < a) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ δ : ℝ, 0 < δ ∧ (∀ i, δ ^ ((d : ℝ)⁻¹) < a ^ (2 * k i)) ∧
      ∀ i, 2 * δ ^ ((d : ℝ)⁻¹ * ((2 * k i : ℕ) : ℝ)⁻¹) < ρ := by
  have hdpos : (0 : ℝ) < (d : ℝ)⁻¹ := inv_pos.2 (by exact_mod_cast hd)
  have h1 : ∀ᶠ δ : ℝ in 𝓝 0, ∀ i, δ ^ ((d : ℝ)⁻¹) < a ^ (2 * k i) :=
    Filter.eventually_all.2 fun i =>
      (tendsto_rpow_const_zero hdpos).eventually_lt_const (pow_pos ha _)
  have h2 : ∀ᶠ δ : ℝ in 𝓝 0, ∀ i, δ ^ ((d : ℝ)⁻¹ * ((2 * k i : ℕ) : ℝ)⁻¹) < ρ / 2 :=
    Filter.eventually_all.2 fun i => by
      have hc : 0 < (d : ℝ)⁻¹ * ((2 * k i : ℕ) : ℝ)⁻¹ := by
        have := hk i
        positivity
      exact (tendsto_rpow_const_zero hc).eventually_lt_const (by linarith)
  have h3 : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), 0 < δ := self_mem_nhdsWithin
  obtain ⟨δ, hδ, h1δ, h2δ⟩ :=
    (h3.and ((h1.and h2).filter_mono nhdsWithin_le_nhds)).exists
  exact ⟨δ, hδ, h1δ, fun i => by linarith [h2δ i]⟩

variable (ϕ φ : (Fin d → ℝ) → ℝ)

/-- ★★★ **The compact-box expansion from original-variable face series, for some collar level**:
no smallness hypothesis is left to the user; the certificate and the coefficient field are
exhibited for the chosen `δ`. -/
theorem hasCoordFreeExpansion_collar_of_face_exists (hd : 0 < d) (ha : 0 < a)
    (hϕm : Measurable ϕ) (hϕ0 : ∀ w, 0 ≤ ϕ w) (hφm : Measurable φ)
    (hφint : Integrable φ
      ((volume.restrict (piBox d (Icc 0 a))).withDensity fun w => ENNReal.ofReal (ϕ w)))
    (O : ∀ I : NonemptyIdx d, OriginalFaceSeries a ϕ φ I) :
    ∃ (δ : ℝ) (hδ : 0 < δ) (hδa : ∀ i, δ ^ ((d : ℝ)⁻¹) < a ^ (2 * k i))
      (hsmall : ∀ (I : NonemptyIdx d) (i : Fin (nI I + 1)),
        2 * δ ^ ((d : ℝ)⁻¹ * ((2 * k (σI I i).1 : ℕ) : ℝ)⁻¹) < (O I).ρ),
      (normalData d k (zeroOrders d) hk).HasCoordFreeExpansion
        (certificate k hk a δ hδ ϕ φ hϕm hϕ0 hφint hd ha hδa
          fun I => (O I).toFaceSeries k hk a δ hδ hd ha (hsmall I)).stratumMeasure
        (coeffCertificate k hk a δ hδ ϕ φ hϕm hϕ0 hφint hd ha hδa
          fun I => (O I).toFaceSeries k hk a δ hδ hd ha (hsmall I)).field
        (spectrumLe (commonQ (certificate k hk a δ hδ ϕ φ hϕm hϕ0 hφint hd ha hδa
          fun I => (O I).toFaceSeries k hk a δ hδ hd ha (hsmall I)).cores.k) (d - 1))
        (piBox d (Icc 0 a)) (CoordModel.phase d k) ϕ φ := by
  -- the common lower radius over the finitely many faces
  have hne : Nonempty (NonemptyIdx d) :=
    ⟨⟨Finset.univ, ⟨⟨0, hd⟩, Finset.mem_univ _⟩⟩⟩
  obtain ⟨I₀, -, hI₀⟩ := Finset.exists_min_image Finset.univ (fun I : NonemptyIdx d => (O I).ρ)
    Finset.univ_nonempty
  obtain ⟨δ, hδ, hδa, hsm⟩ := exists_delta k hk a hd ha (O I₀).hρ
  have hsmall : ∀ (I : NonemptyIdx d) (i : Fin (nI I + 1)),
      2 * δ ^ ((d : ℝ)⁻¹ * ((2 * k (σI I i).1 : ℕ) : ℝ)⁻¹) < (O I).ρ := fun I i =>
    (hsm (σI I i).1).trans_le (hI₀ I (Finset.mem_univ _))
  exact ⟨δ, hδ, hδa, hsmall,
    hasCoordFreeExpansion_collar_of_face k hk a δ hϕm hφm hφint hδ hd ha hδa hϕ0 O hsmall⟩

end WaterFilling

end Grammar
