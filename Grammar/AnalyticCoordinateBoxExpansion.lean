/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.HolomorphicOriginalFaceSeries
import Grammar.CollarDeltaSelection

/-!
# The coordinate-free expansion from holomorphic data near the box (CCCXXXII; phase 3, unit P5)

Consult #98 §7. Composition of the bridge (CCCXXVIII–CCCXXXI) with the compact-box producer
(CCCXXIV–CCCXXVII): for the coordinate monomial phase on `[0,a]^d`, a prior and an observable that
are the real parts of holomorphic functions on a complex neighbourhood of the embedded box
(`HolomorphicBoxExtension`; the wrapper `HolomorphicBoxExtension.ofRealNhd` accepts agreement on a
real neighbourhood of the box instead of the real slice), together with the measurability,
nonnegativity and integrability assumptions of the producer, the original integral
`∫_{[0,a]^d} φ ϕ e^{−nK}` has the coordinate-free expansion for some collar level `δ`, with the
stratum measures and the coefficient field of the certificates constructed from these extensions
(★★★ `hasCoordFreeExpansion_of_holomorphicBoxExtension`; box-local nonnegativity:
★★★ `hasCoordFreeExpansion_of_holomorphicBoxExtension_nonneg_on`, with the certificate of `ϕ⁺`).

Non-claims: the holomorphic extensions are hypotheses (constructing them from real analyticity
is not part of this phase); the observable identity is used on the full open normal balls
(two-sided germs); global measurability of the functions is retained. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Grammar

namespace WaterFilling

open CoordModel

variable {d : ℕ} (a : ℝ)

/-- The real parts of the coordinates `ℂ^d → ℝ^d`. -/
def realParts (z : Fin d → ℂ) : Fin d → ℝ := fun j => (z j).re

theorem continuous_realParts : Continuous (realParts (d := d)) :=
  continuous_pi fun j => Complex.continuous_re.comp (continuous_apply j)

theorem realParts_complexify (w : Fin d → ℝ) : realParts (complexify w) = w := by
  funext j
  simp [realParts, complexify]

/-- **Agreement on a real neighbourhood suffices**: holomorphic extensions on an open `Ω ⊇` box
agreeing with `ϕ, φ` on an open real neighbourhood `V ⊇` box give a holomorphic box extension
(on `Ω ∩ {z : Re z ∈ V}`). -/
noncomputable def HolomorphicBoxExtension.ofRealNhd {ϕ φ : (Fin d → ℝ) → ℝ}
    {Ω : Set (Fin d → ℂ)} (hΩ : IsOpen Ω) (hWΩ : ∀ w ∈ piBox d (Icc 0 a), complexify w ∈ Ω)
    {Hϕ Hφ : (Fin d → ℂ) → ℂ} (hHϕ : DifferentiableOn ℂ Hϕ Ω) (hHφ : DifferentiableOn ℂ Hφ Ω)
    {V : Set (Fin d → ℝ)} (hV : IsOpen V) (hWV : piBox d (Icc 0 a) ⊆ V)
    (heqϕ : ∀ w ∈ V, ϕ w = (Hϕ (complexify w)).re) (heqφ : ∀ w ∈ V, φ w = (Hφ (complexify w)).re) :
    HolomorphicBoxExtension a ϕ φ where
  Ω := Ω ∩ realParts ⁻¹' V
  isOpen_Ω := hΩ.inter (hV.preimage continuous_realParts)
  box_subset := fun w hw => ⟨hWΩ w hw, by
    rw [mem_preimage, realParts_complexify]
    exact hWV hw⟩
  Hϕ := Hϕ
  Hφ := Hφ
  holϕ := hHϕ.mono inter_subset_left
  holφ := hHφ.mono inter_subset_left
  eqϕ := fun w hw => heqϕ w (by
    have := hw.2
    rwa [mem_preimage, realParts_complexify] at this)
  eqφ := fun w hw => heqφ w (by
    have := hw.2
    rwa [mem_preimage, realParts_complexify] at this)

variable (k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (ϕ φ : (Fin d → ℝ) → ℝ)
  (A : HolomorphicBoxExtension a ϕ φ) (hd : 0 < d) (ha : 0 < a) (hϕm : Measurable ϕ)
  (hφm : Measurable φ)
  (hφint : Integrable φ
    ((volume.restrict (piBox d (Icc 0 a))).withDensity fun w => ENNReal.ofReal (ϕ w)))

include hφm in
/-- ★★★ **The coordinate-free expansion from holomorphic data near the box** (globally nonnegative
prior): for some collar level `δ`, with the certificates built from the face series of the
extension. -/
theorem hasCoordFreeExpansion_of_holomorphicBoxExtension (hϕ0 : ∀ w, 0 ≤ ϕ w) :
    ∃ (δ : ℝ) (hδ : 0 < δ) (hδa : ∀ i, δ ^ ((d : ℝ)⁻¹) < a ^ (2 * k i))
      (hsmall : ∀ (I : NonemptyIdx d) (i : Fin (nI I + 1)),
        2 * δ ^ ((d : ℝ)⁻¹ * ((2 * k (σI I i).1 : ℕ) : ℝ)⁻¹) < (A.faceSeries a I).ρ),
      (normalData d k (zeroOrders d) hk).HasCoordFreeExpansion
        (certificate k hk a δ hδ ϕ φ hϕm hϕ0 hφint hd ha hδa
          fun I => (A.faceSeries a I).toFaceSeries k hk a δ hδ hd ha (hsmall I)).stratumMeasure
        (coeffCertificate k hk a δ hδ ϕ φ hϕm hϕ0 hφint hd ha hδa
          fun I => (A.faceSeries a I).toFaceSeries k hk a δ hδ hd ha (hsmall I)).field
        (spectrumLe (commonQ (certificate k hk a δ hδ ϕ φ hϕm hϕ0 hφint hd ha hδa
          fun I => (A.faceSeries a I).toFaceSeries k hk a δ hδ hd ha (hsmall I)).cores.k) (d - 1))
        (piBox d (Icc 0 a)) (CoordModel.phase d k) ϕ φ :=
  hasCoordFreeExpansion_collar_of_face_exists k hk a ϕ φ hd ha hϕm hϕ0 hφm hφint (A.faceSeries a)

include hφm in
/-- ★★★ **The coordinate-free expansion from holomorphic data near the box** (prior nonnegative on
the box): for some collar level `δ`, with the certificates of the positive part `ϕ⁺` built from the
face series of the extension. -/
theorem hasCoordFreeExpansion_of_holomorphicBoxExtension_nonneg_on
    (hϕ0W : ∀ w ∈ piBox d (Icc 0 a), 0 ≤ ϕ w) :
    ∃ (δ : ℝ) (hδ : 0 < δ) (hδa : ∀ i, δ ^ ((d : ℝ)⁻¹) < a ^ (2 * k i))
      (hsmall : ∀ (I : NonemptyIdx d) (i : Fin (nI I + 1)),
        2 * δ ^ ((d : ℝ)⁻¹ * ((2 * k (σI I i).1 : ℕ) : ℝ)⁻¹) < (A.faceSeries a I).ρ),
      (normalData d k (zeroOrders d) hk).HasCoordFreeExpansion
        (certificate k hk a δ hδ (posPart ϕ) φ (measurable_posPart hϕm) (posPart_nonneg ϕ)
          ((withDensity_posPart a hϕ0W).symm ▸ hφint) hd ha hδa fun I =>
            ((A.faceSeries a I).toFaceSeries k hk a δ hδ hd ha (hsmall I)).toPosPart k hk a δ hδ
              hd ha hδa hϕ0W).stratumMeasure
        (coeffCertificate k hk a δ hδ (posPart ϕ) φ (measurable_posPart hϕm) (posPart_nonneg ϕ)
          ((withDensity_posPart a hϕ0W).symm ▸ hφint) hd ha hδa fun I =>
            ((A.faceSeries a I).toFaceSeries k hk a δ hδ hd ha (hsmall I)).toPosPart k hk a δ hδ
              hd ha hδa hϕ0W).field
        (spectrumLe (commonQ (certificate k hk a δ hδ (posPart ϕ) φ (measurable_posPart hϕm)
          (posPart_nonneg ϕ) ((withDensity_posPart a hϕ0W).symm ▸ hφint) hd ha hδa fun I =>
            ((A.faceSeries a I).toFaceSeries k hk a δ hδ hd ha (hsmall I)).toPosPart k hk a δ hδ
              hd ha hδa hϕ0W).cores.k) (d - 1))
        (piBox d (Icc 0 a)) (CoordModel.phase d k) ϕ φ := by
  obtain ⟨δ, hδ, hδa, hsm⟩ := exists_delta k hk a hd ha (A.radius_pos a)
  have hsmall : ∀ (I : NonemptyIdx d) (i : Fin (nI I + 1)),
      2 * δ ^ ((d : ℝ)⁻¹ * ((2 * k (σI I i).1 : ℕ) : ℝ)⁻¹) < (A.faceSeries a I).ρ :=
    fun I i => hsm (σI I i).1
  exact ⟨δ, hδ, hδa, hsmall, hasCoordFreeExpansion_collar_of_nonneg_on k hk a δ hϕm hφm hφint hδ
    hd ha hδa hϕ0W fun I => (A.faceSeries a I).toFaceSeries k hk a δ hδ hd ha (hsmall I)⟩

end WaterFilling

end Grammar
