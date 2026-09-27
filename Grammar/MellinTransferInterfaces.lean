/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.MellinLogPolynomialTransfer
import Grammar.PowerLogFaceCertificate

/-!
# Interfaces: the a.e.-measurable Mellin transfer, the fixed-domain parameter integral, and the
cube-set adapters

Astra round-16 targets 2–3 (polish): (1) `tendsto_mellin_sub_logPolynomial_ae` — DCXLIX with only
`AEStronglyMeasurable q (volume.restrict (Ioi 0))`, through a measurable representative;
(2) `measurable_fixedDomainIntegral` — measurability in the parameter of a fixed-domain integral
`p ↦ ∫ t in Ioo 0 1, (t(1−t))⁻¹ h p.1 t (p.2/(t(1−t)))` (the shape of the naive-Bayes pushforward
density `ρ(λ,μ) = ∫₀¹ dt/(t(1−t)) h_t(μ/(t(1−t)))`, examples_slop eq. nb_rho_integral) from joint
measurability of the composed kernel; (3) `integrableOn_powerLogFaceWeight_cube` and
`integrableOn_of_le_powerLogFaceWeight_cube` — DCXLVIII on the cube as a SET of `Fin d → ℝ` under
Lebesgue measure (`Measure.restrict_pi_pi`), with an a.e. domination adapter.  Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

/-! ### The a.e.-measurable Mellin transfer -/

/-- ★★ DCXLIX with an a.e.-strongly-measurable residual on `(0,∞)`. -/
theorem tendsto_mellin_sub_logPolynomial_ae {d : ℕ} (p : Fin (d + 1) → ℝ) {q : ℝ → ℝ} {a : ℝ}
    (ha : a < 1) (hq : AEStronglyMeasurable q (volume.restrict (Ioi (0 : ℝ))))
    (hsmall : IntegrableOn (fun v => v ^ (a - 1) * q v) (Ioc 0 1))
    (hlarge : IntegrableOn q (Ioi 1)) :
    Tendsto (fun z : ℝ => (∫ v in Ioi (0 : ℝ), v ^ (z - 1) * (q v + mellinLogTail p v)) -
      ∑ k : Fin (d + 1), p k * ((k : ℕ).factorial : ℝ) / (1 - z) ^ ((k : ℕ) + 1))
      (𝓝[<] (1 : ℝ)) (𝓝 (∫ v in Ioi (0 : ℝ), q v)) := by
  set q' := hq.mk q with hq'
  have hmeas : Measurable q' := hq.stronglyMeasurable_mk.measurable
  have hae : q =ᵐ[volume.restrict (Ioi (0 : ℝ))] q' := hq.ae_eq_mk
  have hae1 : q =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] q' :=
    ae_restrict_of_ae_restrict_of_subset Ioc_subset_Ioi_self hae
  have hae2 : q =ᵐ[volume.restrict (Ioi (1 : ℝ))] q' :=
    ae_restrict_of_ae_restrict_of_subset (Ioi_subset_Ioi zero_le_one) hae
  have hsmall' : IntegrableOn (fun v => v ^ (a - 1) * q' v) (Ioc 0 1) :=
    hsmall.congr (hae1.mono fun v hv => by simp only [hv])
  have hlarge' : IntegrableOn q' (Ioi 1) := hlarge.congr hae2
  have h := tendsto_mellin_sub_logPolynomial p ha hmeas hsmall' hlarge'
  have e1 : ∀ z : ℝ, (∫ v in Ioi (0 : ℝ), v ^ (z - 1) * (q' v + mellinLogTail p v)) =
      ∫ v in Ioi (0 : ℝ), v ^ (z - 1) * (q v + mellinLogTail p v) := fun z =>
    integral_congr_ae (hae.mono fun v hv => by simp only [hv])
  have e2 : (∫ v in Ioi (0 : ℝ), q' v) = ∫ v in Ioi (0 : ℝ), q v :=
    integral_congr_ae (hae.mono fun v hv => by simp only [hv])
  simp only [e1, e2] at h
  exact h

/-! ### Measurability of a fixed-domain parameter integral -/

variable {Λ : Type*} [MeasurableSpace Λ]

/-- ★★ The parameter integral `p ↦ ∫ t in (0,1), (t(1−t))⁻¹ h p.1 t (p.2/(t(1−t)))` is measurable
in `p : Λ × ℝ` when the composed kernel is jointly measurable. -/
theorem measurable_fixedDomainIntegral {h : Λ → ℝ → ℝ → ℝ}
    (hh : Measurable fun p : (Λ × ℝ) × ℝ => h p.1.1 p.2 (p.1.2 / (p.2 * (1 - p.2)))) :
    Measurable fun p : Λ × ℝ =>
      ∫ t in Ioo (0 : ℝ) 1, (t * (1 - t))⁻¹ * h p.1 t (p.2 / (t * (1 - t))) := by
  have hm : Measurable fun p : (Λ × ℝ) × ℝ =>
      (p.2 * (1 - p.2))⁻¹ * h p.1.1 p.2 (p.1.2 / (p.2 * (1 - p.2))) :=
    (measurable_snd.mul (measurable_const.sub measurable_snd)).inv.mul hh
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

/-! ### The certificate on the cube as a set -/

/-- The cube `(0,1)^d` as a set of `Fin d → ℝ`. -/
def unitCube (d : ℕ) : Set (Fin d → ℝ) := Set.pi univ fun _ => Ioo (0 : ℝ) 1

theorem measurableSet_unitCube (d : ℕ) : MeasurableSet (unitCube d) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioo

/-- The product-restricted measure of DCXLVIII is Lebesgue measure restricted to the cube. -/
theorem measure_pi_restrict_eq_restrict_unitCube (d : ℕ) :
    (Measure.pi fun _ : Fin d => (volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)) =
      (volume : Measure (Fin d → ℝ)).restrict (unitCube d) := by
  rw [unitCube, ← Measure.restrict_pi_pi]
  rfl

/-- ★★ DCXLVIII on the cube as a set: the face weight is integrable on `(0,1)^d`. -/
theorem integrableOn_powerLogFaceWeight_cube {d : ℕ} (a : Fin d → ℝ) (k : Fin d → ℕ)
    (ha : ∀ i, -1 < a i) : IntegrableOn (powerLogFaceWeight a k) (unitCube d) := by
  have := integrable_powerLogFaceWeight a k ha
  rwa [measure_pi_restrict_eq_restrict_unitCube] at this

/-- The a.e. domination adapter on the cube: `‖f‖ ≤ C·W` a.e. on the cube suffices. -/
theorem integrableOn_of_le_powerLogFaceWeight_cube {d : ℕ} {a : Fin d → ℝ} {k : Fin d → ℕ}
    (ha : ∀ i, -1 < a i) {f : (Fin d → ℝ) → ℝ}
    (hf : AEStronglyMeasurable f ((volume : Measure (Fin d → ℝ)).restrict (unitCube d)))
    {C : ℝ} (hC : ∀ᵐ x ∂(volume : Measure (Fin d → ℝ)).restrict (unitCube d),
      ‖f x‖ ≤ C * powerLogFaceWeight a k x) :
    IntegrableOn f (unitCube d) :=
  ((integrableOn_powerLogFaceWeight_cube a k ha).const_mul C).mono' hf hC

end Grammar
