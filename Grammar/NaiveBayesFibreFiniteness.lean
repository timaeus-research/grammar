/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.NaiveBayesFixedDomainDensity
import Grammar.NaiveBayesPushforward

/-!
# Fibre finiteness of the naive-Bayes pushforward density

The joint mass of the pushforward density is the mass of the uniform prior,
`∫_{(0,1)²} ∫ ρ(λ, μ) dμ dλ = 1` (`lintegral_nbFibreDensity_joint`, from DXCV's
`lintegral_nbBox_moments` with `Ψ = 1` and `volume nbBox = 1`), so by Tonelli the fibre integral
`∫ ρ(λ, μ) dμ` is finite for a.e. `λ` (`ae_lintegral_nbFibreDensity_lt_top`) and the real
fixed-domain density `μ ↦ nbFixedDensity (λ, μ)` of DCLV is integrable for a.e. `λ`, with real
fibre mass equal to the `ℝ≥0∞` one (`ae_integrable_nbFixedDensity`); the real double integral
is `1` (`integral_nbFixedDensity_joint`).  The fixed-`λ` density is NOT a probability density
(Astra round 18: at `λ = (½, ½)` the two sign intervals carry mass `2`); the pointwise fibre mass
`m(λ) = 2M₊(log(V/M₊²) + 2) + 2M₋(log(V/M₋²) + 2)` needs the support theorem and is not included.
Examples_slop §6.
Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Grammar

/-- The parameter cube has volume `1`. -/
theorem volume_nbBox : volume nbBox = 1 := by
  simp only [nbBox, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, sub_zero,
    ENNReal.ofReal_one, mul_one]

/-- ★★ The joint mass of the pushforward density is `1`. -/
theorem lintegral_nbFibreDensity_joint :
    ∫⁻ l in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, ∫⁻ z, nbFibreDensity l.1 l.2 z = 1 := by
  have h := lintegral_nbBox_moments (Ψ := fun _ => (1 : ℝ≥0∞)) measurable_const
  simp only [one_mul] at h
  rw [← h, setLIntegral_one, volume_nbBox]

theorem measurable_lintegral_nbFibreDensity :
    Measurable fun l : ℝ × ℝ => ∫⁻ z, nbFibreDensity l.1 l.2 z :=
  measurable_nbFibreDensity.lintegral_prod_right'

/-- ★★ A.e. fibre finiteness: for a.e. `λ ∈ (0,1)²`, `∫ ρ(λ, μ) dμ < ∞`. -/
theorem ae_lintegral_nbFibreDensity_lt_top :
    ∀ᵐ l ∂(volume.restrict (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)),
      ∫⁻ z, nbFibreDensity l.1 l.2 z < ⊤ :=
  ae_lt_top measurable_lintegral_nbFibreDensity
    (by rw [lintegral_nbFibreDensity_joint]; exact ENNReal.one_ne_top)

theorem measurable_nbFibreDensity_right (l : ℝ × ℝ) :
    Measurable fun z : ℝ => nbFibreDensity l.1 l.2 z :=
  measurable_nbFibreDensity.comp (measurable_const.prodMk measurable_id)

theorem nbFixedDensity_eq_toReal' (l : ℝ × ℝ) :
    (fun z : ℝ => nbFixedDensity (l, z)) = fun z => (nbFibreDensity l.1 l.2 z).toReal := by
  funext z
  exact nbFixedDensity_eq_toReal l.1 l.2 z

/-- ★★ A.e. fibre integrability of the real fixed-domain density, with the real fibre mass
equal to the `ℝ≥0∞` one. -/
theorem ae_integrable_nbFixedDensity :
    ∀ᵐ l ∂(volume.restrict (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)),
      Integrable (fun z : ℝ => nbFixedDensity (l, z)) ∧
        ENNReal.ofReal (∫ z : ℝ, nbFixedDensity (l, z)) = ∫⁻ z, nbFibreDensity l.1 l.2 z := by
  filter_upwards [ae_lintegral_nbFibreDensity_lt_top] with l hl
  have hm := measurable_nbFibreDensity_right l
  rw [nbFixedDensity_eq_toReal']
  refine ⟨integrable_toReal_of_lintegral_ne_top hm.aemeasurable hl.ne, ?_⟩
  rw [integral_toReal hm.aemeasurable (ae_lt_top hm hl.ne), ENNReal.ofReal_toReal hl.ne]

/-- ★★ The real double integral of the fixed-domain density over `(0,1)² × ℝ` is `1`. -/
theorem integral_nbFixedDensity_joint :
    ∫ l in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, ∫ z : ℝ, nbFixedDensity (l, z) = 1 := by
  have he : ∀ᵐ l ∂(volume.restrict (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)),
      ∫ z : ℝ, nbFixedDensity (l, z) = (∫⁻ z, nbFibreDensity l.1 l.2 z).toReal := by
    filter_upwards [ae_lintegral_nbFibreDensity_lt_top] with l hl
    have hm := measurable_nbFibreDensity_right l
    rw [nbFixedDensity_eq_toReal', integral_toReal hm.aemeasurable (ae_lt_top hm hl.ne)]
  rw [integral_congr_ae he,
    integral_toReal measurable_lintegral_nbFibreDensity.aemeasurable
      ae_lintegral_nbFibreDensity_lt_top,
    lintegral_nbFibreDensity_joint, ENNReal.toReal_one]

end Grammar
