/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.AnalyticCoordinateBoxExpansion
import Grammar.ExpansionCongruence

/-!
# Local analytic inputs: no global measure hypotheses (CCCXXXIV; hygiene units H1–H3)

Consult #99 §A2/§B. The public expansion theorem from holomorphic data near the box
(CCCXXXII) still carried global hypotheses on the prior and the observable — measurability on
`ℝ^d` and integrability of the observable against the prior-weighted box measure — although
both functions are real parts of holomorphic functions near the box and arbitrary elsewhere.
Here they are discharged. On the **real domain** `{w : complexify w ∈ Ω}` (an open real
neighbourhood of the box) the extension packet determines the functions; the **measurable
representatives** `ϕ̃ = 1_U · Re Hϕ∘complexify`, `φ̃ = 1_U · Re Hφ∘complexify` agree with `ϕ, φ` on
the whole real domain (so they have the same two-sided normal germs at every point of the box),
are measurable (continuous on the open real domain, zero off it), bounded on the compact box,
and `φ̃` is integrable against the `ϕ̃`-weighted box measure (H1–H2). The same `Ω, Hϕ, Hφ` form an
extension packet for the representatives (`toRep`), the existing theorem applies to them, and the
expansion transfers to the original functions by the congruence of CCCXXXIII (the products agree
on the box; the certificate's stratum measures live in the box, where the germs agree) — H3:
★★★ `hasCoordFreeExpansion_of_holomorphicBoxExtension_local`, whose hypotheses are the packet,
`0 < d`, `0 < a` and nonnegativity of the prior on the box only, stated with the named produced
certificates `producedCertificate`, `producedCoeffCertificate`.

Non-claims: the certificates are those of the representatives' positive part (visibly produced);
the holomorphic extensions remain hypotheses. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Grammar

namespace WaterFilling

open CoordModel

variable {d : ℕ} {a : ℝ} {ϕ φ : (Fin d → ℝ) → ℝ}

namespace HolomorphicBoxExtension

variable (A : HolomorphicBoxExtension a ϕ φ)

/-- **The real domain** `{w : complexify w ∈ Ω}` of the extension: an open real neighbourhood of
the box on which the packet determines the prior and the observable. -/
def realDomain : Set (Fin d → ℝ) := complexify ⁻¹' A.Ω

theorem isOpen_realDomain : IsOpen A.realDomain := A.isOpen_Ω.preimage continuous_complexify

theorem box_subset_realDomain : piBox d (Icc 0 a) ⊆ A.realDomain := fun w hw => A.box_subset w hw

/-- The measurable representative of the prior: `Re Hϕ ∘ complexify` on the real domain, `0`
off it. -/
noncomputable def priorRep : (Fin d → ℝ) → ℝ :=
  A.realDomain.indicator fun w => (A.Hϕ (complexify w)).re

/-- The measurable representative of the observable. -/
noncomputable def obsRep : (Fin d → ℝ) → ℝ :=
  A.realDomain.indicator fun w => (A.Hφ (complexify w)).re

theorem priorRep_eq_of_mem {w : Fin d → ℝ} (hw : w ∈ A.realDomain) : A.priorRep w = ϕ w := by
  unfold priorRep
  rw [indicator_of_mem hw, A.eqϕ w hw]

theorem obsRep_eq_of_mem {w : Fin d → ℝ} (hw : w ∈ A.realDomain) : A.obsRep w = φ w := by
  unfold obsRep
  rw [indicator_of_mem hw, A.eqφ w hw]

theorem continuousOn_re_Hϕ :
    ContinuousOn (fun w => (A.Hϕ (complexify w)).re) A.realDomain :=
  Complex.continuous_re.comp_continuousOn
    (A.holϕ.continuousOn.comp continuous_complexify.continuousOn (mapsTo_preimage _ _))

theorem continuousOn_re_Hφ :
    ContinuousOn (fun w => (A.Hφ (complexify w)).re) A.realDomain :=
  Complex.continuous_re.comp_continuousOn
    (A.holφ.continuousOn.comp continuous_complexify.continuousOn (mapsTo_preimage _ _))

theorem continuousOn_priorRep : ContinuousOn A.priorRep A.realDomain :=
  A.continuousOn_re_Hϕ.congr fun _ hw => indicator_of_mem hw _

theorem continuousOn_obsRep : ContinuousOn A.obsRep A.realDomain :=
  A.continuousOn_re_Hφ.congr fun _ hw => indicator_of_mem hw _

/-- ★ **The representatives are measurable** (continuous on the open real domain, `0` off it). -/
theorem measurable_priorRep : Measurable A.priorRep := by
  classical
  unfold priorRep
  rw [← Set.piecewise_eq_indicator]
  exact A.continuousOn_re_Hϕ.measurable_piecewise continuousOn_const
    A.isOpen_realDomain.measurableSet

theorem measurable_obsRep : Measurable A.obsRep := by
  classical
  unfold obsRep
  rw [← Set.piecewise_eq_indicator]
  exact A.continuousOn_re_Hφ.measurable_piecewise continuousOn_const
    A.isOpen_realDomain.measurableSet

/-- **The extension packet of the representatives**: the same `Ω`, `Hϕ`, `Hφ`. -/
def toRep : HolomorphicBoxExtension a A.priorRep A.obsRep where
  Ω := A.Ω
  isOpen_Ω := A.isOpen_Ω
  box_subset := A.box_subset
  Hϕ := A.Hϕ
  Hφ := A.Hφ
  holϕ := A.holϕ
  holφ := A.holφ
  eqϕ := fun w hw => by
    unfold priorRep
    rw [indicator_of_mem (show w ∈ A.realDomain from hw)]
  eqφ := fun w hw => by
    unfold obsRep
    rw [indicator_of_mem (show w ∈ A.realDomain from hw)]

theorem priorRep_nonneg_on (hϕ0W : ∀ w ∈ piBox d (Icc 0 a), 0 ≤ ϕ w) :
    ∀ w ∈ piBox d (Icc 0 a), 0 ≤ A.priorRep w := fun w hw => by
  rw [A.priorRep_eq_of_mem (A.box_subset_realDomain hw)]
  exact hϕ0W w hw

theorem isCompact_box : IsCompact (piBox d (Icc 0 a)) :=
  isCompact_univ_pi fun _ => isCompact_Icc

theorem exists_bound_priorRep : ∃ B : ℝ, ∀ w ∈ piBox d (Icc 0 a), ‖A.priorRep w‖ ≤ B :=
  isCompact_box.exists_bound_of_continuousOn
    (A.continuousOn_priorRep.mono A.box_subset_realDomain)

theorem exists_bound_obsRep : ∃ B : ℝ, ∀ w ∈ piBox d (Icc 0 a), ‖A.obsRep w‖ ≤ B :=
  isCompact_box.exists_bound_of_continuousOn (A.continuousOn_obsRep.mono A.box_subset_realDomain)

/-- ★ **Weighted integrability of the observable representative** against the prior-weighted
box measure: both representatives are bounded on the compact box. -/
theorem integrable_obsRep :
    Integrable A.obsRep ((volume.restrict (piBox d (Icc 0 a))).withDensity
      fun w => ENNReal.ofReal (A.priorRep w)) := by
  obtain ⟨Bϕ, hBϕ⟩ := A.exists_bound_priorRep
  obtain ⟨Bφ, hBφ⟩ := A.exists_bound_obsRep
  have hW : MeasurableSet (piBox d (Icc 0 a)) := measurableSet_W a
  have hle : ∫⁻ w in piBox d (Icc 0 a), ENNReal.ofReal (A.priorRep w) ≤
      ∫⁻ _ in piBox d (Icc 0 a), ENNReal.ofReal Bϕ := by
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem hW] with w hw
    exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (by
      have := hBϕ w hw
      rwa [Real.norm_eq_abs] at this))
  have hfin : ∫⁻ w in piBox d (Icc 0 a), ENNReal.ofReal (A.priorRep w) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ hle
    rw [setLIntegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top isCompact_box.measure_lt_top.ne
  have : IsFiniteMeasure
      ((volume.restrict (piBox d (Icc 0 a))).withDensity fun w => ENNReal.ofReal (A.priorRep w)) :=
    isFiniteMeasure_withDensity hfin
  refine Integrable.of_bound A.measurable_obsRep.aestronglyMeasurable Bφ ?_
  have hae : ∀ᵐ w ∂((volume.restrict (piBox d (Icc 0 a))).withDensity
      fun w => ENNReal.ofReal (A.priorRep w)), w ∈ piBox d (Icc 0 a) :=
    mem_ae_iff.2 ((withDensity_absolutelyContinuous _ _) (mem_ae_iff.1 (ae_restrict_mem hW)))
  filter_upwards [hae] with w hw
  exact hBφ w hw

end HolomorphicBoxExtension

variable (k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (A : HolomorphicBoxExtension a ϕ φ) (hd : 0 < d)
  (ha : 0 < a) (hϕ0W : ∀ w ∈ piBox d (Icc 0 a), 0 ≤ ϕ w) (δ : ℝ) (hδ : 0 < δ)
  (hδa : ∀ i, δ ^ ((d : ℝ)⁻¹) < a ^ (2 * k i))
  (hsmall : ∀ (I : NonemptyIdx d) (i : Fin (nI I + 1)),
    2 * δ ^ ((d : ℝ)⁻¹ * ((2 * k (σI I i).1 : ℕ) : ℝ)⁻¹) < (A.toRep.faceSeries a I).ρ)

/-- **The produced certificate**: the compact-box certificate of the positive part of the prior
representative and the observable representative at collar level `δ`, from the face series of
the representatives' packet. -/
noncomputable def producedCertificate :
    ResolvedCertificate (geometry d k (zeroOrders d) hk) (normalData d k (zeroOrders d) hk)
      (piBox d (Icc 0 a)) (CoordModel.phase d k) (posPart A.priorRep) A.obsRep :=
  certificate k hk a δ hδ (posPart A.priorRep) A.obsRep (measurable_posPart A.measurable_priorRep)
    (posPart_nonneg A.priorRep)
    (integrable_posPart a (A.priorRep_nonneg_on hϕ0W) A.integrable_obsRep) hd ha hδa fun I =>
      ((A.toRep.faceSeries a I).toFaceSeries k hk a δ hδ hd ha (hsmall I)).toPosPart k hk a δ hδ hd
        ha hδa (A.priorRep_nonneg_on hϕ0W)

/-- **The produced coefficient certificate.** -/
noncomputable def producedCoeffCertificate :
    (producedCertificate k hk A hd ha hϕ0W δ hδ hδa hsmall).CoefficientCertificate :=
  coeffCertificate k hk a δ hδ (posPart A.priorRep) A.obsRep
    (measurable_posPart A.measurable_priorRep) (posPart_nonneg A.priorRep)
    (integrable_posPart a (A.priorRep_nonneg_on hϕ0W) A.integrable_obsRep) hd ha hδa fun I =>
      ((A.toRep.faceSeries a I).toFaceSeries k hk a δ hδ hd ha (hsmall I)).toPosPart k hk a δ hδ hd
        ha hδa (A.priorRep_nonneg_on hϕ0W)

omit δ hδ hδa hsmall in
/-- ★★★ **The coordinate-free expansion from holomorphic data near the box, with local inputs
only**: the hypotheses are the extension packet, `0 < d`, `0 < a` and nonnegativity of the prior
on the box. For some collar level `δ`, the original integral `∫_{[0,a]^d} φ ϕ e^{−nK}` has the
coordinate-free expansion with the stratum measures and the coefficient field of the produced
certificates (`producedCertificate`, `producedCoeffCertificate`). -/
theorem hasCoordFreeExpansion_of_holomorphicBoxExtension_local :
    ∃ (δ : ℝ) (hδ : 0 < δ) (hδa : ∀ i, δ ^ ((d : ℝ)⁻¹) < a ^ (2 * k i))
      (hsmall : ∀ (I : NonemptyIdx d) (i : Fin (nI I + 1)),
        2 * δ ^ ((d : ℝ)⁻¹ * ((2 * k (σI I i).1 : ℕ) : ℝ)⁻¹) < (A.toRep.faceSeries a I).ρ),
      (normalData d k (zeroOrders d) hk).HasCoordFreeExpansion
        (producedCertificate k hk A hd ha hϕ0W δ hδ hδa hsmall).stratumMeasure
        (producedCoeffCertificate k hk A hd ha hϕ0W δ hδ hδa hsmall).field
        (spectrumLe (commonQ (producedCertificate k hk A hd ha hϕ0W δ hδ hδa hsmall).cores.k)
          (d - 1))
        (piBox d (Icc 0 a)) (CoordModel.phase d k) ϕ φ := by
  obtain ⟨δ, hδ, hδa, hsmall, h⟩ :=
    hasCoordFreeExpansion_of_holomorphicBoxExtension_nonneg_on a k hk A.priorRep A.obsRep
      A.toRep hd ha A.measurable_priorRep A.measurable_obsRep A.integrable_obsRep
      (A.priorRep_nonneg_on hϕ0W)
  refine ⟨δ, hδ, hδa, hsmall, ?_⟩
  refine h.congr (measurableSet_W a) ?_ ?_
  · intro w hw
    rw [A.obsRep_eq_of_mem (A.box_subset_realDomain hw),
      A.priorRep_eq_of_mem (A.box_subset_realDomain hw)]
  · intro I
    filter_upwards [ae_stratumMeasure_mem_box k hk a δ hδ (posPart A.priorRep) A.obsRep
      (measurable_posPart A.measurable_priorRep) (posPart_nonneg A.priorRep)
      (integrable_posPart a (A.priorRep_nonneg_on hϕ0W) A.integrable_obsRep) hd ha hδa
      (fun I => ((A.toRep.faceSeries a I).toFaceSeries k hk a δ hδ hd ha (hsmall I)).toPosPart k
        hk a δ hδ hd ha hδa (A.priorRep_nonneg_on hϕ0W)) I] with s hs
    exact eventually_of_mem (A.isOpen_realDomain.mem_nhds (A.box_subset_realDomain hs))
      fun w hw => A.obsRep_eq_of_mem hw

end WaterFilling

end Grammar
