/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.MomentKernelData
import Grammar.LocalAnalyticInputs
import Grammar.ExpansionCongruence

/-!
# The explicit kernel of the coordinate box producer and its observable independence
(CCCLI; programme J-min, unit J2)

The kernel data of the coordinate box certificate (CCCXXV) is the explicit
`coordKernelData k hk a δ hδ f`: bases the compact stratum pieces of the collar, base measures the
coordinate Lebesgue measures pulled back along the tangential embeddings, orders `(0, k)`, sides
`side k I δ`, the diagonal frames, and density families `J · f_I` where `f_I` is the prior's
normalised face series — the observable does not appear (`kernelData_coeffCertificate`, by `rfl`).
For a holomorphic packet the produced kernel depends on the packet only through its complex
neighbourhood and the prior's extension: replacing the observable's extension (`withObs`) leaves the
kernel unchanged (★ `producedKernel_withObs`, by `rfl` on the prior's face-series coefficients).
Hence ★★ `hasCoordFreeExpansion_withObs`: every observable with a holomorphic extension on the
packet's neighbourhood has the coordinate-free expansion with the SAME stratum measures and the
SAME coefficient field — the transfer of the expansion to an observable-independent kernel
(J2 gate of #104). Not included: linearity of the jet functional (J3), the continuity bound (J4).
-/

open MeasureTheory Set Filter Topology

namespace Grammar

namespace WaterFilling

open NormalisedBox CoeffFamily CoordModel

section CoordKernel

variable {d : ℕ} (k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (a δ : ℝ) (hδ : 0 < δ)

/-! ### The explicit coordinate kernel -/

/-- ★ **The explicit kernel of the coordinate box collar** for prior face series `f`. -/
noncomputable def coordKernelData
    (f : ∀ I : NonemptyIdx d, KI k hk a δ I.1 → CoeffFamily (nI I + 1)) :
    MomentKernelData (geometry d k (zeroOrders d) hk) (normalData d k (zeroOrders d) hk) where
  M := numCores d
  n := fun i => nI (coreIdx i)
  strat := fun i => (coreIdx i).1
  base := fun i => baseStratum k hk a δ (coreIdx i).1
  isCompact_base := fun i => isCompact_baseStratum k hk a δ (coreIdx i).1 (coreIdx i).2 hδ
  ν := fun i => baseMeasure (coreIdx i).1 (eI k hk a δ (coreIdx i).1)
  isFiniteMeasure_ν := fun i => by
    have := instK k hk a δ hδ
    exact isFiniteMeasure_baseMeasure (coreIdx i).1 (eI k hk a δ (coreIdx i).1)
      (continuous_eI k hk a δ (coreIdx i).1) (eI_injective k hk a δ (coreIdx i).1)
  h := fun _ _ => 0
  k := fun i => kι k (coreIdx i).1 (σI (coreIdx i))
  β := 1
  b := fun i => side k (coreIdx i).1 δ
  frame := fun i s => frameI k hk a δ hδ (coreIdx i) s
  cc := fun i s γ => J (coreIdx i).1 (eI k hk a δ (coreIdx i).1) (lamT k (coreIdx i).1 δ) s *
    f (coreIdx i) s γ

/-- The common lattice of the coordinate kernel. -/
noncomputable def coordQ : ℕ :=
  commonQ fun i : Fin (numCores d) => kι k (coreIdx i).1 (σI (coreIdx i))

variable (ϕ φ : (Fin d → ℝ) → ℝ) (hϕm : Measurable ϕ) (hϕ0 : ∀ w, 0 ≤ ϕ w)
  (hφint : Integrable φ
    ((volume.restrict (piBox d (Icc 0 a))).withDensity fun w => ENNReal.ofReal (ϕ w)))
  (hd : 0 < d) (ha : 0 < a) (hδa : ∀ i, δ ^ ((d : ℝ)⁻¹) < a ^ (2 * k i))
  (F : ∀ I : NonemptyIdx d, FaceSeries k hk a δ ϕ φ I)

/-- ★ **The kernel data of the coordinate certificate is the explicit kernel** of the prior's
face series: the observable does not enter. -/
theorem kernelData_coeffCertificate :
    (coeffCertificate k hk a δ hδ ϕ φ hϕm hϕ0 hφint hd ha hδa F).kernelData =
      coordKernelData k hk a δ hδ (fun I => (F I).Fϕ.f) := rfl

theorem commonQ_coordKernelData
    (f : ∀ I : NonemptyIdx d, KI k hk a δ I.1 → CoeffFamily (nI I + 1)) :
    commonQ (coordKernelData k hk a δ hδ f).k = coordQ k := rfl

theorem commonD_coordKernelData (hd : 0 < d)
    (f : ∀ I : NonemptyIdx d, KI k hk a δ I.1 → CoeffFamily (nI I + 1)) :
    commonD (coordKernelData k hk a δ hδ f).n = d - 1 := commonD_collar hd

end CoordKernel

/-! ### Packets with the observable's extension replaced -/

namespace HolomorphicBoxExtension

section Packet

variable {d : ℕ} {a : ℝ} {ϕ φ φ' : (Fin d → ℝ) → ℝ} (A : HolomorphicBoxExtension a ϕ φ)
  (H' : (Fin d → ℂ) → ℂ) (hol' : DifferentiableOn ℂ H' A.Ω)
  (eq' : ∀ w, complexify w ∈ A.Ω → φ' w = (H' (complexify w)).re)

/-- The packet with the observable's extension replaced (same neighbourhood, same prior). -/
def withObs : HolomorphicBoxExtension a ϕ φ' where
  Ω := A.Ω
  isOpen_Ω := A.isOpen_Ω
  box_subset := A.box_subset
  Hϕ := A.Hϕ
  Hφ := H'
  holϕ := A.holϕ
  holφ := hol'
  eqϕ := A.eqϕ
  eqφ := eq'

theorem withObs_Ω : (A.withObs H' hol' eq').Ω = A.Ω := rfl

theorem withObs_radius : (A.withObs H' hol' eq').radius a = A.radius a := rfl

theorem withObs_faceSeries_ρ (I : NonemptyIdx d) :
    ((A.withObs H' hol' eq').toRep.faceSeries a I).ρ = (A.toRep.faceSeries a I).ρ := rfl

theorem withObs_faceSeries_Fϕ_f (I : NonemptyIdx d) :
    ((A.withObs H' hol' eq').toRep.faceSeries a I).Fϕ.f = (A.toRep.faceSeries a I).Fϕ.f := rfl

variable (k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (δ : ℝ) (hδ : 0 < δ) (hd : 0 < d) (ha : 0 < a)
  (hδa : ∀ i, δ ^ ((d : ℝ)⁻¹) < a ^ (2 * k i)) (hϕ0W : ∀ w ∈ piBox d (Icc 0 a), 0 ≤ ϕ w)
  (hsmall : ∀ (I : NonemptyIdx d) (i : Fin (nI I + 1)),
    2 * δ ^ ((d : ℝ)⁻¹ * ((2 * k (σI I i).1 : ℕ) : ℝ)⁻¹) < (A.toRep.faceSeries a I).ρ)
  (hsmall' : ∀ (I : NonemptyIdx d) (i : Fin (nI I + 1)),
    2 * δ ^ ((d : ℝ)⁻¹ * ((2 * k (σI I i).1 : ℕ) : ℝ)⁻¹) <
      ((A.withObs H' hol' eq').toRep.faceSeries a I).ρ)

/-- The produced kernel of a packet. -/
noncomputable def producedKernel :
    MomentKernelData (geometry d k (zeroOrders d) hk) (normalData d k (zeroOrders d) hk) :=
  (producedCoeffCertificate k hk A hd ha hϕ0W δ hδ hδa hsmall).kernelData

/-- The prior's normalised face-series coefficients of the produced certificate. -/
noncomputable def producedPriorCoeff (I : NonemptyIdx d) :
    KI k hk a δ I.1 → CoeffFamily (nI I + 1) :=
  (((A.toRep.faceSeries a I).toFaceSeries k hk a δ hδ hd ha (hsmall I)).toPosPart k hk a δ hδ hd ha
    hδa (A.priorRep_nonneg_on hϕ0W)).Fϕ.f

theorem producedKernel_eq :
    producedKernel A k hk δ hδ hd ha hδa hϕ0W hsmall =
      coordKernelData k hk a δ hδ (producedPriorCoeff A k hk δ hδ hd ha hδa hϕ0W hsmall) := rfl

/-- The prior's face-series coefficients do not depend on the observable's extension. -/
theorem producedPriorCoeff_withObs :
    producedPriorCoeff (A.withObs H' hol' eq') k hk δ hδ hd ha hδa hϕ0W hsmall' =
      producedPriorCoeff A k hk δ hδ hd ha hδa hϕ0W hsmall := rfl

/-- ★ **The produced kernel does not depend on the observable's extension.** -/
theorem producedKernel_withObs :
    producedKernel (A.withObs H' hol' eq') k hk δ hδ hd ha hδa hϕ0W hsmall' =
      producedKernel A k hk δ hδ hd ha hδa hϕ0W hsmall := by
  rw [producedKernel_eq, producedKernel_eq, producedPriorCoeff_withObs]

/-! ### The transfer of the expansion to any observable with an extension on the packet's
neighbourhood -/

include H' hol' eq' in
/-- ★★ **The expansion with the observable-independent kernel**: every `φ'` with a holomorphic
extension on the packet's neighbourhood has the coordinate-free expansion with the stratum
measures and the coefficient field of the PRIOR's produced kernel, on the coordinate lattice with
log degree `d − 1`. -/
theorem hasCoordFreeExpansion_withObs :
    (normalData d k (zeroOrders d) hk).HasCoordFreeExpansion
      (producedKernel A k hk δ hδ hd ha hδa hϕ0W hsmall).stratumMeasure
      (producedKernel A k hk δ hδ hd ha hδa hϕ0W hsmall).field
      (spectrumLe (coordQ k) (d - 1)) (piBox d (Icc 0 a)) (CoordModel.phase d k) ϕ φ' := by
  have hsmall' : ∀ (I : NonemptyIdx d) (i : Fin (nI I + 1)),
      2 * δ ^ ((d : ℝ)⁻¹ * ((2 * k (σI I i).1 : ℕ) : ℝ)⁻¹) <
        ((A.withObs H' hol' eq').toRep.faceSeries a I).ρ := fun I i => by
    rw [withObs_faceSeries_ρ]
    exact hsmall I i
  set A' := A.withObs H' hol' eq' with hA'
  have h := (producedCoeffCertificate k hk A' hd ha hϕ0W δ hδ hδa hsmall').hasCoordFreeExpansion_le
    (measurable_phase d k) (measurable_posPart A'.measurable_priorRep) (posPart_nonneg _)
    A'.measurable_obsRep
  have hQ : commonQ (producedCertificate k hk A' hd ha hϕ0W δ hδ hδa hsmall').cores.k = coordQ k :=
    rfl
  have hD : commonD (producedCertificate k hk A' hd ha hϕ0W δ hδ hδa hsmall').n = d - 1 :=
    commonD_collar hd
  have hν : (producedCertificate k hk A' hd ha hϕ0W δ hδ hδa hsmall').stratumMeasure =
      (producedKernel A k hk δ hδ hd ha hδa hϕ0W hsmall).stratumMeasure :=
    ((producedCoeffCertificate k hk A' hd ha hϕ0W δ hδ hδa
      hsmall').stratumMeasure_eq_kernelData).trans (congrArg MomentKernelData.stratumMeasure
        (producedKernel_withObs A H' hol' eq' k hk δ hδ hd ha hδa hϕ0W hsmall hsmall'))
  have hB : (producedCoeffCertificate k hk A' hd ha hϕ0W δ hδ hδa hsmall').field =
      (producedKernel A k hk δ hδ hd ha hδa hϕ0W hsmall).field :=
    ((producedCoeffCertificate k hk A' hd ha hϕ0W δ hδ hδa
      hsmall').field_eq_kernelData).trans (congrArg MomentKernelData.field
        (producedKernel_withObs A H' hol' eq' k hk δ hδ hd ha hδa hϕ0W hsmall hsmall'))
  rw [hQ, hD, hν, hB] at h
  refine h.congr (measurableSet_W a) ?_ ?_
  · intro w hw
    rw [A'.obsRep_eq_of_mem (A'.box_subset_realDomain hw),
      posPart_eq_of_mem a (A'.priorRep_nonneg_on hϕ0W) hw,
      A'.priorRep_eq_of_mem (A'.box_subset_realDomain hw)]
  · intro I
    rw [← hν]
    filter_upwards [ae_stratumMeasure_mem_box k hk a δ hδ (posPart A'.priorRep) A'.obsRep
      (measurable_posPart A'.measurable_priorRep) (posPart_nonneg A'.priorRep)
      (integrable_posPart a (A'.priorRep_nonneg_on hϕ0W) A'.integrable_obsRep) hd ha hδa
      (fun I => ((A'.toRep.faceSeries a I).toFaceSeries k hk a δ hδ hd ha (hsmall' I)).toPosPart k
        hk a δ hδ hd ha hδa (A'.priorRep_nonneg_on hϕ0W)) I] with s hs
    exact eventually_of_mem (A'.isOpen_realDomain.mem_nhds (A'.box_subset_realDomain hs))
      fun w hw => A'.obsRep_eq_of_mem hw

end Packet

end HolomorphicBoxExtension

end WaterFilling

end Grammar
