/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.JetFunctionalLinear

/-!
# The linear jet functional of the coordinate box (CCCLIII; programme J-min, unit J3 endpoint)

For a fixed prior packet (complex neighbourhood `Ω` of the box, holomorphic extension of the prior)
the observables with a holomorphic extension on `Ω` form a real vector space `obsSpace Ω`
(closed under sums and real scalars). Every such observable is certified for the prior's produced
kernel (`certified_of_mem`: the certificate of the packet with the observable's extension has the
same kernel, and the representative agrees with the observable on a neighbourhood of every base
point, `Certified.congr`). Hence the **linear jet functional**
★★★ `jetFunctional A … q : obsSpace A.Ω →ₗ[ℝ] ℝ`,
`ψ ↦ ∑_I ∫_{S_I} ∑'_r (1/r!)⟨D^r_⊥ψ, B_{I,r,q}⟩ dν_I` with the prior's stratum measures and
coefficient field, and ★★★ `hasCoordFreeExpansion_obsSpace`: for every `ψ ∈ obsSpace A.Ω`,
`∫_{[0,a]^d} ψ ϕ e^{−nK} = ∑_q (jetFunctional q ψ) · q.scale n + o(n^{−A})` on the coordinate
lattice — the observable-independent coefficient functional of consult #104 §3 (J3 gate: one
kernel, a linear functional on a genuine real vector space of observables; canonicity of its scalar
values across certificates is CCCVIII). Terminology (consult #105): a **linear coefficient
functional on analytic observables, represented by a convergent series of normal-jet pairings**
("analytic jet functional"). The exact-moment representation need not have finite normal order (at
a fixed spectral index it can involve arbitrarily high normal derivatives); no topology or
continuity on a smooth test-function space, and no distributional extension, is asserted.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

/-! ### Transport of certification along germs at the bases -/

namespace MomentKernelData

variable {d : ℕ} {U : Type*} [TopologicalSpace U] [T2Space U] [MeasurableSpace U] [BorelSpace U]
  {R : ResolvedGeometry d U} {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [MeasurableSpace A] [BorelSpace A] {D : ResolvedNormalData R A} {Kd : MomentKernelData R D}

omit [T2Space U] [BorelSpace U] [MeasurableSpace A] [BorelSpace A] in
/-- The pairing with the field only sees the germs of the observable at the base points. -/
theorem field_pair_congr {ψ ψ' : (Fin d → ℝ) → ℝ}
    (hψ : ∀ (J : Fin Kd.M) (t : ↥(Kd.base J)), ψ' =ᶠ[𝓝 (R.π (t.1 : U))] ψ)
    (I : Finset R.Component) (s : R.Stratum I) (r : ℕ) (q : PowerLogIndex) :
    (Kd.field I r q s).pair (D.normalDifferential ψ' I s r) =
      (Kd.field I r q s).pair (D.normalDifferential ψ I s r) := by
  by_cases hs : Kd.Covered I s
  · obtain ⟨J, hJ, hmem⟩ := hs
    subst hJ
    rw [D.normalDifferential_congr _ s (hψ J ⟨s, hmem⟩) r]
  · rw [Kd.field_eq_zero_of_not_covered hs]
    simp [MomentTensor.pair]

omit [T2Space U] [BorelSpace U] [MeasurableSpace A] [BorelSpace A] in
/-- ★ **Certification transports along germs at the bases.** -/
theorem Certified.congr {ψ ψ' : (Fin d → ℝ) → ℝ} (h : Kd.Certified ψ)
    (hψ : ∀ (J : Fin Kd.M) (t : ↥(Kd.base J)), ψ' =ᶠ[𝓝 (R.π (t.1 : U))] ψ) : Kd.Certified ψ' where
  smooth := h.smooth.congr hψ
  summable := fun I q s => by
    have := h.summable I q s
    refine this.congr fun r => ?_
    rw [field_pair_congr hψ I s r q]
  integrable := fun I q => by
    have := h.integrable I q
    refine this.congr (Eventually.of_forall fun s => ?_)
    simp only [field_pair_congr hψ I s _ q]

end MomentKernelData

namespace WaterFilling

open NormalisedBox CoeffFamily CoordModel

/-! ### The vector space of observables with a holomorphic extension on a fixed neighbourhood -/

variable {d : ℕ}

/-- **The observables with a holomorphic extension on `Ω`**, as a real subspace of the functions
on `ℝ^d`. -/
def obsSpace (Ω : Set (Fin d → ℂ)) : Submodule ℝ ((Fin d → ℝ) → ℝ) where
  carrier := {ψ | ∃ H : (Fin d → ℂ) → ℂ, DifferentiableOn ℂ H Ω ∧
    ∀ w, complexify w ∈ Ω → ψ w = (H (complexify w)).re}
  add_mem' := by
    rintro ψ₁ ψ₂ ⟨H₁, h₁, e₁⟩ ⟨H₂, h₂, e₂⟩
    exact ⟨H₁ + H₂, h₁.add h₂, fun w hw => by
      simp only [Pi.add_apply, e₁ w hw, e₂ w hw, Complex.add_re]⟩
  zero_mem' := ⟨0, differentiableOn_const 0, fun w _ => by simp⟩
  smul_mem' := by
    rintro c ψ ⟨H, h, e⟩
    exact ⟨fun z => (c : ℂ) * H z, h.const_mul _, fun w hw => by
      simp only [Pi.smul_apply, smul_eq_mul, e w hw, Complex.re_ofReal_mul]⟩

theorem mem_obsSpace {Ω : Set (Fin d → ℂ)} {ψ : (Fin d → ℝ) → ℝ} :
    ψ ∈ obsSpace Ω ↔ ∃ H : (Fin d → ℂ) → ℂ, DifferentiableOn ℂ H Ω ∧
      ∀ w, complexify w ∈ Ω → ψ w = (H (complexify w)).re := Iff.rfl

namespace HolomorphicBoxExtension

variable {a : ℝ} {ϕ φ : (Fin d → ℝ) → ℝ} (A : HolomorphicBoxExtension a ϕ φ)
  (k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (δ : ℝ) (hδ : 0 < δ) (hd : 0 < d) (ha : 0 < a)
  (hδa : ∀ i, δ ^ ((d : ℝ)⁻¹) < a ^ (2 * k i)) (hϕ0W : ∀ w ∈ piBox d (Icc 0 a), 0 ≤ ϕ w)
  (hsmall : ∀ (I : NonemptyIdx d) (i : Fin (nI I + 1)),
    2 * δ ^ ((d : ℝ)⁻¹ * ((2 * k (σI I i).1 : ℕ) : ℝ)⁻¹) < (A.toRep.faceSeries a I).ρ)

/-- The observable's extension of a packet lies in the observable space of its neighbourhood. -/
theorem obs_mem_obsSpace : φ ∈ obsSpace A.Ω := ⟨A.Hφ, A.holφ, A.eqφ⟩

/-- ★ **Every observable with an extension on the packet's neighbourhood is certified for the
prior's produced kernel.** -/
theorem certified_of_mem {ψ : (Fin d → ℝ) → ℝ} (hψ : ψ ∈ obsSpace A.Ω) :
    (producedKernel A k hk δ hδ hd ha hδa hϕ0W hsmall).Certified ψ := by
  obtain ⟨H, hH, e⟩ := hψ
  have hsmall' : ∀ (I : NonemptyIdx d) (i : Fin (nI I + 1)),
      2 * δ ^ ((d : ℝ)⁻¹ * ((2 * k (σI I i).1 : ℕ) : ℝ)⁻¹) <
        ((A.withObs H hH e).toRep.faceSeries a I).ρ := fun I i => by
    rw [withObs_faceSeries_ρ]
    exact hsmall I i
  have hcert := (producedCoeffCertificate k hk (A.withObs H hH e) hd ha hϕ0W δ hδ hδa
    hsmall').certified
  have hK : (producedCoeffCertificate k hk (A.withObs H hH e) hd ha hϕ0W δ hδ hδa
      hsmall').kernelData = producedKernel A k hk δ hδ hd ha hδa hϕ0W hsmall :=
    producedKernel_withObs A H hH e k hk δ hδ hd ha hδa hϕ0W hsmall hsmall'
  rw [hK] at hcert
  refine hcert.congr fun J t => ?_
  have hbox : (t.1 : Fin d → ℝ) ∈ piBox d (Icc 0 a) :=
    mem_box_of_mem_baseStratum k hk a δ ha _ t
  exact eventually_of_mem ((A.withObs H hH e).isOpen_realDomain.mem_nhds
    ((A.withObs H hH e).box_subset_realDomain hbox))
    fun w hw => ((A.withObs H hH e).obsRep_eq_of_mem hw).symm

/-- ★★★ **The linear jet functional** of the prior's produced kernel on the observables with a
holomorphic extension on the packet's neighbourhood. -/
noncomputable def jetFunctional (q : PowerLogIndex) : obsSpace A.Ω →ₗ[ℝ] ℝ where
  toFun ψ := (producedKernel A k hk δ hδ hd ha hδa hϕ0W hsmall).coefficient ψ.1 q
  map_add' ψ₁ ψ₂ := MomentKernelData.coefficient_add
    (certified_of_mem A k hk δ hδ hd ha hδa hϕ0W hsmall ψ₁.2)
    (certified_of_mem A k hk δ hδ hd ha hδa hϕ0W hsmall ψ₂.2) q
  map_smul' c ψ := MomentKernelData.coefficient_smul
    (certified_of_mem A k hk δ hδ hd ha hδa hϕ0W hsmall ψ.2).smooth c q

theorem jetFunctional_apply (q : PowerLogIndex) (ψ : obsSpace A.Ω) :
    jetFunctional A k hk δ hδ hd ha hδa hϕ0W hsmall q ψ =
      (normalData d k (zeroOrders d) hk).expansionCoefficient
        (producedKernel A k hk δ hδ hd ha hδa hϕ0W hsmall).stratumMeasure
        (producedKernel A k hk δ hδ hd ha hδa hϕ0W hsmall).field ψ.1 q := rfl

/-- ★★★ **The expansion with the functional's values as coefficients**: for every observable
with a holomorphic extension on the packet's neighbourhood,
`∫_{[0,a]^d} ψ ϕ e^{−nK} − ∑_{q} (L_q ψ) · q.scale n = o(n^{−A})` on the coordinate lattice with
log degree `d − 1`, with ONE kernel for all `ψ`. -/
theorem hasCoordFreeExpansion_obsSpace (ψ : obsSpace A.Ω) (Ac : ℝ) :
    (fun n : ℝ => globalLaplace (piBox d (Icc 0 a)) (CoordModel.phase d k)
      (fun w => ψ.1 w * ϕ w) n -
      ∑ q ∈ spectrumLe (coordQ k) (d - 1) Ac,
        jetFunctional A k hk δ hδ hd ha hδa hϕ0W hsmall q ψ * q.scale n) =o[atTop]
      fun n : ℝ => n ^ (-Ac) := by
  obtain ⟨H, hH, e⟩ := ψ.2
  exact hasCoordFreeExpansion_withObs A H hH e k hk δ hδ hd ha hδa hϕ0W hsmall Ac

end HolomorphicBoxExtension

end WaterFilling

end Grammar
