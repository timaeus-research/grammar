/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothTargetB
import Grammar.SmoothTargetAClean

/-!
# Target B, paper-facing (consult #121 §2)

The paper-facing form of Target B (`exists_smoothExpansionCertificate_domain_of_analyticOnNhd`):
no measurability of the phase, no distinguished origin, and the positive-phase case included.

* **Arbitrary anchor** (`exists_smoothExpansionCertificate_domain_of_analyticOnNhd_at`): the zero
  of the phase may sit anywhere in the ambient connected open `A`; it is translated to the origin
  (the domain integral is translation invariant), and the measurable representative of the phase
  is its indicator on `A`.
* **Pure tail on the domain** (`NormalisedDomainCoreTransport.ofEmptyCores`,
  `exists_smoothExpansionCertificate_domain_of_pos`, `coeff_eq_zero_of_pos_phase_domain`): with
  no zero of the phase on `tsupport prior ∩ D` the prior sees a phase gap on the domain, the whole
  prior-weighted volume of the domain is the tail, and every certificate has all coefficients
  zero.
* ★★★ **Target B, paper-facing** (`exists_smoothExpansionCertificate_domain`): an analytic
  nonnegative phase `K` and analytic boundary functions `π_ℓ` on a connected open `A`, the
  product `K · ∏ π_ℓ` not identically zero on `A`, the compact domain `D = A ∩ {∀ ℓ, 0 ≤ π_ℓ}`,
  a smooth nonnegative prior with `tsupport prior ⊆ A` and a smooth observable: the partition
  function with insertions `∫_D prior·obs·e^{−NK}` has a smooth expansion certificate of
  logarithmic degree `≤ d − 1`.
* **Local data** (`exists_smoothExpansionCertificate_domain_of_local`): the prior and the
  observable need only be smooth on an open `U` with `D ⊆ U ⊆ A`, the prior nonnegative on `U`
  (cutoff and extension).
* **Named domain**, the `∃ c Q D` form and the intrinsic coefficients of the domain integral.
* **Regression**: the interval `D = [0,1]` in the line, cut out of the ball of radius `2` by the
  walls `y ↦ y` and `y ↦ 1 − y`, with the phase `y²` and the box bump: the certificate has no
  logarithms.

Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology TopologicalSpace
open scoped ENNReal ContDiff
open Monomialize.VolumeScaling

namespace Grammar

namespace SmoothEngine

variable {d r : ℕ}

/-! ### Locality and translation invariance of the domain integral -/

/-- The partition function with insertions on a domain only sees the phase on the support of the
prior. -/
theorem laplace_domain_congr_of_support {S : Set (Fin d → ℝ)} {K₁ K₂ prior obs : (Fin d → ℝ) → ℝ}
    (h : ∀ y, prior y ≠ 0 → K₁ y = K₂ y) :
    (fun N : ℝ => ∫ y in S, prior y * obs y * Real.exp (-N * K₁ y)) =
      fun N => ∫ y in S, prior y * obs y * Real.exp (-N * K₂ y) := by
  funext N
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  by_cases hy : prior y = 0
  · simp [hy]
  · simp only [h y hy]

/-- The set integral is translation invariant: `∫_{S − p} f(y + p) = ∫_S f`. -/
theorem setIntegral_preimage_add_right {S : Set (Fin d → ℝ)} (hS : MeasurableSet S)
    (f : (Fin d → ℝ) → ℝ) (p : Fin d → ℝ) :
    ∫ y in (fun x => x + p) ⁻¹' S, f (y + p) = ∫ y in S, f y := by
  have hS' : MeasurableSet ((fun x => x + p) ⁻¹' S) := (measurable_id.add_const p) hS
  rw [← integral_indicator hS', ← integral_indicator hS,
    ← integral_add_right_eq_self (S.indicator f) p]
  exact integral_congr_ae (Eventually.of_forall fun y =>
    indicator_comp_right (fun x => x + p) (g := f) (x := y))

/-- The domain of the translated data is the translated domain. -/
theorem boundaryDomain_preimage_add_right (A : Set (Fin d → ℝ)) (π : Fin r → (Fin d → ℝ) → ℝ)
    (p : Fin d → ℝ) :
    boundaryDomain ((fun x => x + p) ⁻¹' A) (fun ℓ x => π ℓ (x + p)) =
      (fun x => x + p) ⁻¹' boundaryDomain A π := rfl

/-! ### Arbitrary anchor -/

/-- **Target B with an arbitrary anchor**: the zero `p` of the phase may sit anywhere in the
ambient connected open `A`; no measurability of the phase. -/
theorem exists_smoothExpansionCertificate_domain_of_analyticOnNhd_at {A : Set (Fin d → ℝ)}
    (hAo : IsOpen A) (hAc : IsConnected A) {K : (Fin d → ℝ) → ℝ} (hK : AnalyticOnNhd ℝ K A)
    {π : Fin r → (Fin d → ℝ) → ℝ} (hπ : ∀ ℓ, AnalyticOnNhd ℝ (π ℓ) A) (hK0 : ∀ x ∈ A, 0 ≤ K x)
    (hDc : IsCompact (boundaryDomain A π)) (hFnt : ∃ x ∈ A, K x * ∏ ℓ, π ℓ x ≠ 0)
    {p : Fin d → ℝ} (hpA : p ∈ A) (hKp : K p = 0) {prior obs : (Fin d → ℝ) → ℝ}
    (hprior : ContDiff ℝ ∞ prior) (hp0 : ∀ y, 0 ≤ prior y) (hpW : tsupport prior ⊆ A)
    (hobs : ContDiff ℝ ∞ obs) :
    ∃ C : SmoothExpansionCertificate
      (fun N => ∫ y in boundaryDomain A π, prior y * obs y * Real.exp (-N * K y)),
      C.D ≤ d - 1 := by
  -- the measurable representative of the phase
  set Kₘ : (Fin d → ℝ) → ℝ := A.indicator K with hKₘ
  have hKₘm : Measurable Kₘ := measurable_indicator_of_continuousOn hAo hK.continuousOn
  have hKₘa : AnalyticOnNhd ℝ Kₘ A := analyticOnNhd_indicator hAo hK
  have hKₘeq : ∀ x ∈ A, Kₘ x = K x := fun x hx => indicator_of_mem hx K
  -- translate the zero to the origin
  set φ : (Fin d → ℝ) ≃ₜ (Fin d → ℝ) := Homeomorph.addRight p with hφ
  have hφc : (⇑φ : (Fin d → ℝ) → Fin d → ℝ) = fun x => x + p := Homeomorph.coe_addRight p
  set A' : Set (Fin d → ℝ) := (fun x => x + p) ⁻¹' A with hA'
  have hA'o : IsOpen A' := hAo.preimage (continuous_id.add continuous_const)
  have hA'c : IsConnected A' := by
    have := φ.isConnected_preimage.2 hAc
    rwa [hφc] at this
  have h0A : (0 : Fin d → ℝ) ∈ A' := by
    change (0 : Fin d → ℝ) + p ∈ A
    rwa [zero_add]
  have hK' : AnalyticOnNhd ℝ (fun x => Kₘ (x + p)) A' := fun x hx =>
    (hKₘa (x + p) hx).comp (f := fun x : Fin d → ℝ => x + p) (analyticAt_id.add analyticAt_const)
  have hKm' : Measurable fun x => Kₘ (x + p) := hKₘm.comp (measurable_id.add_const p)
  have hπ' : ∀ ℓ, AnalyticOnNhd ℝ (fun x => π ℓ (x + p)) A' := fun ℓ x hx =>
    (hπ ℓ (x + p) hx).comp (f := fun x : Fin d → ℝ => x + p) (analyticAt_id.add analyticAt_const)
  have h0 : Kₘ (0 + p) * ∏ ℓ, π ℓ (0 + p) = 0 := by
    rw [zero_add, hKₘeq p hpA, hKp, zero_mul]
  have hne : ¬ ∀ᶠ x in 𝓝 (0 : Fin d → ℝ), Kₘ (x + p) * ∏ ℓ, π ℓ (x + p) = 0 := by
    intro hev
    obtain ⟨x, hxA, hFx⟩ := hFnt
    have hFa : AnalyticOnNhd ℝ (fun x => Kₘ (x + p) * ∏ ℓ, π ℓ (x + p)) A' := fun y hy =>
      ((hK' y hy).mul (Finset.analyticAt_prod Finset.univ fun ℓ _ => hπ' ℓ y hy)).congr
        (Eventually.of_forall fun z => by simp [Finset.prod_apply])
    have hEq : EqOn (fun x => Kₘ (x + p) * ∏ ℓ, π ℓ (x + p)) 0 A' :=
      hFa.eqOn_zero_of_preconnected_of_eventuallyEq_zero hA'c.isPreconnected h0A hev
    have hx' : x - p ∈ A' := by
      change x - p + p ∈ A
      rwa [sub_add_cancel]
    have := hEq hx'
    simp only [sub_add_cancel, Pi.zero_apply, hKₘeq x hxA] at this
    exact hFx this
  have hK0' : ∀ x ∈ A', 0 ≤ Kₘ (x + p) := fun x hx => by
    rw [hKₘeq _ hx]
    exact hK0 _ hx
  have hDc' : IsCompact (boundaryDomain A' fun ℓ x => π ℓ (x + p)) := by
    rw [hA', boundaryDomain_preimage_add_right, ← hφc]
    exact φ.isCompact_preimage.2 hDc
  have hprior' : ContDiff ℝ ∞ fun x => prior (x + p) :=
    hprior.comp (contDiff_id.add contDiff_const)
  have hp0' : ∀ y, 0 ≤ prior (y + p) := fun y => hp0 _
  have hpW' : tsupport (fun x => prior (x + p)) ⊆ A' := by
    have := tsupport_comp_eq_preimage prior φ
    rw [hφc] at this
    exact this.le.trans (preimage_mono hpW)
  have hobs' : ContDiff ℝ ∞ fun x => obs (x + p) := hobs.comp (contDiff_id.add contDiff_const)
  obtain ⟨C, hC⟩ := exists_smoothExpansionCertificate_domain_of_analyticOnNhd hA'o hK' hKm' hπ'
    h0 hne ⟨A', hA'o⟩ hA'c h0A subset_rfl hK0' hDc' hprior' hp0' hpW' hobs'
  -- transport the certificate back
  have hZ : globalLaplace (boundaryDomain A' fun ℓ x => π ℓ (x + p)) (fun x => Kₘ (x + p))
      (fun y => prior (y + p) * obs (y + p)) =
      fun N => ∫ y in boundaryDomain A π, prior y * obs y * Real.exp (-N * K y) := by
    funext N
    unfold globalLaplace
    rw [hA', boundaryDomain_preimage_add_right]
    exact (setIntegral_preimage_add_right hDc.isClosed.measurableSet
      (fun y => prior y * obs y * Real.exp (-N * Kₘ y)) p).trans
      (congrFun (laplace_domain_congr_of_support (S := boundaryDomain A π) (obs := obs)
        fun y hy => hKₘeq y (hpW (subset_tsupport prior hy))) N)
  rw [← hZ]
  exact ⟨C, hC⟩

/-! ### The pure tail on the domain -/

/-- The empty-core normalised domain core transport of a prior seeing a phase gap on the domain:
the whole prior-weighted volume of the domain is the tail. -/
noncomputable def _root_.Monomialize.VolumeScaling.NormalisedDomainCoreTransport.ofEmptyCores
    (K prior : (Fin d → ℝ) → ℝ) (D : Set (Fin d → ℝ)) (hDm : MeasurableSet D)
    (hpm : Measurable prior) {δ : ℝ} (hδ : 0 < δ) (hgap : ∀ y ∈ D, prior y ≠ 0 → δ ≤ K y) :
    NormalisedDomainCoreTransport d K prior D where
  ι := Empty
  a := Empty.elim
  a_pos i := i.elim
  ψ := Empty.elim
  V := Empty.elim
  V_open i := i.elim
  box_subset_V i := i.elim
  ψ_measurable i := i.elim
  ψ_analytic i := i.elim
  k := Empty.elim
  k_active i := i.elim
  phaseConst := Empty.elim
  phaseConst_pos i := i.elim
  phase_eq i := i.elim
  h := Empty.elim
  jacUnit := Empty.elim
  jacUnit_analytic i := i.elim
  jacUnit_ne_zero i := i.elim
  jac_eq i := i.elim
  «ω» := Empty.elim
  «ω_measurable» i := i.elim
  «ω_smoothOn» i := i.elim
  «ω_nonneg» i := i.elim
  «ω_le_one» i := i.elim
  sectors := Empty.elim
  tail := (volume.restrict D).withDensity fun y => ENNReal.ofReal (prior y)
  δ := δ
  δ_pos := hδ
  tail_gap := by
    rw [ae_withDensity_iff hpm.ennreal_ofReal, ae_restrict_iff' hDm]
    exact Eventually.of_forall fun y hyD hy => hgap y hyD fun h0 => hy (by simp [h0])
  transport := by simp

/-- The domain bridge inputs of the empty-core transport. -/
noncomputable def DomainBridgeInputs.ofEmptyCores {K prior obs : (Fin d → ℝ) → ℝ}
    {D : Set (Fin d → ℝ)} (hDc : IsCompact D) (hKm : Measurable K) (hprior : ContDiff ℝ ∞ prior)
    (hp0 : ∀ y, 0 ≤ prior y) {δ : ℝ} (hδ : 0 < δ) (hgap : ∀ y ∈ D, prior y ≠ 0 → δ ≤ K y)
    (hobs : ContDiff ℝ ∞ obs) : DomainBridgeInputs d :=
  DomainBridgeInputs.ofTransport
    (NormalisedDomainCoreTransport.ofEmptyCores K prior D hDc.isClosed.measurableSet
      hprior.continuous.measurable hδ hgap) hDc hKm hprior hp0 hobs

/-- With no charts the coefficient array of the domain bridge decomposition vanishes. -/
theorem DomainBridgeInputs.coeff_eq_zero_of_isEmpty (X : DomainBridgeInputs d)
    (h : IsEmpty X.T.ι) (μ : ℝ) (q : ℕ) : X.decomp.coeff μ q = 0 := by
  have hcard : Fintype.card X.PIdx = 0 := Fintype.card_eq_zero_iff.2 ⟨fun p => h.elim p.1⟩
  unfold SmoothCoreDecomposition.coeff
  exact Finset.sum_eq_zero fun I _ => (Fin.cast hcard I).elim0

/-- The empty-core domain bridge inputs have vanishing coefficients. -/
theorem DomainBridgeInputs.coeff_ofEmptyCores {K prior obs : (Fin d → ℝ) → ℝ}
    {D : Set (Fin d → ℝ)} (hDc : IsCompact D) (hKm : Measurable K) (hprior : ContDiff ℝ ∞ prior)
    (hp0 : ∀ y, 0 ≤ prior y) {δ : ℝ} (hδ : 0 < δ) (hgap : ∀ y ∈ D, prior y ≠ 0 → δ ≤ K y)
    (hobs : ContDiff ℝ ∞ obs) (μ : ℝ) (q : ℕ) :
    (DomainBridgeInputs.ofEmptyCores hDc hKm hprior hp0 hδ hgap hobs).decomp.coeff μ q = 0 :=
  (DomainBridgeInputs.ofEmptyCores hDc hKm hprior hp0 hδ hgap hobs).coeff_eq_zero_of_isEmpty
    (inferInstanceAs (IsEmpty Empty)) μ q

/-- A phase continuous on `A` and positive on the compact `tsupport prior ∩ D ⊆ A` is bounded
below by a positive constant on the domain where the prior is nonzero. -/
theorem exists_gap_of_pos_domain {A D : Set (Fin d → ℝ)} {K : (Fin d → ℝ) → ℝ}
    (hKc : ContinuousOn K A) (hDc : IsCompact D) {prior : (Fin d → ℝ) → ℝ}
    (hpW : tsupport prior ⊆ A) (hKpos : ∀ x ∈ tsupport prior ∩ D, 0 < K x) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y ∈ D, prior y ≠ 0 → δ ≤ K y := by
  have hSc : IsCompact (tsupport prior ∩ D) := hDc.inter_left (isClosed_tsupport prior)
  rcases (tsupport prior ∩ D).eq_empty_or_nonempty with hemp | hne
  · refine ⟨1, one_pos, fun y hyD hy => ?_⟩
    have hmem : y ∈ tsupport prior ∩ D := ⟨subset_tsupport prior hy, hyD⟩
    rw [hemp] at hmem
    exact hmem.elim
  · obtain ⟨x₀, hx₀, hmin⟩ := hSc.exists_isMinOn hne (hKc.mono (inter_subset_left.trans hpW))
    exact ⟨K x₀, hKpos x₀ hx₀, fun y hyD hy =>
      isMinOn_iff.1 hmin y ⟨subset_tsupport prior hy, hyD⟩⟩

/-- **Pure tail on the domain**: a phase continuous on an open `A ⊇ tsupport prior` and positive
on `tsupport prior ∩ D`, `D` compact: the partition function with insertions on `D` has a
certificate of logarithmic degree `≤ d − 1` with all coefficients zero. -/
theorem exists_smoothExpansionCertificate_domain_of_pos {A : Set (Fin d → ℝ)} (hAo : IsOpen A)
    {K : (Fin d → ℝ) → ℝ} (hKc : ContinuousOn K A) {D : Set (Fin d → ℝ)} (hDc : IsCompact D)
    {prior obs : (Fin d → ℝ) → ℝ} (hprior : ContDiff ℝ ∞ prior) (hp0 : ∀ y, 0 ≤ prior y)
    (hpW : tsupport prior ⊆ A) (hKpos : ∀ x ∈ tsupport prior ∩ D, 0 < K x)
    (hobs : ContDiff ℝ ∞ obs) :
    ∃ C : SmoothExpansionCertificate (fun N => ∫ y in D, prior y * obs y * Real.exp (-N * K y)),
      C.D ≤ d - 1 ∧ ∀ μ q, C.coeff μ q = 0 := by
  have hZ := laplace_domain_congr_of_support (S := D) (K₂ := A.indicator K) (prior := prior)
    (obs := obs) fun y hy => (indicator_of_mem (hpW (subset_tsupport prior hy)) K).symm
  have hKpos' : ∀ x ∈ tsupport prior ∩ D, 0 < A.indicator K x := fun x hx => by
    rw [indicator_of_mem (hpW hx.1)]
    exact hKpos x hx
  obtain ⟨δ, hδ, hgap⟩ := exists_gap_of_pos_domain (hKc.congr eqOn_indicator) hDc hpW hKpos'
  rw [hZ]
  exact ⟨(DomainBridgeInputs.ofEmptyCores hDc (measurable_indicator_of_continuousOn hAo hKc)
      hprior hp0 hδ hgap hobs).certificate,
    (DomainBridgeInputs.ofEmptyCores hDc (measurable_indicator_of_continuousOn hAo hKc) hprior
      hp0 hδ hgap hobs).commonD_le,
    DomainBridgeInputs.coeff_ofEmptyCores hDc (measurable_indicator_of_continuousOn hAo hKc)
      hprior hp0 hδ hgap hobs⟩

/-- ★★ **Pure-tail vanishing on the domain**: with no zero of the phase on `tsupport prior ∩ D`,
every certificate of the partition function with insertions on `D` has all coefficients zero. -/
theorem coeff_eq_zero_of_pos_phase_domain {A : Set (Fin d → ℝ)} (hAo : IsOpen A)
    {K : (Fin d → ℝ) → ℝ} (hKc : ContinuousOn K A) {D : Set (Fin d → ℝ)} (hDc : IsCompact D)
    {prior obs : (Fin d → ℝ) → ℝ} (hprior : ContDiff ℝ ∞ prior) (hp0 : ∀ y, 0 ≤ prior y)
    (hpW : tsupport prior ⊆ A) (hKpos : ∀ x ∈ tsupport prior ∩ D, 0 < K x)
    (hobs : ContDiff ℝ ∞ obs)
    (C : SmoothExpansionCertificate (fun N => ∫ y in D, prior y * obs y * Real.exp (-N * K y)))
    (μ : ℝ) (q : ℕ) : C.coeff μ q = 0 := by
  obtain ⟨C', -, hC'⟩ := exists_smoothExpansionCertificate_domain_of_pos hAo hKc hDc hprior hp0
    hpW hKpos hobs
  rw [C.coeff_eq C' μ q]
  exact hC' μ q

/-! ### Target B, paper-facing -/

/-- ★★★ **Target B, paper-facing.** An analytic nonnegative phase `K` and analytic boundary
functions `π_ℓ` on a connected open `A`, the product `K · ∏ π_ℓ` not identically zero on `A`, the
compact domain `D = A ∩ {∀ ℓ, 0 ≤ π_ℓ}`, a smooth nonnegative prior with `tsupport prior ⊆ A`
and a smooth observable: the partition function with insertions `∫_D prior·obs·e^{−NK}` has a
smooth expansion certificate of logarithmic degree `≤ d − 1`. No measurability of `K`, no
distinguished origin, and `K` may have no zero on `D`. -/
theorem exists_smoothExpansionCertificate_domain {A : Set (Fin d → ℝ)} (hAo : IsOpen A)
    (hAc : IsConnected A) {K : (Fin d → ℝ) → ℝ} (hK : AnalyticOnNhd ℝ K A)
    {π : Fin r → (Fin d → ℝ) → ℝ} (hπ : ∀ ℓ, AnalyticOnNhd ℝ (π ℓ) A) (hK0 : ∀ x ∈ A, 0 ≤ K x)
    (hDc : IsCompact (boundaryDomain A π)) (hFnt : ∃ x ∈ A, K x * ∏ ℓ, π ℓ x ≠ 0)
    {prior obs : (Fin d → ℝ) → ℝ} (hprior : ContDiff ℝ ∞ prior) (hp0 : ∀ y, 0 ≤ prior y)
    (hpW : tsupport prior ⊆ A) (hobs : ContDiff ℝ ∞ obs) :
    ∃ C : SmoothExpansionCertificate
      (fun N => ∫ y in boundaryDomain A π, prior y * obs y * Real.exp (-N * K y)),
      C.D ≤ d - 1 := by
  by_cases hzero : ∃ p ∈ boundaryDomain A π, K p = 0
  · obtain ⟨p, hpD, hKp⟩ := hzero
    exact exists_smoothExpansionCertificate_domain_of_analyticOnNhd_at hAo hAc hK hπ hK0 hDc
      hFnt hpD.1 hKp hprior hp0 hpW hobs
  · push Not at hzero
    have hKpos : ∀ x ∈ tsupport prior ∩ boundaryDomain A π, 0 < K x := fun x hx =>
      lt_of_le_of_ne (hK0 x hx.2.1) (hzero x hx.2).symm
    obtain ⟨C, hC, -⟩ := exists_smoothExpansionCertificate_domain_of_pos hAo hK.continuousOn hDc
      hprior hp0 hpW hKpos hobs
    exact ⟨C, hC⟩

/-- **Target B with local data**: the prior and the observable need only be smooth on an open `U`
with `D ⊆ U ⊆ A`, the prior nonnegative on `U`. -/
theorem exists_smoothExpansionCertificate_domain_of_local {A : Set (Fin d → ℝ)} (hAo : IsOpen A)
    (hAc : IsConnected A) {K : (Fin d → ℝ) → ℝ} (hK : AnalyticOnNhd ℝ K A)
    {π : Fin r → (Fin d → ℝ) → ℝ} (hπ : ∀ ℓ, AnalyticOnNhd ℝ (π ℓ) A) (hK0 : ∀ x ∈ A, 0 ≤ K x)
    (hDc : IsCompact (boundaryDomain A π)) (hFnt : ∃ x ∈ A, K x * ∏ ℓ, π ℓ x ≠ 0)
    {U : Set (Fin d → ℝ)} (hUo : IsOpen U) (hDU : boundaryDomain A π ⊆ U) (hUA : U ⊆ A)
    {prior obs : (Fin d → ℝ) → ℝ} (hprior : ContDiffOn ℝ ∞ prior U) (hp0 : ∀ y ∈ U, 0 ≤ prior y)
    (hobs : ContDiffOn ℝ ∞ obs U) :
    ∃ C : SmoothExpansionCertificate
      (fun N => ∫ y in boundaryDomain A π, prior y * obs y * Real.exp (-N * K y)),
      C.D ≤ d - 1 := by
  obtain ⟨χ, hχ, hχ0, hχ1, hχ01⟩ := exists_contDiff_zero_one_nhds hUo.isClosed_compl
    hDc.isClosed (disjoint_compl_left_iff_subset.mpr hDU)
  obtain ⟨V, hVo, hVU, hV0⟩ := eventually_nhdsSet_iff_exists.mp hχ0
  obtain ⟨prior₁, hprior₁, hprior₁eq, hprior₁nn⟩ :=
    exists_contDiff_eqOn_of_contDiffOn hUo hDc.isClosed hDU hprior
  obtain ⟨obs₁, hobs₁, hobs₁eq, -⟩ := exists_contDiff_eqOn_of_contDiffOn hUo hDc.isClosed hDU hobs
  have hsupp : tsupport (fun y => χ y * prior₁ y) ⊆ A := by
    refine tsupport_mul_subset_left.trans ((closure_minimal (fun y hy hyV => ?_)
      hVo.isClosed_compl).trans ((compl_subset_comm.1 hVU).trans hUA))
    exact Function.mem_support.1 hy (by simp [hV0 y hyV])
  have hint : (fun N : ℝ => ∫ y in boundaryDomain A π, prior y * obs y * Real.exp (-N * K y)) =
      fun N => ∫ y in boundaryDomain A π, χ y * prior₁ y * obs₁ y * Real.exp (-N * K y) := by
    funext N
    refine setIntegral_congr_fun hDc.isClosed.measurableSet fun y hy => ?_
    rw [hχ1.self_of_nhdsSet y hy, hprior₁eq hy, hobs₁eq hy, one_mul]
  rw [hint]
  exact exists_smoothExpansionCertificate_domain hAo hAc hK hπ hK0 hDc hFnt (hχ.mul hprior₁)
    (fun y => mul_nonneg (hχ01 y).1 (hprior₁nn hp0 y)) hsupp hobs₁

/-- **Target B for a named domain** `D = A ∩ {∀ ℓ, 0 ≤ π_ℓ}`. -/
theorem exists_smoothExpansionCertificate_of_domain_eq {A : Set (Fin d → ℝ)} (hAo : IsOpen A)
    (hAc : IsConnected A) {K : (Fin d → ℝ) → ℝ} (hK : AnalyticOnNhd ℝ K A)
    {π : Fin r → (Fin d → ℝ) → ℝ} (hπ : ∀ ℓ, AnalyticOnNhd ℝ (π ℓ) A) (hK0 : ∀ x ∈ A, 0 ≤ K x)
    {D : Set (Fin d → ℝ)} (hD : D = boundaryDomain A π) (hDc : IsCompact D)
    (hFnt : ∃ x ∈ A, K x * ∏ ℓ, π ℓ x ≠ 0) {prior obs : (Fin d → ℝ) → ℝ}
    (hprior : ContDiff ℝ ∞ prior) (hp0 : ∀ y, 0 ≤ prior y) (hpW : tsupport prior ⊆ A)
    (hobs : ContDiff ℝ ∞ obs) :
    ∃ C : SmoothExpansionCertificate (fun N => ∫ y in D, prior y * obs y * Real.exp (-N * K y)),
      C.D ≤ d - 1 := by
  subst hD
  exact exists_smoothExpansionCertificate_domain hAo hAc hK hπ hK0 hDc hFnt hprior hp0 hpW hobs

/-- Target B in the `∃ c Q D` form, with the logarithmic degree bound. -/
theorem exists_hasSmoothCoordFreeExpansion_domain {A : Set (Fin d → ℝ)} (hAo : IsOpen A)
    (hAc : IsConnected A) {K : (Fin d → ℝ) → ℝ} (hK : AnalyticOnNhd ℝ K A)
    {π : Fin r → (Fin d → ℝ) → ℝ} (hπ : ∀ ℓ, AnalyticOnNhd ℝ (π ℓ) A) (hK0 : ∀ x ∈ A, 0 ≤ K x)
    (hDc : IsCompact (boundaryDomain A π)) (hFnt : ∃ x ∈ A, K x * ∏ ℓ, π ℓ x ≠ 0)
    {prior obs : (Fin d → ℝ) → ℝ} (hprior : ContDiff ℝ ∞ prior) (hp0 : ∀ y, 0 ≤ prior y)
    (hpW : tsupport prior ⊆ A) (hobs : ContDiff ℝ ∞ obs) :
    ∃ (c : ℝ → ℕ → ℝ) (Q D : ℕ), D ≤ d - 1 ∧
      HasSmoothCoordFreeExpansion
        (fun N => ∫ y in boundaryDomain A π, prior y * obs y * Real.exp (-N * K y)) c Q D := by
  obtain ⟨C, hC⟩ := exists_smoothExpansionCertificate_domain hAo hAc hK hπ hK0 hDc hFnt hprior
    hp0 hpW hobs
  exact ⟨C.coeff, C.Q, C.D, hC, C.hasSmoothCoordFreeExpansion⟩

/-- **Intrinsic coefficients of the domain integral**: any two certificates of the partition
function with insertions on the domain have the same coefficient array. -/
theorem coeff_unique_domain {D : Set (Fin d → ℝ)} {K prior obs : (Fin d → ℝ) → ℝ}
    (C C' : SmoothExpansionCertificate
      (fun N => ∫ y in D, prior y * obs y * Real.exp (-N * K y))) :
    C.coeff = C'.coeff :=
  C.coeff_unique C'

/-! ### Regression: the interval `[0,1]` in the line -/

/-- The walls of the regression: `y ↦ y` and `y ↦ 1 − y`, cutting `[0,1]` out of the line. -/
def intervalWalls : Fin 2 → (Fin 1 → ℝ) → ℝ := ![fun y => y 0, fun y => 1 - y 0]

theorem analyticOnNhd_coord (A : Set (Fin 1 → ℝ)) :
    AnalyticOnNhd ℝ (fun y : Fin 1 → ℝ => y 0) A :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).analyticOnNhd A

theorem analyticOnNhd_intervalWalls (A : Set (Fin 1 → ℝ)) (ℓ : Fin 2) :
    AnalyticOnNhd ℝ (intervalWalls ℓ) A := by
  fin_cases ℓ
  · exact analyticOnNhd_coord A
  · exact analyticOnNhd_const.sub (analyticOnNhd_coord A)

/-- The domain cut by the walls out of the ball of radius `2` is the interval `[0,1]`. -/
theorem boundaryDomain_intervalWalls :
    boundaryDomain (Metric.ball (0 : Fin 1 → ℝ) 2) intervalWalls =
      Icc (fun _ => 0) (fun _ => 1) := by
  ext y
  simp only [boundaryDomain, intervalWalls, mem_inter_iff, mem_ofPred_eq, Fin.forall_fin_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, mem_Icc, Pi.le_def, Fin.forall_fin_one,
    mem_ball_zero_iff, pi_norm_lt_iff two_pos, Real.norm_eq_abs, abs_lt]
  constructor
  · rintro ⟨-, h0, h1⟩
    exact ⟨h0, by linarith⟩
  · rintro ⟨h0, h1⟩
    exact ⟨by constructor <;> linarith, h0, by linarith⟩

theorem tsupport_boxBump_subset_ball :
    tsupport (boxBump (1 / 2) 1 : (Fin 1 → ℝ) → ℝ) ⊆ Metric.ball (0 : Fin 1 → ℝ) 2 := by
  refine (closure_minimal (fun y hy => ?_) (isCompact_centeredBox 1 1).isClosed).trans
    fun y hy => ?_
  · by_contra hn
    exact Function.mem_support.1 hy (boxBump_eq_zero_of_notMem_centeredBox one_pos hn)
  · rw [mem_ball_zero_iff, pi_norm_lt_iff two_pos]
    intro i
    rw [Real.norm_eq_abs]
    linarith [hy i]

/-- ★ **Regression**: `∫_0^1 boxBump·obs·e^{−N y²}` has a smooth expansion certificate, with no
logarithms. -/
theorem interval_regression {obs : (Fin 1 → ℝ) → ℝ} (hobs : ContDiff ℝ ∞ obs) :
    ∃ C : SmoothExpansionCertificate
      (fun N => ∫ y in boundaryDomain (Metric.ball (0 : Fin 1 → ℝ) 2) intervalWalls,
        boxBump (1 / 2) 1 y * obs y * Real.exp (-N * y 0 ^ 2)),
      C.D = 0 := by
  have hK : AnalyticOnNhd ℝ (fun y : Fin 1 → ℝ => y 0 ^ 2) (Metric.ball 0 2) := fun x hx =>
    (analyticOnNhd_coord (Metric.ball 0 2) x hx).pow 2
  have hFnt : ∃ x ∈ Metric.ball (0 : Fin 1 → ℝ) 2, x 0 ^ 2 * ∏ ℓ, intervalWalls ℓ x ≠ 0 := by
    refine ⟨fun _ => 1 / 2, ?_, ?_⟩
    · rw [mem_ball_zero_iff, pi_norm_lt_iff two_pos]
      intro i
      rw [Real.norm_eq_abs]
      norm_num
    · simp [intervalWalls, Fin.prod_univ_two]
      norm_num
  obtain ⟨C, hC⟩ := exists_smoothExpansionCertificate_domain Metric.isOpen_ball
    (Metric.isConnected_ball two_pos) hK (analyticOnNhd_intervalWalls _) (fun x _ => sq_nonneg _)
    (boundaryDomain_intervalWalls ▸ isCompact_Icc) hFnt (contDiff_boxBump _ _) (boxBump_nonneg _ _)
    tsupport_boxBump_subset_ball hobs
  exact ⟨C, Nat.le_zero.1 hC⟩

end SmoothEngine

end Grammar
