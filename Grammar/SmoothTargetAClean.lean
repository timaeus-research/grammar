/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothTargetA
import Grammar.SmoothCoefficientLinearity
import Monomialize.Transport.NormalisedCoreTransportRegression

/-!
# Target A, cleaned up (consult #120, §2, §3, §8)

Consequences and tidy-ups of Target A (`exists_hasSmoothCoordFreeExpansion_of_analyticOnNhd`).

* **Locality in the phase** (`laplace_congr_of_support`): `∫ prior·obs·e^{−NK}` only sees `K` on
  the support of the prior.
* **The measurable representative** (`measurable_indicator_of_continuousOn`): a phase continuous
  on an open `W` has the measurable representative `W.indicator K`, agreeing with `K` on `W`; so the
  `Measurable K` hypothesis of Target A is redundant.
* ★★★ **Target A in certificate form** (`exists_smoothExpansionCertificate_of_analyticOnNhd`):
  no measurability, no distinguished origin, and the positive-phase case included. An analytic
  nonnegative phase on a connected open `W`, not identically zero, and a smooth nonnegative prior
  with compact support in `W`: the partition function with insertions has a smooth expansion
  certificate of logarithmic degree `≤ d − 1`. The zero at a general point `p ∈ W` is translated to
  the origin (the integral is translation invariant); with no zero the prior sees a phase gap and
  the whole prior-weighted volume is the tail (`ofEmptyCores`).
* **Pure-tail vanishing** (`coeff_eq_zero_of_pos_phase`): with a positive phase on the support all
  the expansion coefficients vanish (the integral is `O(N^{−∞})`), by coefficient uniqueness.
* **Consumer regressions**: the genuine-tail monomial transport `ofMonomialWithTail` and the
  empty-core transport feed the consumer.

Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology TopologicalSpace
open scoped ENNReal ContDiff
open Monomialize.VolumeScaling

namespace Grammar

namespace SmoothEngine

variable {d : ℕ}

/-! ### Locality of the integral in the phase -/

/-- The partition function with insertions only sees the phase on the support of the prior. -/
theorem laplace_congr_of_support {K₁ K₂ prior obs : (Fin d → ℝ) → ℝ}
    (h : ∀ y, prior y ≠ 0 → K₁ y = K₂ y) :
    (fun N : ℝ => ∫ y, prior y * obs y * Real.exp (-N * K₁ y)) =
      fun N => ∫ y, prior y * obs y * Real.exp (-N * K₂ y) := by
  funext N
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  by_cases hy : prior y = 0
  · simp [hy]
  · simp only [h y hy]

/-! ### The measurable representative -/

/-- A function continuous on an open set has a measurable representative: its indicator. -/
theorem measurable_indicator_of_continuousOn {U : Set (Fin d → ℝ)} (hU : IsOpen U)
    {K : (Fin d → ℝ) → ℝ} (hK : ContinuousOn K U) : Measurable (U.indicator K) := by
  classical
  rw [← piecewise_eq_indicator]
  exact hK.measurable_piecewise continuousOn_const hU.measurableSet

/-- The indicator of an analytic function on an open set is analytic there. -/
theorem analyticOnNhd_indicator {U : Set (Fin d → ℝ)} (hU : IsOpen U) {K : (Fin d → ℝ) → ℝ}
    (hK : AnalyticOnNhd ℝ K U) : AnalyticOnNhd ℝ (U.indicator K) U :=
  hK.congr hU eqOn_indicator.symm

/-! ### The phase gap of a positive phase -/

/-- A phase continuous and positive on a set containing the (compact) support of the prior is
bounded below by a positive constant where the prior is nonzero. -/
theorem exists_gap_of_pos {W : Set (Fin d → ℝ)} {K : (Fin d → ℝ) → ℝ} (hKc : ContinuousOn K W)
    (hKpos : ∀ x ∈ W, 0 < K x) {prior : (Fin d → ℝ) → ℝ} (hpc : HasCompactSupport prior)
    (hpW : tsupport prior ⊆ W) : ∃ δ : ℝ, 0 < δ ∧ ∀ y, prior y ≠ 0 → δ ≤ K y := by
  rcases (tsupport prior).eq_empty_or_nonempty with hemp | hne
  · refine ⟨1, one_pos, fun y hy => ?_⟩
    exact absurd (tsupport_eq_empty_iff.1 hemp ▸ rfl : prior y = 0) hy
  · obtain ⟨x₀, hx₀, hmin⟩ := hpc.exists_isMinOn hne (hKc.mono hpW)
    refine ⟨K x₀, hKpos x₀ (hpW hx₀), fun y hy => ?_⟩
    exact isMinOn_iff.1 hmin y (subset_tsupport prior hy)

/-! ### Certificate-facing Target A -/

/-- **Target A, measurable phase**: the certificate for an analytic nonnegative phase on a
connected open `W`, not identically zero there; the zero (if any) may sit anywhere in `W`. -/
theorem exists_smoothExpansionCertificate_of_analyticOnNhd_of_measurable {W : Set (Fin d → ℝ)}
    (hWo : IsOpen W) (hWc : IsConnected W) {K : (Fin d → ℝ) → ℝ} (hK : AnalyticOnNhd ℝ K W)
    (hKm : Measurable K) (hK0 : ∀ x ∈ W, 0 ≤ K x) (hKnt : ∃ x ∈ W, K x ≠ 0)
    {prior obs : (Fin d → ℝ) → ℝ} (hprior : ContDiff ℝ ∞ prior) (hp0 : ∀ y, 0 ≤ prior y)
    (hpc : HasCompactSupport prior) (hpW : tsupport prior ⊆ W) (hobs : ContDiff ℝ ∞ obs) :
    ∃ C : SmoothExpansionCertificate (fun N => ∫ y, prior y * obs y * Real.exp (-N * K y)),
      C.D ≤ d - 1 := by
  by_cases hzero : ∃ p ∈ W, K p = 0
  · -- translate the zero to the origin
    obtain ⟨p, hpW', hKp⟩ := hzero
    set φ : (Fin d → ℝ) ≃ₜ (Fin d → ℝ) := Homeomorph.addRight p with hφ
    have hφc : (⇑φ : (Fin d → ℝ) → Fin d → ℝ) = fun x => x + p := Homeomorph.coe_addRight p
    set W' : Set (Fin d → ℝ) := (fun x => x + p) ⁻¹' W with hW'
    have hW'o : IsOpen W' := hWo.preimage (continuous_id.add continuous_const)
    have hW'c : IsConnected W' := by
      have := φ.isConnected_preimage.2 hWc
      rwa [hφc] at this
    have h0W : (0 : Fin d → ℝ) ∈ W' := by
      change (0 : Fin d → ℝ) + p ∈ W
      rwa [zero_add]
    have hK' : AnalyticOnNhd ℝ (fun x => K (x + p)) W' := fun x hx =>
      (hK (x + p) hx).comp (f := fun x : Fin d → ℝ => x + p) (analyticAt_id.add analyticAt_const)
    have hKm' : Measurable fun x => K (x + p) := hKm.comp (measurable_id.add_const p)
    have h0 : K (0 + p) = 0 := by rwa [zero_add]
    have hne : ¬ ∀ᶠ x in 𝓝 (0 : Fin d → ℝ), K (x + p) = 0 := by
      intro hev
      obtain ⟨x, hxW, hKx⟩ := hKnt
      have hEq : EqOn (fun x => K (x + p)) 0 W' :=
        hK'.eqOn_zero_of_preconnected_of_eventuallyEq_zero hW'c.isPreconnected h0W hev
      have hx' : x - p ∈ W' := by
        change x - p + p ∈ W
        rwa [sub_add_cancel]
      have := hEq hx'
      simp only [sub_add_cancel, Pi.zero_apply] at this
      exact hKx this
    have hprior' : ContDiff ℝ ∞ fun x => prior (x + p) :=
      hprior.comp (contDiff_id.add contDiff_const)
    have hp0' : ∀ y, 0 ≤ prior (y + p) := fun y => hp0 _
    have hpc' : HasCompactSupport fun x => prior (x + p) := by
      have := hpc.comp_homeomorph φ
      rwa [hφc] at this
    have hpW' : tsupport (fun x => prior (x + p)) ⊆ W' := by
      have := tsupport_comp_eq_preimage prior φ
      rw [hφc] at this
      exact this.le.trans (preimage_mono hpW)
    have hobs' : ContDiff ℝ ∞ fun x => obs (x + p) := hobs.comp (contDiff_id.add contDiff_const)
    obtain ⟨T⟩ := exists_normalisedCoreTransport_of_analyticOnNhd hW'o hK' h0 hne ⟨W', hW'o⟩ hW'c
      h0W subset_rfl (fun x hx => hK0 _ hx) hprior'.continuous.measurable hp0' hpc' hpW'
    have hZ : (fun N : ℝ => ∫ y, prior (y + p) * obs (y + p) * Real.exp (-N * K (y + p))) =
        fun N => ∫ y, prior y * obs y * Real.exp (-N * K y) :=
      funext fun N => integral_add_right_eq_self (fun y => prior y * obs y * Real.exp (-N * K y)) p
    rw [← hZ]
    exact ⟨(BridgeInputs.ofTransport T hKm' hprior' hp0' hpc' hobs').certificate,
      (BridgeInputs.ofTransport T hKm' hprior' hp0' hpc' hobs').commonD_le⟩
  · -- positive phase: the whole prior-weighted volume is the tail
    push Not at hzero
    have hKpos : ∀ x ∈ W, 0 < K x := fun x hx => lt_of_le_of_ne (hK0 x hx) (hzero x hx).symm
    obtain ⟨δ, hδ, hgap⟩ := exists_gap_of_pos hK.continuousOn hKpos hpc hpW
    let T := NormalisedCoreTransport.ofEmptyCores K prior hprior.continuous.measurable hδ hgap
    exact ⟨(BridgeInputs.ofTransport T hKm hprior hp0 hpc hobs).certificate,
      (BridgeInputs.ofTransport T hKm hprior hp0 hpc hobs).commonD_le⟩

/-- ★★★ **Target A in certificate form.** An analytic nonnegative phase on a connected open `W`, not
identically zero on `W`, and a smooth nonnegative prior with compact support in `W`: the partition
function with insertions `∫ prior·obs·e^{−NK}` has a smooth expansion certificate of logarithmic
degree `≤ d − 1`. No measurability of `K`, no distinguished origin, and `K` may be positive. -/
theorem exists_smoothExpansionCertificate_of_analyticOnNhd {W : Set (Fin d → ℝ)} (hWo : IsOpen W)
    (hWc : IsConnected W) {K : (Fin d → ℝ) → ℝ} (hK : AnalyticOnNhd ℝ K W)
    (hK0 : ∀ x ∈ W, 0 ≤ K x) (hKnt : ∃ x ∈ W, K x ≠ 0) {prior obs : (Fin d → ℝ) → ℝ}
    (hprior : ContDiff ℝ ∞ prior) (hp0 : ∀ y, 0 ≤ prior y) (hpc : HasCompactSupport prior)
    (hpW : tsupport prior ⊆ W) (hobs : ContDiff ℝ ∞ obs) :
    ∃ C : SmoothExpansionCertificate (fun N => ∫ y, prior y * obs y * Real.exp (-N * K y)),
      C.D ≤ d - 1 := by
  have hZ := laplace_congr_of_support (K₂ := W.indicator K) (prior := prior) (obs := obs)
    fun y hy => (indicator_of_mem (hpW (subset_tsupport prior hy)) K).symm
  rw [hZ]
  obtain ⟨x, hxW, hKx⟩ := hKnt
  exact exists_smoothExpansionCertificate_of_analyticOnNhd_of_measurable hWo hWc
    (analyticOnNhd_indicator hWo hK) (measurable_indicator_of_continuousOn hWo hK.continuousOn)
    (fun x hx => by rw [indicator_of_mem hx]; exact hK0 x hx)
    ⟨x, hxW, by rwa [indicator_of_mem hxW]⟩ hprior hp0 hpc hpW hobs

/-- Target A in the `∃ c Q D` form, with the logarithmic degree bound. -/
theorem exists_hasSmoothCoordFreeExpansion_of_analyticOnNhd' {W : Set (Fin d → ℝ)}
    (hWo : IsOpen W) (hWc : IsConnected W) {K : (Fin d → ℝ) → ℝ} (hK : AnalyticOnNhd ℝ K W)
    (hK0 : ∀ x ∈ W, 0 ≤ K x) (hKnt : ∃ x ∈ W, K x ≠ 0) {prior obs : (Fin d → ℝ) → ℝ}
    (hprior : ContDiff ℝ ∞ prior) (hp0 : ∀ y, 0 ≤ prior y) (hpc : HasCompactSupport prior)
    (hpW : tsupport prior ⊆ W) (hobs : ContDiff ℝ ∞ obs) :
    ∃ (c : ℝ → ℕ → ℝ) (Q D : ℕ), D ≤ d - 1 ∧
      HasSmoothCoordFreeExpansion (fun N => ∫ y, prior y * obs y * Real.exp (-N * K y)) c Q D := by
  obtain ⟨C, hC⟩ := exists_smoothExpansionCertificate_of_analyticOnNhd hWo hWc hK hK0 hKnt hprior
    hp0 hpc hpW hobs
  exact ⟨C.coeff, C.Q, C.D, hC, C.hasSmoothCoordFreeExpansion⟩

/-- **Coefficient uniqueness**: any two certificates of the same function have the same
coefficient array. -/
theorem _root_.Grammar.SmoothExpansionCertificate.coeff_unique {Z : ℝ → ℝ}
    (C C' : SmoothExpansionCertificate Z) : C.coeff = C'.coeff :=
  funext fun μ => funext fun q => C.coeff_eq C' μ q

/-! ### Pure-tail vanishing -/

/-- With no core charts the coefficient array of the bridge decomposition vanishes. -/
theorem BridgeInputs.coeff_eq_zero_of_isEmpty (X : BridgeInputs d) (h : IsEmpty X.T.ι) (μ : ℝ)
    (q : ℕ) : X.decomp.coeff μ q = 0 := by
  have hcard : Fintype.card X.PIdx = 0 := by
    have := h
    exact Fintype.card_eq_zero
  unfold SmoothCoreDecomposition.coeff
  exact Finset.sum_eq_zero fun I _ => (Fin.cast hcard I).elim0

/-- The bridge inputs of the empty-core transport of a prior seeing a phase gap. -/
noncomputable def BridgeInputs.ofEmptyCores {K prior obs : (Fin d → ℝ) → ℝ} (hKm : Measurable K)
    (hprior : ContDiff ℝ ∞ prior) (hp0 : ∀ y, 0 ≤ prior y) (hpc : HasCompactSupport prior)
    {δ : ℝ} (hδ : 0 < δ) (hgap : ∀ y, prior y ≠ 0 → δ ≤ K y) (hobs : ContDiff ℝ ∞ obs) :
    BridgeInputs d :=
  BridgeInputs.ofTransport
    (NormalisedCoreTransport.ofEmptyCores K prior hprior.continuous.measurable hδ hgap) hKm hprior
    hp0 hpc hobs

/-- The empty-core bridge inputs have vanishing coefficients. -/
theorem BridgeInputs.coeff_ofEmptyCores {K prior obs : (Fin d → ℝ) → ℝ} (hKm : Measurable K)
    (hprior : ContDiff ℝ ∞ prior) (hp0 : ∀ y, 0 ≤ prior y) (hpc : HasCompactSupport prior)
    {δ : ℝ} (hδ : 0 < δ) (hgap : ∀ y, prior y ≠ 0 → δ ≤ K y) (hobs : ContDiff ℝ ∞ obs) (μ : ℝ)
    (q : ℕ) : (BridgeInputs.ofEmptyCores hKm hprior hp0 hpc hδ hgap hobs).decomp.coeff μ q = 0 :=
  (BridgeInputs.ofEmptyCores hKm hprior hp0 hpc hδ hgap hobs).coeff_eq_zero_of_isEmpty
    (inferInstanceAs (IsEmpty Empty)) μ q

/-- ★ **Consumer regression, empty cores**: the partition function with insertions of a prior
seeing a phase gap has the smooth coordinate-free expansion, with all coefficients zero. -/
theorem BridgeInputs.emptyCores_hasSmoothCoordFreeExpansion {K prior obs : (Fin d → ℝ) → ℝ}
    (hKm : Measurable K) (hprior : ContDiff ℝ ∞ prior) (hp0 : ∀ y, 0 ≤ prior y)
    (hpc : HasCompactSupport prior) {δ : ℝ} (hδ : 0 < δ) (hgap : ∀ y, prior y ≠ 0 → δ ≤ K y)
    (hobs : ContDiff ℝ ∞ obs) :
    HasSmoothCoordFreeExpansion (fun N => ∫ y, prior y * obs y * Real.exp (-N * K y))
      (fun _ _ => 0) (BridgeInputs.ofEmptyCores hKm hprior hp0 hpc hδ hgap hobs).decomp.commonQ
      (BridgeInputs.ofEmptyCores hKm hprior hp0 hpc hδ hgap hobs).decomp.commonD := by
  have h := (BridgeInputs.ofEmptyCores hKm hprior hp0 hpc hδ hgap hobs).hasSmoothCoordFreeExpansion
  have hc : (BridgeInputs.ofEmptyCores hKm hprior hp0 hpc hδ hgap hobs).decomp.coeff =
      fun _ _ => 0 :=
    funext fun μ => funext fun q =>
      BridgeInputs.coeff_ofEmptyCores hKm hprior hp0 hpc hδ hgap hobs μ q
  rwa [hc] at h

/-- ★★ **Pure-tail vanishing**: if the phase is continuous and positive on an open set containing
the support of the prior, every certificate of the partition function with insertions has all
coefficients zero. -/
theorem coeff_eq_zero_of_pos_phase {W : Set (Fin d → ℝ)} (hWo : IsOpen W)
    {K : (Fin d → ℝ) → ℝ} (hKc : ContinuousOn K W) (hKpos : ∀ x ∈ W, 0 < K x)
    {prior obs : (Fin d → ℝ) → ℝ} (hprior : ContDiff ℝ ∞ prior) (hp0 : ∀ y, 0 ≤ prior y)
    (hpc : HasCompactSupport prior) (hpW : tsupport prior ⊆ W) (hobs : ContDiff ℝ ∞ obs)
    (C : SmoothExpansionCertificate (fun N => ∫ y, prior y * obs y * Real.exp (-N * K y)))
    (μ : ℝ) (q : ℕ) : C.coeff μ q = 0 := by
  have hZ := laplace_congr_of_support (K₂ := W.indicator K) (prior := prior) (obs := obs)
    fun y hy => (indicator_of_mem (hpW (subset_tsupport prior hy)) K).symm
  have hKpos' : ∀ x ∈ W, 0 < W.indicator K x := fun x hx => by
    rw [indicator_of_mem hx]; exact hKpos x hx
  obtain ⟨δ, hδ, hgap⟩ :=
    exists_gap_of_pos (hKc.congr eqOn_indicator) hKpos' hpc hpW
  have hD : ∃ D : SmoothExpansionCertificate
      (fun N => ∫ y, prior y * obs y * Real.exp (-N * K y)), D.coeff μ q = 0 := by
    rw [hZ]
    exact ⟨(BridgeInputs.ofEmptyCores (measurable_indicator_of_continuousOn hWo hKc) hprior hp0
      hpc hδ hgap hobs).certificate,
      BridgeInputs.coeff_ofEmptyCores (measurable_indicator_of_continuousOn hWo hKc) hprior hp0
        hpc hδ hgap hobs μ q⟩
  obtain ⟨D, hD⟩ := hD
  rw [C.coeff_eq D μ q]
  exact hD

/-! ### Consumer regression: the genuine-tail monomial transport -/

/-- The bridge inputs of the one-dimensional monomial transport with a genuine tail. -/
noncomputable def BridgeInputs.ofMonomialWithTail (k : Fin 1 → ℕ) (hk : ∀ j, 0 < k j) {c : ℝ}
    (hc : 0 < c) {r a : ℝ} (hr : 0 < r) (hra : r < a) {prior obs : (Fin 1 → ℝ) → ℝ}
    (hprior : ContDiff ℝ ∞ prior) (hp0 : ∀ y, 0 ≤ prior y)
    (hsupp : ∀ y, y ∉ centeredBox 1 a → prior y = 0) (hobs : ContDiff ℝ ∞ obs) : BridgeInputs 1 :=
  BridgeInputs.ofTransport
    (NormalisedCoreTransport.ofMonomialWithTail k hk hc hr hra hprior.continuous.measurable hp0
      hsupp)
    (measurable_monomialPhase k c) hprior hp0 (HasCompactSupport.intro (isCompact_centeredBox 1 a)
      hsupp) hobs

/-- ★ **Consumer regression, genuine tail**: the one-dimensional monomial phase with the
chartwise cutoff at `r < a` and the tail beyond it feeds the consumer. -/
theorem BridgeInputs.monomialWithTail_hasSmoothCoordFreeExpansion (k : Fin 1 → ℕ)
    (hk : ∀ j, 0 < k j) {c : ℝ} (hc : 0 < c) {r a : ℝ} (hr : 0 < r) (hra : r < a)
    {prior obs : (Fin 1 → ℝ) → ℝ} (hprior : ContDiff ℝ ∞ prior) (hp0 : ∀ y, 0 ≤ prior y)
    (hsupp : ∀ y, y ∉ centeredBox 1 a → prior y = 0) (hobs : ContDiff ℝ ∞ obs) :
    HasSmoothCoordFreeExpansion
      (fun N => ∫ y, prior y * obs y * Real.exp (-N * (c * ∏ j, y j ^ (2 * k j))))
      (BridgeInputs.ofMonomialWithTail k hk hc hr hra hprior hp0 hsupp hobs).decomp.coeff
      (BridgeInputs.ofMonomialWithTail k hk hc hr hra hprior hp0 hsupp hobs).decomp.commonQ
      (BridgeInputs.ofMonomialWithTail k hk hc hr hra hprior hp0 hsupp hobs).decomp.commonD :=
  (BridgeInputs.ofMonomialWithTail k hk hc hr hra hprior hp0 hsupp hobs).hasSmoothCoordFreeExpansion

/-- The box bump `boxBump (a/2) a` vanishes off the closed box of half side `a`. -/
theorem boxBump_eq_zero_of_notMem_centeredBox {a : ℝ} (ha : 0 < a) {y : Fin d → ℝ}
    (hy : y ∉ centeredBox d a) : boxBump (a / 2) a y = 0 := by
  simp only [centeredBox, mem_ofPred_eq, not_forall, not_le] at hy
  obtain ⟨j, hj⟩ := hy
  exact boxBump_eq_zero (by linarith) (by linarith) ⟨j, hj.le⟩

/-- ★ **Consumer regression, nonzero tail**: a normalised core transport of the box bump for the
one-dimensional monomial phase with a nonzero tail, whose partition function with insertions has
the smooth coordinate-free expansion. -/
theorem exists_tail_ne_zero_hasSmoothCoordFreeExpansion (k : Fin 1 → ℕ) (hk : ∀ j, 0 < k j)
    {c : ℝ} (hc : 0 < c) {r a : ℝ} (hr : 0 < r) (hra : r < a) {obs : (Fin 1 → ℝ) → ℝ}
    (hobs : ContDiff ℝ ∞ obs) :
    ∃ T : NormalisedCoreTransport 1 (fun u => c * ∏ j, u j ^ (2 * k j)) (boxBump (a / 2) a),
      T.tail ≠ 0 ∧
      HasSmoothCoordFreeExpansion
        (fun N => ∫ y, boxBump (a / 2) a y * obs y * Real.exp (-N * (c * ∏ j, y j ^ (2 * k j))))
        (BridgeInputs.ofTransport T (measurable_monomialPhase k c) (contDiff_boxBump _ _)
          (boxBump_nonneg _ _)
          (HasCompactSupport.intro (isCompact_centeredBox 1 a) fun _ hy =>
            boxBump_eq_zero_of_notMem_centeredBox (hr.trans hra) hy) hobs).decomp.coeff
        (BridgeInputs.ofTransport T (measurable_monomialPhase k c) (contDiff_boxBump _ _)
          (boxBump_nonneg _ _)
          (HasCompactSupport.intro (isCompact_centeredBox 1 a) fun _ hy =>
            boxBump_eq_zero_of_notMem_centeredBox (hr.trans hra) hy) hobs).decomp.commonQ
        (BridgeInputs.ofTransport T (measurable_monomialPhase k c) (contDiff_boxBump _ _)
          (boxBump_nonneg _ _)
          (HasCompactSupport.intro (isCompact_centeredBox 1 a) fun _ hy =>
            boxBump_eq_zero_of_notMem_centeredBox (hr.trans hra) hy) hobs).decomp.commonD := by
  obtain ⟨T, hT⟩ := NormalisedCoreTransport.exists_tail_ne_zero k hk hc hr hra
  exact ⟨T, hT, T.hasSmoothCoordFreeExpansion (measurable_monomialPhase k c) (contDiff_boxBump _ _)
    (boxBump_nonneg _ _) _ hobs⟩

end SmoothEngine

end Grammar
