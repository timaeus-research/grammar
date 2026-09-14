/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothDomainConsumer
import Monomialize.Transport.DomainBridgeFinal

/-!
# Target B: the smooth coordinate-free expansion over a compact semianalytic domain

The second unconditional theorem of the "atlas from resolution data" project (consult #120 §4–§7).
For a phase `K` and boundary functions `π_ℓ` analytic on an open `U₀`, `K ≥ 0` on a connected open
`W ∋ 0` (`W ⊆ U₀`), the product `K · ∏ π_ℓ` vanishing at `0` and not identically zero near `0`,
the COMPACT semianalytic domain `Wdom = W ∩ {∀ ℓ, 0 ≤ π_ℓ}`, a smooth nonnegative prior with compact
support inside `W`, and a smooth observable, the partition function with insertions
`∫_{Wdom} prior·obs·e^{−NK}` has the smooth coordinate-free expansion. The proof composes
hironaka's domain bridge (Watanabe's modification of the PRODUCT, factor splitting in the analytic
local ring, unit absorption, the sign rules reading the domain as selected orthants, and a gap
tail — `exists_normalisedDomainCoreTransport_of_analyticOnNhd`) with the grammar consumer
`NormalisedDomainCoreTransport.hasSmoothCoordFreeExpansion`. `Measurable K` is the one extra
hypothesis (a representative off `W`). Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology TopologicalSpace
open scoped ENNReal ContDiff
open Monomialize.VolumeScaling

namespace Grammar

namespace SmoothEngine

variable {d r : ℕ}

/-- ★★★ **Target B.** The smooth coordinate-free expansion of `∫_{W ∩ {π ≥ 0}} prior·obs·e^{−NK}`
for an analytic nonnegative phase and analytic boundary functions on a connected neighbourhood of
`0`, a compact domain, and a smooth compactly supported prior inside the neighbourhood. -/
theorem exists_hasSmoothCoordFreeExpansion_domain_of_analyticOnNhd {U₀ : Set (Fin d → ℝ)}
    (hU₀ : IsOpen U₀) {K : (Fin d → ℝ) → ℝ} (hK : AnalyticOnNhd ℝ K U₀) (hKm : Measurable K)
    {π : Fin r → (Fin d → ℝ) → ℝ} (hπ : ∀ ℓ, AnalyticOnNhd ℝ (π ℓ) U₀)
    (h0 : K 0 * ∏ ℓ, π ℓ 0 = 0) (hne : ¬ ∀ᶠ x in 𝓝 (0 : Fin d → ℝ), K x * ∏ ℓ, π ℓ x = 0)
    (W : Opens (Fin d → ℝ)) (hW : IsConnected (W : Set (Fin d → ℝ))) (h0W : (0 : Fin d → ℝ) ∈ W)
    (hWU : (W : Set (Fin d → ℝ)) ⊆ U₀) (hK0 : ∀ x ∈ (W : Set (Fin d → ℝ)), 0 ≤ K x)
    (hWc : IsCompact (boundaryDomain (W : Set (Fin d → ℝ)) π))
    {prior obs : (Fin d → ℝ) → ℝ} (hprior : ContDiff ℝ ∞ prior) (hp0 : ∀ y, 0 ≤ prior y)
    (hpW : tsupport prior ⊆ (W : Set (Fin d → ℝ))) (hobs : ContDiff ℝ ∞ obs) :
    ∃ (c : ℝ → ℕ → ℝ) (Q D : ℕ),
      HasSmoothCoordFreeExpansion (fun N => ∫ y in boundaryDomain (W : Set (Fin d → ℝ)) π,
        prior y * obs y * Real.exp (-N * K y)) c Q D := by
  obtain ⟨T⟩ := exists_normalisedDomainCoreTransport_of_analyticOnNhd hU₀ hK hπ h0 hne W hW h0W
    hWU hK0 hWc hprior.continuous.measurable hp0 hpW
  exact ⟨_, _, _, T.hasSmoothCoordFreeExpansion hWc hKm hprior hp0 hobs⟩

/-- The certificate form: the expansion certificate with logarithmic degree at most `d − 1`. -/
theorem exists_smoothExpansionCertificate_domain_of_analyticOnNhd {U₀ : Set (Fin d → ℝ)}
    (hU₀ : IsOpen U₀) {K : (Fin d → ℝ) → ℝ} (hK : AnalyticOnNhd ℝ K U₀) (hKm : Measurable K)
    {π : Fin r → (Fin d → ℝ) → ℝ} (hπ : ∀ ℓ, AnalyticOnNhd ℝ (π ℓ) U₀)
    (h0 : K 0 * ∏ ℓ, π ℓ 0 = 0) (hne : ¬ ∀ᶠ x in 𝓝 (0 : Fin d → ℝ), K x * ∏ ℓ, π ℓ x = 0)
    (W : Opens (Fin d → ℝ)) (hW : IsConnected (W : Set (Fin d → ℝ))) (h0W : (0 : Fin d → ℝ) ∈ W)
    (hWU : (W : Set (Fin d → ℝ)) ⊆ U₀) (hK0 : ∀ x ∈ (W : Set (Fin d → ℝ)), 0 ≤ K x)
    (hWc : IsCompact (boundaryDomain (W : Set (Fin d → ℝ)) π))
    {prior obs : (Fin d → ℝ) → ℝ} (hprior : ContDiff ℝ ∞ prior) (hp0 : ∀ y, 0 ≤ prior y)
    (hpW : tsupport prior ⊆ (W : Set (Fin d → ℝ))) (hobs : ContDiff ℝ ∞ obs) :
    ∃ C : SmoothExpansionCertificate
      (globalLaplace (boundaryDomain (W : Set (Fin d → ℝ)) π) K fun y => prior y * obs y),
      C.D ≤ d - 1 := by
  obtain ⟨T⟩ := exists_normalisedDomainCoreTransport_of_analyticOnNhd hU₀ hK hπ h0 hne W hW h0W
    hWU hK0 hWc hprior.continuous.measurable hp0 hpW
  exact ⟨(DomainBridgeInputs.ofTransport T hWc hKm hprior hp0 hobs).certificate,
    (DomainBridgeInputs.ofTransport T hWc hKm hprior hp0 hobs).commonD_le⟩

end SmoothEngine

end Grammar
