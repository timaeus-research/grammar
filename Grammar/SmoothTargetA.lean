/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothBridgeConsumer
import Monomialize.Transport.ResolutionBridge

/-!
# Target A: the smooth coordinate-free expansion from an analytic phase (consult #119)

The first UNCONDITIONAL theorem of the "atlas from resolution data" project. For an analytic
phase `K` on an open `U₀`, vanishing but not identically zero at `0`, nonnegative on a connected
open `W ∋ 0`, a smooth nonnegative prior with compact support inside `W`, and a smooth
observable, the partition function with insertions `∫ prior·obs·e^{−NK}` has the smooth
coordinate-free expansion: a lattice power–log expansion with a `o(N^{−A})` remainder at every
order, whose scalar coefficients are intrinsic (any two normalised core transports give the same
coefficients, `BridgeInputs.coeff_eq_of_transports`).

The proof composes hironaka's resolution bridge — Watanabe's modification
(`exists_watanabeModificationOn`) turned into a `NormalisedCoreTransport` by finitely many even
chart boxes with chartwise cutoffs and a gap tail
(`exists_normalisedCoreTransport_of_analyticOnNhd`) — with the grammar consumer
`NormalisedCoreTransport.hasSmoothCoordFreeExpansion`. The one
hypothesis beyond the paper's is `Measurable K` (the phase is arbitrary off `W`; a measurable
representative can always be chosen). Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology TopologicalSpace
open scoped ENNReal ContDiff
open Monomialize.VolumeScaling

namespace Grammar

namespace SmoothEngine

variable {d : ℕ}

/-- ★★★ **Target A.** An analytic nonnegative phase on a connected neighbourhood of `0` and a
smooth compactly supported prior inside it: `∫ prior·obs·e^{−NK}` has the smooth coordinate-free
expansion for every smooth observable. -/
theorem exists_hasSmoothCoordFreeExpansion_of_analyticOnNhd {U₀ : Set (Fin d → ℝ)}
    (hU₀ : IsOpen U₀) {K : (Fin d → ℝ) → ℝ} (hK : AnalyticOnNhd ℝ K U₀) (hKm : Measurable K)
    (h0 : K 0 = 0) (hne : ¬ ∀ᶠ x in 𝓝 (0 : Fin d → ℝ), K x = 0) (W : Opens (Fin d → ℝ))
    (hW : IsConnected (W : Set (Fin d → ℝ))) (h0W : (0 : Fin d → ℝ) ∈ W)
    (hWU : (W : Set (Fin d → ℝ)) ⊆ U₀) (hK0 : ∀ x ∈ (W : Set (Fin d → ℝ)), 0 ≤ K x)
    {prior obs : (Fin d → ℝ) → ℝ} (hprior : ContDiff ℝ ∞ prior) (hp0 : ∀ y, 0 ≤ prior y)
    (hpc : HasCompactSupport prior) (hpW : tsupport prior ⊆ (W : Set (Fin d → ℝ)))
    (hobs : ContDiff ℝ ∞ obs) :
    ∃ (c : ℝ → ℕ → ℝ) (Q D : ℕ),
      HasSmoothCoordFreeExpansion (fun N => ∫ y, prior y * obs y * Real.exp (-N * K y)) c Q D := by
  obtain ⟨T⟩ := exists_normalisedCoreTransport_of_analyticOnNhd hU₀ hK h0 hne W hW h0W hWU hK0
    hprior.continuous.measurable hp0 hpc hpW
  exact ⟨_, _, _, T.hasSmoothCoordFreeExpansion hKm hprior hp0 hpc hobs⟩

/-- The same statement for the global Laplace integral over `ℝ^d`. -/
theorem exists_hasSmoothCoordFreeExpansion_globalLaplace_of_analyticOnNhd {U₀ : Set (Fin d → ℝ)}
    (hU₀ : IsOpen U₀) {K : (Fin d → ℝ) → ℝ} (hK : AnalyticOnNhd ℝ K U₀) (hKm : Measurable K)
    (h0 : K 0 = 0) (hne : ¬ ∀ᶠ x in 𝓝 (0 : Fin d → ℝ), K x = 0) (W : Opens (Fin d → ℝ))
    (hW : IsConnected (W : Set (Fin d → ℝ))) (h0W : (0 : Fin d → ℝ) ∈ W)
    (hWU : (W : Set (Fin d → ℝ)) ⊆ U₀) (hK0 : ∀ x ∈ (W : Set (Fin d → ℝ)), 0 ≤ K x)
    {prior obs : (Fin d → ℝ) → ℝ} (hprior : ContDiff ℝ ∞ prior) (hp0 : ∀ y, 0 ≤ prior y)
    (hpc : HasCompactSupport prior) (hpW : tsupport prior ⊆ (W : Set (Fin d → ℝ)))
    (hobs : ContDiff ℝ ∞ obs) :
    ∃ (c : ℝ → ℕ → ℝ) (Q D : ℕ),
      HasSmoothCoordFreeExpansion (globalLaplace Set.univ K fun y => prior y * obs y) c Q D := by
  obtain ⟨c, Q, D, h⟩ := exists_hasSmoothCoordFreeExpansion_of_analyticOnNhd hU₀ hK hKm h0 hne W
    hW h0W hWU hK0 hprior hp0 hpc hpW hobs
  refine ⟨c, Q, D, ?_⟩
  have : (globalLaplace Set.univ K fun y => prior y * obs y) =
      fun N => ∫ y, prior y * obs y * Real.exp (-N * K y) := by
    funext N
    simp [globalLaplace]
  rwa [this]

end SmoothEngine

end Grammar
