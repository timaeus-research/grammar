/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothResolvedStratumPositive
import Grammar.SmoothResolvedRLCTIndex

/-!
# The zero-order condition at the extremal exponent

Consult #131, optional corollary (1). At the extremal exponent `λ*` of Theorem D
(`IsExtremalData λ* m*`: every wall through the zero fibre has `2kλ* ≤ h + 1`), a wall
resonating with `λ*` has `2kλ* = h + 1 + n ≥ h + 1 ≥ 2kλ*`, so `n = 0`: the zero-order condition
of Theorem E holds on every exact stratum `S^{λ*}_c` (★★ `zeroOrder_of_extremalData`). Hence the
leading functional `𝒯^U_{λ*,c−1}`, restricted to observables vanishing near the zero fibre of
depth `≥ c+1`, is nonnegative on nonnegative observables and depends only on their values on
`S^{λ*}_c` (`coeff_nonneg_of_deep_extremal`, `coeff_eq_of_eqOn_exactStratum_extremal`). This links
Theorem E to Theorem D's leading functional without a global-minimum hypothesis on Theorem E
itself. Non-claims: the restriction to observables vanishing near the deeper fibre is not
vacuous (`m*` bounds the resonance count, not the depth). Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff Manifold
open Monomialize.VolumeScaling Monomialize.Transport Monomialize.Manifold
open Grammar.NormalCrossing

namespace Grammar

namespace SmoothEngine

variable {d : ℕ}

namespace ResolvedData

variable (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)

open Classical in
/-- On a point whose resonance count equals its depth, every wall resonates. -/
theorem resonates_of_resonanceCount_eq_depth {μ : ℝ} {P : Ξ.R.U}
    (h : resonanceCount Ξ.R Ξ.hK0 μ P = depth Ξ.R Ξ.hK0 P) :
    ∀ q ∈ pairs Ξ.R Ξ.hK0 P, Resonates μ q := by
  unfold resonanceCount depth at h
  exact Multiset.filter_eq_self.1
    (Multiset.eq_of_le_of_card_le (Multiset.filter_le _ _) h.symm.le)

/-- ★★ **The zero-order condition holds at the extremal exponent** on every exact stratum. -/
theorem zeroOrder_of_extremalData {lam : ℝ} {m : ℕ} (h : Ξ.IsExtremalData lam m) (c : ℕ) :
    Ξ.ZeroOrder lam c := by
  intro P hP q hq
  obtain ⟨hP0, hdepth, hres⟩ := hP
  have hall := Ξ.resonates_of_resonanceCount_eq_depth (μ := lam) (P := P) (by rw [hres, hdepth])
  obtain ⟨n, hn⟩ := hall q hq
  have hle := h.1 P hP0 q hq
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

/-- ★★ **Positivity of the leading functional on each stratum**: at the extremal exponent, a
nonnegative observable vanishing near the zero fibre of depth `≥ c+1` has nonnegative
`(λ*, c−1)` coefficient. -/
theorem coeff_nonneg_of_deep_extremal {lam : ℝ} {m : ℕ} (h : Ξ.IsExtremalData lam m) {c : ℕ}
    (hc : 1 ≤ c) (hF : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), Ξ.F P = 0) (hF0 : ∀ P, 0 ≤ Ξ.F P) :
    0 ≤ Ξ.coeff Y lam (c - 1) :=
  Ξ.coeff_nonneg_of_deep Y hc (Ξ.zeroOrder_of_extremalData h c) hF hF0

/-- ★★ **Values-only dependence of the leading functional on each stratum** at the extremal
exponent. -/
theorem coeff_eq_of_eqOn_exactStratum_extremal {lam : ℝ} {m : ℕ} (h : Ξ.IsExtremalData lam m)
    {c : ℕ} (hc : 1 ≤ c) {G G' : Ξ.R.U → ℝ} (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G)
    (hG' : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G')
    (hG0 : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), G P = 0)
    (hG0' : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), G' P = 0)
    (heq : EqOn G G' (Ξ.exactStratum lam c)) :
    (Ξ.withF G hG).coeff Y lam (c - 1) = (Ξ.withF G' hG').coeff Y lam (c - 1) :=
  Ξ.coeff_eq_of_eqOn_exactStratum Y hc (Ξ.zeroOrder_of_extremalData h c) hG hG' hG0 hG0' heq

end ResolvedData

end SmoothEngine

end Grammar
