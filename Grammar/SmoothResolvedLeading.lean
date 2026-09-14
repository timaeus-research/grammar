/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothResolvedCoefficient
import Grammar.SmoothLeadingTerm

/-!
# Positivity of the leading resolved coefficient functional

Consult #127, Unit D8a. Fix the resolved data `Ξ` (modification, prior) and a resolved core
transport `Y`, and write `𝒯_{ν,p}[G] = (Ξ.withF G).coeff Y ν p` for the resolved coefficient
functionals. An index `(μ₀, q₀)` is **leading** (`IsLeadingIndex`) when every functional
`𝒯_{ν,p}` at an index PRECEDING it (smaller exponent, or the same exponent with a higher log
power) vanishes identically. Then:

* `tendsto_normalised_Z`: `N^{μ₀} (log N)^{−q₀} Z^U_N[G] → 𝒯_{μ₀,q₀}[G]` for every smooth `G`;
* ★★ `coeff_nonneg_of_leading`: `G ≥ 0` a.e. for `μ_U` (in particular `G ≥ 0` on the compact
  set `π⁻¹(supp prior)`, `coeff_nonneg_of_leading_of_nonneg_on`) implies `𝒯_{μ₀,q₀}[G] ≥ 0` —
  the leading functional is a POSITIVE linear functional on smooth functions on `U`;
* ★★ `abs_coeff_le_of_leading`: `|G| ≤ M` on `π⁻¹(supp prior)` implies
  `|𝒯_{μ₀,q₀}[G]| ≤ M · 𝒯_{μ₀,q₀}[1]` — the leading functional is of order zero (bounded by the
  sup norm on the carrier of `μ_U`), with mass `𝒯_{μ₀,q₀}[1] ≥ 0`.

Non-claims: no existence of a leading index (some coefficient functional may be nonzero — a
non-claim of the whole programme — and then a first index exists on the lattice; this is left
conditional); no Riesz representation of the leading functional as a measure on the zero fibre
(a separate unit); the order-zero bound uses `sup` over the whole carrier `π⁻¹(supp prior)`, not
only over the zero fibre.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff Manifold
open Monomialize.VolumeScaling Monomialize.Transport

namespace Grammar

namespace SmoothEngine

variable {d : ℕ}

namespace ResolvedData

variable (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)

/-- The coefficient functional depends on the observable only through its values. -/
theorem coeff_congr {G G' : Ξ.R.U → ℝ} (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G)
    (hG' : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G') (h : G = G') (μ : ℝ) (q : ℕ) :
    (Ξ.withF G hG).coeff Y μ q = (Ξ.withF G' hG').coeff Y μ q := by
  subst h; rfl

/-- The coefficient of a constant observable. -/
theorem coeff_const (M : ℝ) (μ : ℝ) (q : ℕ) :
    (Ξ.withF (fun _ => M) contMDiff_const).coeff Y μ q =
      M * (Ξ.withF (fun _ => (1 : ℝ)) contMDiff_const).coeff Y μ q := by
  rw [← Ξ.coeff_smul Y (G := fun _ => (1 : ℝ)) contMDiff_const M μ q]
  exact Ξ.coeff_congr Y _ _ (funext fun _ => (mul_one M).symm) μ q

/-- `(μ₀, q₀)` is a leading index of the resolved expansion: every coefficient functional at a
preceding index vanishes identically. -/
def IsLeadingIndex (μ₀ : ℝ) (q₀ : ℕ) : Prop :=
  ∀ ν p, Precedes ν p μ₀ q₀ → ∀ (G : Ξ.R.U → ℝ) (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G),
    (Ξ.withF G hG).coeff Y ν p = 0

variable {μ₀ : ℝ} {q₀ : ℕ}

/-- ★★ **The normalised limit**: at a leading index, `N^{μ₀} (log N)^{−q₀} Z^U_N[G]` converges to
the leading coefficient functional. -/
theorem tendsto_normalised_Z (hlead : Ξ.IsLeadingIndex Y μ₀ q₀) {G : Ξ.R.U → ℝ}
    (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) :
    Tendsto (normalised μ₀ q₀ (Ξ.withF G hG).Z) atTop (𝓝 ((Ξ.withF G hG).coeff Y μ₀ q₀)) :=
  tendsto_normalised_of_leading ((Ξ.withF G hG).decomp Y).commonQ_pos
    ((Ξ.withF G hG).hasSmoothCoordFreeExpansion Y)
    ((Ξ.withF G hG).decomp Y).toCertificate.coeff_support fun ν p hp => hlead ν p hp G hG

theorem Z_nonneg {G : Ξ.R.U → ℝ} (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G)
    (hG0 : ∀ᵐ P ∂Ξ.μU, 0 ≤ G P) (N : ℝ) : 0 ≤ (Ξ.withF G hG).Z N := by
  change 0 ≤ ∫ P, G P * Real.exp (-N * Ξ.K (Ξ.R.gv P)) ∂Ξ.μU
  exact integral_nonneg_of_ae (hG0.mono fun P hP => mul_nonneg hP (Real.exp_pos _).le)

/-- ★★ **Positivity of the leading functional**: an observable nonnegative a.e. for `μ_U` has a
nonnegative leading coefficient. -/
theorem coeff_nonneg_of_leading (hlead : Ξ.IsLeadingIndex Y μ₀ q₀) {G : Ξ.R.U → ℝ}
    (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) (hG0 : ∀ᵐ P ∂Ξ.μU, 0 ≤ G P) :
    0 ≤ (Ξ.withF G hG).coeff Y μ₀ q₀ :=
  ge_of_tendsto (Ξ.tendsto_normalised_Z Y hlead hG)
    ((eventually_gt_atTop 1).mono fun N hN => normalised_nonneg hN (Ξ.Z_nonneg hG hG0 N))

/-- Positivity for observables nonnegative on the carrier `π⁻¹(supp prior)` of `μ_U`. -/
theorem coeff_nonneg_of_leading_of_nonneg_on (hlead : Ξ.IsLeadingIndex Y μ₀ q₀)
    {G : Ξ.R.U → ℝ} (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G)
    (hG0 : ∀ P, Ξ.R.gv P ∈ tsupport Ξ.prior → 0 ≤ G P) :
    0 ≤ (Ξ.withF G hG).coeff Y μ₀ q₀ :=
  Ξ.coeff_nonneg_of_leading Y hlead hG (Ξ.ae_μU_mem.mono fun P hP => hG0 P hP)

/-- The mass of the leading functional is nonnegative. -/
theorem coeff_one_nonneg_of_leading (hlead : Ξ.IsLeadingIndex Y μ₀ q₀) :
    0 ≤ (Ξ.withF (fun _ => (1 : ℝ)) contMDiff_const).coeff Y μ₀ q₀ :=
  Ξ.coeff_nonneg_of_leading Y hlead contMDiff_const (Eventually.of_forall fun _ => zero_le_one)

/-- ★★ **The leading functional has order zero**: `|G| ≤ M` on the carrier `π⁻¹(supp prior)`
implies `|𝒯_{μ₀,q₀}[G]| ≤ M · 𝒯_{μ₀,q₀}[1]`. -/
theorem abs_coeff_le_of_leading (hlead : Ξ.IsLeadingIndex Y μ₀ q₀) {G : Ξ.R.U → ℝ}
    (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) {M : ℝ}
    (hM : ∀ P, Ξ.R.gv P ∈ tsupport Ξ.prior → |G P| ≤ M) :
    |(Ξ.withF G hG).coeff Y μ₀ q₀| ≤
      M * (Ξ.withF (fun _ => (1 : ℝ)) contMDiff_const).coeff Y μ₀ q₀ := by
  have hneg : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ (fun P => (-1 : ℝ) * G P) :=
    contMDiff_const.mul hG
  -- `M − G ≥ 0` on the carrier
  have h1 : 0 ≤ (Ξ.withF (fun P => M + (-1 : ℝ) * G P) (contMDiff_const.add hneg)).coeff Y μ₀ q₀ :=
    Ξ.coeff_nonneg_of_leading_of_nonneg_on Y hlead _ fun P hP => by
      have := (abs_le.1 (hM P hP)).2; linarith
  -- `M + G ≥ 0` on the carrier
  have h2 : 0 ≤ (Ξ.withF (fun P => M + G P) (contMDiff_const.add hG)).coeff Y μ₀ q₀ :=
    Ξ.coeff_nonneg_of_leading_of_nonneg_on Y hlead _ fun P hP => by
      have := (abs_le.1 (hM P hP)).1; linarith
  rw [Ξ.coeff_add Y contMDiff_const hneg, Ξ.coeff_smul Y hG, Ξ.coeff_const Y] at h1
  rw [Ξ.coeff_add Y contMDiff_const hG, Ξ.coeff_const Y] at h2
  exact abs_le.2 ⟨by linarith, by linarith⟩

end ResolvedData

end SmoothEngine

end Grammar
