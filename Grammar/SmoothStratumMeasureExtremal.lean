/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothStratumMeasure
import Grammar.SmoothResolvedStratumExtremal
import Grammar.SmoothResolvedRLCTAsymptotic

/-!
# The extremal stratum measure and the leading asymptotic

At extremal data `(λ*, m*)` the zero-order condition holds on every stratum
(`zeroOrder_of_extremalData`), so the stratum measure `ν^{λ*}_{m*}` on `U ∖ D_{m*+1}` is defined
(`extremalStratumMeasure`). For an observable `F` vanishing near the deep zero fibre `D_{m*+1}`
the normalised partition function `N^{λ*} (log N)^{−(m*−1)} Z^U_N[F]` converges to `∫ F dν`
(`tendsto_normalised_Z_extremal`); for a base observable `f` with `f ∘ π ∈ 𝓘_{m*+1}` this reads
`N^{λ*} (log N)^{−(m*−1)} ∫ prior · f · e^{−NK} → ∫ f ∘ π dν`
(`tendsto_normalised_partitionObs_extremal`), and when the limit is nonzero
`∫ prior · f · e^{−NK} ∼ (∫ f ∘ π dν) N^{−λ*} (log N)^{m*−1}`
(`partitionObs_isEquivalent_extremal`). Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology Asymptotics
open scoped ENNReal ContDiff Manifold
open Monomialize.VolumeScaling Monomialize.Transport Monomialize.Manifold
open Grammar.NormalCrossing

namespace Grammar

namespace SmoothEngine

namespace ResolvedData

variable {d : ℕ} (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)

/-- ★★★ **The extremal stratum measure** `ν^{λ*}_{m*}` on `U ∖ D_{m*+1}`. -/
noncomputable def extremalStratumMeasure {lam : ℝ} {m : ℕ} (h : Ξ.IsExtremalData lam m)
    (hm : 1 ≤ m) : Measure (Ξ.stratumOpen m) :=
  Ξ.stratumMeasure Y hm (Ξ.zeroOrder_of_extremalData h m)

/-- ★★★ **Leading-index characterisation**: for `F ∈ 𝓘_{m*+1}`, the normalised resolved partition
function converges to the integral of `F` against the extremal stratum measure. -/
theorem tendsto_normalised_Z_extremal {lam : ℝ} {m : ℕ} (h : Ξ.IsExtremalData lam m) (hm : 1 ≤ m)
    {G : Ξ.R.U → ℝ} (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G)
    (hG0 : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre m), G P = 0) :
    Tendsto (normalised lam (m - 1) (Ξ.withF G hG).Z) atTop
      (𝓝 (∫ x, G x.1 ∂(Ξ.extremalStratumMeasure Y h hm))) := by
  unfold extremalStratumMeasure
  rw [← Ξ.coeff_withF_eq_integral_stratumMeasure Y hm _ hG hG0]
  exact Ξ.tendsto_normalised_Z_of_extremalData Y h hG

/-- ★★★ **Euclidean leading-index characterisation**: for a base observable `f` with
`f ∘ π ∈ 𝓘_{m*+1}`, `N^{λ*} (log N)^{−(m*−1)} ∫ prior · f · e^{−NK} → ∫ f ∘ π dν^{λ*}_{m*}`. -/
theorem tendsto_normalised_partitionObs_extremal {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f)
    {lam : ℝ} {m : ℕ} (h : Ξ.IsExtremalData lam m) (hm : 1 ≤ m)
    (h0 : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre m), f (Ξ.R.gv P) = 0) :
    Tendsto (normalised lam (m - 1) (partitionObs Ξ.K Ξ.prior f)) atTop
      (𝓝 (∫ x, f (Ξ.R.gv x.1) ∂(Ξ.extremalStratumMeasure Y h hm))) := by
  refine (Ξ.tendsto_normalised_Z_extremal Y h hm (Ξ.contMDiff_comp_gv hf) h0).congr fun N => ?_
  unfold normalised
  rw [Ξ.Z_withF_comp_gv hf N]

/-- ★★★ **The leading asymptotic with insertion**: when `∫ f ∘ π dν^{λ*}_{m*} ≠ 0`,
`∫ prior · f · e^{−NK} ∼ (∫ f ∘ π dν^{λ*}_{m*}) N^{−λ*} (log N)^{m*−1}`. -/
theorem partitionObs_isEquivalent_extremal {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f)
    {lam : ℝ} {m : ℕ} (h : Ξ.IsExtremalData lam m) (hm : 1 ≤ m)
    (h0 : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre m), f (Ξ.R.gv P) = 0)
    (hne : ∫ x, f (Ξ.R.gv x.1) ∂(Ξ.extremalStratumMeasure Y h hm) ≠ 0) :
    (fun N => partitionObs Ξ.K Ξ.prior f N) ~[atTop]
      fun N => (∫ x, f (Ξ.R.gv x.1) ∂(Ξ.extremalStratumMeasure Y h hm)) *
        (N ^ (-lam) * Real.log N ^ (m - 1)) := by
  set I := ∫ x, f (Ξ.R.gv x.1) ∂(Ξ.extremalStratumMeasure Y h hm) with hI
  have hv : ∀ᶠ N : ℝ in atTop, I * (N ^ (-lam) * Real.log N ^ (m - 1)) ≠ 0 := by
    filter_upwards [eventually_gt_atTop 1] with N hN
    exact mul_ne_zero hne (mul_pos (Real.rpow_pos_of_pos (by linarith) _)
      (pow_pos (Real.log_pos hN) _)).ne'
  refine (isEquivalent_iff_tendsto_one hv).2 ?_
  have hlim := (Ξ.tendsto_normalised_partitionObs_extremal Y hf h hm h0).div_const I
  rw [div_self hne] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with N hN
  have hN0 : 0 ≤ N := by linarith
  have hA : (N ^ lam : ℝ) ≠ 0 := (Real.rpow_pos_of_pos (by linarith) _).ne'
  have hL : (Real.log N ^ (m - 1) : ℝ) ≠ 0 := (pow_pos (Real.log_pos hN) _).ne'
  simp only [Pi.div_apply]
  unfold normalised
  rw [Real.rpow_neg hN0]
  field_simp

end ResolvedData

end SmoothEngine

end Grammar
