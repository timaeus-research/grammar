/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.IntegralGeneratingSeries

/-!
# The annealed generating series: Tonelli packaging and Wick weights (§20, moments)

* `integral_eq_tsum_integral_of_summable_integral_abs`: if `c = Σ_r g_r` a.s., every `g_r` is
  integrable and `Σ_r ∫|g_r| < ∞`, then `c` is integrable and `∫ c = Σ_r ∫ g_r` (Tonelli produces
  the a.s. absolute summability and the integrable envelope of `IntegralGeneratingSeries`).
* `summable_integral_of_summable_integral_abs`: the series of expectations converges absolutely.
* `integral_eq_tsum_wickWeights`: with `g_r = T_r/r!`, vanishing odd expectations and
  `∫ T_{2j} = (2j)!/(2^j j!) · w_j`, the expectation is `Σ_j w_j/(2^j j!)`.

Applied to `g_r(ω) = (1/r!) C^pop_{μ+r/2,q}[η Y_ω^r]` (`hasSum_empCoeffRect_population`) this is
the annealed generating identity `E C_{μ,q}[Y,η] = Σ_r (1/r!) E C^pop_{μ+r/2,q}[η Y^r]` and, for a
centred Gaussian field with `E[T_{2j}] = (2j)!/(2^j j!) C^pop_{μ+j,q}[η W^j]` (`W = Var Y`), the
Wick form `E C_{μ,q}[Y,η] = Σ_j (1/(2^j j!)) C^pop_{μ+j,q}[η W^j]` (consult #159, A1–A2).  The
absolute-moment hypothesis is genuine (the Gaussian threshold); the Gaussian evaluation of the
even moments is not proved here.

Zero `sorry`/`axiom`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace Grammar

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The series of expectations converges absolutely. -/
theorem summable_integral_of_summable_integral_abs {g : ℕ → Ω → ℝ}
    (habs : Summable fun r => ∫ ω, |g r ω| ∂P) : Summable fun r => ∫ ω, g r ω ∂P := by
  have habs' : Summable fun r => ∫ ω, ‖g r ω‖ ∂P := by
    simpa only [Real.norm_eq_abs] using habs
  exact Summable.of_norm_bounded habs' fun r => norm_integral_le_integral_norm _

/-- ★ **Expectation of a generating series with summable absolute moments** (Tonelli). -/
theorem integral_eq_tsum_integral_of_summable_integral_abs {g : ℕ → Ω → ℝ} {c : Ω → ℝ}
    (hc : AEStronglyMeasurable c P) (hg : ∀ r, Integrable (g r) P)
    (hsum : ∀ᵐ ω ∂P, HasSum (fun r => g r ω) (c ω))
    (habs : Summable fun r => ∫ ω, |g r ω| ∂P) :
    Integrable c P ∧ ∫ ω, c ω ∂P = ∑' r, ∫ ω, g r ω ∂P := by
  have habs' : Summable fun r => ∫ ω, ‖g r ω‖ ∂P := by
    simpa only [Real.norm_eq_abs] using habs
  set F : Ω → ℝ≥0∞ := fun ω => ∑' r, ENNReal.ofReal ‖g r ω‖ with hF
  have hFmeas : AEMeasurable F P :=
    AEMeasurable.tsum fun r => (hg r).norm.1.aemeasurable.ennreal_ofReal
  have hlint : ∫⁻ ω, F ω ∂P = ∑' r, ENNReal.ofReal (∫ ω, ‖g r ω‖ ∂P) := by
    simp only [hF]
    rw [lintegral_tsum fun r => (hg r).norm.1.aemeasurable.ennreal_ofReal]
    congr 1
    funext r
    exact (ofReal_integral_eq_lintegral_ofReal (hg r).norm
      (Eventually.of_forall fun ω => norm_nonneg _)).symm
  have hfin : ∫⁻ ω, F ω ∂P ≠ ∞ := by
    rw [hlint, ← ENNReal.ofReal_tsum_of_nonneg (fun r => integral_nonneg fun ω => norm_nonneg _)
      habs']
    exact ENNReal.ofReal_ne_top
  have hae : ∀ᵐ ω ∂P, F ω < ∞ := ae_lt_top' hFmeas hfin
  have hsumm : ∀ᵐ ω ∂P, Summable fun r => |g r ω| := by
    filter_upwards [hae] with ω hω
    have h1 : ∑' r, ENNReal.ofReal ‖g r ω‖ ≠ ∞ := by simpa only [hF] using hω.ne
    refine (ENNReal.summable_toReal h1).congr fun r => ?_
    rw [ENNReal.toReal_ofReal (norm_nonneg _), Real.norm_eq_abs]
  have henv : Integrable (fun ω => ∑' r, |g r ω|) P := by
    have hint : Integrable (fun ω => (F ω).toReal) P :=
      ⟨hFmeas.ennreal_toReal.aestronglyMeasurable,
        hasFiniteIntegral_toReal_of_lintegral_ne_top hfin⟩
    refine hint.congr (Eventually.of_forall fun ω => ?_)
    simp only [hF]
    rw [ENNReal.tsum_toReal_eq fun r => ENNReal.ofReal_ne_top]
    exact tsum_congr fun r => by rw [ENNReal.toReal_ofReal (norm_nonneg _), Real.norm_eq_abs]
  exact integral_eq_tsum_integral_of_hasSum (fun r => (hg r).1) hc hsum hsumm henv

/-- Even/odd split of an absolutely convergent series of expectations with vanishing odd terms. -/
theorem tsum_eq_tsum_even_of_odd_eq_zero {f : ℕ → ℝ} (hsum : Summable f)
    (hodd : ∀ j, f (2 * j + 1) = 0) : ∑' r, f r = ∑' j, f (2 * j) := by
  have he : Summable fun j => f (2 * j) :=
    hsum.comp_injective (mul_right_injective₀ two_ne_zero)
  have ho : Summable fun j => f (2 * j + 1) := hsum.comp_injective fun a b h => by omega
  rw [← tsum_even_add_odd he ho]
  simp only [hodd, tsum_zero, add_zero]

/-- ★★ **The annealed generating series with Wick weights**: `g_r = T_r/r!`, odd expectations
vanish, `∫ T_{2j} = (2j)!/(2^j j!) · w_j` ⇒ `∫ c = Σ_j w_j/(2^j j!)`, with the Wick series
absolutely convergent. -/
theorem integral_eq_tsum_wickWeights {g T : ℕ → Ω → ℝ} {c : Ω → ℝ} {w : ℕ → ℝ}
    (hgT : ∀ r ω, g r ω = (1 / (r.factorial : ℝ)) * T r ω)
    (hc : AEStronglyMeasurable c P) (hg : ∀ r, Integrable (g r) P)
    (hsum : ∀ᵐ ω ∂P, HasSum (fun r => g r ω) (c ω))
    (habs : Summable fun r => ∫ ω, |g r ω| ∂P)
    (hodd : ∀ j, ∫ ω, T (2 * j + 1) ω ∂P = 0)
    (heven : ∀ j, ∫ ω, T (2 * j) ω ∂P =
      (((2 * j).factorial : ℝ) / (2 ^ j * (j.factorial : ℝ))) * w j) :
    Integrable c P ∧ Summable (fun j => (1 / (2 ^ j * (j.factorial : ℝ))) * w j) ∧
      ∫ ω, c ω ∂P = ∑' j, (1 / (2 ^ j * (j.factorial : ℝ))) * w j := by
  obtain ⟨hcint, hceq⟩ := integral_eq_tsum_integral_of_summable_integral_abs hc hg hsum habs
  have hgr : ∀ r, ∫ ω, g r ω ∂P = (1 / (r.factorial : ℝ)) * ∫ ω, T r ω ∂P := fun r => by
    simp only [hgT, integral_const_mul]
  have hodd' : ∀ j, ∫ ω, g (2 * j + 1) ω ∂P = 0 := fun j => by rw [hgr, hodd, mul_zero]
  have heven' : ∀ j, ∫ ω, g (2 * j) ω ∂P = (1 / (2 ^ j * (j.factorial : ℝ))) * w j := fun j => by
    rw [hgr, heven]
    have h2j : ((2 * j).factorial : ℝ) ≠ 0 := by exact_mod_cast (2 * j).factorial_ne_zero
    field_simp
  have hS := summable_integral_of_summable_integral_abs habs
  have he : Summable fun j => ∫ ω, g (2 * j) ω ∂P :=
    hS.comp_injective (mul_right_injective₀ two_ne_zero)
  refine ⟨hcint, ?_, ?_⟩
  · exact he.congr heven'
  · rw [hceq, tsum_eq_tsum_even_of_odd_eq_zero hS hodd']
    exact tsum_congr heven'

end Grammar
