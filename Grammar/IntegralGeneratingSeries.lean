/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Expectation of a generating series under an integrable envelope (§20, moments)

If `c ω = Σ_r g r ω` almost surely and the absolute series `Σ_r |g r ω|` has an integrable
envelope, then `c` is integrable and `∫ c = Σ_r ∫ g r` (`integral_eq_tsum_integral_of_hasSum`).
This is the interface for the Wick-type formula
`E C_{μ,q}[G, φ] = Σ_r (1/r!) E C^pop_{μ+r/2,q}[φ G^r]`
(consult #158, item 6); the envelope is a genuine hypothesis — the limit coefficient need not be
integrable.

Zero `sorry`/`axiom`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Grammar

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

set_option maxHeartbeats 1000000 in
-- the `tsum`/`lintegral` conversions make the elaborator unfold `‖·‖ₑ` at whnf
/-- ★ **Expectation of a generating series under an integrable envelope.** -/
theorem integral_eq_tsum_integral_of_hasSum {g : ℕ → Ω → ℝ} {c : Ω → ℝ}
    (hg : ∀ r, AEStronglyMeasurable (g r) P) (hc : AEStronglyMeasurable c P)
    (hsum : ∀ᵐ ω ∂P, HasSum (fun r => g r ω) (c ω))
    (habs : ∀ᵐ ω ∂P, Summable fun r => |g r ω|)
    (henv : Integrable (fun ω => ∑' r, |g r ω|) P) :
    Integrable c P ∧ ∫ ω, c ω ∂P = ∑' r, ∫ ω, g r ω ∂P := by
  have hce : c =ᵐ[P] fun ω => ∑' r, g r ω := by
    filter_upwards [hsum] with ω hω
    exact hω.tsum_eq.symm
  have hbound : ∀ᵐ ω ∂P, ‖c ω‖ ≤ ∑' r, |g r ω| := by
    filter_upwards [hsum, habs] with ω hω hs
    rw [← hω.tsum_eq]
    have hs' : Summable fun r => ‖g r ω‖ := by simpa only [Real.norm_eq_abs] using hs
    have := norm_tsum_le_tsum_norm hs'
    simpa only [Real.norm_eq_abs] using this
  have hint : Integrable c P := henv.mono' hc hbound
  refine ⟨hint, ?_⟩
  rw [integral_congr_ae hce]
  refine integral_tsum hg ?_
  rw [← lintegral_tsum fun r => (hg r).aemeasurable.enorm]
  have hpt : ∀ᵐ ω ∂P, ∑' r, ‖g r ω‖ₑ = ENNReal.ofReal (∑' r, |g r ω|) := by
    filter_upwards [habs] with ω hs
    rw [ENNReal.ofReal_tsum_of_nonneg (fun r => abs_nonneg _) hs]
    refine tsum_congr fun r => ?_
    rw [← ofReal_norm, Real.norm_eq_abs]
  rw [lintegral_congr_ae hpt]
  have hfe : (fun ω => ENNReal.ofReal (∑' r, |g r ω|)) = fun ω => ‖∑' r, |g r ω|‖ₑ := by
    funext ω
    rw [← ofReal_norm, Real.norm_of_nonneg (tsum_nonneg fun r => abs_nonneg _)]
  rw [hfe]
  exact henv.hasFiniteIntegral.ne

end Grammar
