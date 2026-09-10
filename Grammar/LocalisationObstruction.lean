/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.ResolutionTransport
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# The localisation obstruction: chart-exact analytic amplitudes cannot absorb a sublevel cutoff

`ChartPresentation.amplitude_eq` asks the chart amplitude `c · obs ∘ Φ` to be a convergent power
series in the normal variable on the whole box `(0, b]^{n+1}`, while `transport` restricts the
target measure to the sublevel set `{K < δ}`.  If the box crosses the sublevel boundary, the
nonnegative source density vanishes a.e. above it, and analyticity propagates the vanishing across
the connected normal interval: **a nontrivial chart-exact analytic amplitude cannot absorb an
exact sublevel cutoff** (`eqOn_zero_of_ae_zero_Ioo`).  In one normal variable with exact phase
`β u^{2k}` the threshold is `t = (δ/β)^{1/(2k)}`; the same argument applies to an open upper corner
in several normal variables.

This records why the resolution input (a finite chart cover with measurable weights,
`ResolutionTransport.lean`) does not by itself produce an `AdaptedStrataData`: a compatible
localisation — cutoffs depending on the tangential variable only, or an analytic-core
decomposition modulo an exponentially small remainder — is a separate geometric input.
-/

open MeasureTheory Filter Topology Set

namespace Grammar

/-- **Analytic amplitudes cannot vanish on a terminal interval without vanishing identically**: a
function real-analytic on `(0, b)` and a.e. zero on `(t, b)` for some `0 < t < b` is zero on all of
`(0, b)`. -/
theorem eqOn_zero_of_ae_zero_Ioo {A : ℝ → ℝ} {b t : ℝ} (ht : t ∈ Ioo (0 : ℝ) b)
    (hA : AnalyticOnNhd ℝ A (Ioo 0 b)) (hzero : ∀ᵐ x ∂volume.restrict (Ioo t b), A x = 0) :
    EqOn A 0 (Ioo 0 b) := by
  have hsub : Ioo t b ⊆ Ioo 0 b := Ioo_subset_Ioo ht.1.le le_rfl
  have hcont : ContinuousOn A (Ioo t b) := (hA.continuousOn).mono hsub
  have hpt : EqOn A 0 (Ioo t b) :=
    Measure.eqOn_of_ae_eq hzero hcont continuousOn_const
      (by rw [isOpen_Ioo.interior_eq]; exact subset_closure)
  have hmid : (t + b) / 2 ∈ Ioo t b := ⟨by linarith [ht.2], by linarith [ht.2]⟩
  refine hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_Ioo (hsub hmid) ?_
  filter_upwards [Ioo_mem_nhds hmid.1 hmid.2] with x hx
  exact hpt hx

/-- The one-variable threshold: the exact phase `β u^{2k}` reaches the level `δ` at
`u = (δ/β)^{1/(2k)}`, which lies inside `(0, b)` when `β b^{2k} > δ`. -/
theorem threshold_mem_Ioo {β δ b : ℝ} {k : ℕ} (hβ : 0 < β) (hδ : 0 < δ) (hb : 0 < b) (hk : 0 < k)
    (hbox : δ < β * b ^ (2 * k)) : (δ / β) ^ (1 / (2 * (k : ℝ))) ∈ Ioo (0 : ℝ) b := by
  have hq : 0 < δ / β := div_pos hδ hβ
  have h2k : (0 : ℝ) < 2 * (k : ℝ) := by positivity
  refine ⟨Real.rpow_pos_of_pos hq _, ?_⟩
  have hlt : δ / β < b ^ (2 * (k : ℝ)) := by
    rw [div_lt_iff₀ hβ, mul_comm]
    have : (b : ℝ) ^ (2 * (k : ℝ)) = b ^ (2 * k) := by
      rw [show (2 * (k : ℝ)) = ((2 * k : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    rw [this]; exact hbox
  calc (δ / β) ^ (1 / (2 * (k : ℝ))) < (b ^ (2 * (k : ℝ))) ^ (1 / (2 * (k : ℝ))) :=
        Real.rpow_lt_rpow hq.le hlt (by positivity)
    _ = b := by
        rw [← Real.rpow_mul hb.le, mul_one_div_cancel h2k.ne', Real.rpow_one]

end Grammar
