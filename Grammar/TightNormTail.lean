/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Tight laws have uniform norm tails

If the laws of random elements `Y n` of a normed group form a tight set, then for every `ε > 0`
there is a radius `B` with `P {‖Y n‖ > B} ≤ ε` for every `n` (compact sets are bounded). This is
the `O_p(1)` bound on the jets that the uniform remainder estimate of the empirical expansion is
localised with (consult #152, deliverable 3).
-/

open MeasureTheory Set
open scoped ENNReal

namespace Grammar

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [OpensMeasurableSpace E]
  {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Tight laws have uniform norm tails.** -/
theorem exists_norm_tail_bound_of_isTightMeasureSet {Y : ℕ → Ω → E} (hYm : ∀ n, Measurable (Y n))
    (ht : IsTightMeasureSet (Set.range fun n => P.map (Y n))) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n, P {ω | B < ‖Y n ω‖} ≤ ε := by
  obtain ⟨K, hKc, hK⟩ := (isTightMeasureSet_iff_exists_isCompact_measure_compl_le.1 ht) ε hε
  obtain ⟨B₀, hB₀⟩ := Bornology.IsBounded.exists_norm_le hKc.isBounded
  refine ⟨max B₀ 0, le_max_right _ _, fun n => ?_⟩
  have hsub : {ω | max B₀ 0 < ‖Y n ω‖} ⊆ Y n ⁻¹' Kᶜ := by
    intro ω hω hK'
    have h1 : ‖Y n ω‖ ≤ B₀ := hB₀ _ hK'
    have h2 : max B₀ 0 < ‖Y n ω‖ := hω
    linarith [le_max_left B₀ 0]
  calc P {ω | max B₀ 0 < ‖Y n ω‖} ≤ P (Y n ⁻¹' Kᶜ) := measure_mono hsub
    _ = P.map (Y n) Kᶜ := (Measure.map_apply (hYm n) hKc.isClosed.measurableSet.compl).symm
    _ ≤ ε := hK _ ⟨n, rfl⟩

end Grammar
