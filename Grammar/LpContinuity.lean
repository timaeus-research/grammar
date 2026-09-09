/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.StochasticData

/-!
# Continuity into weighted ℓ¹ from coordinatewise continuity and a summable majorant
(Programme Q, N3, unit 309)

The tangential-data interface of Programme S represents a chart datum as an element of the ℓ¹ data
space, and a tangential family as a *continuous* map `K → DataSpace d`. Coefficientwise continuity
does not give ℓ¹ continuity; a common summable majorant does:
```
(∀ i, Continuous (fun x => F x i))  ∧  (∀ x i, |F x i| ≤ B i)  ∧  Summable B   ⇒   Continuous F
```
(`continuous_dataSpace_of_majorant`). Proof: `‖F x − F x₀‖ = ∑ᵢ |F x i − F x₀ i|`; split at a finite
set `s` whose complementary tail of `B` is small (`tendsto_tsum_compl_atTop_zero`); the head is a
finite sum of continuous functions vanishing at `x₀`, the tail is bounded by `2 ∑_{i∉s} B i`. This
is
the generic criterion Astra #38/review v37 asked for; the analytic-family application (Cauchy
coefficients with the geometric majorant `M (b/r)^{|γ|}`) follows in the next units.
Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

/-- **ℓ¹ continuity from a summable majorant**: coordinatewise continuous, uniformly dominated by a
summable `B`, hence continuous into the data space. -/
theorem continuous_dataSpace_of_majorant {X : Type*} [TopologicalSpace X] {d : ℕ}
    (F : X → DataSpace d) (hcoord : ∀ i, Continuous fun x => F x i) (B : DataIdx d → ℝ)
    (hB : Summable B) (hbound : ∀ x i, |F x i| ≤ B i) : Continuous F := by
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  -- a finite set outside which the majorant's tail is small
  have htail := tendsto_tsum_compl_atTop_zero B
  obtain ⟨s, hs⟩ := (htail.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 4))).exists
  -- the head tends to zero
  have hhead : Tendsto (fun x => ∑ i ∈ s, |F x i - F x₀ i|) (𝓝 x₀) (𝓝 0) := by
    have : Tendsto (fun x => ∑ i ∈ s, |F x i - F x₀ i|) (𝓝 x₀)
        (𝓝 (∑ i ∈ s, |F x₀ i - F x₀ i|)) :=
      tendsto_finsetSum _ fun i _ => (((hcoord i).tendsto x₀).sub_const _).abs
    simpa using this
  filter_upwards [hhead.eventually (gt_mem_nhds (half_pos hε))] with x hx
  rw [dist_eq_norm, dataNorm_eq_tsum_abs]
  have hsum : Summable fun i => |(F x - F x₀) i| := summable_abs_coord _
  have hcoe : ∀ i, (F x - F x₀) i = F x i - F x₀ i := fun i => by
    rw [lp.coeFn_sub, Pi.sub_apply]
  simp only [hcoe] at hsum ⊢
  rw [← hsum.sum_add_tsum_compl (s := s)]
  have hle : ∀ i, |F x i - F x₀ i| ≤ 2 * B i := fun i =>
    (abs_sub _ _).trans (by linarith [hbound x i, hbound x₀ i])
  have htail_le : ∑' i : ↑(↑s : Set (DataIdx d))ᶜ, |F x i - F x₀ i| ≤
      ∑' i : ↑(↑s : Set (DataIdx d))ᶜ, 2 * B i :=
    Summable.tsum_le_tsum (fun i => hle i) (hsum.subtype _) ((hB.mul_left 2).subtype _)
  rw [tsum_mul_left] at htail_le
  have hs' : ∑' i : ↑(↑s : Set (DataIdx d))ᶜ, B i < ε / 4 := hs
  linarith

end Grammar
