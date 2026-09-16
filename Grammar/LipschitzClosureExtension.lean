/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Continuous extension to the closure from Lipschitz control on bounded parts

A real function `φ` on a subset `S` of a normed group which is Lipschitz on every bounded part of
`S` (at distances `≤ 1`) extends uniquely and continuously to the closure of `S`: the extension is
the limit of `φ` along `S`, which exists by completeness (`closureExtend`), agrees with `φ` on `S`,
and is continuous on `closure S`.

This is the geometry-free core of the closed-realizable-jet extension of the resolved coefficient
(`EmpiricalClosedJets`); it is instantiated again for the jets on a single cube.
-/

open Filter Topology Metric Set

namespace Grammar

variable {X : Type*} [NormedAddCommGroup X] {S : Set X} {φ : X → ℝ}

/-- `φ` is Lipschitz on every bounded part of `S`, at distances `≤ 1`. -/
def LipschitzOnBounded (S : Set X) (φ : X → ℝ) : Prop :=
  ∀ B : ℝ, 0 ≤ B → ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ S, ∀ y ∈ S, ‖y‖ ≤ B → dist x y ≤ 1 →
    |φ x - φ y| ≤ K * dist x y

theorem LipschitzOnBounded.tendsto_nhdsWithin_of_mem (h : LipschitzOnBounded S φ) {x : X}
    (hx : x ∈ S) : Tendsto φ (𝓝[S] x) (𝓝 (φ x)) := by
  obtain ⟨K, hK0, hK⟩ := h (‖x‖ + 1) (by positivity)
  refine Metric.tendsto_nhdsWithin_nhds.2 fun ε hε => ?_
  refine ⟨min 1 (ε / (K + 1)), lt_min one_pos (div_pos hε (by linarith)), fun y hy hyx => ?_⟩
  have h1 : dist y x < 1 := lt_of_lt_of_le hyx (min_le_left _ _)
  have h2 : dist y x < ε / (K + 1) := lt_of_lt_of_le hyx (min_le_right _ _)
  have hxB : ‖x‖ ≤ ‖x‖ + 1 := by linarith
  rw [Real.dist_eq]
  calc |φ y - φ x| ≤ K * dist y x := hK y hy x hx hxB h1.le
    _ ≤ (K + 1) * dist y x := mul_le_mul_of_nonneg_right (by linarith) dist_nonneg
    _ < (K + 1) * (ε / (K + 1)) := mul_lt_mul_of_pos_left h2 (by linarith)
    _ = ε := by field_simp

theorem LipschitzOnBounded.exists_tendsto (h : LipschitzOnBounded S φ) {z : X}
    (hz : z ∈ closure S) : ∃ l, Tendsto φ (𝓝[S] z) (𝓝 l) := by
  have hne : (𝓝[S] z).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hz
  obtain ⟨K, hK0, hK⟩ := h (‖z‖ + 1) (by positivity)
  have hcauchy : Cauchy (map φ (𝓝[S] z)) := by
    refine Metric.cauchy_iff.2 ⟨map_neBot, fun ε hε => ?_⟩
    set δ : ℝ := min (1 / 2) (ε / (2 * (K + 1))) with hδ
    have hδ0 : 0 < δ := lt_min (by norm_num) (div_pos hε (by positivity))
    have hδ1 : δ ≤ 1 / 2 := min_le_left _ _
    have hδ2 : δ ≤ ε / (2 * (K + 1)) := min_le_right _ _
    refine ⟨φ '' (S ∩ ball z δ), image_mem_map (inter_mem_nhdsWithin S (ball_mem_nhds z hδ0)), ?_⟩
    rintro _ ⟨x, ⟨hxS, hxb⟩, rfl⟩ _ ⟨y, ⟨hyS, hyb⟩, rfl⟩
    have hxb' : dist x z < δ := hxb
    have hyb' : dist y z < δ := hyb
    have hy : ‖y‖ ≤ ‖z‖ + 1 := by
      have : ‖y‖ ≤ ‖z‖ + ‖y - z‖ := by
        calc ‖y‖ = ‖z + (y - z)‖ := by rw [add_sub_cancel]
          _ ≤ ‖z‖ + ‖y - z‖ := norm_add_le _ _
      rw [← dist_eq_norm] at this
      linarith
    have hxy : dist x y ≤ 1 := by
      have := dist_triangle_right x y z
      linarith
    have hxy2 : dist x y < 2 * δ := by
      have := dist_triangle_right x y z
      linarith
    rw [Real.dist_eq]
    calc |φ x - φ y| ≤ K * dist x y := hK x hxS y hyS hy hxy
      _ ≤ (K + 1) * dist x y := mul_le_mul_of_nonneg_right (by linarith) dist_nonneg
      _ < (K + 1) * (2 * δ) := mul_lt_mul_of_pos_left hxy2 (by linarith)
      _ ≤ (K + 1) * (2 * (ε / (2 * (K + 1)))) := by gcongr
      _ = ε := by field_simp
  exact CompleteSpace.complete hcauchy

/-- The extension of `φ` to the closure of `S`: the limit of `φ` along `S`. -/
noncomputable def closureExtend (S : Set X) (φ : X → ℝ) (z : closure S) : ℝ :=
  limUnder (𝓝[S] z.1) φ

theorem LipschitzOnBounded.tendsto_closureExtend (h : LipschitzOnBounded S φ) (z : closure S) :
    Tendsto φ (𝓝[S] z.1) (𝓝 (closureExtend S φ z)) :=
  tendsto_nhds_limUnder (h.exists_tendsto z.2)

theorem LipschitzOnBounded.closureExtend_of_mem (h : LipschitzOnBounded S φ) {x : X} (hx : x ∈ S) :
    closureExtend S φ ⟨x, subset_closure hx⟩ = φ x := by
  have hne : (𝓝[S] x).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (subset_closure hx)
  exact tendsto_nhds_unique (h.tendsto_closureExtend ⟨x, subset_closure hx⟩)
    (h.tendsto_nhdsWithin_of_mem hx)

/-- **The extension is continuous on the closure.** -/
theorem LipschitzOnBounded.continuous_closureExtend (h : LipschitzOnBounded S φ) :
    Continuous (closureExtend S φ) := by
  refine Metric.continuous_iff.2 fun z₀ ε hε => ?_
  obtain ⟨K, hK0, hK⟩ := h (‖z₀.1‖ + 2) (by positivity)
  set δ : ℝ := min (1 / 4) (ε / (8 * (K + 1))) with hδ
  have hδ0 : 0 < δ := lt_min (by norm_num) (div_pos hε (by positivity))
  have hδ1 : δ ≤ 1 / 4 := min_le_left _ _
  have hδ2 : δ ≤ ε / (8 * (K + 1)) := min_le_right _ _
  refine ⟨δ, hδ0, fun z hz => ?_⟩
  have hzz : dist z.1 z₀.1 < δ := hz
  have happrox : ∀ w : closure S, ∃ x ∈ S, dist x w.1 < δ ∧
      dist (φ x) (closureExtend S φ w) < ε / 4 := by
    intro w
    have hne : (𝓝[S] w.1).NeBot := mem_closure_iff_nhdsWithin_neBot.1 w.2
    have h1 : ∀ᶠ x in 𝓝[S] w.1, x ∈ S := self_mem_nhdsWithin
    have h2 : ∀ᶠ x in 𝓝[S] w.1, dist x w.1 < δ :=
      eventually_nhdsWithin_of_eventually_nhds (ball_mem_nhds w.1 hδ0)
    have h3 : ∀ᶠ x in 𝓝[S] w.1, dist (φ x) (closureExtend S φ w) < ε / 4 :=
      Metric.tendsto_nhds.1 (h.tendsto_closureExtend w) _ (by positivity)
    obtain ⟨x, hx1, hx2, hx3⟩ := (h1.and (h2.and h3)).exists
    exact ⟨x, hx1, hx2, hx3⟩
  obtain ⟨x, hxS, hxz, hxf⟩ := happrox z
  obtain ⟨x₀, hx₀S, hx₀z, hx₀f⟩ := happrox z₀
  have hx₀B : ‖x₀‖ ≤ ‖z₀.1‖ + 2 := by
    have : ‖x₀‖ ≤ ‖z₀.1‖ + ‖x₀ - z₀.1‖ := by
      calc ‖x₀‖ = ‖z₀.1 + (x₀ - z₀.1)‖ := by rw [add_sub_cancel]
        _ ≤ ‖z₀.1‖ + ‖x₀ - z₀.1‖ := norm_add_le _ _
    rw [← dist_eq_norm] at this
    linarith
  have hxx₀ : dist x x₀ < 3 * δ := by
    have h1 := dist_triangle x z.1 x₀
    have h2 := dist_triangle z.1 z₀.1 x₀
    rw [dist_comm z₀.1 x₀] at h2
    linarith
  have hxx₀1 : dist x x₀ ≤ 1 := by linarith
  have hmid : |φ x - φ x₀| ≤ 3 * ε / 8 := by
    calc |φ x - φ x₀| ≤ K * dist x x₀ := hK x hxS x₀ hx₀S hx₀B hxx₀1
      _ ≤ (K + 1) * dist x x₀ := mul_le_mul_of_nonneg_right (by linarith) dist_nonneg
      _ ≤ (K + 1) * (3 * δ) := mul_le_mul_of_nonneg_left hxx₀.le (by linarith)
      _ ≤ (K + 1) * (3 * (ε / (8 * (K + 1)))) := by gcongr
      _ = 3 * ε / 8 := by field_simp
  rw [Real.dist_eq] at hxf hx₀f ⊢
  calc |closureExtend S φ z - closureExtend S φ z₀|
      = |(closureExtend S φ z - φ x) + (φ x - φ x₀) + (φ x₀ - closureExtend S φ z₀)| := by ring_nf
    _ ≤ |closureExtend S φ z - φ x| + |φ x - φ x₀| + |φ x₀ - closureExtend S φ z₀| :=
        abs_add_three _ _ _
    _ < ε / 4 + 3 * ε / 8 + ε / 4 := by
        rw [abs_sub_comm (closureExtend S φ z)]
        linarith
    _ ≤ ε := by linarith

end Grammar
