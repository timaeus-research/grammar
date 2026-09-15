/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Analysis.Normed.Group.Basic

/-!
# Uniform asymptotics on compact families

An abstract ε-net lemma: if `T N f → Tlim f` for every `f` in a compact set `C` of a pseudo-metric
space, and the maps `T N` are eventually uniformly Lipschitz on `C` (constant `L` independent of
`N`), then the convergence is uniform on `C` (`tendstoUniformlyOn_of_eventually_lipschitz`).
The limit inherits the Lipschitz bound (`abs_limit_sub_le_of_eventually_lipschitz`), so no
separate regularity of `Tlim` is assumed. Zero `sorry`/`axiom`.
-/

open Filter Topology

namespace Grammar

variable {E : Type*} [PseudoMetricSpace E] {T : ℝ → E → ℝ} {Tlim : E → ℝ} {C : Set E} {L : ℝ}

/-- The pointwise limit of eventually `L`-Lipschitz maps is `L`-Lipschitz. -/
theorem abs_limit_sub_le_of_eventually_lipschitz
    (hpt : ∀ f ∈ C, Tendsto (fun N => T N f) atTop (𝓝 (Tlim f)))
    (hlip : ∀ᶠ N in atTop, ∀ f ∈ C, ∀ g ∈ C, |T N f - T N g| ≤ L * dist f g)
    {f g : E} (hf : f ∈ C) (hg : g ∈ C) : |Tlim f - Tlim g| ≤ L * dist f g := by
  have h : Tendsto (fun N => |T N f - T N g|) atTop (𝓝 |Tlim f - Tlim g|) :=
    ((hpt f hf).sub (hpt g hg)).abs
  exact le_of_tendsto h (hlip.mono fun N hN => hN f hf g hg)

/-- ★★ **Uniform asymptotics on compact families**: pointwise convergence on a compact set `C`
together with an eventual uniform Lipschitz bound on `C` gives uniform convergence on `C`. -/
theorem tendstoUniformlyOn_of_eventually_lipschitz (hC : IsCompact C)
    (hpt : ∀ f ∈ C, Tendsto (fun N => T N f) atTop (𝓝 (Tlim f)))
    (hlip : ∀ᶠ N in atTop, ∀ f ∈ C, ∀ g ∈ C, |T N f - T N g| ≤ L * dist f g) :
    TendstoUniformlyOn T Tlim atTop C := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  set L' := max L 0 with hL'
  have hL'0 : 0 ≤ L' := le_max_right _ _
  have hLL' : L ≤ L' := le_max_left _ _
  set r := ε / (3 * (L' + 1)) with hr
  have hr0 : 0 < r := by positivity
  have hLr : L' * r < ε / 3 := by
    have h1 : L' * r = ε / 3 * (L' / (L' + 1)) := by
      rw [hr]; field_simp
    have h2 : L' / (L' + 1) < 1 := (div_lt_one (by positivity)).2 (by linarith)
    rw [h1]
    exact mul_lt_of_lt_one_right (by positivity) h2
  obtain ⟨t, htC, hcover⟩ := hC.elim_nhds_subcover (fun x => Metric.ball x r)
    fun x _ => Metric.ball_mem_nhds x hr0
  have hcen : ∀ᶠ N in atTop, ∀ x ∈ t, dist (T N x) (Tlim x) < ε / 3 :=
    (eventually_all_finset t).2 fun x hx =>
      Metric.tendsto_nhds.1 (hpt x (htC x hx)) (ε / 3) (by positivity)
  filter_upwards [hlip, hcen] with N hN hNc
  intro f hf
  obtain ⟨x, hxt, hfx⟩ : ∃ x ∈ t, f ∈ Metric.ball x r := by
    simpa using hcover hf
  have hxC : x ∈ C := htC x hxt
  have hdist : dist f x < r := Metric.mem_ball.1 hfx
  have hlim := abs_limit_sub_le_of_eventually_lipschitz hpt hlip hf hxC
  have hNfx := hN f hf x hxC
  have hd0 : 0 ≤ dist f x := dist_nonneg
  have hb1 : |Tlim f - Tlim x| ≤ L' * r :=
    hlim.trans (mul_le_mul hLL' hdist.le hd0 hL'0)
  have hb2 : |T N f - T N x| ≤ L' * r :=
    hNfx.trans (mul_le_mul hLL' hdist.le hd0 hL'0)
  have hb3 : |T N x - Tlim x| < ε / 3 := by
    rw [← Real.dist_eq]; exact hNc x hxt
  rw [Real.dist_eq]
  calc |Tlim f - T N f|
      = |(Tlim f - Tlim x) + (Tlim x - T N x) + (T N x - T N f)| := by ring_nf
    _ ≤ |Tlim f - Tlim x| + |Tlim x - T N x| + |T N x - T N f| :=
        (abs_add_three _ _ _)
    _ < ε / 3 + ε / 3 + ε / 3 := by
        have hb2' : |T N x - T N f| ≤ L' * r := by rwa [abs_sub_comm]
        have hb3' : |Tlim x - T N x| < ε / 3 := by rwa [abs_sub_comm]
        linarith
    _ = ε := by ring

end Grammar
