/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Continuous convergence of a sequence of maps

`ContinuouslyConverges Tn T` says that `Tn q → T p` along the product filter `atTop ×ˢ 𝓝 p`, for
every `p`: for every `ε` there are `n₀` and a neighbourhood `U` of `p` with
`n ≥ n₀, q ∈ U ⇒ d(Tn n q, T p) < ε`.  This is the form of "the posterior law is a continuously
convergent function of the phase" used for the random-field transfer.

Main results.
* `ContinuouslyConverges.tendsto_seq`: along any `κ_j → ∞`, `x_j → p`, `Tn (κ j) (x j) → T p`.
* `continuouslyConverges_of_seq`: the converse on a pseudo-metric domain (the sequential bridge,
  by contradiction: a failure produces `κ_j ≥ j` and `d(x_j, p) < 1/(j+1)` violating a fixed
  output neighbourhood).
* `ContinuouslyConverges.continuous_limit`: the limit `T` is continuous (pseudo-metric codomain).
* `ContinuouslyConverges.tendstoUniformlyOn`: uniform convergence on compact sets, by a finite
  subcover of the neighbourhoods furnished by continuous convergence and continuity of `T`.
-/

open Filter Topology

namespace Grammar

section topological

variable {P V : Type*} [TopologicalSpace P] [TopologicalSpace V]

/-- Continuous convergence of `Tn : ℕ → P → V` to `T : P → V`. -/
def ContinuouslyConverges (Tn : ℕ → P → V) (T : P → V) : Prop :=
  ∀ p : P, Tendsto (fun q : ℕ × P => Tn q.1 q.2) (atTop ×ˢ 𝓝 p) (𝓝 (T p))

namespace ContinuouslyConverges

variable {Tn : ℕ → P → V} {T : P → V}

/-- Along any `κ_j → ∞` and `x_j → p`, `Tn (κ j) (x j) → T p`. -/
theorem tendsto_seq (hcc : ContinuouslyConverges Tn T) {ι : Type*} {F : Filter ι} (κ : ι → ℕ)
    (hκ : Tendsto κ F atTop) (x : ι → P) (p : P) (hx : Tendsto x F (𝓝 p)) :
    Tendsto (fun j => Tn (κ j) (x j)) F (𝓝 (T p)) :=
  (hcc p).comp (hκ.prodMk hx)

/-- Pointwise convergence `Tn n p → T p`. -/
theorem tendsto_pointwise (hcc : ContinuouslyConverges Tn T) (p : P) :
    Tendsto (fun n => Tn n p) atTop (𝓝 (T p)) :=
  hcc.tendsto_seq id tendsto_id (fun _ => p) p tendsto_const_nhds

end ContinuouslyConverges

end topological

section bridge

variable {P V : Type*} [PseudoMetricSpace P] [TopologicalSpace V]

/-- **Sequential bridge.**  On a pseudo-metric domain, arbitrary-index sequential convergence
(`κ_j → ∞`, `x_j → p ⇒ Tn (κ j) (x j) → T p`) implies continuous convergence. -/
theorem continuouslyConverges_of_seq {Tn : ℕ → P → V} {T : P → V}
    (hseq : ∀ (p : P) (κ : ℕ → ℕ) (x : ℕ → P), Tendsto κ atTop atTop → Tendsto x atTop (𝓝 p) →
      Tendsto (fun j => Tn (κ j) (x j)) atTop (𝓝 (T p))) :
    ContinuouslyConverges Tn T := by
  intro p
  rw [tendsto_def]
  intro s hs
  by_contra hcon
  -- for every `j`, `Ici j ×ˢ ball p (1/(j+1))` is not contained in the preimage
  have hfail : ∀ j : ℕ, ∃ q : ℕ × P, j ≤ q.1 ∧ dist q.2 p < 1 / ((j : ℝ) + 1) ∧
      Tn q.1 q.2 ∉ s := fun j => by
    by_contra hall
    push Not at hall
    refine hcon (mem_prod_iff.2 ⟨Set.Ici j, mem_atTop j, Metric.ball p (1 / ((j : ℝ) + 1)),
      Metric.ball_mem_nhds p (by positivity), ?_⟩)
    rintro ⟨a, b⟩ ⟨ha, hb⟩
    exact hall (a, b) ha (Metric.mem_ball.1 hb)
  choose q hq using hfail
  have hκ : Tendsto (fun j => (q j).1) atTop atTop :=
    tendsto_atTop_mono (fun j => (hq j).1) tendsto_id
  have hx : Tendsto (fun j => (q j).2) atTop (𝓝 p) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun _ => dist_nonneg) (fun j => (hq j).2.1.le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have := (hseq p _ _ hκ hx).eventually hs
  obtain ⟨j, hj⟩ := this.exists
  exact (hq j).2.2 hj

end bridge

section metricCodomain

variable {P V : Type*} [TopologicalSpace P] [PseudoMetricSpace V]

namespace ContinuouslyConverges

/-- **Continuity of the limit** of a continuously convergent sequence (pseudo-metric codomain). -/
theorem continuous_limit {Tn : ℕ → P → V} {T : P → V} (hcc : ContinuouslyConverges Tn T) :
    Continuous T := by
  refine continuous_iff_continuousAt.2 fun p => Metric.tendsto_nhds.2 fun ε hε => ?_
  have h := (hcc p).eventually (Metric.ball_mem_nhds (T p) (half_pos hε))
  rw [eventually_prod_iff] at h
  obtain ⟨pa, hpa, pb, hpb, hab⟩ := h
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hpa
  filter_upwards [hpb] with q hqb
  -- `T q` is the limit of `Tn n q`, each within `ε/2` of `T p` for `n ≥ n₀`
  have hlim : Tendsto (fun n => dist (Tn n q) (T p)) atTop (𝓝 (dist (T q) (T p))) :=
    (hcc.tendsto_pointwise q).dist tendsto_const_nhds
  have hle : dist (T q) (T p) ≤ ε / 2 :=
    le_of_tendsto hlim (eventually_atTop.2 ⟨n₀, fun n hn =>
      (Metric.mem_ball.1 (hab (hn₀ n hn) hqb)).le⟩)
  linarith

/-- **Uniform convergence on compact sets** for a continuously convergent sequence: continuous
convergence gives, around each `p`, a threshold and a neighbourhood on which `Tn n` is close to
`T p`, continuity of `T` keeps `T` close to `T p` there, and a finite subcover yields a common
threshold. -/
theorem tendstoUniformlyOn {Tn : ℕ → P → V} {T : P → V} (hcc : ContinuouslyConverges Tn T)
    {C : Set P} (hC : IsCompact C) :
    TendstoUniformlyOn Tn T atTop C := by
  have hT := hcc.continuous_limit
  refine Metric.tendstoUniformlyOn_iff.2 fun ε hε => ?_
  have key : ∀ p ∈ C, ∃ n₀ : ℕ, ∃ U ∈ 𝓝 p, ∀ n ≥ n₀, ∀ q ∈ U, dist (T q) (Tn n q) < ε := by
    intro p _
    have h := (hcc p).eventually (Metric.ball_mem_nhds (T p) (half_pos hε))
    rw [eventually_prod_iff] at h
    obtain ⟨pa, hpa, pb, hpb, hab⟩ := h
    obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hpa
    refine ⟨n₀, {q | pb q} ∩ T ⁻¹' Metric.ball (T p) (ε / 2), inter_mem hpb
      (hT.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ (half_pos hε))),
      fun n hn q hq => ?_⟩
    have h1 : dist (Tn n q) (T p) < ε / 2 := Metric.mem_ball.1 (hab (hn₀ n hn) hq.1)
    have h2 : dist (T q) (T p) < ε / 2 := Metric.mem_ball.1 hq.2
    calc dist (T q) (Tn n q) ≤ dist (T q) (T p) + dist (Tn n q) (T p) :=
          dist_triangle_right _ _ _
      _ < ε := by linarith
  choose! n₀ U hU hUε using key
  obtain ⟨t, ht⟩ := hC.elim_nhds_subcover' (fun p _ => U p) fun p hp => hU p hp
  filter_upwards [(eventually_all_finset t).2 fun p _ => eventually_ge_atTop (n₀ p)] with n hn q hq
  obtain ⟨p, hp, hqU⟩ := Set.mem_iUnion₂.1 (ht hq)
  exact hUε p p.2 n (hn p hp) q hqU

end ContinuouslyConverges

end metricCodomain

end Grammar
