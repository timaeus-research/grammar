/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.EmpiricalCoeffDistribution

/-!
# The coefficient on the closed realizable jets (§20, consult #146 item 1)

The realizable branch jets `range (branchJet μ)` need not be closed in the jet space, and a
limit in distribution of jets of smooth fields need not be the jet of a smooth field. The
coefficient map extends canonically to the closure: on bounded sets of realizable jets it is
Lipschitz (★ `exists_coeffOnJets'_dist_le`, the local Lipschitz bound of the resolved
coefficient), so along realizable jets approaching a closure point it is Cauchy and has a limit
in `ℝ` (`exists_tendsto_coeffOnJets'`); `coeffOnClosedJets` is that limit
(`tendsto_coeffOnClosedJets` characterises it uniquely), it agrees with the coefficient on the
realizable jets (`coeffOnClosedJets_closedRealizableJet`), and it is continuous
(★★ `continuous_coeffOnClosedJets`), hence Borel. The conditional random-field theorem then holds
with limits in the CLOSED realizable jets (★★ `tendstoInDistribution_resolvedCoeff_top_closed`):
smooth realizability of the limiting random jet is no longer required. Values off the closure
are not defined (no ambient extension is asserted). Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal ContDiff Manifold
open Monomialize.VolumeScaling Monomialize.Transport Monomialize.Manifold
open Grammar.NormalCrossing Grammar.NormalCrossing.EvenChartBoxDepth

namespace Grammar

namespace SmoothEngine

namespace ResolvedData

variable {d : ℕ} (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)

open Classical in
/-- The coefficient on the ambient jet space (junk value `0` off the realizable jets). -/
noncomputable def coeffOnJets' (μ : ℝ) (c : ℕ) (x : Ξ.BranchJetSpace Y μ) : ℝ :=
  if h : x ∈ Set.range (Ξ.branchJet Y μ) then Ξ.coeffOnJets Y μ c ⟨x, h⟩ else 0

theorem coeffOnJets'_branchJet {c : ℕ} (hc : 1 ≤ c)
    (hF : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), Ξ.F P = 0) {μ : ℝ} (hμ : 0 < μ)
    (ξ : Ξ.SmoothRootField Y) :
    Ξ.coeffOnJets' Y μ c (Ξ.branchJet Y μ ξ) = ξ.resolvedCoeff μ (c - 1) := by
  unfold coeffOnJets'
  rw [dif_pos ⟨ξ, rfl⟩]
  exact Ξ.coeffOnJets_eq Y hc hF hμ _ ξ rfl

theorem coeffOnJets'_coe (μ : ℝ) (c : ℕ) (p : Set.range (Ξ.branchJet Y μ)) :
    Ξ.coeffOnJets' Y μ c p.1 = Ξ.coeffOnJets Y μ c p := by
  unfold coeffOnJets'
  rw [dif_pos p.2]

/-- ★ **The bounded-ball Lipschitz estimate on the realizable jets.** -/
theorem exists_coeffOnJets'_dist_le {c : ℕ} (hc : 1 ≤ c)
    (hF : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), Ξ.F P = 0) {μ : ℝ} (hμ : 0 < μ) {B : ℝ}
    (hB : 0 ≤ B) :
    ∃ K, 0 ≤ K ∧ ∀ x ∈ Set.range (Ξ.branchJet Y μ), ∀ y ∈ Set.range (Ξ.branchJet Y μ),
      ‖y‖ ≤ B → dist x y ≤ 1 →
      |Ξ.coeffOnJets' Y μ c x - Ξ.coeffOnJets' Y μ c y| ≤ K * dist x y := by
  obtain ⟨K, hK0, hK⟩ := Ξ.exists_resolvedCoeff_top_bound Y hc hF hμ hB
  refine ⟨K, hK0, ?_⟩
  rintro x ⟨ξ₁, rfl⟩ y ⟨ξ₂, rfl⟩ hy hxy
  rw [dist_eq_norm] at hxy ⊢
  rw [Ξ.coeffOnJets'_branchJet Y hc hF hμ, Ξ.coeffOnJets'_branchJet Y hc hF hμ]
  exact hK ξ₁ ξ₂ (Ξ.jetBoundOn_of_norm_branchJet_le Y hy) _ (norm_nonneg _) hxy
    (Ξ.jetClose_of_norm_branchJet_sub_le Y le_rfl)

/-! ### The closed realizable jets -/

/-- The closure of the realizable branch jets, as a metric space. -/
abbrev ClosedRealizableJets (μ : ℝ) : Type := closure (Set.range (Ξ.branchJet Y μ))

/-- The branch jets of a field as a closed realizable jet. -/
noncomputable def closedRealizableJet (μ : ℝ) (ξ : Ξ.SmoothRootField Y) :
    Ξ.ClosedRealizableJets Y μ :=
  ⟨Ξ.branchJet Y μ ξ, subset_closure ⟨ξ, rfl⟩⟩

/-- Along realizable jets approaching a closure point the coefficient has a limit. -/
theorem exists_tendsto_coeffOnJets' {c : ℕ} (hc : 1 ≤ c)
    (hF : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), Ξ.F P = 0) {μ : ℝ} (hμ : 0 < μ)
    (z : Ξ.BranchJetSpace Y μ) (hz : z ∈ closure (Set.range (Ξ.branchJet Y μ))) :
    ∃ l, Tendsto (Ξ.coeffOnJets' Y μ c) (𝓝[Set.range (Ξ.branchJet Y μ)] z) (𝓝 l) := by
  set S := Set.range (Ξ.branchJet Y μ) with hS
  have hne : (𝓝[S] z).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hz
  obtain ⟨K, hK0, hK⟩ := Ξ.exists_coeffOnJets'_dist_le Y hc hF hμ (B := ‖z‖ + 1) (by positivity)
  have hcauchy : Cauchy (map (Ξ.coeffOnJets' Y μ c) (𝓝[S] z)) := by
    refine Metric.cauchy_iff.2 ⟨map_neBot, fun ε hε => ?_⟩
    set δ : ℝ := min (1 / 2) (ε / (2 * (K + 1))) with hδ
    have hδ0 : 0 < δ := lt_min (by norm_num) (div_pos hε (by positivity))
    have hδ1 : δ ≤ 1 / 2 := min_le_left _ _
    have hδ2 : δ ≤ ε / (2 * (K + 1)) := min_le_right _ _
    refine ⟨Ξ.coeffOnJets' Y μ c '' (S ∩ ball z δ),
      image_mem_map (inter_mem_nhdsWithin S (ball_mem_nhds z hδ0)), ?_⟩
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
    calc |Ξ.coeffOnJets' Y μ c x - Ξ.coeffOnJets' Y μ c y| ≤ K * dist x y :=
          hK x hxS y hyS hy hxy
      _ ≤ (K + 1) * dist x y := mul_le_mul_of_nonneg_right (by linarith) dist_nonneg
      _ < (K + 1) * (2 * δ) := mul_lt_mul_of_pos_left hxy2 (by linarith)
      _ ≤ (K + 1) * (2 * (ε / (2 * (K + 1)))) := by gcongr
      _ = ε := by field_simp
  obtain ⟨l, hl⟩ := CompleteSpace.complete hcauchy
  exact ⟨l, hl⟩

/-- The coefficient extended to the closed realizable jets: the limit along realizable jets. -/
noncomputable def coeffOnClosedJets (μ : ℝ) (c : ℕ) (z : Ξ.ClosedRealizableJets Y μ) : ℝ :=
  limUnder (𝓝[Set.range (Ξ.branchJet Y μ)] z.1) (Ξ.coeffOnJets' Y μ c)

/-- The extended coefficient is the limit of the coefficient along realizable jets (this
characterises it uniquely). -/
theorem tendsto_coeffOnClosedJets {c : ℕ} (hc : 1 ≤ c)
    (hF : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), Ξ.F P = 0) {μ : ℝ} (hμ : 0 < μ)
    (z : Ξ.ClosedRealizableJets Y μ) :
    Tendsto (Ξ.coeffOnJets' Y μ c) (𝓝[Set.range (Ξ.branchJet Y μ)] z.1)
      (𝓝 (Ξ.coeffOnClosedJets Y μ c z)) :=
  tendsto_nhds_limUnder (Ξ.exists_tendsto_coeffOnJets' Y hc hF hμ z.1 z.2)

/-- On the realizable jets the extension is the coefficient. -/
theorem coeffOnClosedJets_closedRealizableJet {c : ℕ} (hc : 1 ≤ c)
    (hF : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), Ξ.F P = 0) {μ : ℝ} (hμ : 0 < μ)
    (ξ : Ξ.SmoothRootField Y) :
    Ξ.coeffOnClosedJets Y μ c (Ξ.closedRealizableJet Y μ ξ) = ξ.resolvedCoeff μ (c - 1) := by
  have hx : Ξ.branchJet Y μ ξ ∈ Set.range (Ξ.branchJet Y μ) := ⟨ξ, rfl⟩
  have hne : (𝓝[Set.range (Ξ.branchJet Y μ)] (Ξ.closedRealizableJet Y μ ξ).1).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.1 (Ξ.closedRealizableJet Y μ ξ).2
  have h1 := Ξ.tendsto_coeffOnClosedJets Y hc hF hμ (Ξ.closedRealizableJet Y μ ξ)
  have hcont := (Ξ.continuous_coeffOnJets Y hc hF hμ).tendsto ⟨_, hx⟩
  rw [Ξ.coeffOnJets_branchJet Y hc hF hμ ξ] at hcont
  have h2 : Tendsto (Ξ.coeffOnJets' Y μ c) (𝓝[Set.range (Ξ.branchJet Y μ)] (Ξ.branchJet Y μ ξ))
      (𝓝 (ξ.resolvedCoeff μ (c - 1))) := by
    rw [nhdsWithin_eq_map_subtype_coe hx, tendsto_map'_iff]
    refine hcont.congr fun p => ?_
    exact (Ξ.coeffOnJets'_coe Y μ c p).symm
  exact tendsto_nhds_unique h1 h2

/-- ★★ **The extended coefficient is continuous on the closed realizable jets.** -/
theorem continuous_coeffOnClosedJets {c : ℕ} (hc : 1 ≤ c)
    (hF : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), Ξ.F P = 0) {μ : ℝ} (hμ : 0 < μ) :
    Continuous (Ξ.coeffOnClosedJets Y μ c) := by
  set S := Set.range (Ξ.branchJet Y μ) with hS
  refine Metric.continuous_iff.2 fun z₀ ε hε => ?_
  obtain ⟨K, hK0, hK⟩ :=
    Ξ.exists_coeffOnJets'_dist_le Y hc hF hμ (B := ‖z₀.1‖ + 2) (by positivity)
  set δ : ℝ := min (1 / 4) (ε / (8 * (K + 1))) with hδ
  have hδ0 : 0 < δ := lt_min (by norm_num) (div_pos hε (by positivity))
  have hδ1 : δ ≤ 1 / 4 := min_le_left _ _
  have hδ2 : δ ≤ ε / (8 * (K + 1)) := min_le_right _ _
  refine ⟨δ, hδ0, fun z hz => ?_⟩
  have hzz : dist z.1 z₀.1 < δ := hz
  -- approximants of `z` and `z₀` by realizable jets
  have happrox : ∀ w : Ξ.ClosedRealizableJets Y μ, ∃ x ∈ S, dist x w.1 < δ ∧
      dist (Ξ.coeffOnJets' Y μ c x) (Ξ.coeffOnClosedJets Y μ c w) < ε / 4 := by
    intro w
    have hne : (𝓝[S] w.1).NeBot := mem_closure_iff_nhdsWithin_neBot.1 w.2
    have h1 : ∀ᶠ x in 𝓝[S] w.1, x ∈ S := self_mem_nhdsWithin
    have h2 : ∀ᶠ x in 𝓝[S] w.1, dist x w.1 < δ :=
      eventually_nhdsWithin_of_eventually_nhds (ball_mem_nhds w.1 hδ0)
    have h3 : ∀ᶠ x in 𝓝[S] w.1,
        dist (Ξ.coeffOnJets' Y μ c x) (Ξ.coeffOnClosedJets Y μ c w) < ε / 4 :=
      Metric.tendsto_nhds.1 (Ξ.tendsto_coeffOnClosedJets Y hc hF hμ w) _ (by positivity)
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
  have hmid : |Ξ.coeffOnJets' Y μ c x - Ξ.coeffOnJets' Y μ c x₀| ≤ 3 * ε / 8 := by
    calc |Ξ.coeffOnJets' Y μ c x - Ξ.coeffOnJets' Y μ c x₀| ≤ K * dist x x₀ :=
          hK x hxS x₀ hx₀S hx₀B hxx₀1
      _ ≤ (K + 1) * dist x x₀ := mul_le_mul_of_nonneg_right (by linarith) dist_nonneg
      _ ≤ (K + 1) * (3 * δ) := mul_le_mul_of_nonneg_left hxx₀.le (by linarith)
      _ ≤ (K + 1) * (3 * (ε / (8 * (K + 1)))) := by gcongr
      _ = 3 * ε / 8 := by field_simp
  rw [Real.dist_eq] at hxf hx₀f ⊢
  calc |Ξ.coeffOnClosedJets Y μ c z - Ξ.coeffOnClosedJets Y μ c z₀|
      = |(Ξ.coeffOnClosedJets Y μ c z - Ξ.coeffOnJets' Y μ c x) +
          (Ξ.coeffOnJets' Y μ c x - Ξ.coeffOnJets' Y μ c x₀) +
          (Ξ.coeffOnJets' Y μ c x₀ - Ξ.coeffOnClosedJets Y μ c z₀)| := by ring_nf
    _ ≤ |Ξ.coeffOnClosedJets Y μ c z - Ξ.coeffOnJets' Y μ c x| +
          |Ξ.coeffOnJets' Y μ c x - Ξ.coeffOnJets' Y μ c x₀| +
          |Ξ.coeffOnJets' Y μ c x₀ - Ξ.coeffOnClosedJets Y μ c z₀| :=
        (abs_add_three _ _ _)
    _ < ε / 4 + 3 * ε / 8 + ε / 4 := by
        rw [abs_sub_comm (Ξ.coeffOnClosedJets Y μ c z)]
        linarith
    _ ≤ ε := by linarith

theorem measurable_coeffOnClosedJets {c : ℕ} (hc : 1 ≤ c)
    (hF : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), Ξ.F P = 0) {μ : ℝ} (hμ : 0 < μ) :
    Measurable (Ξ.coeffOnClosedJets Y μ c) :=
  (Ξ.continuous_coeffOnClosedJets Y hc hF hμ).measurable

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']

/-- ★★ **The conditional random-field theorem with limits in the closed realizable jets**: the
limiting random jet need not be the jet of a smooth field. -/
theorem tendstoInDistribution_resolvedCoeff_top_closed {c : ℕ} (hc : 1 ≤ c)
    (hF : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), Ξ.F P = 0) {μ : ℝ} (hμ : 0 < μ)
    (ξ : ℕ → Ω → Ξ.SmoothRootField Y) {G : Ω' → Ξ.ClosedRealizableJets Y μ}
    (hLG : TendstoInDistribution (fun n w => Ξ.closedRealizableJet Y μ (ξ n w)) atTop G
      (fun _ => P) P') :
    TendstoInDistribution (fun (n : ℕ) w => (ξ n w).resolvedCoeff μ (c - 1)) atTop
      (fun w' => Ξ.coeffOnClosedJets Y μ c (G w')) (fun _ => P) P' := by
  have h := hLG.continuous_comp (Ξ.continuous_coeffOnClosedJets Y hc hF hμ)
  have heq : (fun n : ℕ => Ξ.coeffOnClosedJets Y μ c ∘ fun w => Ξ.closedRealizableJet Y μ (ξ n w))
      = fun (n : ℕ) w => (ξ n w).resolvedCoeff μ (c - 1) :=
    funext fun n => funext fun w => Ξ.coeffOnClosedJets_closedRealizableJet Y hc hF hμ (ξ n w)
  rw [heq] at h
  exact h

end ResolvedData

end SmoothEngine

end Grammar
