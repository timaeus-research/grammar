/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.CoreFinsum
import Grammar.SheetGeometry

/-!
# Finite sums of multi-core decompositions; a.e.-compatible transport of data (unit H, part 1)

Three small generalisations of CCCLXIII–LXIV needed to assemble the pieces of a domain-sector
atlas on the sheet geometry: `LocalisationData.map_ae` (the pushed datum with phase
compatibility only `μ`-a.e. — a clamped sheet inclusion agrees with the chart phase only on the
box, where the measure lives), `AnalyticCoreDecomposition.reindexAll` (every core reindexed along
its own base homeomorphism), and ★ `AnalyticCoreDecomposition.sigma` (finitely many
decompositions with arbitrary numbers of cores assembled into one: cores relabelled along
`e : Fin N ≃ Σ i, Fin (M i)`, tails summed, phase gap the minimum). Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Grammar

section MapAe

variable {V U : Type*} [MeasurableSpace V] [MeasurableSpace U]

/-- The pushed datum with phase compatibility almost everywhere on the source measure. -/
noncomputable def LocalisationData.map_ae (D : LocalisationData V) (Ψ : V → U) (hΨ : Measurable Ψ)
    (phase' obs' : U → ℝ) (hpm : Measurable phase') (hp : ∀ᵐ z ∂D.μ, phase' (Ψ z) = D.phase z)
    (hom : AEStronglyMeasurable obs' (D.μ.map Ψ)) (ho : ∀ᵐ z ∂D.μ, obs' (Ψ z) = D.obs z) :
    LocalisationData U where
  μ := D.μ.map Ψ
  phase := phase'
  obs := obs'
  phase_measurable := hpm
  phase_nonneg := by
    rw [ae_map_iff hΨ.aemeasurable (measurableSet_le measurable_const hpm)]
    filter_upwards [D.phase_nonneg, hp] with z hz h2
    change 0 ≤ phase' (Ψ z)
    rw [h2]
    exact hz
  obs_integrable := (integrable_map_measure hom hΨ.aemeasurable).2
    ((D.obs_integrable.congr (ho.mono fun z hz => hz.symm)))
  δ := D.δ
  δ_pos := D.δ_pos

theorem LocalisationData.map_ae_μ (D : LocalisationData V) (Ψ : V → U) (hΨ : Measurable Ψ)
    (phase' obs' : U → ℝ) (hpm) (hp) (hom) (ho) :
    (D.map_ae Ψ hΨ phase' obs' hpm hp hom ho).μ = D.μ.map Ψ := rfl

theorem LocalisationData.map_ae_phase (D : LocalisationData V) (Ψ : V → U) (hΨ : Measurable Ψ)
    (phase' obs' : U → ℝ) (hpm) (hp) (hom) (ho) :
    (D.map_ae Ψ hΨ phase' obs' hpm hp hom ho).phase = phase' := rfl

theorem LocalisationData.map_ae_obs (D : LocalisationData V) (Ψ : V → U) (hΨ : Measurable Ψ)
    (phase' obs' : U → ℝ) (hpm) (hp) (hom) (ho) :
    (D.map_ae Ψ hΨ phase' obs' hpm hp hom ho).obs = obs' := rfl

end MapAe

section ReindexAll

variable {U : Type*} [MeasurableSpace U] {D : LocalisationData U} {M : ℕ} {K K' : Fin M → Type*}
  [∀ k, TopologicalSpace (K k)] [∀ k, MeasurableSpace (K k)] [∀ k, BorelSpace (K k)]
  [∀ k, TopologicalSpace (K' k)] [∀ k, MeasurableSpace (K' k)] [∀ k, BorelSpace (K' k)]
  {n : Fin M → ℕ} {β : ℝ}

/-- Reindexing every core of a decomposition along a homeomorphism of its base. -/
noncomputable def AnalyticCoreDecomposition.reindexAll (A : AnalyticCoreDecomposition D M K n β)
    (e : ∀ k, K k ≃ₜ K' k) : AnalyticCoreDecomposition D M K' n β where
  core := A.core
  tail := A.tail
  measure_eq := A.measure_eq
  δ₀ := A.δ₀
  δ₀_pos := A.δ₀_pos
  gap := A.gap
  chart := fun k => (A.chart k).reindex (e k)

theorem AnalyticCoreDecomposition.reindexAll_chart (A : AnalyticCoreDecomposition D M K n β)
    (e : ∀ k, K k ≃ₜ K' k) (k : Fin M) :
    (A.reindexAll e).chart k = (A.chart k).reindex (e k) := rfl

end ReindexAll

section Sigma

variable {U : Type*} [MeasurableSpace U] {ι : Type*} [Fintype ι] {D : ι → LocalisationData U}
  {phase obs : U → ℝ} {hpm : Measurable phase} {hp : ∀ i, (D i).phase = phase}
  {ho : ∀ i, (D i).obs = obs} {δ : ℝ} {hδ : 0 < δ} {M : ι → ℕ} {K : ∀ i, Fin (M i) → Type*}
  [∀ i k, TopologicalSpace (K i k)] [∀ i k, MeasurableSpace (K i k)] {n : ∀ i, Fin (M i) → ℕ}
  {β : ℝ}

/-- ★ **Assembly of multi-core decompositions**: the cores of all the summands relabelled along
`e : Fin N ≃ Σ i, Fin (M i)`, the tails summed, the phase gap the minimum of the gaps. -/
noncomputable def AnalyticCoreDecomposition.sigma
    (A : ∀ i, AnalyticCoreDecomposition (D i) (M i) (K i) (n i) β) {N : ℕ}
    (e : Fin N ≃ Σ i, Fin (M i)) :
    AnalyticCoreDecomposition (LocalisationData.finsum D phase obs hpm hp ho δ hδ) N
      (fun k => K (e k).1 (e k).2) (fun k => n (e k).1 (e k).2) β where
  core := fun k => (A (e k).1).core (e k).2
  tail := ∑ i, (A i).tail
  measure_eq := by
    change ∑ i, (D i).μ = _
    rw [Finset.sum_congr rfl fun i _ => (A i).measure_eq, Finset.sum_add_distrib]
    congr 1
    exact ((Fintype.sum_sigma fun p : Σ i, Fin (M i) => (A p.1).core p.2).symm.trans
      (Equiv.sum_comp e fun p : Σ i, Fin (M i) => (A p.1).core p.2).symm)
  δ₀ := if h : (Finset.univ : Finset ι).Nonempty then Finset.univ.inf' h fun i => (A i).δ₀ else 1
  δ₀_pos := by
    split_ifs with h
    · exact (Finset.lt_inf'_iff _).2 fun i _ => (A i).δ₀_pos
    · exact one_pos
  gap := by
    change ∀ᵐ z ∂(∑ i, (A i).tail), _ ≤ phase z
    rw [← Measure.sum_fintype, Measure.ae_sum_iff]
    intro i
    refine (A i).gap.mono fun z hz => ?_
    rw [← hp i, dif_pos ⟨i, Finset.mem_univ i⟩]
    exact (Finset.inf'_le _ (Finset.mem_univ i)).trans hz
  chart := fun k => ((A (e k).1).chart (e k).2).congrData _ (hp _).symm (ho _).symm

theorem AnalyticCoreDecomposition.sigma_core
    (A : ∀ i, AnalyticCoreDecomposition (D i) (M i) (K i) (n i) β) {N : ℕ}
    (e : Fin N ≃ Σ i, Fin (M i)) (k : Fin N) :
    (AnalyticCoreDecomposition.sigma (hpm := hpm) (hp := hp) (ho := ho) (hδ := hδ) A e).core k =
      (A (e k).1).core (e k).2 := rfl

theorem AnalyticCoreDecomposition.sigma_chart
    (A : ∀ i, AnalyticCoreDecomposition (D i) (M i) (K i) (n i) β) {N : ℕ}
    (e : Fin N ≃ Σ i, Fin (M i)) (k : Fin N) :
    (AnalyticCoreDecomposition.sigma (hpm := hpm) (hp := hp) (ho := ho) (hδ := hδ) A e).chart k =
      ((A (e k).1).chart (e k).2).congrData _ (hp _).symm (ho _).symm := rfl

end Sigma

end Grammar
