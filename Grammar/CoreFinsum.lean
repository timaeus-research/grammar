/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.CoreTransport

/-!
# Finite sums of localisation data and of single-core decompositions (B3b)

Finitely many localisation data on the same space with a common phase, observable and level add
up to one (`LocalisationData.finsum`, measure `∑ μ_i`), and single-core analytic decompositions of
the summands assemble into one decomposition of the sum, with the cores relabelled along
`e : Fin M ≃ ι`, the tails summed and the phase gap the minimum of the gaps
(`AnalyticCoreDecomposition.finsum`). The normal-moment presentations follow the datum
(`CoreNormalMomentPresentation.congrData`). This is the bookkeeping that turns the `d · 2^d`
transported chart cores of the cube blow-up into one certificate on the genuine blow-up space.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Grammar

section Finsum

variable {U : Type*} [MeasurableSpace U] {ι : Type*} [Fintype ι]

/-- **The sum of finitely many localisation data** with a common phase, observable and level. -/
noncomputable def LocalisationData.finsum (D : ι → LocalisationData U) (phase obs : U → ℝ)
    (hpm : Measurable phase) (hp : ∀ i, (D i).phase = phase) (ho : ∀ i, (D i).obs = obs) (δ : ℝ)
    (hδ : 0 < δ) : LocalisationData U where
  μ := ∑ i, (D i).μ
  phase := phase
  obs := obs
  phase_measurable := hpm
  phase_nonneg := by
    rw [← Measure.sum_fintype, Measure.ae_sum_iff]
    intro i
    rw [← hp i]
    exact (D i).phase_nonneg
  obs_integrable := (integrable_finsetSum_measure).2 fun i _ => by
    rw [← ho i]
    exact (D i).obs_integrable
  δ := δ
  δ_pos := hδ

@[simp] theorem LocalisationData.finsum_μ (D : ι → LocalisationData U) (phase obs : U → ℝ) (hpm)
    (hp) (ho) (δ : ℝ) (hδ) :
    (LocalisationData.finsum D phase obs hpm hp ho δ hδ).μ = ∑ i, (D i).μ := rfl

@[simp] theorem LocalisationData.finsum_phase (D : ι → LocalisationData U) (phase obs : U → ℝ)
    (hpm) (hp) (ho) (δ : ℝ) (hδ) :
    (LocalisationData.finsum D phase obs hpm hp ho δ hδ).phase = phase := rfl

@[simp] theorem LocalisationData.finsum_obs (D : ι → LocalisationData U) (phase obs : U → ℝ)
    (hpm) (hp) (ho) (δ : ℝ) (hδ) :
    (LocalisationData.finsum D phase obs hpm hp ho δ hδ).obs = obs := rfl

variable {D : ι → LocalisationData U} {phase obs : U → ℝ} {hpm : Measurable phase}
  {hp : ∀ i, (D i).phase = phase} {ho : ∀ i, (D i).obs = obs} {δ : ℝ} {hδ : 0 < δ}
  {K : ι → Type*} [∀ i, TopologicalSpace (K i)] [∀ i, MeasurableSpace (K i)] {n : ι → ℕ} {β : ℝ}

/-- **Assembly of single-core decompositions**: the cores relabelled along `e : Fin M ≃ ι`, the
tails summed, the phase gap the minimum of the gaps. -/
noncomputable def AnalyticCoreDecomposition.finsum [Nonempty ι]
    (A : ∀ i, AnalyticCoreDecomposition (D i) 1 (fun _ => K i) (fun _ => n i) β) {M : ℕ}
    (e : Fin M ≃ ι) :
    AnalyticCoreDecomposition (LocalisationData.finsum D phase obs hpm hp ho δ hδ) M
      (fun k => K (e k)) (fun k => n (e k)) β where
  core := fun k => (A (e k)).core 0
  tail := ∑ i, (A i).tail
  measure_eq := by
    change ∑ i, (D i).μ = _
    rw [Finset.sum_congr rfl fun i _ => (A i).measure_eq]
    simp only [Fin.sum_univ_one]
    rw [Finset.sum_add_distrib]
    congr 1
    exact (Equiv.sum_comp e fun i => (A i).core 0).symm
  δ₀ := Finset.univ.inf' Finset.univ_nonempty fun i => (A i).δ₀
  δ₀_pos := (Finset.lt_inf'_iff _).2 fun i _ => (A i).δ₀_pos
  gap := by
    change ∀ᵐ z ∂(∑ i, (A i).tail), _ ≤ phase z
    rw [← Measure.sum_fintype, Measure.ae_sum_iff]
    intro i
    refine (A i).gap.mono fun z hz => ?_
    rw [← hp i]
    exact (Finset.inf'_le _ (Finset.mem_univ i)).trans hz
  chart := fun k => ((A (e k)).chart 0).congrData _ (hp _).symm (ho _).symm

theorem AnalyticCoreDecomposition.finsum_core [Nonempty ι]
    (A : ∀ i, AnalyticCoreDecomposition (D i) 1 (fun _ => K i) (fun _ => n i) β) {M : ℕ}
    (e : Fin M ≃ ι) (k : Fin M) :
    (AnalyticCoreDecomposition.finsum (hpm := hpm) (hp := hp) (ho := ho) (hδ := hδ) A e).core k =
      (A (e k)).core 0 := rfl

theorem AnalyticCoreDecomposition.finsum_chart [Nonempty ι]
    (A : ∀ i, AnalyticCoreDecomposition (D i) 1 (fun _ => K i) (fun _ => n i) β) {M : ℕ}
    (e : Fin M ≃ ι) (k : Fin M) :
    (AnalyticCoreDecomposition.finsum (hpm := hpm) (hp := hp) (ho := ho) (hδ := hδ) A e).chart k =
      ((A (e k)).chart 0).congrData _ (hp _).symm (ho _).symm := rfl

end Finsum

/-! ### Normal-moment presentations follow the datum -/

section CongrData

variable {V : Type*} [MeasurableSpace V] {D : LocalisationData V} {target : Measure V}
  {K : Type*} [TopologicalSpace K] [MeasurableSpace K] {n : ℕ} {β : ℝ}

theorem CorePresentation.congrData_obsFibre (C : CorePresentation D target K n β)
    (D' : LocalisationData V) (hp : D'.phase = D.phase) (ho : D'.obs = D.obs) (v : K) :
    (C.congrData D' hp ho).obsFibre v = C.obsFibre v := by
  funext u
  unfold CorePresentation.obsFibre
  rw [ho]
  rfl

/-- A normal-moment presentation for a datum with the same phase and observable. -/
noncomputable def CoreNormalMomentPresentation.congrData {C : CorePresentation D target K n β}
    (T : CoreNormalMomentPresentation C) (D' : LocalisationData V) (hp : D'.phase = D.phase)
    (ho : D'.obs = D.obs) : CoreNormalMomentPresentation (C.congrData D' hp ho) where
  p := T.p
  R := T.R
  analytic := fun v => by
    rw [CorePresentation.congrData_obsFibre]
    exact T.analytic v
  radius := T.radius
  cBound := T.cBound
  c_le := T.c_le

end CongrData

end Grammar
