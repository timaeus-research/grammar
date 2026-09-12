/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.ResolvedCoordFreeExpansion
import Grammar.CoordinateBoxCertificate

/-!
# Congruence of the coordinate-free expansion (CCCXXXIII; hygiene unit H-A)

Consult #99 §A2/§B (H3). The coordinate-free expansion depends on the prior and the observable
only through the integral over `W` and the **germs** of the observable at the points of the
strata that carry the stratum measures: the normal differential `D^r_⊥(φ∘π)(s)` is the iterated
derivative of `φ ∘ π ∘ Φ_s` at `0`, so two observables agreeing near `π s` have the same normal
differentials (`normalDifferential_congr`), the expansion coefficients agree when the germs agree
`ν_I`-a.e. (`expansionCoefficient_congr`), and the expansion transfers
(`HasCoordFreeExpansion.congr`). For a certificate, the stratum measures are pushforwards of the
base measures from the compact bases, so any pointwise property of the bases holds a.e.
(`ResolvedCertificate.ae_stratumMeasure`); for the compact-box certificate the bases lie in the
box (`mem_box_of_mem_baseStratum`, `ae_stratumMeasure_mem_box`). Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

section rawJet

variable {S : Type*} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {M : Type*}
  [TopologicalSpace M]

/-- Two functions agreeing near `Φ_s 0` have the same raw normal jets at `s`. -/
theorem rawNormalJet_congr_fun (N : S → Submodule ℝ E) (Φ : ∀ s, N s → M) {F F' : M → ℝ} (s : S)
    (hΦ : ContinuousAt (Φ s) 0) (h : F' =ᶠ[𝓝 (Φ s 0)] F) (r : ℕ) :
    rawNormalJet N Φ F' s r = rawNormalJet N Φ F s r := by
  unfold rawNormalJet
  have := ((h.comp_tendsto hΦ).iteratedFDeriv (𝕜 := ℝ) r).eq_of_nhds
  exact this

end rawJet

section normalData

variable {d : ℕ} {U : Type*} [TopologicalSpace U] {R : ResolvedGeometry d U} {A : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] (D : ResolvedNormalData R A)

namespace ResolvedNormalData

/-- **Normal differentials depend only on the germ of the observable at `π s`.** -/
theorem normalDifferential_congr {φ φ' : (Fin d → ℝ) → ℝ} (I : Finset R.Component)
    (s : R.Stratum I) (h : φ' =ᶠ[𝓝 (R.π s)] φ) (r : ℕ) :
    D.normalDifferential φ' I s r = D.normalDifferential φ I s r := by
  unfold ResolvedNormalData.normalDifferential Grammar.normalDifferential
  apply rawNormalJet_congr_fun _ _ _ (D.continuousAt_Φ I s)
  rw [D.Φ_zero]
  exact h.comp_tendsto R.continuous_π.continuousAt

variable [MeasurableSpace U]

/-- **Expansion coefficients depend only on the `ν_I`-a.e. germs of the observable.** -/
theorem expansionCoefficient_congr (ν : ∀ I : Finset R.Component, Measure (R.Stratum I))
    (B : D.MomentCoefficientField) {φ φ' : (Fin d → ℝ) → ℝ}
    (h : ∀ I, ∀ᵐ (s : R.Stratum I) ∂ν I, φ' =ᶠ[𝓝 (R.π (s : U))] φ) (q : PowerLogIndex) :
    D.expansionCoefficient ν B φ' q = D.expansionCoefficient ν B φ q := by
  unfold ResolvedNormalData.expansionCoefficient
  refine Finset.sum_congr rfl fun I _ => integral_congr_ae ?_
  filter_upwards [h I] with s hs
  exact tsum_congr fun r => by rw [D.normalDifferential_congr I s hs r]

variable {D} in
/-- ★ **Congruence of the coordinate-free expansion**: the expansion transfers between pairs
`(ϕ', φ')` and `(ϕ, φ)` whose products agree on `W` and whose observables have the same germs
`ν_I`-a.e. on every stratum. -/
theorem HasCoordFreeExpansion.congr {ν : ∀ I : Finset R.Component, Measure (R.Stratum I)}
    {B : D.MomentCoefficientField} {spec : ℝ → Finset PowerLogIndex} {W : Set (Fin d → ℝ)}
    {K ϕ φ ϕ' φ' : (Fin d → ℝ) → ℝ} (hW : MeasurableSet W)
    (hprod : ∀ w ∈ W, φ' w * ϕ' w = φ w * ϕ w)
    (hgerm : ∀ I, ∀ᵐ (s : R.Stratum I) ∂ν I, φ' =ᶠ[𝓝 (R.π (s : U))] φ)
    (h : D.HasCoordFreeExpansion ν B spec W K ϕ' φ') :
    D.HasCoordFreeExpansion ν B spec W K ϕ φ := by
  intro A
  have hL : ∀ n : ℝ, globalLaplace W K (fun w => φ w * ϕ w) n =
      globalLaplace W K (fun w => φ' w * ϕ' w) n := fun n => by
    unfold globalLaplace
    exact setIntegral_congr_fun hW fun w hw => by simp only [hprod w hw]
  have hc : ∀ q, D.expansionCoefficient ν B φ q = D.expansionCoefficient ν B φ' q :=
    fun q => (D.expansionCoefficient_congr ν B hgerm q).symm
  simp only [hL, hc]
  exact h A

end ResolvedNormalData

end normalData

section certificate

variable {d : ℕ} {U : Type*} [TopologicalSpace U] [T2Space U] [MeasurableSpace U] [BorelSpace U]
  {R : ResolvedGeometry d U} {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [MeasurableSpace A] [BorelSpace A] {D : ResolvedNormalData R A} {W : Set (Fin d → ℝ)}
  {K ϕ φ : (Fin d → ℝ) → ℝ}

namespace ResolvedCertificate

variable (C : ResolvedCertificate R D W K ϕ φ)

omit [T2Space U] [BorelSpace U] [MeasurableSpace A] [BorelSpace A] in
/-- Transport along an identification of strata preserves a.e. properties of the underlying
points. -/
theorem ae_transportMeasure {J : Fin C.M} {I : Finset R.Component} (hJ : C.strat J = I)
    (μ : Measure (R.Stratum (C.strat J))) {P : U → Prop}
    (h : ∀ᵐ (s : R.Stratum (C.strat J)) ∂μ, P (s : U)) :
    ∀ᵐ (s : R.Stratum I) ∂C.transportMeasure hJ μ, P (s : U) := by
  subst hJ
  exact h

omit [T2Space U] [BorelSpace U] [MeasurableSpace A] [BorelSpace A] in
/-- ★ **Pointwise properties of the bases hold a.e. for the stratum measures**: the stratum
measure is a sum of pushforwards of the base measures. -/
theorem ae_stratumMeasure {P : U → Prop} (hP : MeasurableSet {u | P u})
    (hbase : ∀ (J : Fin C.M) (t : ↥(C.base J)), P (t.1 : U)) (I : Finset R.Component) :
    ∀ᵐ (s : R.Stratum I) ∂C.stratumMeasure I, P (s : U) := by
  have hP' : ∀ J : Finset R.Component, MeasurableSet {s : R.Stratum J | P (s : U)} :=
    fun J => hP.preimage measurable_subtype_coe
  unfold stratumMeasure
  rw [← Measure.sum_fintype, Measure.ae_sum_iff' (hP' I)]
  intro J
  split_ifs with hJ
  · refine C.ae_transportMeasure hJ _ ?_
    unfold pushedMeasure
    rw [ae_map_iff measurable_subtype_coe.aemeasurable (hP' _)]
    exact Eventually.of_forall fun t => hbase J t
  · simp

end ResolvedCertificate

end certificate

namespace WaterFilling

variable {d : ℕ} (k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (a δ : ℝ)

/-- The compact bases of the collar lie in the box. -/
theorem mem_box_of_mem_baseStratum (ha : 0 < a) (I : Finset (Fin d)) (s : KI k hk a δ I) :
    (s.1 : Fin d → ℝ) ∈ piBox d (Icc 0 a) := by
  intro i _
  by_cases hi : i ∈ I
  · have h0 : (s.1 : Fin d → ℝ) i = 0 := (s.1.2 i).2 hi
    rw [h0]
    exact ⟨le_rfl, ha.le⟩
  · have ht := s.2 ⟨i, hi⟩
    exact ⟨ht.1, ht.2.1⟩

variable (hδ : 0 < δ) (ϕ φ : (Fin d → ℝ) → ℝ) (hϕm : Measurable ϕ) (hϕ0 : ∀ w, 0 ≤ ϕ w)
  (hφint : Integrable φ
    ((volume.restrict (piBox d (Icc 0 a))).withDensity fun w => ENNReal.ofReal (ϕ w)))
  (hd : 0 < d) (ha : 0 < a) (hδa : ∀ i, δ ^ ((d : ℝ)⁻¹) < a ^ (2 * k i))
  (F : ∀ I : NonemptyIdx d, FaceSeries k hk a δ ϕ φ I)

/-- ★ **The stratum measures of the compact-box certificate live in the box.** -/
theorem ae_stratumMeasure_mem_box (I : Finset (Fin d)) :
    ∀ᵐ (s : (CoordModel.geometry d k (zeroOrders d) hk).Stratum I)
      ∂(certificate k hk a δ hδ ϕ φ hϕm hϕ0 hφint hd ha hδa F).stratumMeasure I,
      (s : Fin d → ℝ) ∈ piBox d (Icc 0 a) :=
  (certificate k hk a δ hδ ϕ φ hϕm hϕ0 hφint hd ha hδa F).ae_stratumMeasure (measurableSet_W a)
    (fun _ t => mem_box_of_mem_baseStratum k hk a δ ha _ t) I

end WaterFilling

end Grammar
