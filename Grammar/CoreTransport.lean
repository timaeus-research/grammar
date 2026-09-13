/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.ResolvedMomentRepresentation

/-!
# Transport of localisation data and core presentations (B3a)

The certificate machinery (`LocalisationData`, `CorePresentation`, `CoreNormalMomentPresentation`,
`AnalyticCoreDecomposition`) lives on an abstract measurable space. To move chart certificates
(built on `ℝ^d` with `π = id`) onto a genuine resolved space `U` we need two operations:

* **ambient transport** along a measurable map `Ψ : V → U` whose target datum has the same phase
  (pointwise) and observable (a.e. on the chart image, and pointwise on the fibre balls for the
  analytic presentation): `LocalisationData.map`, `CorePresentation.mapAmbient`,
  `CoreNormalMomentPresentation.mapAmbient`, `AnalyticCoreDecomposition.mapAmbient`;
* **base reindexing** along a homeomorphism of base spaces `e : K ≃ₜ K'`:
  `CorePresentation.reindex`, `CoreNormalMomentPresentation.reindex`;
* **change of datum** for a presentation, when two data share phase and observable
  (`CorePresentation.congrData`).

Everything is definitional bookkeeping plus `Measure.map_map`, the product-map identity for the
chart measure and the transport of a.e. statements along measurable equivalences.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Grammar

/-! ### Localisation data -/

section LocData

variable {V U : Type*} [MeasurableSpace V] [MeasurableSpace U]

/-- Transport of a localisation datum along a measurable map, into a phase and an observable on
the target agreeing with the source through `Ψ`. -/
noncomputable def LocalisationData.map (D : LocalisationData V) (Ψ : V → U) (hΨ : Measurable Ψ)
    (phase' obs' : U → ℝ) (hpm : Measurable phase') (hp : ∀ z, phase' (Ψ z) = D.phase z)
    (hom : AEStronglyMeasurable obs' (D.μ.map Ψ)) (ho : ∀ᵐ z ∂D.μ, obs' (Ψ z) = D.obs z) :
    LocalisationData U where
  μ := D.μ.map Ψ
  phase := phase'
  obs := obs'
  phase_measurable := hpm
  phase_nonneg := by
    rw [ae_map_iff hΨ.aemeasurable (measurableSet_le measurable_const hpm)]
    exact D.phase_nonneg.mono fun z hz => by
      change 0 ≤ phase' (Ψ z)
      rw [hp]
      exact hz
  obs_integrable := (integrable_map_measure hom hΨ.aemeasurable).2
    (D.obs_integrable.congr (ho.mono fun z hz => hz.symm))
  δ := D.δ
  δ_pos := D.δ_pos

@[simp] theorem LocalisationData.map_μ (D : LocalisationData V) (Ψ : V → U) (hΨ : Measurable Ψ)
    (phase' obs' : U → ℝ) (hpm) (hp) (hom) (ho) :
    (D.map Ψ hΨ phase' obs' hpm hp hom ho).μ = D.μ.map Ψ := rfl

@[simp] theorem LocalisationData.map_phase (D : LocalisationData V) (Ψ : V → U) (hΨ : Measurable Ψ)
    (phase' obs' : U → ℝ) (hpm) (hp) (hom) (ho) :
    (D.map Ψ hΨ phase' obs' hpm hp hom ho).phase = phase' := rfl

@[simp] theorem LocalisationData.map_obs (D : LocalisationData V) (Ψ : V → U) (hΨ : Measurable Ψ)
    (phase' obs' : U → ℝ) (hpm) (hp) (hom) (ho) :
    (D.map Ψ hΨ phase' obs' hpm hp hom ho).obs = obs' := rfl

end LocData

/-! ### Core presentations: change of datum and ambient transport -/

section Ambient

variable {V U : Type*} [MeasurableSpace V] [MeasurableSpace U] {D : LocalisationData V}
  {target : Measure V} {K : Type*} [TopologicalSpace K] [MeasurableSpace K] {n : ℕ} {β : ℝ}

/-- A core presentation for a datum with the same phase and observable. -/
def CorePresentation.congrData (C : CorePresentation D target K n β) (D' : LocalisationData V)
    (hp : D'.phase = D.phase) (ho : D'.obs = D.obs) : CorePresentation D' target K n β where
  ν := C.ν
  h := C.h
  k := C.k
  k_pos := C.k_pos
  b := C.b
  b_pos := C.b_pos
  Φ := C.Φ
  measurable_Φ := C.measurable_Φ
  c := C.c
  measurable_c := C.measurable_c
  nonneg_c := C.nonneg_c
  x := C.x
  transport := C.transport
  phase_normal := by rw [hp]; exact C.phase_normal
  amplitude_eq := by rw [ho]; exact C.amplitude_eq
  fluct_zero := C.fluct_zero

/-- **Ambient transport of a core presentation** along a measurable map `Ψ`, into a datum `D'`
whose phase agrees with `D`'s through `Ψ` pointwise and whose observable agrees a.e. on the chart
image. The base, exponents, box, density and tangential data are unchanged; the chart map becomes
`Ψ ∘ Φ`. -/
noncomputable def CorePresentation.mapAmbient (C : CorePresentation D target K n β) (Ψ : V → U)
    (hΨ : Measurable Ψ) (D' : LocalisationData U) (hp : ∀ z, D'.phase (Ψ z) = D.phase z)
    (ho : ∀ᵐ q ∂chartMeasure C.ν n C.b, D'.obs (Ψ (C.Φ q)) = D.obs (C.Φ q)) :
    CorePresentation D' (target.map Ψ) K n β where
  ν := C.ν
  h := C.h
  k := C.k
  k_pos := C.k_pos
  b := C.b
  b_pos := C.b_pos
  Φ := Ψ ∘ C.Φ
  measurable_Φ := hΨ.comp C.measurable_Φ
  c := C.c
  measurable_c := C.measurable_c
  nonneg_c := C.nonneg_c
  x := C.x
  transport := by rw [← Measure.map_map hΨ C.measurable_Φ, C.transport]
  phase_normal := C.phase_normal.mono fun q hq => by
    change D'.phase (Ψ (C.Φ q)) = _
    rw [hp]
    exact hq
  amplitude_eq := by
    filter_upwards [C.amplitude_eq, ho] with q h1 h2
    change _ = C.c q * D'.obs (Ψ (C.Φ q))
    rw [h2]
    exact h1
  fluct_zero := C.fluct_zero

theorem CorePresentation.mapAmbient_obsFibre (C : CorePresentation D target K n β) (Ψ : V → U)
    (hΨ : Measurable Ψ) (D' : LocalisationData U) (hp) (ho) (v : K) (u : Fin (n + 1) → ℝ) :
    (C.mapAmbient Ψ hΨ D' hp ho).obsFibre v u = D'.obs (Ψ (C.Φ (v, u))) := rfl

/-- Ambient transport of the normal-moment presentation: the fibre power series are unchanged
when the observables agree on the fibre balls. -/
noncomputable def CoreNormalMomentPresentation.mapAmbient {C : CorePresentation D target K n β}
    (T : CoreNormalMomentPresentation C) (Ψ : V → U) (hΨ : Measurable Ψ) (D' : LocalisationData U)
    (hp : ∀ z, D'.phase (Ψ z) = D.phase z)
    (ho : ∀ᵐ q ∂chartMeasure C.ν n C.b, D'.obs (Ψ (C.Φ q)) = D.obs (C.Φ q))
    (hball : ∀ v, ∀ u ∈ Metric.eball (0 : Fin (n + 1) → ℝ) (T.R v),
      D'.obs (Ψ (C.Φ (v, u))) = D.obs (C.Φ (v, u))) :
    CoreNormalMomentPresentation (C.mapAmbient Ψ hΨ D' hp ho) where
  p := T.p
  R := T.R
  analytic := fun v => (T.analytic v).congr fun u hu => (hball v u hu).symm
  radius := T.radius
  cBound := T.cBound
  c_le := T.c_le

/-- Ambient transport of an analytic core decomposition into a transported datum. -/
noncomputable def AnalyticCoreDecomposition.mapAmbient {M : ℕ} {K : Fin M → Type*}
    [∀ I, TopologicalSpace (K I)] [∀ I, MeasurableSpace (K I)] {n : Fin M → ℕ}
    (A : AnalyticCoreDecomposition D M K n β) (Ψ : V → U) (hΨ : Measurable Ψ)
    (D' : LocalisationData U) (hμ : D'.μ = D.μ.map Ψ) (hp : ∀ z, D'.phase (Ψ z) = D.phase z)
    (ho : ∀ I, ∀ᵐ q ∂chartMeasure (A.chart I).ν (n I) (A.chart I).b,
      D'.obs (Ψ ((A.chart I).Φ q)) = D.obs ((A.chart I).Φ q)) :
    AnalyticCoreDecomposition D' M K n β where
  core := fun I => (A.core I).map Ψ
  tail := A.tail.map Ψ
  measure_eq := by
    rw [hμ, A.measure_eq, Measure.map_add _ _ hΨ]
    congr 1
    induction (Finset.univ : Finset (Fin M)) using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Measure.map_add _ _ hΨ, ih]
  δ₀ := A.δ₀
  δ₀_pos := A.δ₀_pos
  gap := by
    rw [ae_map_iff hΨ.aemeasurable (measurableSet_le measurable_const D'.phase_measurable)]
    exact A.gap.mono fun z hz => by
      change A.δ₀ ≤ D'.phase (Ψ z)
      rw [hp]
      exact hz
  chart := fun I => (A.chart I).mapAmbient Ψ hΨ D' hp (ho I)

end Ambient

/-! ### Base reindexing along a homeomorphism -/

section Reindex

variable {V : Type*} [MeasurableSpace V] {D : LocalisationData V} {target : Measure V}
  {K K' : Type*} [TopologicalSpace K] [MeasurableSpace K] [BorelSpace K] [TopologicalSpace K']
  [MeasurableSpace K'] [BorelSpace K'] {n : ℕ} {β : ℝ}

/-- The product measurable equivalence `e × id` on the chart space. -/
noncomputable def chartEquiv (e : K ≃ₜ K') (n : ℕ) :
    K × (Fin (n + 1) → ℝ) ≃ᵐ K' × (Fin (n + 1) → ℝ) :=
  e.toMeasurableEquiv.prodCongr (MeasurableEquiv.refl _)

theorem chartEquiv_apply (e : K ≃ₜ K') (n : ℕ) (q : K × (Fin (n + 1) → ℝ)) :
    chartEquiv e n q = (e q.1, q.2) := rfl

theorem chartEquiv_symm_apply (e : K ≃ₜ K') (n : ℕ) (q : K' × (Fin (n + 1) → ℝ)) :
    (chartEquiv e n).symm q = (e.symm q.1, q.2) := rfl

@[simp] theorem chartEquiv_fst (e : K ≃ₜ K') (n : ℕ) (q : K × (Fin (n + 1) → ℝ)) :
    (chartEquiv e n q).1 = e q.1 := rfl

@[simp] theorem chartEquiv_snd (e : K ≃ₜ K') (n : ℕ) (q : K × (Fin (n + 1) → ℝ)) :
    (chartEquiv e n q).2 = q.2 := rfl

@[simp] theorem chartEquiv_symm_apply_apply (e : K ≃ₜ K') (n : ℕ) (q : K × (Fin (n + 1) → ℝ)) :
    (chartEquiv e n).symm (chartEquiv e n q) = q := MeasurableEquiv.symm_apply_apply _ _

/-- The chart measure of the pushed base measure is the pushforward of the chart measure. -/
theorem chartMeasure_map (ν : Measure K) [SFinite ν] (e : K ≃ₜ K') (n : ℕ) (b : ℝ) :
    chartMeasure (ν.map e) n b = (chartMeasure ν n b).map (chartEquiv e n) := by
  unfold chartMeasure
  have h := Measure.map_prod_map (μa := ν) (μc := volume.restrict (piBox (n + 1) (Ioc 0 b)))
    e.measurable measurable_id
  rw [Measure.map_id] at h
  rw [h]
  rfl

/-- Pushing a density forward along a measurable equivalence. -/
theorem withDensity_map_equiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (E : α ≃ᵐ β) (g : β → ℝ≥0∞) :
    (μ.map E).withDensity g = (μ.withDensity fun a => g (E a)).map E := by
  ext s hs
  rw [withDensity_apply _ hs, MeasurableEquiv.map_apply, withDensity_apply _ (E.measurable hs),
    Measure.restrict_map E.measurable hs, lintegral_map_equiv]

omit [MeasurableSpace V] in
theorem chartEquiv_symm_comp (e : K ≃ₜ K') (n : ℕ) (f : K × (Fin (n + 1) → ℝ) → V) :
    (fun q => f ((chartEquiv e n).symm q)) ∘ chartEquiv e n = f := by
  funext q
  simp

/-- **Base reindexing of a core presentation** along a homeomorphism of base spaces. -/
noncomputable def CorePresentation.reindex (C : CorePresentation D target K n β) (e : K ≃ₜ K') :
    CorePresentation D target K' n β where
  ν := C.ν.map e
  isFiniteMeasure_ν := Measure.isFiniteMeasure_map _ _
  h := C.h
  k := C.k
  k_pos := C.k_pos
  b := C.b
  b_pos := C.b_pos
  Φ := fun q => C.Φ ((chartEquiv e n).symm q)
  measurable_Φ := C.measurable_Φ.comp (chartEquiv e n).symm.measurable
  c := fun q => C.c ((chartEquiv e n).symm q)
  measurable_c := C.measurable_c.comp (chartEquiv e n).symm.measurable
  nonneg_c := by
    rw [chartMeasure_map, ← MeasurableEquiv.map_ae, eventually_map]
    exact C.nonneg_c.mono fun q hq => by simpa using hq
  x := C.x.comp ⟨e.symm, e.symm.continuous⟩
  transport := by
    rw [chartMeasure_map]
    have h1 : ((chartMeasure C.ν n C.b).map (chartEquiv e n)).withDensity
        (fun q => ((chartDensity C.h (fun q => C.c ((chartEquiv e n).symm q)) q).toNNReal :
          ℝ≥0∞)) =
        ((chartMeasure C.ν n C.b).withDensity fun q =>
          ((chartDensity C.h C.c q).toNNReal : ℝ≥0∞)).map (chartEquiv e n) := by
      rw [withDensity_map_equiv]
      congr 1
      refine congrArg (Measure.withDensity _) (funext fun a => ?_)
      simp [chartDensity]
    rw [h1, Measure.map_map (g := fun q => C.Φ ((chartEquiv e n).symm q))
      (C.measurable_Φ.comp (chartEquiv e n).symm.measurable) (chartEquiv e n).measurable,
      chartEquiv_symm_comp, C.transport]
  phase_normal := by
    rw [chartMeasure_map, ← MeasurableEquiv.map_ae, eventually_map]
    exact C.phase_normal.mono fun q hq => by simpa using hq
  amplitude_eq := by
    rw [chartMeasure_map, ← MeasurableEquiv.map_ae, eventually_map]
    exact C.amplitude_eq.mono fun q hq => by simpa using hq
  fluct_zero := fun v => C.fluct_zero _

theorem CorePresentation.reindex_obsFibre (C : CorePresentation D target K n β) (e : K ≃ₜ K')
    (v : K') : (C.reindex e).obsFibre v = C.obsFibre (e.symm v) := rfl

theorem CorePresentation.reindex_c (C : CorePresentation D target K n β) (e : K ≃ₜ K')
    (q : K' × (Fin (n + 1) → ℝ)) : (C.reindex e).c q = C.c (e.symm q.1, q.2) := rfl

theorem CorePresentation.reindex_Φ (C : CorePresentation D target K n β) (e : K ≃ₜ K')
    (q : K' × (Fin (n + 1) → ℝ)) : (C.reindex e).Φ q = C.Φ (e.symm q.1, q.2) := rfl

theorem CorePresentation.reindex_x (C : CorePresentation D target K n β) (e : K ≃ₜ K') (v : K') :
    (C.reindex e).x v = C.x (e.symm v) := ContinuousMap.comp_apply _ _ _

/-- Base reindexing of the normal-moment presentation. -/
noncomputable def CoreNormalMomentPresentation.reindex {C : CorePresentation D target K n β}
    (T : CoreNormalMomentPresentation C) (e : K ≃ₜ K') :
    CoreNormalMomentPresentation (C.reindex e) where
  p := fun v => T.p (e.symm v)
  R := fun v => T.R (e.symm v)
  analytic := fun v => T.analytic (e.symm v)
  radius := fun v => T.radius (e.symm v)
  cBound := T.cBound
  c_le := fun _ => T.c_le _

end Reindex

end Grammar
