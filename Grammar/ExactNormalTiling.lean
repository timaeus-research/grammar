/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.PositiveBoxCore
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# The exact-normal tiling interface and the conditional bridge (Astra #68 unit 4b)

The **exact-normal tiling** of a Laplace integral on `Fin d → ℝ` (Astra #68's interface A):
finitely many **tiling pieces**, each a positive box chart in product coordinates
`(Fin t → ℝ) × (Fin (n+1) → ℝ)` carried into the resolved space by a volume-preserving measurable
equivalence, over a compact tangential base — with images inside the integration region, pairwise
disjoint up to null sets, and a positive phase gap `δ₀` off their union (`ExactNormalTiling`).

* A core presentation pulls back and pushes forward along a measurable equivalence
  (`LocalisationData.comapEquiv`, `CorePresentation.mapEquiv`), so every tiling piece exactly
  presents the Lebesgue measure on its image (`TilingPiece.exists_corePresentation`, from
  `PositiveBoxChart.exists_corePresentation`; the image is measurable as the continuous injective
  image of a Borel set).
* **The bridge**: an exact-normal tiling is an analytic core decomposition — the cores are the
  Lebesgue measures of the images, the tail is the rest of the region
  (`ExactNormalTiling.hasAnalyticCoreDecomposition`, via `Measure.restrict_iUnion_ae`) — hence the
  population integral has the full power–log cutoff expansion with the assembled canonical
  coefficients (`cutoffExpansion_of_exactNormalTiling`).

This isolates the remaining geometric obligation exactly: to prove `CompatibleDivisorLocalisation`
one must **inhabit** `ExactNormalTiling` for the cube data from the hironaka charts — the
cross-chart compatibility that the `PartialResolution` readout does not supply (Astra #68).
Non-claims: no inhabitance; the pieces' amplitude data and injectivity certificates are
hypotheses of the interface.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Grammar

open CoeffFamily

/-! ### Transport along a measurable equivalence -/

section Equiv

variable {U U' : Type*} [MeasurableSpace U] [MeasurableSpace U']

/-- The pullback of a localisation datum along a measurable equivalence `e : U' ≃ᵐ U`. -/
noncomputable def LocalisationData.comapEquiv (D : LocalisationData U) (e : U' ≃ᵐ U) :
    LocalisationData U' where
  μ := D.μ.map e.symm
  phase := D.phase ∘ e
  obs := D.obs ∘ e
  phase_measurable := D.phase_measurable.comp e.measurable
  phase_nonneg := by
    rw [← MeasurableEquiv.map_ae, Filter.eventually_map]
    exact D.phase_nonneg.mono fun x hx => by simpa using hx
  obs_integrable := by
    rw [integrable_map_equiv]
    have : (D.obs ∘ e) ∘ e.symm = D.obs := by
      funext x
      simp
    rw [this]
    exact D.obs_integrable
  δ := D.δ
  δ_pos := D.δ_pos

theorem LocalisationData.comapEquiv_phase (D : LocalisationData U) (e : U' ≃ᵐ U) (z : U') :
    (D.comapEquiv e).phase z = D.phase (e z) := rfl

theorem LocalisationData.comapEquiv_obs (D : LocalisationData U) (e : U' ≃ᵐ U) (z : U') :
    (D.comapEquiv e).obs z = D.obs (e z) := rfl

theorem LocalisationData.comapEquiv_μ_map (D : LocalisationData U) (e : U' ≃ᵐ U) :
    (D.comapEquiv e).μ.map e = D.μ := by
  change (D.μ.map e.symm).map e = D.μ
  have := e.symm.map_symm_map (μ := D.μ)
  simp

/-- **Transport of a core presentation along a measurable equivalence**: a presentation of a
target for the pulled-back datum pushes forward to a presentation of the pushed-forward target. -/
noncomputable def CorePresentation.mapEquiv {D : LocalisationData U} (e : U' ≃ᵐ U)
    {target : Measure U'} {K : Type*} [TopologicalSpace K] [MeasurableSpace K] {n : ℕ} {β : ℝ}
    (C : CorePresentation (D.comapEquiv e) target K n β) :
    CorePresentation D (target.map e) K n β := by
  haveI := C.isFiniteMeasure_ν
  exact ⟨C.ν, C.h, C.k, C.k_pos, C.b, C.b_pos, e ∘ C.Φ, e.measurable.comp C.measurable_Φ, C.c,
    C.measurable_c, C.nonneg_c, C.x,
    by rw [← Measure.map_map e.measurable C.measurable_Φ, C.transport],
    C.phase_normal, C.amplitude_eq, C.fluct_zero⟩

end Equiv

/-! ### Tiling pieces -/

variable {d : ℕ}

/-- **A tiling piece**: a positive box chart in product coordinates over a compact tangential
base, carried into the resolved space by a volume-preserving measurable equivalence. -/
structure TilingPiece (D : LocalisationData (Fin d → ℝ)) (β : ℝ) where
  /-- the tangential dimension -/
  t : ℕ
  /-- the normal dimension minus one -/
  n : ℕ
  /-- the product coordinates -/
  e : ((Fin t → ℝ) × (Fin (n + 1) → ℝ)) ≃ᵐ (Fin d → ℝ)
  e_vol : MeasurePreserving e volume volume
  /-- the tangential base -/
  A : Set (Fin t → ℝ)
  A_compact : IsCompact A
  /-- the box side -/
  b : ℝ
  b_pos : 0 < b
  /-- the positive box chart for the pulled-back datum -/
  chart : PositiveBoxChart (D.comapEquiv e) A b β

namespace TilingPiece

variable {D : LocalisationData (Fin d → ℝ)} {β : ℝ} (P : TilingPiece D β)

/-- The box in product coordinates. -/
def box : Set ((Fin P.t → ℝ) × (Fin (P.n + 1) → ℝ)) := P.A ×ˢ piBox (P.n + 1) (Ioc 0 P.b)

/-- The image of the piece in the resolved space. -/
def image : Set (Fin d → ℝ) := P.e '' (P.chart.Ψ '' P.box)

theorem measurableSet_box : MeasurableSet P.box :=
  P.A_compact.isClosed.measurableSet.prod (measurableSet_piBox _ _ measurableSet_Ioc)

theorem measurableSet_chart_image : MeasurableSet (P.chart.Ψ '' P.box) :=
  P.measurableSet_box.image_of_continuousOn_injOn
    (P.chart.contDiffOn.continuousOn.mono P.chart.box_subset) P.chart.injOn

theorem measurableSet_image : MeasurableSet P.image :=
  P.e.measurableSet_image.2 P.measurableSet_chart_image

/-- **A tiling piece exactly presents the Lebesgue measure on its image.** -/
theorem exists_corePresentation :
    Nonempty (CorePresentation D (volume.restrict P.image) P.A P.n β) := by
  obtain ⟨C₀⟩ := P.chart.exists_corePresentation P.A_compact.isClosed.measurableSet
    P.A_compact.measure_lt_top P.b_pos
  have h : (volume.restrict (P.chart.Ψ '' P.box)).map P.e = volume.restrict P.image := by
    rw [image, ← P.e_vol.map_eq, MeasurableEquiv.restrict_map,
      Set.preimage_image_eq _ P.e.injective]
  refine ⟨?_⟩
  rw [← h]
  exact C₀.mapEquiv P.e

end TilingPiece

/-! ### The tiling and the bridge -/

/-- **An exact-normal tiling** of a Laplace integral on the region `Ω`: finitely many tiling
pieces with images inside `Ω`, pairwise disjoint up to null sets, and a positive phase gap off
their union. -/
structure ExactNormalTiling (D : LocalisationData (Fin d → ℝ)) (β : ℝ) where
  /-- the integration region -/
  Ω : Set (Fin d → ℝ)
  μ_eq : D.μ = volume.restrict Ω
  /-- the number of pieces -/
  M : ℕ
  /-- the pieces -/
  piece : Fin M → TilingPiece D β
  image_subset : ∀ I, (piece I).image ⊆ Ω
  aedisjoint : ∀ I J, I ≠ J → volume ((piece I).image ∩ (piece J).image) = 0
  /-- the phase gap off the pieces -/
  δ₀ : ℝ
  δ₀_pos : 0 < δ₀
  gap : ∀ᵐ z ∂D.μ, z ∉ ⋃ I, (piece I).image → δ₀ ≤ D.phase z

namespace ExactNormalTiling

variable {D : LocalisationData (Fin d → ℝ)} {β : ℝ}

/-- **The bridge**: an exact-normal tiling is an analytic core decomposition. -/
theorem hasAnalyticCoreDecomposition (T : ExactNormalTiling D β) :
    HasAnalyticCoreDecomposition D β := by
  classical
  have hmeas : ∀ I, MeasurableSet (T.piece I).image := fun I => (T.piece I).measurableSet_image
  have hU : MeasurableSet (⋃ I, (T.piece I).image) := MeasurableSet.iUnion hmeas
  have hsub : (⋃ I, (T.piece I).image) ⊆ T.Ω := iUnion_subset T.image_subset
  have hsum : volume.restrict (⋃ I, (T.piece I).image) =
      ∑ I, volume.restrict (T.piece I).image := by
    rw [Measure.restrict_iUnion_ae (fun I J hIJ => T.aedisjoint I J hIJ)
      (fun I => (hmeas I).nullMeasurableSet), Measure.sum_fintype]
  have h1 : (volume.restrict T.Ω).restrict (⋃ I, (T.piece I).image) =
      volume.restrict (⋃ I, (T.piece I).image) := by
    rw [Measure.restrict_restrict hU, inter_eq_left.2 hsub]
  have h2 : (volume.restrict T.Ω).restrict (⋃ I, (T.piece I).image)ᶜ =
      volume.restrict (T.Ω \ ⋃ I, (T.piece I).image) := by
    rw [Measure.restrict_restrict hU.compl, sdiff_eq, inter_comm]
  refine ⟨T.M, fun I => (T.piece I).A, fun I => inferInstance, fun I => inferInstance,
    fun I => isCompact_iff_compactSpace.1 (T.piece I).A_compact, fun I => inferInstance,
    fun I => inferInstance, fun I => (T.piece I).n, ⟨⟨fun I => volume.restrict (T.piece I).image,
      volume.restrict (T.Ω \ ⋃ I, (T.piece I).image), ?_, T.δ₀, T.δ₀_pos, ?_,
      fun I => (T.piece I).exists_corePresentation.some⟩⟩⟩
  · rw [T.μ_eq, ← hsum, ← h1, ← h2]
    exact (Measure.restrict_add_restrict_compl hU).symm
  · rw [← h2, ← T.μ_eq, ae_restrict_iff' hU.compl]
    exact T.gap

/-- **The population expansion from an exact-normal tiling**: the Laplace integral has the full
power–log cutoff expansion with the assembled canonical coefficients. -/
theorem cutoffExpansion (T : ExactNormalTiling D β) (hβ : 0 < β) :
    ∃ (Q Dg : ℕ) (c : ℝ → ℕ → ℝ), 0 < Q ∧ CutoffExpansion Q Dg D.Z c :=
  cutoffExpansion_of_hasAnalyticCoreDecomposition hβ T.hasAnalyticCoreDecomposition

end ExactNormalTiling

/-- **The remaining geometric obligation**: exact-normal tilings for all small cubes around a zero
of a real-analytic `K ≥ 0` (with real-analytic observable). Inhabiting this for the cube data from
the hironaka charts is exactly `CompatibleDivisorLocalisation`. -/
def HasExactNormalTilings (d : ℕ) : Prop :=
  ∀ {U : Set (Fin d → ℝ)}, IsOpen U → ∀ {K : (Fin d → ℝ) → ℝ}, AnalyticOnNhd ℝ K U →
    ∀ {w : Fin d → ℝ}, w ∈ U → K w = 0 → (¬ ∀ᶠ x in 𝓝 w, K x = 0) → (∀ x, 0 ≤ K x) →
    ∀ (hK : Measurable K) (hK0 : ∀ x, 0 ≤ K x) {F : (Fin d → ℝ) → ℝ}, AnalyticOnNhd ℝ F U →
    ∀ {β : ℝ}, 0 < β → ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r ≤ r₀ →
      ∀ (hFr : Integrable F (volume.restrict (Metric.closedBall w r))) (δ : ℝ) (hδ : 0 < δ),
        Nonempty (ExactNormalTiling (cubeLocalisationData K F hK hK0 w r hFr δ hδ) β)

/-- **Exact-normal tilings give the compatible divisor localisation.** -/
theorem compatibleDivisorLocalisation_of_hasExactNormalTilings {d : ℕ}
    (h : HasExactNormalTilings d) : CompatibleDivisorLocalisation d := by
  intro U hU K hK w hw hKw hne hK0' hKm hK0 F hF β hβ
  obtain ⟨r₀, hr₀, hr⟩ := h hU hK hw hKw hne hK0' hKm hK0 hF hβ
  refine ⟨r₀, hr₀, fun r hr0 hrr₀ hFr δ hδ => ?_⟩
  obtain ⟨T⟩ := hr r hr0 hrr₀ hFr δ hδ
  exact T.hasAnalyticCoreDecomposition

end Grammar
