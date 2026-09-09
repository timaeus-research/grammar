/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.AnalyticFamilyData
import Grammar.PopulationTangential
import Grammar.FirstNonzeroAsymptotic

/-!
# The public bridge: analytic amplitude families in the stratum theorems (Programme Q, N3, u312)

For an analytic family `F : K → (Fin (n+1) → ℂ) → ℂ` on a compact tangential space (hypotheses of
unit 311: holomorphic on the polydisc of radius `R`, jointly continuous and bounded by `M` on
`K × closedPolydisc r`, `1 < r < R`), the tangential integral of the analytic data is the paper's
stratum integral of the chart population integrals of the real amplitudes `Re F_v`
(`tanIntegral_analyticTangential`), and Theorem A(c) with tangential integration reads
```
∫_K ∫ (Re F_v)(u) u^h e^{-βN u^{2k}} du dν(v) / (N^{-λ}(log N)^{m−1})
      → ∫_K amplitudeCoeff h k λ β (Re F_v) dν(v)              (tanIntegral_analytic_tendsto)
```
with asymptotic equivalence when the integrated face functional is nonzero. A continuous
tangential factor `ρ ∈ C(K, ℝ)` (the paper's cutoff, constant in the normal directions) preserves
the hypotheses (`analyticFamily_smul_*`), with `Re(ρ(v) F_v) = ρ(v) Re F_v`. Only amplitude values
on the closed cube matter (`amplitudeCoeff_congr_closedCube`, `origPhaseIntegral_congr_box`).

Not established: existence of the common holomorphic neighbourhood or of the cutoff; the geometric
origin of `F_v` (chart maps, Jacobians) is external. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology Asymptotics

namespace Grammar

/-- Two amplitudes agreeing on the closed cube have the same face functional. -/
theorem amplitudeCoeff_congr_closedCube {d : ℕ} (h k : Fin d → ℕ) (l β : ℝ)
    {η₁ η₂ : (Fin d → ℝ) → ℝ} (hη : ∀ u ∈ closedCube d, η₁ u = η₂ u) :
    amplitudeCoeff h k l β η₁ = amplitudeCoeff h k l β η₂ := by
  unfold amplitudeCoeff
  congr 1
  refine setIntegral_congr_fun (measurableSet_unitBox d) fun u hu => ?_
  rw [hη _ (faceProj_mapsTo h k l hu)]

/-- Two amplitudes agreeing on the unit box have the same population integral. -/
theorem origPhaseIntegral_congr_box (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N : ℝ)
    {η₁ η₂ : (Fin (n + 1) → ℝ) → ℝ} (hη : ∀ u ∈ unitBox (n + 1), η₁ u = η₂ u) :
    origPhaseIntegral n h k β N 1 (fun _ => 0) η₁ = origPhaseIntegral n h k β N 1 (fun _ => 0) η₂
:= by
  unfold origPhaseIntegral
  have hset : piBox (n + 1) (Ioc (0 : ℝ) 1) = unitBox (n + 1) := rfl
  rw [hset]
  refine setIntegral_congr_fun (measurableSet_unitBox _) fun u hu => ?_
  rw [hη u hu]

variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K] [MeasurableSpace K]
  [OpensMeasurableSpace K] (ν : Measure K) [IsFiniteMeasure ν]

/-- The real amplitude of an analytic family. -/
noncomputable def realAmp {d : ℕ} (F : K → (Fin d → ℂ) → ℂ) (v : K) (u : Fin d → ℝ) : ℝ :=
  (F v fun i => (u i : ℂ)).re

omit [CompactSpace K] [T2Space K] [OpensMeasurableSpace K] [IsFiniteMeasure ν] in
/-- **The tangential integral of analytic data is the stratum integral of the chart population
integrals of `Re F_v`.** -/
theorem tanIntegral_analyticTangential (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N : ℝ) {r R M : ℝ}
    (hr : 0 < r) (hrR : r < R) (h1r : 1 < r) (F : K → (Fin (n + 1) → ℂ) → ℂ)
    (hF : ∀ v, DifferentiableOn ℂ (F v) (openPolydisc (n + 1) R))
    (hFc : ContinuousOn (fun p : K × (Fin (n + 1) → ℂ) => F p.1 p.2)
      (univ ×ˢ closedPolydisc (n + 1) r))
    (hM : ∀ v, ∀ w ∈ closedPolydisc (n + 1) r, ‖F v w‖ ≤ M) :
    tanIntegral ν n h k β N 1 (analyticTangential hr hrR h1r F hF hFc hM) =
      ∫ v, origPhaseIntegral n h k β N 1 (fun _ => 0) (realAmp F v) ∂ν := by
  unfold tanIntegral
  congr 1
  funext v
  rw [analyticTangential_apply, dataBoxIntegral_population n h k β N _
    (xiCoord_analyticDatum hr hrR h1r F hF v)]
  refine origPhaseIntegral_congr_box n h k β N fun u hu => ?_
  exact dataAmplitude_analyticDatum hr hrR h1r F hF v (unitBox_subset_closedCube _ hu)

/-- **Theorem A(c) for an analytic amplitude family on a stratum.** -/
theorem tanIntegral_analytic_tendsto (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (β : ℝ) (hβ : 0 < β) {r R M : ℝ} (hr : 0 < r) (hrR : r < R) (h1r : 1 < r)
    (F : K → (Fin (n + 1) → ℂ) → ℂ) (hF : ∀ v, DifferentiableOn ℂ (F v) (openPolydisc (n + 1) R))
    (hFc : ContinuousOn (fun p : K × (Fin (n + 1) → ℂ) => F p.1 p.2)
      (univ ×ˢ closedPolydisc (n + 1) r))
    (hM : ∀ v, ∀ w ∈ closedPolydisc (n + 1) r, ‖F v w‖ ≤ M) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l) :
    Tendsto (fun N => (∫ v, origPhaseIntegral n h k β N 1 (fun _ => 0) (realAmp F v) ∂ν) /
        (N ^ (-l) * Real.log N ^ (multCount (ratioExp h k) l - 1))) atTop
      (𝓝 (∫ v, amplitudeCoeff h k l β (realAmp F v) ∂ν)) := by
  have hT := tanIntegral_population_tendsto ν n h k hk β hβ
    (analyticTangential hr hrR h1r F hF hFc hM) (xiCoord_analyticTangential hr hrR h1r F hF hFc hM)
    hmin hatt
  have hamp : ∀ v, amplitudeCoeff h k l β (dataAmplitude (analyticTangential hr hrR h1r F hF hFc hM
v)) =
      amplitudeCoeff h k l β (realAmp F v) := fun v =>
    amplitudeCoeff_congr_closedCube h k l β fun u hu => by
      rw [analyticTangential_apply]
      exact dataAmplitude_analyticDatum hr hrR h1r F hF v hu
  simp only [hamp] at hT
  refine hT.congr' (Eventually.of_forall fun N => ?_)
  rw [tanIntegral_analyticTangential ν n h k β N hr hrR h1r F hF hFc hM]

/-- Asymptotic equivalence when the integrated face functional is nonzero. -/
theorem tanIntegral_analytic_isEquivalent (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (β : ℝ) (hβ : 0 < β) {r R M : ℝ} (hr : 0 < r) (hrR : r < R) (h1r : 1 < r)
    (F : K → (Fin (n + 1) → ℂ) → ℂ) (hF : ∀ v, DifferentiableOn ℂ (F v) (openPolydisc (n + 1) R))
    (hFc : ContinuousOn (fun p : K × (Fin (n + 1) → ℂ) => F p.1 p.2)
      (univ ×ˢ closedPolydisc (n + 1) r))
    (hM : ∀ v, ∀ w ∈ closedPolydisc (n + 1) r, ‖F v w‖ ≤ M) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (hA : (∫ v, amplitudeCoeff h k l β (realAmp F v) ∂ν) ≠ 0) :
    (fun N => ∫ v, origPhaseIntegral n h k β N 1 (fun _ => 0) (realAmp F v) ∂ν) ~[atTop]
      fun N => (∫ v, amplitudeCoeff h k l β (realAmp F v) ∂ν) *
        (N ^ (-l) * Real.log N ^ (multCount (ratioExp h k) l - 1)) :=
  isEquivalent_of_tendsto_remainder
    (tanIntegral_analytic_tendsto ν n h k hk β hβ hr hrR h1r F hF hFc hM hmin hatt) hA

omit [CompactSpace K] [T2Space K] [MeasurableSpace K] [OpensMeasurableSpace K] in
/-- **A continuous tangential factor preserves the hypotheses**: holomorphy… -/
theorem analyticFamily_smul_differentiableOn {d : ℕ} {R : ℝ} (ρ : C(K, ℝ))
    (F : K → (Fin d → ℂ) → ℂ) (hF : ∀ v, DifferentiableOn ℂ (F v) (openPolydisc d R)) (v : K) :
    DifferentiableOn ℂ (fun w => ((ρ v : ℝ) : ℂ) * F v w) (openPolydisc d R) :=
  (hF v).const_mul _

omit [CompactSpace K] [T2Space K] [MeasurableSpace K] [OpensMeasurableSpace K] in
/-- …joint continuity… -/
theorem analyticFamily_smul_continuousOn {d : ℕ} {r : ℝ} (ρ : C(K, ℝ))
    (F : K → (Fin d → ℂ) → ℂ)
    (hFc : ContinuousOn (fun p : K × (Fin d → ℂ) => F p.1 p.2) (univ ×ˢ closedPolydisc d r)) :
    ContinuousOn (fun p : K × (Fin d → ℂ) => ((ρ p.1 : ℝ) : ℂ) * F p.1 p.2)
      (univ ×ˢ closedPolydisc d r) :=
  ((Complex.continuous_ofReal.comp (ρ.continuous.comp continuous_fst)).continuousOn).mul hFc

omit [T2Space K] [MeasurableSpace K] [OpensMeasurableSpace K] in
/-- …and the uniform bound (with `‖ρ‖` the sup norm). -/
theorem analyticFamily_smul_bound {d : ℕ} {r M : ℝ} (ρ : C(K, ℝ)) (F : K → (Fin d → ℂ) → ℂ)
    (hM : ∀ v, ∀ w ∈ closedPolydisc d r, ‖F v w‖ ≤ M) (v : K) (w : Fin d → ℂ)
    (hw : w ∈ closedPolydisc d r) : ‖((ρ v : ℝ) : ℂ) * F v w‖ ≤ ‖ρ‖ * M := by
  rw [norm_mul, Complex.norm_real]
  exact mul_le_mul (ρ.norm_coe_le_norm v) (hM v w hw) (norm_nonneg _) (norm_nonneg _)

omit [CompactSpace K] [T2Space K] [MeasurableSpace K] [OpensMeasurableSpace K] in
/-- The real amplitude of the scaled family is the scaled real amplitude. -/
theorem realAmp_smul {d : ℕ} (ρ : C(K, ℝ)) (F : K → (Fin d → ℂ) → ℂ) (v : K) (u : Fin d → ℝ) :
    realAmp (fun v w => ((ρ v : ℝ) : ℂ) * F v w) v u = ρ v * realAmp F v u := by
  simp [realAmp]

end Grammar
