/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.AnalyticCorePresentation

/-!
# The moment representation for core presentations (CCCXVI)

Consult #95, first unit. The library's Taylor–moment representation of the resolved integral
(`AdaptedStrataData.Z_eq_moment_series`) is built on `ChartPresentation`, whose transport identity
targets the sharp sublevel restriction — an interface that product-box charts cannot inhabit for a
phase with a curved sublevel set (`LocalisationObstruction.lean`). The core route
(`CorePresentation`, `AnalyticCoreDecomposition`: cores with arbitrary targets and a tail with a
positive phase gap) has no such obstruction. This unit transfers the moment argument to cores:

* `CorePresentation.obsFibre`, `fibreMeasure` and `CoreNormalMomentPresentation` (analytic fibre
  observable, bounded density), with the fibre Taylor–moment series
  (`integral_obsFibre_eq_tsum`) and the chart identity `tanIntegral = ∫ ∑_r (1/r!)⟨M_r, D^rF⟩ dν`
  (`tanIntegral_eq_moment_series`) — the proofs use only the box, the density and the amplitude
  identity, never the transport target;
* ★★ `AnalyticCoreDecomposition.Z_eq_moment_series`: `Z(N) = ∑_I ∫_{K_I} ∑'_r (1/r!)
  ⟨M_{I,r}(N), D^r(F∘Φ_I)⟩ dν_I + resid(N)` with `|resid(N)| ≤ (∫|F| d tail) e^{−δ₀N}`, and
  `momentSeries_cutoffExpansion`, `expectation_expansion_of_analyticCoreDecomposition` — the
  conditional geometric main theorem for cores;
* the adapters: a chart presentation IS a core presentation for its weighted sublevel target
  (`ChartPresentation.toCore`, `NormalMomentPresentation.toCore`), and adapted strata data give an
  analytic core decomposition whose tail is the complement of the sublevel set
  (`AdaptedStrataData.toCoreDecomposition`; the measure identity `μ = ∑_I μ|_{K<δ}·ρ_I + μ|_{K≥δ}`
  uses `∑ρ_I = 1` a.e. on the sublevel set). So the sublevel-partition interface is a special
  case of the core interface, which becomes the primary certificate interface.

Non-claims: no production of core decompositions from geometry (next units).
-/

open MeasureTheory Set Filter Topology Asymptotics
open scoped ENNReal NNReal

namespace Grammar

open MonoRep CoeffFamily

/-! ### Fibre data of a core presentation -/

namespace CorePresentation

variable {U : Type*} [MeasurableSpace U] {D : LocalisationData U} {target : Measure U}
  {K : Type*} [TopologicalSpace K] [MeasurableSpace K] {n : ℕ} {β : ℝ}
  (C : CorePresentation D target K n β)

/-- The observable in the normal fibre over `v`: `u ↦ F(Φ(v,u))`. -/
def obsFibre (v : K) (u : Fin (n + 1) → ℝ) : ℝ := D.obs (C.Φ (v, u))

/-- The raw fibre measure `|μ|_{v,N} = c(v,u) u^h e^{−βN u^{2k}} du` on the normal box. -/
noncomputable def fibreMeasure (v : K) (N : ℝ) : Measure (Fin (n + 1) → ℝ) :=
  (dressedMeasure n C.h C.k β N C.b).withDensity fun u => ENNReal.ofReal (C.c (v, u))

theorem fibreMeasure_ac (v : K) (N : ℝ) :
    C.fibreMeasure v N ≪ dressedMeasure n C.h C.k β N C.b :=
  withDensity_absolutelyContinuous _ _

theorem fibreMeasure_ae_norm_le (v : K) (N : ℝ) : ∀ᵐ u ∂C.fibreMeasure v N, ‖u‖ ≤ C.b :=
  (C.fibreMeasure_ac v N).ae_le (dressedMeasure_ae_norm_le n C.h C.k β N C.b C.b_pos)

end CorePresentation

/-- A normal-moment presentation of a core: the observable is analytic in the normal fibre on a
ball containing the box, and the density factor is bounded. -/
structure CoreNormalMomentPresentation {U : Type*} [MeasurableSpace U] {D : LocalisationData U}
    {target : Measure U} {K : Type*} [TopologicalSpace K] [MeasurableSpace K] {n : ℕ} {β : ℝ}
    (C : CorePresentation D target K n β) where
  /-- the fibre power series of the observable -/
  p : K → FormalMultilinearSeries ℝ (Fin (n + 1) → ℝ) ℝ
  /-- the fibre radii -/
  R : K → ℝ≥0∞
  analytic : ∀ v, HasFPowerSeriesOnBall (C.obsFibre v) (p v) 0 (R v)
  radius : ∀ v, ENNReal.ofReal C.b < R v
  /-- a bound for the density factor -/
  cBound : ℝ
  c_le : ∀ q, C.c q ≤ cBound

namespace CoreNormalMomentPresentation

variable {U : Type*} [MeasurableSpace U] {D : LocalisationData U} {target : Measure U}
  {K : Type*} [TopologicalSpace K] [MeasurableSpace K] {n : ℕ} {β : ℝ}
  {C : CorePresentation D target K n β} (T : CoreNormalMomentPresentation C)
include T

theorem isFiniteMeasure_fibreMeasure (hβ : 0 ≤ β) {N : ℝ} (hN : 0 ≤ N) (v : K) :
    IsFiniteMeasure (C.fibreMeasure v N) := by
  have := isFiniteMeasure_dressedMeasure n C.h C.k β N C.b hβ hN
  unfold CorePresentation.fibreMeasure
  refine isFiniteMeasure_withDensity (ne_top_of_le_ne_top ?_
    (lintegral_mono fun u => ENNReal.ofReal_le_ofReal (T.c_le (v, u))))
  rw [lintegral_const]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)

theorem integrable_norm_pow_fibre (hβ : 0 ≤ β) {N : ℝ} (hN : 0 ≤ N) (v : K) (r : ℕ) :
    Integrable (fun u => ‖u‖ ^ r) (C.fibreMeasure v N) :=
  haveI := T.isFiniteMeasure_fibreMeasure hβ hN v
  integrable_norm_pow_of_ae_le _ (C.fibreMeasure_ae_norm_le v N) r

/-- The fibre integral of the observable against the raw fibre measure is its Taylor–moment
series. -/
theorem integral_obsFibre_eq_tsum (hβ : 0 ≤ β) {N : ℝ} (hN : 0 ≤ N) (v : K) :
    ∫ u, C.obsFibre v u ∂C.fibreMeasure v N = ∑' r, (r.factorial : ℝ)⁻¹ *
      ∫ u, normalJet (C.obsFibre v) r (fun _ => u) ∂C.fibreMeasure v N := by
  have := T.isFiniteMeasure_fibreMeasure hβ hN v
  exact integral_eq_tsum_moment (T.analytic v) _
    ((C.fibreMeasure_ac v N).ae_le (dressedMeasure_ae_mem_eball C.b_pos (T.radius v)))
    (T.integrable_norm_pow_fibre hβ hN v)
    (summable_norm_mul_integral_of_ae_le _
      ((C.fibreMeasure_ac v N).ae_le (dressedMeasure_ae_norm_le_toNNReal C.b_pos))
      (lt_of_lt_of_le (T.radius v) (T.analytic v).r_le))

/-- **The core integral as a base integral of fibre Taylor–moment series**:
`𝒵(N) = ∫_K ∑_r (1/r!) ⟨Moment_{|μ|_{v,N},r}, D^r(F∘Φ_v)(0)⟩ dν(v)` for `N ≥ 0`. -/
theorem tanIntegral_eq_moment_series (hβ : 0 ≤ β) {N : ℝ} (hN : 0 ≤ N) :
    tanIntegral C.ν n C.h C.k β N C.b C.x = ∫ v, ∑' r, (r.factorial : ℝ)⁻¹ *
      ∫ u, normalJet (C.obsFibre v) r (fun _ => u) ∂C.fibreMeasure v N ∂C.ν := by
  unfold tanIntegral
  have hA := Measure.ae_ae_of_ae_prod (μ := C.ν)
    (ν := volume.restrict (piBox (n + 1) (Ioc 0 C.b))) C.amplitude_eq
  have hc := Measure.ae_ae_of_ae_prod (μ := C.ν)
    (ν := volume.restrict (piBox (n + 1) (Ioc 0 C.b))) C.nonneg_c
  refine integral_congr_ae ?_
  filter_upwards [hA, hc] with v hAv hcv
  have hac : dressedMeasure n C.h C.k β N C.b ≪ volume.restrict (piBox (n + 1) (Ioc 0 C.b)) :=
    withDensity_absolutelyContinuous _ _
  have hmv : Measurable fun u : Fin (n + 1) → ℝ => ENNReal.ofReal (C.c (v, u)) :=
    (C.measurable_c.comp measurable_prodMk_left).ennreal_ofReal
  rw [dataBoxIntegral_eq_integral_dressed n C.h C.k β N C.b (C.x v) (C.fluct_zero v),
    ← T.integral_obsFibre_eq_tsum hβ hN v]
  unfold CorePresentation.fibreMeasure
  rw [integral_withDensity_eq_integral_toReal_smul hmv
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae ?_
  filter_upwards [hac.ae_le hAv, hac.ae_le hcv] with u hu1 hu2
  rw [hu1, ENNReal.toReal_ofReal hu2, smul_eq_mul]
  rfl

end CoreNormalMomentPresentation

/-! ### The assembled statements for cores -/

namespace AnalyticCoreDecomposition

variable {U : Type*} [MeasurableSpace U] {D : LocalisationData U} {M : ℕ} {K : Fin M → Type*}
  [∀ I, TopologicalSpace (K I)] [∀ I, MeasurableSpace (K I)] {n : Fin M → ℕ} {β : ℝ}
  (A : AnalyticCoreDecomposition D M K n β)

/-- ★★ **The core integral as a sum of base integrals of fibre Taylor–moment series** plus the
residual, for `N ≥ 0`. -/
theorem Z_eq_moment_series (T : ∀ I, CoreNormalMomentPresentation (A.chart I)) (hβ : 0 ≤ β)
    {N : ℝ} (hN : 0 ≤ N) :
    D.Z N = ∑ I, (∫ v, ∑' r, (r.factorial : ℝ)⁻¹ *
      ∫ u, normalJet ((A.chart I).obsFibre v) r (fun _ => u) ∂(A.chart I).fibreMeasure v N
        ∂(A.chart I).ν) + A.resid N := by
  rw [A.Z_eq N]
  congr 1
  unfold gInt
  exact Finset.sum_congr rfl fun I _ => (T I).tanIntegral_eq_moment_series hβ hN

variable [∀ I, CompactSpace (K I)] [∀ I, T2Space (K I)] [∀ I, OpensMeasurableSpace (K I)]

/-- **Canonical compatibility for cores**: the moment series has the assembled canonical
coefficients. -/
theorem momentSeries_cutoffExpansion (T : ∀ I, CoreNormalMomentPresentation (A.chart I))
    (hβ : 0 < β) :
    CutoffExpansion (commonQ A.k) (commonD n) (fun N => ∑ I, ∫ v, ∑' r, (r.factorial : ℝ)⁻¹ *
      ∫ u, normalJet ((A.chart I).obsFibre v) r (fun _ => u) ∂(A.chart I).fibreMeasure v N
        ∂(A.chart I).ν) (gCoeff A.ν A.h A.k β A.b A.x) := by
  refine (cutoffExpansion_gInt A.ν A.h A.k β A.b A.k_pos hβ A.b_pos A.x).congr_eventually ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with N hN
  have := A.Z_eq_moment_series T hβ.le hN
  rw [A.Z_eq N] at this
  linarith

/-- **The conditional geometric main theorem for cores**: (i) the power–log cutoff expansion with
the assembled canonical coefficients, (ii) the exponentially small residual (phase gap), (iii) the
Taylor–moment representation, (iv) the moment series carries the same coefficients. -/
theorem expectation_expansion_of_analyticCoreDecomposition
    (T : ∀ I, CoreNormalMomentPresentation (A.chart I)) (hβ : 0 < β) :
    CutoffExpansion (commonQ A.k) (commonD n) D.Z (gCoeff A.ν A.h A.k β A.b A.x) ∧
    (∀ N, 0 ≤ N → |A.resid N| ≤ (∫ z, |D.obs z| ∂A.tail) * Real.exp (-A.δ₀ * N)) ∧
    (∀ N, 0 ≤ N → D.Z N = ∑ I, (∫ v, ∑' r, (r.factorial : ℝ)⁻¹ *
      ∫ u, normalJet ((A.chart I).obsFibre v) r (fun _ => u) ∂(A.chart I).fibreMeasure v N
        ∂(A.chart I).ν) + A.resid N) ∧
    CutoffExpansion (commonQ A.k) (commonD n) (fun N => ∑ I, ∫ v, ∑' r, (r.factorial : ℝ)⁻¹ *
      ∫ u, normalJet ((A.chart I).obsFibre v) r (fun _ => u) ∂(A.chart I).fibreMeasure v N
        ∂(A.chart I).ν) (gCoeff A.ν A.h A.k β A.b A.x) :=
  ⟨A.cutoffExpansion hβ, fun _ hN => A.resid_bound hN,
    fun _ hN => A.Z_eq_moment_series T hβ.le hN, A.momentSeries_cutoffExpansion T hβ⟩

end AnalyticCoreDecomposition

/-! ### The sublevel-partition interface is a special case -/

section Adapters

variable {U : Type*} [MeasurableSpace U] {D : LocalisationData U} {ρ : U → ℝ} {K : Type*}
  [TopologicalSpace K] [MeasurableSpace K] {n : ℕ} {β : ℝ}

/-- A chart presentation is a core presentation for its weighted sublevel target. -/
def ChartPresentation.toCore (C : ChartPresentation D ρ K n β) :
    CorePresentation D ((D.μ.restrict D.sublevel).withDensity fun z =>
      ((ρ z).toNNReal : ℝ≥0∞)) K n β where
  ν := C.ν
  isFiniteMeasure_ν := C.isFiniteMeasure_ν
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
  phase_normal := C.phase_normal
  amplitude_eq := C.amplitude_eq
  fluct_zero := C.fluct_zero

/-- A normal-moment presentation of a chart is one of the associated core. -/
def NormalMomentPresentation.toCore {C : ChartPresentation D ρ K n β}
    (T : NormalMomentPresentation C) : CoreNormalMomentPresentation C.toCore where
  p := T.p
  R := T.R
  analytic := T.analytic
  radius := T.radius
  cBound := T.cBound
  c_le := T.c_le

theorem withDensity_finsetSum {ι : Type*} (s : Finset ι) (μ : Measure U) {f : ι → U → ℝ≥0∞}
    (hf : ∀ i, Measurable (f i)) :
    μ.withDensity (fun z => ∑ i ∈ s, f i z) = ∑ i ∈ s, μ.withDensity (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    have : (fun z => f a z + ∑ i ∈ s, f i z) = f a + fun z => ∑ i ∈ s, f i z := rfl
    rw [this, withDensity_add_left (hf a), ih]

variable {M : ℕ} {K' : Fin M → Type*} [∀ I, TopologicalSpace (K' I)]
  [∀ I, MeasurableSpace (K' I)] {n' : Fin M → ℕ}

/-- ★ **Adapted strata data are an analytic core decomposition**: the cores are the weighted
sublevel restrictions, the tail is the complement of the sublevel set (phase gap `δ`). -/
noncomputable def AdaptedStrataData.toCoreDecomposition (A : AdaptedStrataData D M K' n' β) :
    AnalyticCoreDecomposition D M K' n' β where
  core := fun I => (D.μ.restrict D.sublevel).withDensity fun z =>
    ((A.partition.ρ I z).toNNReal : ℝ≥0∞)
  tail := D.μ.restrict D.sublevelᶜ
  measure_eq := by
    have hmeas : ∀ I, Measurable fun z => ((A.partition.ρ I z).toNNReal : ℝ≥0∞) := fun I =>
      (A.partition.measurable_ρ I).real_toNNReal.coe_nnreal_ennreal
    rw [← withDensity_finsetSum Finset.univ _ hmeas]
    have hone : (fun z => ∑ I, ((A.partition.ρ I z).toNNReal : ℝ≥0∞)) =ᵐ[D.μ.restrict D.sublevel]
        fun _ => (1 : ℝ≥0∞) := by
      have hnn : ∀ᵐ z ∂D.μ.restrict D.sublevel, ∀ I, 0 ≤ A.partition.ρ I z :=
        ae_all_iff.2 fun I => ae_restrict_of_ae (A.partition.nonneg_ρ I)
      filter_upwards [hnn, A.partition.sum_eq_one] with z hz hsum
      have : ∀ I, ((A.partition.ρ I z).toNNReal : ℝ≥0∞) = ENNReal.ofReal (A.partition.ρ I z) :=
        fun I => rfl
      simp_rw [this]
      rw [← ENNReal.ofReal_sum_of_nonneg fun I _ => hz I, hsum, ENNReal.ofReal_one]
    have h1 : (fun _ : U => (1 : ℝ≥0∞)) = 1 := rfl
    rw [withDensity_congr_ae hone, h1, withDensity_one]
    exact (Measure.restrict_add_restrict_compl D.measurableSet_sublevel).symm
  δ₀ := D.δ
  δ₀_pos := D.δ_pos
  gap := by
    rw [ae_restrict_iff' D.measurableSet_sublevel.compl]
    exact Eventually.of_forall fun z hz => not_lt.1 hz
  chart := fun I => (A.chart I).toCore

theorem AdaptedStrataData.toCoreDecomposition_chart (A : AdaptedStrataData D M K' n' β)
    (I : Fin M) : A.toCoreDecomposition.chart I = (A.chart I).toCore := rfl

end Adapters

end Grammar
