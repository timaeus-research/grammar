/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothFamilyIntegral
import Grammar.AnalyticCorePresentation
import Grammar.GeometricMainTheorem

/-!
# Smooth core presentations and decompositions (consult #117 §4–§5, U5)

The smooth analogue of `CorePresentation`/`AnalyticCoreDecomposition`: a `SmoothCorePresentation`
transports the weighted box `S × (0,b]^d` (compact base `S`, base measure `ν`) exactly onto a core
measure with a NONNEGATIVE transport density `ρ` (weight × prior × Jacobian unit), an exact
monomial phase with a continuous positive tangential unit `β(s)`, and a smooth amplitude family
equal a.e. to `ρ · obs ∘ Φ` — no tangential datum, no ℓ¹ coefficient family, no fluctuation
field. ★ `integral_eq`: the core integral of `F e^{−NK}` is the family integral of the smooth
engine. A `SmoothCoreDecomposition` is `μ = ∑ cores + tail` with a phase gap on the tail;
★★★ `SmoothCoreDecomposition.cutoffExpansion : CutoffExpansion commonQ commonD D.Z coeff` with
the integrated canonical coefficients summed over the charts (refined to the common lattice
`∏ 2∏kᵢ`, padded to the common degree `max(dᵢ − 1)`), the tail contributing nothing (exponentially
small). No Taylor or face-integral argument appears here. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology Finset
open scoped ContDiff ENNReal NNReal

namespace Grammar

namespace SmoothEngine

/-! ### Smooth core presentations -/

/-- The chart measure `ν ⊗ vol|_{(0,b]^d}`. -/
noncomputable def smoothChartMeasure {S : Type*} [MeasurableSpace S] (ν : Measure S) (d : ℕ)
    (b : ℝ) : Measure (S × (Fin d → ℝ)) :=
  ν.prod (volume.restrict (box (Fin d) b))

/-- **A smooth core presentation**: the weighted box `S × (0,b]^d` transported exactly onto
`target`, with nonnegative transport density `ρ`, exact monomial phase with tangential unit
`β(s)`, and a smooth amplitude family equal to `ρ · obs ∘ Φ`. -/
structure SmoothCorePresentation {U : Type*} [MeasurableSpace U] (D : LocalisationData U)
    (target : Measure U) (S : Type*) [TopologicalSpace S] [MeasurableSpace S] (d : ℕ) where
  /-- the base measure -/
  ν : Measure S
  [isFiniteMeasure_ν : IsFiniteMeasure ν]
  /-- the Jacobian exponents -/
  h : Fin d → ℕ
  /-- the phase exponents, all positive -/
  k : Fin d → ℕ
  k_pos : ∀ i, 0 < k i
  /-- the box side -/
  b : ℝ
  b_pos : 0 < b
  /-- the tangential phase unit -/
  βf : S → ℝ
  β_cont : Continuous βf
  β_pos : ∀ s, 0 < βf s
  /-- the chart map -/
  Φ : S × (Fin d → ℝ) → U
  measurable_Φ : Measurable Φ
  /-- the nonnegative transport density (weight × prior × Jacobian unit) -/
  ρ : S × (Fin d → ℝ) → ℝ
  measurable_ρ : Measurable ρ
  nonneg_ρ : ∀ᵐ z ∂smoothChartMeasure ν d b, 0 ≤ ρ z
  /-- the smooth amplitude family -/
  amp : SmoothAmplitudeFamily S d b
  amplitude_eq : ∀ᵐ z ∂smoothChartMeasure ν d b, amp z.1 z.2 = ρ z * D.obs (Φ z)
  phase_normal : ∀ᵐ z ∂smoothChartMeasure ν d b,
    D.phase (Φ z) = βf z.1 * mono (fun i => 2 * k i) z.2
  transport : ((smoothChartMeasure ν d b).withDensity fun z =>
    ((mono h z.2 * ρ z).toNNReal : ℝ≥0∞)).map Φ = target

attribute [instance] SmoothCorePresentation.isFiniteMeasure_ν

namespace SmoothCorePresentation

variable {U : Type*} [MeasurableSpace U] {D : LocalisationData U} {target : Measure U}
  {S : Type*} [TopologicalSpace S] [MeasurableSpace S] {d : ℕ}
  (C : SmoothCorePresentation D target S d)

theorem measurable_density : Measurable fun z : S × (Fin d → ℝ) => mono C.h z.2 * C.ρ z :=
  ((measurable_mono C.h).comp measurable_snd).mul C.measurable_ρ

/-- Almost every chart point has its box coordinates in `(0,b]^d`. -/
theorem ae_snd_mem_box : ∀ᵐ z ∂smoothChartMeasure C.ν d C.b, z.2 ∈ box (Fin d) C.b := by
  unfold smoothChartMeasure
  rw [← Measure.restrict_univ (μ := C.ν), Measure.prod_restrict]
  exact (ae_restrict_mem (MeasurableSet.univ.prod (measurableSet_box C.b))).mono fun z hz => hz.2

/-- The box integrand of the smooth engine. -/
noncomputable def boxIntegrand (N : ℝ) (z : S × (Fin d → ℝ)) : ℝ :=
  C.amp z.1 z.2 * mono C.h z.2 * exp (-(N * C.βf z.1) * mono (fun i => 2 * C.k i) z.2)

theorem density_smul_eq_boxIntegrand (N : ℝ) : ∀ᵐ z ∂smoothChartMeasure C.ν d C.b,
    (mono C.h z.2 * C.ρ z).toNNReal • D.integrand N (C.Φ z) = C.boxIntegrand N z := by
  filter_upwards [C.nonneg_ρ, C.phase_normal, C.amplitude_eq, C.ae_snd_mem_box] with z hρ hK hA hz
  have hmh : 0 ≤ mono C.h z.2 := (mono_pos C.h (pos_of_mem_box hz)).le
  rw [NNReal.smul_def, Real.coe_toNNReal', max_eq_left (mul_nonneg hmh hρ), smul_eq_mul]
  unfold LocalisationData.integrand boxIntegrand
  rw [hK, hA, show -N * (C.βf z.1 * mono (fun i => 2 * C.k i) z.2) =
    -(N * C.βf z.1) * mono (fun i => 2 * C.k i) z.2 by ring]
  ring

/-- ★ **Core integral = family integral**: the integral of `F e^{−NK}` against the core measure is
the smooth engine's family integral. -/
theorem integral_eq (N : ℝ) (hint : Integrable (D.integrand N) target) :
    ∫ z, D.integrand N z ∂target = familyIntegral C.ν C.amp C.h C.k C.βf C.b N := by
  have hmeas : AEStronglyMeasurable (D.integrand N) target := hint.aestronglyMeasurable
  rw [← C.transport] at hmeas hint
  have hdens := C.measurable_density.real_toNNReal
  have key : ∫ z, D.integrand N z ∂(((smoothChartMeasure C.ν d C.b).withDensity fun z =>
      ((mono C.h z.2 * C.ρ z).toNNReal : ℝ≥0∞)).map C.Φ) =
      familyIntegral C.ν C.amp C.h C.k C.βf C.b N := by
    rw [integral_map C.measurable_Φ.aemeasurable hmeas,
      integral_withDensity_eq_integral_smul hdens,
      integral_congr_ae (C.density_smul_eq_boxIntegrand N)]
    have hint2 : Integrable (C.boxIntegrand N) (smoothChartMeasure C.ν d C.b) := by
      have := ((integrable_map_measure hmeas C.measurable_Φ.aemeasurable).1 hint)
      rw [integrable_withDensity_iff_integrable_smul hdens] at this
      exact this.congr (C.density_smul_eq_boxIntegrand N)
    unfold smoothChartMeasure at hint2 ⊢
    rw [integral_prod _ hint2]
    rfl
  rwa [C.transport] at key

/-- The chart's expansion (a continuous positive tangential unit). -/
theorem cutoffExpansion [CompactSpace S] [FirstCountableTopology S] [OpensMeasurableSpace S] :
    CutoffExpansion (Qamb C.k) (d - 1) (familyIntegral C.ν C.amp C.h C.k C.βf C.b)
      (familyCoeff C.ν C.amp C.h C.k C.βf C.b) :=
  cutoffExpansion_integral_beta C.ν C.amp C.k_pos C.b_pos C.β_cont C.β_pos

/-- The integrated coefficients vanish off the chart lattice. -/
theorem familyCoeff_eq_zero_of_not_lattice {μ : ℝ} (hμ : ∀ m : ℕ, μ ≠ (m : ℝ) / Qamb C.k)
    (q : ℕ) : familyCoeff C.ν C.amp C.h C.k C.βf C.b μ q = 0 := by
  unfold familyCoeff
  simp [smoothCoeff_eq_zero_of_not_lattice C.k_pos (C.β_pos _) C.b_pos hμ]

/-- The integrated coefficients vanish above the chart degree. -/
theorem familyCoeff_eq_zero_of_degree_gt {μ : ℝ} {q : ℕ} (hq : d - 1 < q) :
    familyCoeff C.ν C.amp C.h C.k C.βf C.b μ q = 0 := by
  unfold familyCoeff
  simp [smoothCoeff_eq_zero_of_degree_gt (F := C.amp _) (h := C.h) (k := C.k) (β := C.βf _)
    (b := C.b) hq]

end SmoothCorePresentation

/-! ### Smooth core decompositions -/

/-- **A smooth core decomposition** of a localisation datum: `μ = ∑_I core_I + tail`, every core
carried exactly by a smooth core presentation, and a positive phase gap on the tail. -/
structure SmoothCoreDecomposition {U : Type*} [MeasurableSpace U] (D : LocalisationData U)
    (M : ℕ) (S : Fin M → Type*) [∀ I, TopologicalSpace (S I)] [∀ I, MeasurableSpace (S I)]
    (dim : Fin M → ℕ) where
  /-- the core measures -/
  core : Fin M → Measure U
  /-- the tail measure -/
  tail : Measure U
  measure_eq : D.μ = ∑ I, core I + tail
  /-- the phase gap on the tail -/
  δ₀ : ℝ
  δ₀_pos : 0 < δ₀
  gap : ∀ᵐ z ∂tail, δ₀ ≤ D.phase z
  /-- the smooth core presentations -/
  chart : ∀ I, SmoothCorePresentation D (core I) (S I) (dim I)

namespace SmoothCoreDecomposition

variable {U : Type*} [MeasurableSpace U] {D : LocalisationData U} {M : ℕ} {S : Fin M → Type*}
  [∀ I, TopologicalSpace (S I)] [∀ I, MeasurableSpace (S I)] {dim : Fin M → ℕ}
  (A : SmoothCoreDecomposition D M S dim)

/-- The common lattice denominator `∏_I 2∏ᵢ k_{I,i}`. -/
def commonQ : ℕ := ∏ I, Qamb (A.chart I).k

/-- The common logarithmic degree `max_I (dim I − 1)`. -/
def commonD (_A : SmoothCoreDecomposition D M S dim) : ℕ := Finset.univ.sup fun I => dim I - 1

theorem commonQ_pos : 0 < A.commonQ :=
  Finset.prod_pos fun I _ => Qamb_pos _ (A.chart I).k_pos

theorem Qamb_dvd_commonQ (I : Fin M) : Qamb (A.chart I).k ∣ A.commonQ :=
  Finset.dvd_prod_of_mem _ (Finset.mem_univ I)

theorem le_commonD (I : Fin M) : dim I - 1 ≤ A.commonD :=
  Finset.le_sup (f := fun I => dim I - 1) (Finset.mem_univ I)

/-- The chart integrals. -/
noncomputable def chartInt (I : Fin M) (N : ℝ) : ℝ :=
  familyIntegral (A.chart I).ν (A.chart I).amp (A.chart I).h (A.chart I).k (A.chart I).βf
    (A.chart I).b N

/-- ★ **The global smooth coefficients**: the sum over the charts of the integrated canonical
coefficients. -/
noncomputable def coeff (μ : ℝ) (q : ℕ) : ℝ :=
  ∑ I, familyCoeff (A.chart I).ν (A.chart I).amp (A.chart I).h (A.chart I).k (A.chart I).βf
    (A.chart I).b μ q

theorem core_le (I : Fin M) : A.core I ≤ D.μ := by
  rw [A.measure_eq]
  exact (Finset.single_le_sum (fun J _ => Measure.zero_le (A.core J)) (Finset.mem_univ I)).trans
    (Measure.le_add_right le_rfl)

theorem tail_le : A.tail ≤ D.μ := by
  rw [A.measure_eq]
  exact Measure.le_add_left le_rfl

/-- The tail integral. -/
noncomputable def tailInt (N : ℝ) : ℝ := ∫ z, D.integrand N z ∂A.tail

/-- **The core decomposition of the population integral**: for `N ≥ 0`,
`Z(N) = ∑_I Z_I(N) + ∫ F e^{−NK} d tail`. -/
theorem Z_eq {N : ℝ} (hN : 0 ≤ N) : D.Z N = ∑ I, A.chartInt I N + A.tailInt N := by
  have hint := D.integrable_integrand hN
  unfold LocalisationData.Z
  have hcores : ∑ I, A.core I ≤ D.μ := by
    rw [A.measure_eq]
    exact Measure.le_add_right le_rfl
  rw [A.measure_eq, integral_add_measure (hint.mono_measure hcores) (hint.mono_measure A.tail_le),
    integral_finsetSum_measure fun I _ => hint.mono_measure (A.core_le I)]
  unfold chartInt tailInt
  congr 1
  exact Finset.sum_congr rfl fun I _ =>
    (A.chart I).integral_eq N (hint.mono_measure (A.core_le I))

/-- **The tail is exponentially small.** -/
theorem tailInt_bound {N : ℝ} (hN : 0 ≤ N) :
    |A.tailInt N| ≤ (∫ z, |D.obs z| ∂A.tail) * exp (-A.δ₀ * N) := by
  have hobs : Integrable D.obs A.tail := D.obs_integrable.mono_measure A.tail_le
  have hbound : ∀ᵐ z ∂A.tail, ‖D.integrand N z‖ ≤ |D.obs z| * exp (-A.δ₀ * N) := by
    filter_upwards [A.gap] with z hz
    unfold LocalisationData.integrand
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs (exp _), abs_of_pos (exp_pos _)]
    exact mul_le_mul_of_nonneg_left (exp_le_exp.2 (by nlinarith)) (abs_nonneg _)
  have := norm_integral_le_of_norm_le (hobs.norm.mul_const _) hbound
  rw [Real.norm_eq_abs] at this
  refine this.trans (le_of_eq ?_)
  rw [integral_mul_const]
  simp only [Real.norm_eq_abs]

theorem tailInt_tendsto {ε : ℝ} (hε : ε < A.δ₀) :
    Tendsto (fun N => A.tailInt N * exp (ε * N)) atTop (𝓝 0) :=
  tendsto_mul_exp_of_exp_bound (fun _ hN => A.tailInt_bound hN) hε

/-- The residual `Z − ∑_I Z_I`, defined for every real `N`. -/
noncomputable def resid (N : ℝ) : ℝ := D.Z N - ∑ I, A.chartInt I N

theorem resid_eq {N : ℝ} (hN : 0 ≤ N) : A.resid N = A.tailInt N := by
  rw [resid, A.Z_eq hN]; ring

theorem resid_tendsto {ε : ℝ} (hε : ε < A.δ₀) :
    Tendsto (fun N => A.resid N * exp (ε * N)) atTop (𝓝 0) :=
  tendsto_mul_exp_of_exp_bound (fun _ hN => by rw [A.resid_eq hN]; exact A.tailInt_bound hN) hε

/-- The global coefficients are supported on the common lattice and degree. -/
theorem coeff_eq_zero_of_not_lattice {μ : ℝ} (hμ : ∀ m : ℕ, μ ≠ (m : ℝ) / A.commonQ) (q : ℕ) :
    A.coeff μ q = 0 := by
  unfold coeff
  refine Finset.sum_eq_zero fun I _ => (A.chart I).familyCoeff_eq_zero_of_not_lattice ?_ q
  intro m hm
  obtain ⟨r, hr⟩ := A.Qamb_dvd_commonQ I
  apply hμ (m * r)
  have hQ : (0 : ℝ) < Qamb (A.chart I).k := by exact_mod_cast Qamb_pos _ (A.chart I).k_pos
  have hr0 : (0 : ℝ) < r := by
    have : 0 < Qamb (A.chart I).k * r := hr ▸ A.commonQ_pos
    exact_mod_cast Nat.pos_of_mul_pos_left this
  rw [hm, hr]
  push_cast
  field_simp

theorem coeff_eq_zero_of_degree_gt {μ : ℝ} {q : ℕ} (hq : A.commonD < q) : A.coeff μ q = 0 := by
  unfold coeff
  exact Finset.sum_eq_zero fun I _ =>
    (A.chart I).familyCoeff_eq_zero_of_degree_gt (lt_of_le_of_lt (A.le_commonD I) hq)

variable [∀ I, CompactSpace (S I)] [∀ I, FirstCountableTopology (S I)]
  [∀ I, OpensMeasurableSpace (S I)]

/-- Each chart's expansion on the common lattice and degree. -/
theorem chart_cutoffExpansion (I : Fin M) :
    CutoffExpansion A.commonQ A.commonD (A.chartInt I)
      (familyCoeff (A.chart I).ν (A.chart I).amp (A.chart I).h (A.chart I).k (A.chart I).βf
        (A.chart I).b) :=
  ((A.chart I).cutoffExpansion.refine (Qamb_pos _ (A.chart I).k_pos) A.commonQ_pos
    (A.Qamb_dvd_commonQ I) fun _ hμ j => (A.chart I).familyCoeff_eq_zero_of_not_lattice hμ j).pad
    (A.le_commonD I) fun _ _ hj => (A.chart I).familyCoeff_eq_zero_of_degree_gt hj

/-- ★★★ **The smooth core decomposition theorem**: the population integral is a cutoff expansion
on the common lattice with the global smooth coefficients. -/
theorem cutoffExpansion : CutoffExpansion A.commonQ A.commonD D.Z A.coeff := by
  have hsum := CutoffExpansion.sum Finset.univ fun I _ => A.chart_cutoffExpansion I
  have htail := cutoffExpansion_of_exp_small A.commonQ A.commonD (half_pos A.δ₀_pos)
    (A.resid_tendsto (by linarith [A.δ₀_pos]))
  have h := hsum.add htail
  have hZ : (fun N => ∑ I, A.chartInt I N + A.resid N) = D.Z := funext fun N => by
    unfold resid; ring
  have hc : (fun μ j => ∑ I, familyCoeff (A.chart I).ν (A.chart I).amp (A.chart I).h
      (A.chart I).k (A.chart I).βf (A.chart I).b μ j + 0) = A.coeff := funext fun _ =>
    funext fun _ => by simp [coeff]
  rw [hZ, hc] at h
  exact h

end SmoothCoreDecomposition

end SmoothEngine

end Grammar
