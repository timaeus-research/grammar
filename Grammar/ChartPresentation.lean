/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.Localisation
import Grammar.FirstNonzeroAsymptotic
import Grammar.Flatness

/-!
# Weighted chart presentations and the resolved decomposition

The bridge from a measured localisation datum (`LocalisationData`) to the chart-level standard
integrals of the finite-chart assembly theorems.  A `ChartPresentation` records, for one piece
`ρ` of a finite partition of the sublevel set, a compact base `K` with a finite measure `ν`, a
normal box `(0,b]^{n+1}`, a measurable map `Φ : K × (Fin (n+1) → ℝ) → U`, a density factor `c`,
a tangential datum `x : C(K, DataSpace)` and three certificates:

* **measure transport** — `Φ_*((ν ⊗ vol|_box)·u^h c) = (μ|_{U_δ})·ρ`;
* **exact phase normal form** — `K(Φ(v,u)) = β u^{2k}` a.e.;
* **amplitude realisation** — `η_{x v}(u) = c(v,u) F(Φ(v,u))` a.e., with the evaluation convention
  of `familyPhaseIntegralBox`, and no fluctuation coordinates (`ξ = 0`, the population case).

`chart_integral_eq_tanIntegral` then proves the integral identity
`∫_{U_δ} ρ F e^{−NK} dμ = tanIntegral ν … x N` (transport, then Fubini).  An
`AdaptedStrataData` bundles a finite partition with one presentation per piece; its resolved
decomposition `Z(N) = gInt(N) + tail(N)` with `|tail| ≤ (∫|F|) e^{−δN}` discharges the hypotheses
of the assembled first-nonzero theorem and the flatness theorem (`first_nonzero`, `flat`).

Non-claims: existence of charts, partitions, or normal forms (external geometry); charts with a
positive unit `a(v,u) u^{2k}` are not reduced to exact normal form; no fluctuation term.
-/

open MeasureTheory Set Filter Topology Asymptotics
open scoped NNReal ENNReal

namespace Grammar

open CoeffFamily

/-- The chart parameter measure `ν ⊗ vol|_{(0,b]^{n+1}}`. -/
noncomputable def chartMeasure {K : Type*} [MeasurableSpace K] (ν : Measure K) (n : ℕ) (b : ℝ) :
    Measure (K × (Fin (n + 1) → ℝ)) :=
  ν.prod (volume.restrict (piBox (n + 1) (Ioc 0 b)))

/-- The chart density `u^h c(v,u)`. -/
def chartDensity {K : Type*} {n : ℕ} (h : Fin (n + 1) → ℕ) (c : K × (Fin (n + 1) → ℝ) → ℝ)
    (p : K × (Fin (n + 1) → ℝ)) : ℝ :=
  (∏ i, p.2 i ^ h i) * c p

theorem ae_snd_mem_box {K : Type*} [MeasurableSpace K] (ν : Measure K) [SFinite ν] (n : ℕ)
    (b : ℝ) : ∀ᵐ p ∂chartMeasure ν n b, p.2 ∈ piBox (n + 1) (Ioc 0 b) :=
  Measure.quasiMeasurePreserving_snd.ae
    (ae_restrict_mem (measurableSet_piBox _ _ measurableSet_Ioc))

/-- A weighted chart presentation of the partition piece `ρ` of a localisation datum. -/
structure ChartPresentation {U : Type*} [MeasurableSpace U] (D : LocalisationData U) (ρ : U → ℝ)
    (K : Type*) [TopologicalSpace K] [MeasurableSpace K] (n : ℕ) (β : ℝ) where
  /-- the base measure on the compact stratum piece -/
  ν : Measure K
  [isFiniteMeasure_ν : IsFiniteMeasure ν]
  /-- the normal exponents of the Jacobian -/
  h : Fin (n + 1) → ℕ
  /-- the normal exponents of the phase, all positive -/
  k : Fin (n + 1) → ℕ
  k_pos : ∀ i, 0 < k i
  /-- the box side -/
  b : ℝ
  b_pos : 0 < b
  /-- the chart map into the resolved space -/
  Φ : K × (Fin (n + 1) → ℝ) → U
  measurable_Φ : Measurable Φ
  /-- the smooth density factor (prior, Jacobian unit, cutoff) -/
  c : K × (Fin (n + 1) → ℝ) → ℝ
  measurable_c : Measurable c
  nonneg_c : ∀ᵐ p ∂chartMeasure ν n b, 0 ≤ c p
  /-- the tangential datum realising the amplitude -/
  x : TangentialData K (n + 1)
  transport : ((chartMeasure ν n b).withDensity fun p =>
      ((chartDensity h c p).toNNReal : ENNReal)).map Φ =
    (D.μ.restrict D.sublevel).withDensity fun z => ((ρ z).toNNReal : ENNReal)
  phase_normal : ∀ᵐ p ∂chartMeasure ν n b, D.phase (Φ p) = β * ∏ i, p.2 i ^ (2 * k i)
  amplitude_eq : ∀ᵐ p ∂chartMeasure ν n b, evalF (toEta b (x p.1)) p.2 = c p * D.obs (Φ p)
  fluct_zero : ∀ v, xiCoord (x v) = 0

attribute [instance] ChartPresentation.isFiniteMeasure_ν

theorem toXi_eq_zero {d : ℕ} {b : ℝ} {x : DataSpace d} (hx : xiCoord x = 0) : toXi b x = 0 := by
  funext γ
  have : x (Sum.inl γ) = 0 := congrFun hx γ
  simp [toXi, this]

namespace ChartPresentation

variable {U : Type*} [MeasurableSpace U] {D : LocalisationData U} {ρ : U → ℝ} {K : Type*}
  [TopologicalSpace K] [MeasurableSpace K] {n : ℕ} {β : ℝ} (C : ChartPresentation D ρ K n β)

theorem measurable_chartDensity : Measurable (chartDensity C.h C.c) :=
  (Finset.measurable_prod _ fun i _ =>
    ((measurable_pi_apply i).comp measurable_snd).pow_const _).mul C.measurable_c

theorem chartDensity_nonneg : ∀ᵐ p ∂chartMeasure C.ν n C.b, 0 ≤ chartDensity C.h C.c p := by
  filter_upwards [ae_snd_mem_box C.ν n C.b, C.nonneg_c] with p hp hc
  exact mul_nonneg (Finset.prod_nonneg fun i _ => pow_nonneg (hp i (mem_univ i)).1.le _) hc

/-- The chart-level integrand of `familyPhaseIntegralBox` at the datum `x v`. -/
noncomputable def boxIntegrand (N : ℝ) (p : K × (Fin (n + 1) → ℝ)) : ℝ :=
  evalF (toEta C.b (C.x p.1)) p.2 * (∏ i, p.2 i ^ C.h i) *
    Real.exp (-(β * N * ∏ i, p.2 i ^ (2 * C.k i)) +
      β * (Real.sqrt N * ∏ i, p.2 i ^ C.k i) * evalF (toXi C.b (C.x p.1)) p.2)

theorem integral_boxIntegrand (N : ℝ) (v : K) :
    ∫ u in piBox (n + 1) (Ioc 0 C.b), C.boxIntegrand N (v, u) =
      dataBoxIntegral n C.h C.k β N C.b (C.x v) := rfl

theorem density_smul_eq_boxIntegrand (N : ℝ) :
    ∀ᵐ p ∂chartMeasure C.ν n C.b,
      (chartDensity C.h C.c p).toNNReal • D.integrand N (C.Φ p) = C.boxIntegrand N p := by
  filter_upwards [C.chartDensity_nonneg, C.phase_normal, C.amplitude_eq] with p hq hK hA
  rw [NNReal.smul_def, Real.coe_toNNReal', max_eq_left hq, smul_eq_mul]
  unfold LocalisationData.integrand boxIntegrand chartDensity
  rw [hK, hA, toXi_eq_zero (C.fluct_zero _), evalF_zero, mul_zero, add_zero,
    show -N * (β * ∏ i, p.2 i ^ (2 * C.k i)) = -(β * N * ∏ i, p.2 i ^ (2 * C.k i)) by ring]
  ring

variable [CompactSpace K]

/-- **Chart integral = standard integral**: the weighted contribution of the piece `ρ` to the
localised integral is the tangential standard integral of the chart datum. -/
theorem chart_integral_eq_tanIntegral (hρ : ∀ᵐ z ∂D.μ, 0 ≤ ρ z) (hρm : Measurable ρ) (N : ℝ)
    (hint : Integrable (fun z => ρ z * D.integrand N z) (D.μ.restrict D.sublevel)) :
    ∫ z in D.sublevel, ρ z * D.integrand N z ∂D.μ = tanIntegral C.ν n C.h C.k β N C.b C.x := by
  have hρ' : ∀ᵐ z ∂D.μ.restrict D.sublevel,
      ((ρ z).toNNReal : ℝ≥0) • D.integrand N z = ρ z * D.integrand N z := by
    filter_upwards [ae_restrict_of_ae hρ] with z hz
    rw [NNReal.smul_def, Real.coe_toNNReal', max_eq_left hz, smul_eq_mul]
  have hmeas : AEStronglyMeasurable (D.integrand N)
      ((D.μ.restrict D.sublevel).withDensity fun z => ((ρ z).toNNReal : ENNReal)) :=
    (D.aestronglyMeasurable_integrand N).restrict.mono_ac (withDensity_absolutelyContinuous _ _)
  have h1 : ∫ z in D.sublevel, ρ z * D.integrand N z ∂D.μ =
      ∫ z, D.integrand N z
        ∂((D.μ.restrict D.sublevel).withDensity fun z => ((ρ z).toNNReal : ENNReal)) := by
    rw [integral_withDensity_eq_integral_smul hρm.real_toNNReal]
    exact (integral_congr_ae hρ').symm
  have hint1 : Integrable (D.integrand N)
      ((D.μ.restrict D.sublevel).withDensity fun z => ((ρ z).toNNReal : ENNReal)) := by
    rw [integrable_withDensity_iff_integrable_smul hρm.real_toNNReal]
    exact hint.congr (Filter.EventuallyEq.symm hρ')
  rw [h1]
  rw [← C.transport] at hmeas hint1 ⊢
  rw [integral_map C.measurable_Φ.aemeasurable hmeas,
    integral_withDensity_eq_integral_smul C.measurable_chartDensity.real_toNNReal,
    integral_congr_ae (C.density_smul_eq_boxIntegrand N)]
  have hint2 : Integrable (C.boxIntegrand N) (chartMeasure C.ν n C.b) := by
    have := ((integrable_map_measure hmeas C.measurable_Φ.aemeasurable).1 hint1)
    rw [integrable_withDensity_iff_integrable_smul C.measurable_chartDensity.real_toNNReal] at this
    exact this.congr (C.density_smul_eq_boxIntegrand N)
  unfold chartMeasure at hint2 ⊢
  rw [integral_prod _ hint2]
  rfl

end ChartPresentation

/-! ### Adapted strata data: a finite partition with one chart presentation per piece -/

/-- A finite partition of the sublevel set with a weighted chart presentation of each piece. -/
structure AdaptedStrataData {U : Type*} [MeasurableSpace U] (D : LocalisationData U) (M : ℕ)
    (K : Fin M → Type*) [∀ I, TopologicalSpace (K I)] [∀ I, MeasurableSpace (K I)]
    (n : Fin M → ℕ) (β : ℝ) where
  /-- the finite partition of the sublevel set -/
  partition : D.FiniteSublevelPartition (Fin M)
  /-- the chart presentation of each piece -/
  chart : ∀ I, ChartPresentation D (partition.ρ I) (K I) (n I) β

namespace AdaptedStrataData

variable {U : Type*} [MeasurableSpace U] {D : LocalisationData U} {M : ℕ} {K : Fin M → Type*}
  [∀ I, TopologicalSpace (K I)] [∀ I, MeasurableSpace (K I)] {n : Fin M → ℕ} {β : ℝ}
  (A : AdaptedStrataData D M K n β)

/-- The base measures. -/
noncomputable def ν (I : Fin M) : Measure (K I) := (A.chart I).ν

instance (I : Fin M) : IsFiniteMeasure (A.ν I) := (A.chart I).isFiniteMeasure_ν

/-- The Jacobian exponents. -/
def h (I : Fin M) : Fin (n I + 1) → ℕ := (A.chart I).h

/-- The phase exponents. -/
def k (I : Fin M) : Fin (n I + 1) → ℕ := (A.chart I).k

/-- The box sides. -/
def b (I : Fin M) : ℝ := (A.chart I).b

/-- The joint chart datum. -/
def x : JointData K n := fun I => (A.chart I).x

theorem k_pos : ∀ I i, 0 < A.k I i := fun I => (A.chart I).k_pos

theorem b_pos : ∀ I, 0 < A.b I := fun I => (A.chart I).b_pos

/-- The residual `Z − ∑_I 𝒵^I`, defined for every real `N`. -/
noncomputable def tail (N : ℝ) : ℝ := D.Z N - gInt A.ν A.h A.k β A.b A.x N

theorem Z_eq (N : ℝ) : D.Z N = gInt A.ν A.h A.k β A.b A.x N + A.tail N := by
  unfold tail; ring

variable [∀ I, CompactSpace (K I)]

/-- **The strata decomposition**: for `N ≥ 0` the localised integral is the finite sum of the
chart standard integrals. -/
theorem Zsublevel_eq_gInt {N : ℝ} (hN : 0 ≤ N) : D.Zsublevel N = gInt A.ν A.h A.k β A.b A.x N := by
  rw [A.partition.Zsublevel_eq_sum hN]
  refine Finset.sum_congr rfl fun I _ => ?_
  exact (A.chart I).chart_integral_eq_tanIntegral (A.partition.nonneg_ρ I)
    (A.partition.measurable_ρ I) N (A.partition.integrable_piece I hN)

theorem tail_eq {N : ℝ} (hN : 0 ≤ N) : A.tail N = D.Z N - D.Zsublevel N := by
  rw [tail, A.Zsublevel_eq_gInt hN]

/-- **The residual is exponentially small**: `|tail N| ≤ (∫|F|) e^{−δN}` for `N ≥ 0`. -/
theorem tail_bound {N : ℝ} (hN : 0 ≤ N) :
    |A.tail N| ≤ (∫ z, |D.obs z| ∂D.μ) * Real.exp (-D.δ * N) := by
  rw [A.tail_eq hN]; exact D.localisation_bound hN

theorem tail_tendsto {ε : ℝ} (hεδ : ε < D.δ) :
    Tendsto (fun N => A.tail N * Real.exp (ε * N)) atTop (𝓝 0) :=
  tendsto_mul_exp_of_exp_bound (fun _ hN => A.tail_bound hN) hεδ

variable [∀ I, T2Space (K I)] [∀ I, OpensMeasurableSpace (K I)]

/-- **Conditional geometric main theorem (first nonzero term)**: for a localisation datum with
adapted strata data, the population integral `Z(N) = ∫ F e^{−NK} dμ` is asymptotic to its first
nonzero assembled chart coefficient times `N^{−λ} (log N)^{j}`, provided some assembled coefficient
below some cutoff is nonzero. -/
theorem first_nonzero (hβ : 0 < β) {L : ℝ}
    (hne : ∃ p ∈ indexSet (commonD n) (commonQ A.k) L, gCoeff A.ν A.h A.k β A.b A.x p.1 p.2 ≠ 0) :
    ∃! p : ℝ × ℕ, p ∈ admissible (commonD n) (commonQ A.k) ∧
      gCoeff A.ν A.h A.k β A.b A.x p.1 p.2 ≠ 0 ∧
      (∀ q ∈ admissible (commonD n) (commonQ A.k), precedes q p →
        gCoeff A.ν A.h A.k β A.b A.x q.1 q.2 = 0) ∧
      D.Z ~[atTop] fun N => gCoeff A.ν A.h A.k β A.b A.x p.1 p.2 *
        (N ^ (-p.1) * Real.log N ^ p.2) :=
  population_first_nonzero_assembled_exp A.ν A.h A.k β A.b A.k_pos hβ A.b_pos A.x D.Z A.tail A.Z_eq
    (half_pos D.δ_pos) (A.tail_tendsto (by linarith [D.δ_pos])) hne

/-- **Conditional flatness**: if every assembled coefficient vanishes, `Z(N) = o(N^{−L})` for every
`L`. -/
theorem flat (hβ : 0 < β)
    (hzero : ∀ p ∈ admissible (commonD n) (commonQ A.k), gCoeff A.ν A.h A.k β A.b A.x p.1 p.2 = 0)
    (L : ℝ) : Tendsto (fun N => D.Z N / N ^ (-L)) atTop (𝓝 0) :=
  population_flat_exp A.ν A.h A.k β A.b A.k_pos hβ A.b_pos A.x D.Z A.tail A.Z_eq
    (half_pos D.δ_pos) (A.tail_tendsto (by linarith [D.δ_pos])) hzero L

end AdaptedStrataData

end Grammar
