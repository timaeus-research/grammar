import Grammar.GeometricMainTheorem

/-!
# Analytic core presentations: exact box transport onto a core measure (Astra #67 unit 1)

`ChartPresentation` transports a weighted box onto the **sharp sublevel restriction**
`(μ|_{K<δ})·ρ`, and `LocalisationObstruction.lean` records why a chart-exact analytic amplitude
cannot absorb such a cutoff. This module separates the integration certificate from the geometry:

* a **core presentation** (`CorePresentation D target K n β`) is a `ChartPresentation` whose
  transport identity targets an arbitrary measure `target` on the resolved space — no sublevel
  restriction, no weight — with the same exact monomial phase and analytic amplitude clauses; its
  integral is the tangential standard integral (`CorePresentation.integral_eq_tanIntegral`);
* an **analytic core decomposition** (`AnalyticCoreDecomposition D M K n β`) splits the resolved
  measure as `μ = ∑_I core_I + tail` with a core presentation of every `core_I` and a **positive
  phase gap** `δ₀ ≤ K` almost everywhere on `tail`; then `Z(N) = gInt(N) + tail(N)` with
  `|tail(N)| ≤ (∫|F| d tail) e^{−δ₀N}` (`Z_eq`, `tail_bound`), and the assembled theorems follow:
  the first nonzero term (`first_nonzero`), flatness (`flat`), and the cutoff expansion with the
  assembled canonical coefficients (`cutoffExpansion`, `expansion`) — the same conclusions as for
  `AdaptedStrataData`, now from a certificate that the geometry can hope to supply.

The **compatible divisor localisation statement** (`HasAnalyticCoreDecomposition`,
`CompatibleDivisorLocalisation`) records, as a proposition, the existence theorem that the
geometric units (Astra #67 units 2–7) must prove: every localisation datum of a real-analytic
nonnegative phase on a small closed cube around a zero admits an analytic core decomposition.
`cutoffExpansion_of_hasAnalyticCoreDecomposition` shows that this statement is exactly what the
population expansion needs. Nothing here asserts that it holds.

Non-claims: no geometry (no charts, no partition of unity, no normal form are constructed); the
moment-series canonical compatibility of `NormalMomentPresentation` is not restated for cores.
-/

open MeasureTheory Filter Topology Set Asymptotics
open scoped ENNReal NNReal

namespace Grammar

/-! ### Core presentations -/

/-- **A core presentation**: a weighted box `(K × (0,b]^{n+1}, ν ⊗ du · u^h c)` transported exactly
onto a measure `target` on the resolved space, with exact monomial phase and analytic amplitude. -/
structure CorePresentation {U : Type*} [MeasurableSpace U] (D : LocalisationData U)
    (target : Measure U) (K : Type*) [TopologicalSpace K] [MeasurableSpace K] (n : ℕ) (β : ℝ)
    where
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
  /-- the density factor (prior, Jacobian unit, tangential cutoff) -/
  c : K × (Fin (n + 1) → ℝ) → ℝ
  measurable_c : Measurable c
  nonneg_c : ∀ᵐ p ∂chartMeasure ν n b, 0 ≤ c p
  /-- the tangential datum realising the amplitude -/
  x : TangentialData K (n + 1)
  transport : ((chartMeasure ν n b).withDensity fun p =>
      ((chartDensity h c p).toNNReal : ENNReal)).map Φ = target
  phase_normal : ∀ᵐ p ∂chartMeasure ν n b, D.phase (Φ p) = β * ∏ i, p.2 i ^ (2 * k i)
  amplitude_eq : ∀ᵐ p ∂chartMeasure ν n b,
    CoeffFamily.evalF (toEta b (x p.1)) p.2 = c p * D.obs (Φ p)
  fluct_zero : ∀ v, xiCoord (x v) = 0

attribute [instance] CorePresentation.isFiniteMeasure_ν

namespace CorePresentation

variable {U : Type*} [MeasurableSpace U] {D : LocalisationData U} {target : Measure U}
  {K : Type*} [TopologicalSpace K] [MeasurableSpace K] {n : ℕ} {β : ℝ}
  (C : CorePresentation D target K n β)

theorem measurable_chartDensity : Measurable (chartDensity C.h C.c) :=
  (Finset.measurable_prod _ fun i _ =>
    ((measurable_pi_apply i).comp measurable_snd).pow_const _).mul C.measurable_c

theorem chartDensity_nonneg : ∀ᵐ p ∂chartMeasure C.ν n C.b, 0 ≤ chartDensity C.h C.c p := by
  filter_upwards [ae_snd_mem_box C.ν n C.b, C.nonneg_c] with p hp hc
  exact mul_nonneg (Finset.prod_nonneg fun i _ => pow_nonneg (hp i (mem_univ i)).1.le _) hc

/-- The chart-level integrand of `familyPhaseIntegralBox` at the datum `x v`. -/
noncomputable def boxIntegrand (N : ℝ) (p : K × (Fin (n + 1) → ℝ)) : ℝ :=
  CoeffFamily.evalF (toEta C.b (C.x p.1)) p.2 * (∏ i, p.2 i ^ C.h i) *
    Real.exp (-(β * N * ∏ i, p.2 i ^ (2 * C.k i)) +
      β * (Real.sqrt N * ∏ i, p.2 i ^ C.k i) * CoeffFamily.evalF (toXi C.b (C.x p.1)) p.2)

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

/-- **Core integral = standard integral**: the integral of `F e^{−NK}` against the core measure is
the tangential standard integral of the chart datum. -/
theorem integral_eq_tanIntegral (N : ℝ) (hint : Integrable (D.integrand N) target) :
    ∫ z, D.integrand N z ∂target = tanIntegral C.ν n C.h C.k β N C.b C.x := by
  have hmeas : AEStronglyMeasurable (D.integrand N) target := hint.aestronglyMeasurable
  rw [← C.transport] at hmeas hint
  have key : ∫ z, D.integrand N z ∂(((chartMeasure C.ν n C.b).withDensity fun p =>
      ((chartDensity C.h C.c p).toNNReal : ENNReal)).map C.Φ) =
      tanIntegral C.ν n C.h C.k β N C.b C.x := by
    rw [integral_map C.measurable_Φ.aemeasurable hmeas,
      integral_withDensity_eq_integral_smul C.measurable_chartDensity.real_toNNReal,
      integral_congr_ae (C.density_smul_eq_boxIntegrand N)]
    have hint2 : Integrable (C.boxIntegrand N) (chartMeasure C.ν n C.b) := by
      have := ((integrable_map_measure hmeas C.measurable_Φ.aemeasurable).1 hint)
      rw [integrable_withDensity_iff_integrable_smul C.measurable_chartDensity.real_toNNReal]
        at this
      exact this.congr (C.density_smul_eq_boxIntegrand N)
    unfold chartMeasure at hint2 ⊢
    rw [integral_prod _ hint2]
    rfl
  rwa [C.transport] at key

end CorePresentation

/-! ### Analytic core decompositions -/

/-- **An analytic core decomposition** of a localisation datum: `μ = ∑_I core_I + tail`, every
core carried exactly by a core presentation, and a positive phase gap on the tail. -/
structure AnalyticCoreDecomposition {U : Type*} [MeasurableSpace U] (D : LocalisationData U)
    (M : ℕ) (K : Fin M → Type*) [∀ I, TopologicalSpace (K I)] [∀ I, MeasurableSpace (K I)]
    (n : Fin M → ℕ) (β : ℝ) where
  /-- the core measures -/
  core : Fin M → Measure U
  /-- the tail measure -/
  tail : Measure U
  measure_eq : D.μ = ∑ I, core I + tail
  /-- the phase gap on the tail -/
  δ₀ : ℝ
  δ₀_pos : 0 < δ₀
  gap : ∀ᵐ z ∂tail, δ₀ ≤ D.phase z
  /-- the core presentations -/
  chart : ∀ I, CorePresentation D (core I) (K I) (n I) β

namespace AnalyticCoreDecomposition

variable {U : Type*} [MeasurableSpace U] {D : LocalisationData U} {M : ℕ} {K : Fin M → Type*}
  [∀ I, TopologicalSpace (K I)] [∀ I, MeasurableSpace (K I)] {n : Fin M → ℕ} {β : ℝ}
  (A : AnalyticCoreDecomposition D M K n β)

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

theorem core_le (I : Fin M) : A.core I ≤ D.μ := by
  rw [A.measure_eq]
  exact (Finset.single_le_sum (fun J _ => Measure.zero_le (A.core J)) (Finset.mem_univ I)).trans
    (Measure.le_add_right le_rfl)

theorem tail_le : A.tail ≤ D.μ := by
  rw [A.measure_eq]
  exact Measure.le_add_left le_rfl

/-- The tail integral `∫ F e^{−NK} d tail`. -/
noncomputable def tailInt (N : ℝ) : ℝ := ∫ z, D.integrand N z ∂A.tail

/-- The residual `Z − ∑_I 𝒵^I`, defined for every real `N`. -/
noncomputable def resid (N : ℝ) : ℝ := D.Z N - gInt A.ν A.h A.k β A.b A.x N

theorem Z_eq (N : ℝ) : D.Z N = gInt A.ν A.h A.k β A.b A.x N + A.resid N := by
  unfold resid; ring

variable [∀ I, CompactSpace (K I)]

/-- **The core decomposition of the population integral**: for `N ≥ 0`,
`Z(N) = ∑_I 𝒵^I(N) + ∫ F e^{−NK} d tail`. -/
theorem Z_eq_gInt_add_tailInt {N : ℝ} (hN : 0 ≤ N) :
    D.Z N = gInt A.ν A.h A.k β A.b A.x N + A.tailInt N := by
  have hint := D.integrable_integrand hN
  unfold LocalisationData.Z
  have hcores : ∑ I, A.core I ≤ D.μ := by
    rw [A.measure_eq]
    exact Measure.le_add_right le_rfl
  rw [A.measure_eq, integral_add_measure (hint.mono_measure hcores) (hint.mono_measure A.tail_le),
    integral_finsetSum_measure fun I _ => hint.mono_measure (A.core_le I)]
  unfold gInt tailInt
  congr 1
  exact Finset.sum_congr rfl fun I _ =>
    (A.chart I).integral_eq_tanIntegral N (hint.mono_measure (A.core_le I))

theorem resid_eq {N : ℝ} (hN : 0 ≤ N) : A.resid N = A.tailInt N := by
  rw [resid, A.Z_eq_gInt_add_tailInt hN]; ring

omit [∀ I, CompactSpace (K I)] in
/-- **The tail is exponentially small**: `|∫ F e^{−NK} d tail| ≤ (∫ |F| d tail) e^{−δ₀N}` for
`N ≥ 0`, by the phase gap. -/
theorem tailInt_bound {N : ℝ} (hN : 0 ≤ N) :
    |A.tailInt N| ≤ (∫ z, |D.obs z| ∂A.tail) * Real.exp (-A.δ₀ * N) := by
  have hobs : Integrable D.obs A.tail := D.obs_integrable.mono_measure A.tail_le
  have hbound : ∀ᵐ z ∂A.tail, ‖D.integrand N z‖ ≤ |D.obs z| * Real.exp (-A.δ₀ * N) := by
    filter_upwards [A.gap] with z hz
    unfold LocalisationData.integrand
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs (Real.exp _), abs_of_pos (Real.exp_pos _)]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (abs_nonneg _)
    nlinarith
  unfold tailInt
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le (hobs.norm.mul_const _) hbound).trans (le_of_eq ?_)
  rw [integral_mul_const]
  simp only [Real.norm_eq_abs]

theorem resid_bound {N : ℝ} (hN : 0 ≤ N) :
    |A.resid N| ≤ (∫ z, |D.obs z| ∂A.tail) * Real.exp (-A.δ₀ * N) := by
  rw [A.resid_eq hN]; exact A.tailInt_bound hN

theorem resid_tendsto {ε : ℝ} (hε : ε < A.δ₀) :
    Tendsto (fun N => A.resid N * Real.exp (ε * N)) atTop (𝓝 0) :=
  tendsto_mul_exp_of_exp_bound (fun _ hN => A.resid_bound hN) hε

variable [∀ I, T2Space (K I)] [∀ I, OpensMeasurableSpace (K I)]

/-- **First nonzero term from an analytic core decomposition.** -/
theorem first_nonzero (hβ : 0 < β) {L : ℝ}
    (hne : ∃ p ∈ indexSet (commonD n) (commonQ A.k) L, gCoeff A.ν A.h A.k β A.b A.x p.1 p.2 ≠ 0) :
    ∃! p : ℝ × ℕ, p ∈ admissible (commonD n) (commonQ A.k) ∧
      gCoeff A.ν A.h A.k β A.b A.x p.1 p.2 ≠ 0 ∧
      (∀ q ∈ admissible (commonD n) (commonQ A.k), precedes q p →
        gCoeff A.ν A.h A.k β A.b A.x q.1 q.2 = 0) ∧
      D.Z ~[atTop] fun N => gCoeff A.ν A.h A.k β A.b A.x p.1 p.2 *
        (N ^ (-p.1) * Real.log N ^ p.2) :=
  population_first_nonzero_assembled_exp A.ν A.h A.k β A.b A.k_pos hβ A.b_pos A.x D.Z A.resid
    A.Z_eq (half_pos A.δ₀_pos) (A.resid_tendsto (by linarith [A.δ₀_pos])) hne

/-- **Flatness from an analytic core decomposition.** -/
theorem flat (hβ : 0 < β)
    (hzero : ∀ p ∈ admissible (commonD n) (commonQ A.k), gCoeff A.ν A.h A.k β A.b A.x p.1 p.2 = 0)
    (L : ℝ) : Tendsto (fun N => D.Z N / N ^ (-L)) atTop (𝓝 0) :=
  population_flat_exp A.ν A.h A.k β A.b A.k_pos hβ A.b_pos A.x D.Z A.resid A.Z_eq
    (half_pos A.δ₀_pos) (A.resid_tendsto (by linarith [A.δ₀_pos])) hzero L

/-- **The population integral is a cutoff expansion with the assembled canonical coefficients**,
from an analytic core decomposition. -/
theorem cutoffExpansion (hβ : 0 < β) :
    CutoffExpansion (commonQ A.k) (commonD n) D.Z (gCoeff A.ν A.h A.k β A.b A.x) := by
  have h := (cutoffExpansion_gInt A.ν A.h A.k β A.b A.k_pos hβ A.b_pos A.x).add
    (cutoffExpansion_of_exp_small (commonQ A.k) (commonD n) (half_pos A.δ₀_pos)
      (A.resid_tendsto (by linarith [A.δ₀_pos])))
  have hZ : (fun N => gInt A.ν A.h A.k β A.b A.x N + A.resid N) = D.Z :=
    funext fun N => (A.Z_eq N).symm
  have hc : (fun μ j => gCoeff A.ν A.h A.k β A.b A.x μ j + 0) = gCoeff A.ν A.h A.k β A.b A.x :=
    funext fun μ => funext fun j => add_zero _
  rwa [hZ, hc] at h

/-- **`thm:expectation_expansion` from an analytic core decomposition**: for every cutoff `L > 0`,
`|Z(N) − ∑_{μ<L} N^{−μ} ∑_{j≤D} gCoeff_{μ,j} log^j N| ≤ K N^{−L}(1 + log N)^D` eventually. -/
theorem expansion (hβ : 0 < β) (L : ℝ) (hL : 0 < L) : ∃ Kc : ℝ, ∀ᶠ N in atTop,
    |D.Z N - absSpectralSum (commonQ A.k) (commonD n) (gCoeff A.ν A.h A.k β A.b A.x) L N| ≤
      Kc * (N ^ (-L) * (1 + Real.log N) ^ commonD n) :=
  A.cutoffExpansion hβ L hL

end AnalyticCoreDecomposition

/-! ### The compatible divisor localisation statement (Astra #67 unit 4, to be proved) -/

/-- **The compatible divisor localisation statement for one localisation datum**: there are
finitely many compact base spaces and normal dimensions with an analytic core decomposition. -/
def HasAnalyticCoreDecomposition {U : Type*} [MeasurableSpace U] (D : LocalisationData U)
    (β : ℝ) : Prop :=
  ∃ (M : ℕ) (K : Fin M → Type) (_ : ∀ I, TopologicalSpace (K I))
    (_ : ∀ I, MeasurableSpace (K I)) (_ : ∀ I, CompactSpace (K I)) (_ : ∀ I, T2Space (K I))
    (_ : ∀ I, OpensMeasurableSpace (K I)) (n : Fin M → ℕ),
    Nonempty (AnalyticCoreDecomposition D M K n β)

/-- **The population expansion from the localisation statement**: a localisation datum with an
analytic core decomposition has a power–log cutoff expansion with finitely many chart data. -/
theorem cutoffExpansion_of_hasAnalyticCoreDecomposition {U : Type*} [MeasurableSpace U]
    {D : LocalisationData U} {β : ℝ} (hβ : 0 < β) (h : HasAnalyticCoreDecomposition D β) :
    ∃ (Q Dg : ℕ) (c : ℝ → ℕ → ℝ), 0 < Q ∧ CutoffExpansion Q Dg D.Z c := by
  obtain ⟨M, K, _, _, _, _, _, n, ⟨A⟩⟩ := h
  exact ⟨commonQ A.k, commonD n, gCoeff A.ν A.h A.k β A.b A.x, commonQ_pos A.k A.k_pos,
    A.cutoffExpansion hβ⟩

/-- The localisation datum of a Laplace integral `∫_{closedBall w r} F e^{−NK} dx` on a cube. -/
noncomputable def cubeLocalisationData {d : ℕ} (K F : (Fin d → ℝ) → ℝ) (hK : Measurable K)
    (hK0 : ∀ x, 0 ≤ K x) (w : Fin d → ℝ) (r : ℝ)
    (hFr : Integrable F (volume.restrict (Metric.closedBall w r))) (δ : ℝ) (hδ : 0 < δ) :
    LocalisationData (Fin d → ℝ) where
  μ := volume.restrict (Metric.closedBall w r)
  phase := K
  obs := F
  phase_measurable := hK
  phase_nonneg := Eventually.of_forall hK0
  obs_integrable := hFr
  δ := δ
  δ_pos := hδ

/-- **The compatible divisor localisation statement in dimension `d`** (Astra #67 unit 4): for
every real-analytic `K ≥ 0` with a zero `w` at which it is not identically zero and every
continuous observable, the Laplace integrals on all small closed cubes around `w` admit analytic
core decompositions at every temperature `β > 0`. This is the geometric existence theorem the
programme must prove; nothing here asserts it. -/
def CompatibleDivisorLocalisation (d : ℕ) : Prop :=
  ∀ {U : Set (Fin d → ℝ)}, IsOpen U → ∀ {K : (Fin d → ℝ) → ℝ}, AnalyticOnNhd ℝ K U →
    ∀ {w : Fin d → ℝ}, w ∈ U → K w = 0 → (¬ ∀ᶠ x in 𝓝 w, K x = 0) → (∀ x, 0 ≤ K x) →
    ∀ (hK : Measurable K) (hK0 : ∀ x, 0 ≤ K x) {F : (Fin d → ℝ) → ℝ}, Continuous F →
    ∀ {β : ℝ}, 0 < β → ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r ≤ r₀ →
      ∀ (hFr : Integrable F (volume.restrict (Metric.closedBall w r))) (δ : ℝ) (hδ : 0 < δ),
        HasAnalyticCoreDecomposition (cubeLocalisationData K F hK hK0 w r hFr δ hδ) β

end Grammar
