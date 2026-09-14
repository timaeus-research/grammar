/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothCoeffDistribution

/-!
# The partition function as a distribution; cheap consequences at the release boundary
(consult #124 §2–§3)

* `Zdist X N hN : 𝓓'(ℝ^d, ℝ)` — the partition function with insertions `f ↦ ∫ prior · f · e^{−NK}`
  as a distribution of order zero, for `N ≥ 0`: `|Z_N f| ≤ (∫ prior) · sup_{tsupport prior} |f|`
  (the phase is nonnegative a.e. for the prior measure, by the transport), with
  `dsupport (Zdist X N hN) ⊆ tsupport prior`, and intrinsic in `K, prior`.
* The weak distributional expansion restated: `Zdist X N hN f ~ Σ coeffDistribution X μ q f …`.
* `coeffDistribution X μ q = 0` off the lattice `commonQ⁻¹ℕ` and above the logarithmic degree
  `commonD ≤ d − 1` (from the certificate support).
* Vanishing on any set of points where the phase is nonzero (`isVanishingOn_of_subset_nonzero`),
  and the linear-map alias `coeffLinearMap`.
-/

open MeasureTheory Set Real Filter Topology Finset
open scoped ContDiff Distributions
open Monomialize.VolumeScaling

namespace Grammar

namespace SmoothEngine

namespace BridgeInputs

variable {d : ℕ} (X : BridgeInputs d)

/-! ### The prior measure is finite and lives on the support of the prior -/

theorem integrable_prior : Integrable X.prior :=
  X.prior_smooth.continuous.integrable_of_hasCompactSupport X.prior_compact

instance : IsFiniteMeasure X.priorMeasure :=
  isFiniteMeasure_withDensity_ofReal X.integrable_prior.hasFiniteIntegral

theorem ae_mem_tsupport_prior : ∀ᵐ y ∂X.priorMeasure, y ∈ tsupport X.prior := by
  rw [priorMeasure_eq_restrict]
  exact (withDensity_absolutelyContinuous _ _).ae_le
    (ae_restrict_mem (isClosed_tsupport _).measurableSet)

/-- The total mass of the prior measure is `∫ prior`. -/
theorem priorMeasure_real_univ : X.priorMeasure.real univ = ∫ y, X.prior y := by
  unfold priorMeasure
  rw [measureReal_def, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal X.integrable_prior
      (Eventually.of_forall X.prior_nonneg),
    ENNReal.toReal_ofReal (integral_nonneg X.prior_nonneg)]

/-! ### The partition function as a distribution -/

/-- The partition function with the observable `f`, through the bridge (equal to
`partitionObs X.K X.prior f N`). -/
theorem Z_withObs_eq (f : (Fin d → ℝ) → ℝ) (hf : ContDiff ℝ ∞ f) (N : ℝ) :
    (X.withObs f hf).D.Z N = partitionObs X.K X.prior f N := X.withObs_Z hf N

/-- ★ **The order-zero bound**: for `N ≥ 0`, `|∫ prior · f · e^{−NK}| ≤ (∫ prior) · M` whenever
`|f| ≤ M` on the support of the prior. -/
theorem abs_partitionObs_le {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) {N : ℝ} (hN : 0 ≤ N)
    {M : ℝ} (hM : ∀ y ∈ tsupport X.prior, |f y| ≤ M) :
    |partitionObs X.K X.prior f N| ≤ (∫ y, X.prior y) * M := by
  rw [← X.Z_withObs_eq f hf, ← X.priorMeasure_real_univ, mul_comm]
  unfold LocalisationData.Z
  change |∫ z, (X.withObs f hf).D.integrand N z ∂X.priorMeasure| ≤ _
  rw [← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le_const ?_
  have h1 : ∀ᵐ z ∂X.priorMeasure, ‖(X.withObs f hf).D.integrand N z‖ ≤ ‖f z‖ :=
    (X.withObs f hf).D.abs_integrand_le hN
  filter_upwards [h1, X.ae_mem_tsupport_prior] with y hy hy'
  refine hy.trans ?_
  rw [Real.norm_eq_abs]
  exact hM y hy'

theorem jetBound_zero_of_le {f : (Fin d → ℝ) → ℝ} {S : Set (Fin d → ℝ)} {M : ℝ}
    (hJ : JetBound 0 S f M) : ∀ y ∈ S, |f y| ≤ M := by
  intro y hy
  have := hJ 0 le_rfl y hy
  rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this

theorem partitionObs_testFunction_add {N : ℝ} (hN : 0 ≤ N)
    (f g : 𝓓((⊤ : TopologicalSpace.Opens (Fin d → ℝ)), ℝ)) :
    partitionObs X.K X.prior (f + g) N =
      partitionObs X.K X.prior f N + partitionObs X.K X.prior g N := by
  rw [← X.Z_withObs_eq f f.contDiff, ← X.Z_withObs_eq g g.contDiff,
    ← X.Z_withObs_eq (f + g) (f + g).contDiff, ← X.Z_withObs_add f.contDiff g.contDiff hN]
  rfl

theorem partitionObs_testFunction_smul (N : ℝ) (c : ℝ)
    (f : 𝓓((⊤ : TopologicalSpace.Opens (Fin d → ℝ)), ℝ)) :
    partitionObs X.K X.prior (c • f) N = c * partitionObs X.K X.prior f N := by
  rw [← X.Z_withObs_eq f f.contDiff, ← X.Z_withObs_eq (c • f) (c • f).contDiff,
    ← X.Z_withObs_smul f.contDiff c N]
  rfl

/-- ★★ **The partition function as a distribution** (order zero), for `N ≥ 0`. -/
noncomputable def Zdist (N : ℝ) (hN : 0 ≤ N) :
    𝓓'((⊤ : TopologicalSpace.Opens (Fin d → ℝ)), ℝ) :=
  Distribution.ofJetBound 0 (tsupport X.prior) (∫ y, X.prior y)
    (fun f => partitionObs X.K X.prior f N) (X.partitionObs_testFunction_add hN)
    (X.partitionObs_testFunction_smul N)
    (fun _f _ _ hJ => X.abs_partitionObs_le _f.contDiff hN (jetBound_zero_of_le hJ))

theorem Zdist_apply (N : ℝ) (hN : 0 ≤ N) (f : 𝓓((⊤ : TopologicalSpace.Opens (Fin d → ℝ)), ℝ)) :
    X.Zdist N hN f = ∫ y, X.prior y * f y * Real.exp (-N * X.K y) := rfl

theorem Zdist_bound (N : ℝ) (hN : 0 ≤ N) (f : 𝓓((⊤ : TopologicalSpace.Opens (Fin d → ℝ)), ℝ))
    {M : ℝ} (hM : ∀ y ∈ tsupport X.prior, |f y| ≤ M) :
    |X.Zdist N hN f| ≤ (∫ y, X.prior y) * M :=
  X.abs_partitionObs_le f.contDiff hN hM

theorem partitionObs_eq_zero_of_disjoint_prior {f : (Fin d → ℝ) → ℝ}
    (hsupp : tsupport f ⊆ (tsupport X.prior)ᶜ) (N : ℝ) : partitionObs X.K X.prior f N = 0 := by
  unfold partitionObs
  refine integral_eq_zero_of_ae (Eventually.of_forall fun y => ?_)
  change X.prior y * f y * Real.exp (-N * X.K y) = 0
  by_cases hy : y ∈ tsupport X.prior
  · rw [image_eq_zero_of_notMem_tsupport fun h => hsupp h hy, mul_zero, zero_mul]
  · rw [image_eq_zero_of_notMem_tsupport hy, zero_mul, zero_mul]

theorem isVanishingOn_Zdist (N : ℝ) (hN : 0 ≤ N) :
    Distribution.IsVanishingOn (X.Zdist N hN) (tsupport X.prior)ᶜ := fun _ hf =>
  X.partitionObs_eq_zero_of_disjoint_prior hf N

/-- ★ The partition-function distribution is supported in the support of the prior. -/
theorem dsupport_Zdist_subset (N : ℝ) (hN : 0 ≤ N) :
    Distribution.dsupport (X.Zdist N hN) ⊆ tsupport X.prior :=
  Distribution.dsupport_subset_of_isVanishingOn (isClosed_tsupport _) (X.isVanishingOn_Zdist N hN)

/-- Intrinsicness: `Zdist` depends only on the phase and the prior. -/
theorem Zdist_eq_of_eq {Y : BridgeInputs d} (hK : X.K = Y.K) (hp : X.prior = Y.prior) (N : ℝ)
    (hN : 0 ≤ N) : X.Zdist N hN = Y.Zdist N hN := by
  ext f
  rw [Zdist_apply, Zdist_apply, hK, hp]

/-- ★★ **The weak distributional expansion, in terms of `Zdist`**: for every test function `f`,
`Zdist X N f ~ Σ_{μ,q} coeffDistribution X μ q f · N^{−μ} (log N)^q`. -/
theorem hasSmoothCoordFreeExpansion_Zdist (f : 𝓓((⊤ : TopologicalSpace.Opens (Fin d → ℝ)), ℝ)) :
    HasSmoothCoordFreeExpansion (fun N => if hN : 0 ≤ N then X.Zdist N hN f else 0)
      (fun μ q => X.coeffDistribution μ q f) X.decomp.commonQ X.decomp.commonD := by
  intro A
  refine (X.hasSmoothCoordFreeExpansion_partitionObs f A).congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with N hN
  simp only [hN, dite_true]
  rfl

/-! ### Cheap consequences at the release boundary -/

/-- The coefficient distributions vanish off the lattice `commonQ⁻¹ℕ`. -/
theorem coeffDistribution_eq_zero_of_not_lattice {μ : ℝ}
    (hμ : ∀ m : ℕ, μ ≠ (m : ℝ) / X.decomp.commonQ) (q : ℕ) : X.coeffDistribution μ q = 0 := by
  ext f
  exact (X.withObs f f.contDiff).decomp.coeff_eq_zero_of_not_lattice hμ q

/-- The coefficient distributions vanish above the logarithmic degree `commonD`. -/
theorem coeffDistribution_eq_zero_of_degree_gt (μ : ℝ) {q : ℕ} (hq : X.decomp.commonD < q) :
    X.coeffDistribution μ q = 0 := by
  ext f
  exact (X.withObs f f.contDiff).decomp.coeff_eq_zero_of_degree_gt hq

/-- The coefficient distributions vanish above the logarithmic degree `d − 1`. -/
theorem coeffDistribution_eq_zero_of_dim_lt (μ : ℝ) {q : ℕ} (hq : d - 1 < q) :
    X.coeffDistribution μ q = 0 :=
  X.coeffDistribution_eq_zero_of_degree_gt μ (lt_of_le_of_lt X.commonD_le hq)

/-- ★ The coefficient distributions vanish on test functions supported where the phase is
nonzero. -/
theorem isVanishingOn_of_subset_nonzero (μ : ℝ) (q : ℕ) {U : Set (Fin d → ℝ)}
    (hU : U ⊆ {x | X.K x ≠ 0}) : Distribution.IsVanishingOn (X.coeffDistribution μ q) U :=
  fun f hf => X.observableCoeff_eq_zero_of_tsupport_subset μ q f.contDiff
    (hf.trans (hU.trans fun _ hx hx' => hx (X.wallImage_subset_zeroSet hx')))

/-- The coefficient distribution as a plain linear functional on the test functions. -/
noncomputable def coeffLinearMap (μ : ℝ) (q : ℕ) :
    𝓓((⊤ : TopologicalSpace.Opens (Fin d → ℝ)), ℝ) →ₗ[ℝ] ℝ :=
  (X.coeffDistribution μ q).toLinearMap

theorem coeffLinearMap_apply (μ : ℝ) (q : ℕ)
    (f : 𝓓((⊤ : TopologicalSpace.Opens (Fin d → ℝ)), ℝ)) :
    X.coeffLinearMap μ q f = X.coeffDistribution μ q f := rfl

end BridgeInputs

end SmoothEngine

end Grammar
