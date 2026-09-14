/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothCoeffJetBound
import Mathlib.Analysis.Distribution.Distribution
import Mathlib.Analysis.Distribution.Support

/-!
# The coefficient distributions of the partition function (consult #123, units C2–C3, C4w)

For bridge inputs `X` (phase `K`, prior, normalised core transport) and an index `(μ, q)`, the
observable coefficient functional `f ↦ observableCoeff X μ q f` (the intrinsic coefficient of
`N^{−μ} (log N)^q` in `Z_N[f] = ∫ prior · f · e^{−NK}`) is a **distribution** on `ℝ^d` in
Mathlib's sense — a continuous linear functional on the LF space `𝓓(ℝ^d, ℝ)` of smooth compactly
supported test functions:

  `coeffDistribution X μ q : 𝓓'(⊤, ℝ)`,  `coeffDistribution X μ q f = observableCoeff X μ q f`.

* Continuity comes from the finite-order estimate of CDXVI through the generic constructor
  `Distribution.ofJetBound`: a linear functional bounded by `C · max_{r ≤ R} sup_S ‖D^r f‖` for a
  fixed compact `S` is continuous on every `𝓓_K` (seminorm boundedness,
  `Seminorm.continuous_of_isBounded`), hence on the inductive limit
  (`TestFunction.continuous_iff_continuous_comp`) — with the same `C, R` for every support `K`.
* **Finite order**: `coeffDistribution_bound` records the estimate at the distribution level, with
  order `engineOrder X μ` and the compact set `coreImage X`.
* **Support**: the distribution vanishes on test functions supported off the wall image and on
  those supported off the prior (CDXV), so `dsupport (coeffDistribution X μ q) ⊆ wallImage X ∩
  tsupport prior ⊆ K⁻¹(0) ∩ tsupport prior`; the support is compact.
* **Intrinsicness**: two bridge presentations of the same phase and prior give the same
  distribution (`coeffDistribution_eq_of_eq`).
* **Weak distributional expansion** (`hasSmoothCoordFreeExpansion_partitionObs`): for every test
  function `f`, `Z_N[f] ~ Σ_{μ,q} coeffDistribution X μ q f · N^{−μ} (log N)^q` — the scalar
  theorem read test-function-wise, with the coefficient distributions as coefficients.

The chart-face presentation of these distributions is Theorem B (CDXI); the objects here are the
intrinsic totals. Non-claims: no minimal order, no extension to `C^R` test functions, no
uniformity of the remainder in the test function.
-/

open MeasureTheory Set Real Filter Topology Finset
open scoped ContDiff Distributions
open Monomialize.VolumeScaling

namespace Grammar

namespace SmoothEngine

variable {d : ℕ}

/-! ### The generic constructor -/

/-- The seminorm sum `max_{r ≤ R}` of a compactly supported test function dominates its jets. -/
theorem jetBound_of_supSeminorm {K : TopologicalSpace.Compacts (Fin d → ℝ)} (R : ℕ)
    (S : Set (Fin d → ℝ)) (g : 𝓓_{K}(Fin d → ℝ, ℝ)) :
    JetBound R S g
      ((Finset.range (R + 1)).sup (ContDiffMapSupportedIn.seminorm ℝ (Fin d → ℝ) ℝ ⊤ K) g) := by
  intro r hr x _
  refine (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm ℝ le_top).trans ?_
  exact Seminorm.le_finset_sup_apply (Finset.mem_range.2 (Nat.lt_succ_of_le hr))

/-- ★ **Continuity from a jet bound**: a linear functional on `𝓓(ℝ^d, ℝ)` bounded by
`C · max_{r ≤ R} sup_S ‖D^r f‖` is continuous for the LF topology. -/
theorem continuous_of_jetBound {R : ℕ} {S : Set (Fin d → ℝ)} {C : ℝ}
    (T : 𝓓((⊤ : TopologicalSpace.Opens (Fin d → ℝ)), ℝ) →ₗ[ℝ] ℝ)
    (hT : ∀ (f : 𝓓((⊤ : TopologicalSpace.Opens (Fin d → ℝ)), ℝ)) (M : ℝ), 0 ≤ M →
      JetBound R S f M → |T f| ≤ C * M) :
    Continuous T := by
  rw [TestFunction.continuous_iff_continuous_comp]
  intro K hK
  let L : 𝓓_{K}(Fin d → ℝ, ℝ) →ₗ[ℝ] ℝ :=
    T.comp (TestFunction.ofSupportedInCLM ℝ hK).toLinearMap
  have hL : Continuous L := by
    refine WithSeminorms.continuous_of_isBounded
      (ContDiffMapSupportedIn.withSeminorms ℝ (Fin d → ℝ) ℝ ⊤ K) (norm_withSeminorms ℝ ℝ) L ?_
    refine Seminorm.IsBounded.of_real fun _ => ⟨Finset.range (R + 1), C, fun g => ?_⟩
    change ‖T (TestFunction.ofSupportedIn hK g)‖ ≤ C * _
    rw [Real.norm_eq_abs]
    exact hT _ _ (apply_nonneg _ _) (jetBound_of_supSeminorm R S g)
  exact hL

/-- The linear functional underlying `Distribution.ofJetBound`. -/
def Distribution.jetLinearMap (T : 𝓓((⊤ : TopologicalSpace.Opens (Fin d → ℝ)), ℝ) → ℝ)
    (hadd : ∀ f g, T (f + g) = T f + T g) (hsmul : ∀ (c : ℝ) f, T (c • f) = c * T f) :
    𝓓((⊤ : TopologicalSpace.Opens (Fin d → ℝ)), ℝ) →ₗ[ℝ] ℝ where
  toFun := T
  map_add' := hadd
  map_smul' c f := by simp only [hsmul, smul_eq_mul, RingHom.id_apply]

/-- ★ **A distribution from a jet-bounded linear functional.** -/
noncomputable def Distribution.ofJetBound (R : ℕ) (S : Set (Fin d → ℝ)) (C : ℝ)
    (T : 𝓓((⊤ : TopologicalSpace.Opens (Fin d → ℝ)), ℝ) → ℝ)
    (hadd : ∀ f g, T (f + g) = T f + T g) (hsmul : ∀ (c : ℝ) f, T (c • f) = c * T f)
    (hT : ∀ (f : 𝓓((⊤ : TopologicalSpace.Opens (Fin d → ℝ)), ℝ)) (M : ℝ), 0 ≤ M →
      JetBound R S f M → |T f| ≤ C * M) :
    𝓓'((⊤ : TopologicalSpace.Opens (Fin d → ℝ)), ℝ) where
  toLinearMap := Distribution.jetLinearMap T hadd hsmul
  cont := continuous_of_jetBound (Distribution.jetLinearMap T hadd hsmul) hT

theorem Distribution.ofJetBound_apply (R : ℕ) (S : Set (Fin d → ℝ)) (C : ℝ)
    (T : 𝓓((⊤ : TopologicalSpace.Opens (Fin d → ℝ)), ℝ) → ℝ) (hadd) (hsmul) (hT)
    (f : 𝓓((⊤ : TopologicalSpace.Opens (Fin d → ℝ)), ℝ)) :
    Distribution.ofJetBound R S C T hadd hsmul hT f = T f := rfl

/-- The support of a distribution vanishing off a closed set lies in that set. -/
theorem Distribution.dsupport_subset_of_isVanishingOn
    {T : 𝓓'((⊤ : TopologicalSpace.Opens (Fin d → ℝ)), ℝ)} {S : Set (Fin d → ℝ)}
    (hS : IsClosed S) (h : Distribution.IsVanishingOn T Sᶜ) :
    Distribution.dsupport T ⊆ S :=
  sInter_subset_of_mem ⟨h, hS⟩

namespace BridgeInputs

variable (X : BridgeInputs d)

/-! ### The coefficient distribution -/

theorem observableCoeff_testFunction_add (μ : ℝ) (q : ℕ)
    (f g : 𝓓((⊤ : TopologicalSpace.Opens (Fin d → ℝ)), ℝ)) :
    X.observableCoeff μ q (f + g) (f + g).contDiff =
      X.observableCoeff μ q f f.contDiff + X.observableCoeff μ q g g.contDiff := by
  rw [← X.observableCoeff_add μ q f.contDiff g.contDiff]
  exact X.observableCoeff_congr μ q _ _ rfl

theorem observableCoeff_testFunction_smul (μ : ℝ) (q : ℕ) (c : ℝ)
    (f : 𝓓((⊤ : TopologicalSpace.Opens (Fin d → ℝ)), ℝ)) :
    X.observableCoeff μ q (c • f) (c • f).contDiff = c * X.observableCoeff μ q f f.contDiff := by
  rw [← X.observableCoeff_smul μ q f.contDiff c]
  exact X.observableCoeff_congr μ q _ _ rfl

/-- ★★★ **The coefficient distribution**: the intrinsic coefficient of `N^{−μ}(log N)^q` in
`∫ prior · f · e^{−NK}`, as a distribution in the test function `f`. -/
noncomputable def coeffDistribution (μ : ℝ) (q : ℕ) :
    𝓓'((⊤ : TopologicalSpace.Opens (Fin d → ℝ)), ℝ) :=
  Distribution.ofJetBound (X.engineOrder μ) X.coreImage (X.jetConst μ q)
    (fun f => X.observableCoeff μ q f f.contDiff) (X.observableCoeff_testFunction_add μ q)
    (X.observableCoeff_testFunction_smul μ q)
    (fun f _ hM hJ => X.abs_observableCoeff_le μ q f.contDiff hM hJ)

theorem coeffDistribution_apply (μ : ℝ) (q : ℕ)
    (f : 𝓓((⊤ : TopologicalSpace.Opens (Fin d → ℝ)), ℝ)) :
    X.coeffDistribution μ q f = X.observableCoeff μ q f f.contDiff := rfl

theorem coeffDistribution_obs (μ : ℝ) (q : ℕ)
    (f : 𝓓((⊤ : TopologicalSpace.Opens (Fin d → ℝ)), ℝ)) (hf : X.obs = f) :
    X.coeffDistribution μ q f = X.decomp.coeff μ q := by
  rw [coeffDistribution_apply, ← X.observableCoeff_obs μ q]
  exact (X.observableCoeff_congr μ q _ _ hf).symm

/-- ★★ **Finite order**: the coefficient distribution is bounded by the derivatives of order
`≤ engineOrder X μ` of the test function on the compact core image. -/
theorem coeffDistribution_bound (μ : ℝ) (q : ℕ)
    (f : 𝓓((⊤ : TopologicalSpace.Opens (Fin d → ℝ)), ℝ)) {M : ℝ} (hM : 0 ≤ M)
    (hJ : JetBound (X.engineOrder μ) X.coreImage f M) :
    |X.coeffDistribution μ q f| ≤ X.jetConst μ q * M :=
  X.abs_observableCoeff_le μ q f.contDiff hM hJ

/-- ★★ **Intrinsicness**: two bridge presentations of the same phase and prior give the same
coefficient distribution. -/
theorem coeffDistribution_eq_of_eq {Y : BridgeInputs d} (hK : X.K = Y.K) (hp : X.prior = Y.prior)
    (μ : ℝ) (q : ℕ) : X.coeffDistribution μ q = Y.coeffDistribution μ q := by
  ext f
  exact X.observableCoeff_eq_of_eq hK hp μ q f.contDiff

/-! ### Support -/

theorem isVanishingOn_wallImage_compl (μ : ℝ) (q : ℕ) :
    Distribution.IsVanishingOn (X.coeffDistribution μ q) X.wallImageᶜ := fun f hf =>
  X.observableCoeff_eq_zero_of_tsupport_subset μ q f.contDiff hf

theorem isVanishingOn_prior_compl (μ : ℝ) (q : ℕ) :
    Distribution.IsVanishingOn (X.coeffDistribution μ q) (tsupport X.prior)ᶜ := fun f hf =>
  X.observableCoeff_eq_zero_of_disjoint_prior μ q f.contDiff hf

/-- ★★★ **Support**: the coefficient distribution is supported in the wall image (the image of
the resolved zero divisor) and in the support of the prior. -/
theorem dsupport_coeffDistribution_subset (μ : ℝ) (q : ℕ) :
    Distribution.dsupport (X.coeffDistribution μ q) ⊆ X.wallImage ∩ tsupport X.prior :=
  subset_inter
    (Distribution.dsupport_subset_of_isVanishingOn X.isClosed_wallImage
      (X.isVanishingOn_wallImage_compl μ q))
    (Distribution.dsupport_subset_of_isVanishingOn (isClosed_tsupport _)
      (X.isVanishingOn_prior_compl μ q))

/-- The support lies in the zero set of the phase intersected with the support of the prior. -/
theorem dsupport_coeffDistribution_subset_zeroSet (μ : ℝ) (q : ℕ) :
    Distribution.dsupport (X.coeffDistribution μ q) ⊆ {x | X.K x = 0} ∩ tsupport X.prior :=
  (X.dsupport_coeffDistribution_subset μ q).trans
    (inter_subset_inter_left _ X.wallImage_subset_zeroSet)

theorem isCompact_dsupport_coeffDistribution (μ : ℝ) (q : ℕ) :
    IsCompact (Distribution.dsupport (X.coeffDistribution μ q)) :=
  X.isCompact_wallImage.of_isClosed_subset Distribution.isClosed_dsupport
    ((X.dsupport_coeffDistribution_subset μ q).trans inter_subset_left)

/-! ### The weak distributional expansion -/

/-- ★★★ **The weak distributional expansion**: for every test function `f`,
`∫ prior · f · e^{−NK} ~ Σ_{μ,q} coeffDistribution X μ q f · N^{−μ} (log N)^q` on the lattice
`commonQ⁻¹ℕ` with logarithmic degree `≤ commonD ≤ d − 1`. -/
theorem hasSmoothCoordFreeExpansion_partitionObs
    (f : 𝓓((⊤ : TopologicalSpace.Opens (Fin d → ℝ)), ℝ)) :
    HasSmoothCoordFreeExpansion (partitionObs X.K X.prior f)
      (fun μ q => X.coeffDistribution μ q f) X.decomp.commonQ X.decomp.commonD :=
  (X.withObs f f.contDiff).hasSmoothCoordFreeExpansion

end BridgeInputs

end SmoothEngine

end Grammar
