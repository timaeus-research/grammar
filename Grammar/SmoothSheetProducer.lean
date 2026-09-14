/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothSheetPieces

/-!
# The smooth weighted-atlas producer (U6b.3, consult #117 §7–§8)

From `SmoothSheetInputs` (a weighted domain atlas with smooth chart data, arbitrary SMOOTH weights,
and a tangential phase unit) we build the `SmoothCoreDecomposition` of the localisation datum
`((vol|_W)·prior, K, obs)`: one smooth core presentation per chart piece (chart × selected
orthant), no tail (the pieces exhaust the prior measure by the atlas's exact weighted transport,
`sum_coreMeasure`). Hence ★★★ `hasSmoothCoordFreeExpansion`: the partition function with
insertions `∫_W prior·obs·e^{−NK}` has the smooth coordinate-free expansion — a lattice power–log
expansion on `Q⁻¹ℕ` with logarithmic degree `≤ max(active dimensions) − 1` and INTRINSIC scalar
coefficients (`certificate`, `coeff_eq_of_inputs`: independent of the atlas, the weights, the
orthant selection and the units) — with NO stratum-adapted weight hypotheses (`ω_indep`,
`ω_contOn`) and NO holomorphic packets. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff
open Monomialize.VolumeScaling

namespace Grammar

namespace SmoothEngine

namespace SmoothSheetInputs

variable {d : ℕ} (X : SmoothSheetInputs d)

/-- Pushforward of a finite sum of measures. -/
theorem map_finset_sum' {α γ : Type*} [MeasurableSpace α] [MeasurableSpace γ] {ι : Type*}
    (s : Finset ι) (μ : ι → Measure α) {f : α → γ} (hf : Measurable f) :
    (∑ i ∈ s, μ i).map f = ∑ i ∈ s, (μ i).map f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Measure.map_add _ _ hf, ih]

/-! ### The pieces exhaust the sector measures -/

/-- The orthant box of a sign is, up to the null walls, the chart box intersected with the open
orthant. -/
theorem orthantBox_ae_eq (i : X.A.ι) (σ : WaterFilling.CoordSign d) :
    (WaterFilling.orthantBox σ X.a : Set (Fin d → ℝ)) =ᵐ[volume]
      (X.A.dom i ∩ openOrthant σ : Set (Fin d → ℝ)) := by
  rw [ae_eq_set]
  constructor
  · refine measure_mono_null (fun y hy => ?_) walls_null
    obtain ⟨hy1, hy2⟩ := hy
    have hdom : y ∈ X.A.dom i := by
      rw [X.dom_eq]
      exact WaterFilling.orthantBox_subset σ X.a hy1
    have hno : y ∉ openOrthant σ := fun h => hy2 ⟨hdom, h⟩
    unfold openOrthant at hno
    rw [mem_ofPred_eq] at hno
    push Not at hno
    obtain ⟨j, hj⟩ := hno
    refine ⟨j, ?_⟩
    have h0 : 0 ≤ WaterFilling.sgn σ j * y j := ((WaterFilling.mem_orthantBox.1 hy1) j).1
    have h1 : WaterFilling.sgn σ j * y j = 0 := le_antisymm hj h0
    exact (mul_eq_zero.1 h1).resolve_left (WaterFilling.sgn_ne_zero σ j)
  · have hsub : X.A.dom i ∩ openOrthant σ ⊆ WaterFilling.orthantBox σ X.a := by
      intro y hy
      rw [WaterFilling.mem_orthantBox]
      intro j
      have hpos : 0 < WaterFilling.sgn σ j * y j := hy.2 j
      refine ⟨hpos.le, ?_⟩
      have hdom := hy.1
      rw [X.dom_eq] at hdom
      have hb := hdom j (mem_univ _)
      rw [mem_Icc] at hb
      have : |WaterFilling.sgn σ j * y j| ≤ X.a := by
        rw [abs_mul, WaterFilling.abs_sgn, one_mul]
        exact abs_le.2 hb
      exact (le_abs_self _).trans this
    rw [sdiff_eq_empty.2 hsub, measure_empty]

/-- The restriction to the selected sector is the sum of the restrictions to the selected orthant
boxes. -/
theorem restrict_sector_eq (i : X.A.ι) :
    volume.restrict (X.A.sector i) =
      ∑ σ ∈ X.A.signs i, volume.restrict (WaterFilling.orthantBox σ X.a : Set (Fin d → ℝ)) := by
  unfold WeightedDomainAtlas.sector selectedOrthants
  rw [inter_iUnion₂]
  rw [Measure.restrict_biUnion_finset (fun σ _ τ _ hστ => (openOrthant_disjoint hστ).mono
    inter_subset_right inter_subset_right)
    (fun σ => (X.A.toPartialResolution.dom_measurable i).inter (measurableSet_openOrthant σ))]
  rw [Measure.sum_fintype,
    Finset.sum_coe_sort (X.A.signs i) fun σ => volume.restrict (X.A.dom i ∩ openOrthant σ)]
  exact Finset.sum_congr rfl fun σ _ => (Measure.restrict_congr_set (X.orthantBox_ae_eq i σ)).symm

/-- The weighted prior factor on the sector is the weighted atlas sector measure of the prior. -/
theorem withDensity_sector_eq (i : X.A.ι) :
    ((volume.restrict (X.A.sector i)).withDensity fun w =>
      ENNReal.ofReal (NormalisedBox.wgt (X.A.h i) w * X.ϕf i w)) =
      X.A.sectorMeasure (fun w => ENNReal.ofReal (X.prior w)) i := by
  unfold WeightedDomainAtlas.sectorMeasure
  refine withDensity_congr_ae ?_
  rw [Filter.EventuallyEq, ae_restrict_iff' (X.A.measurableSet_sector i)]
  refine Eventually.of_forall fun w hw => ?_
  have hV : w ∈ X.A.V i := X.A.dom_subset_V i hw.1
  rw [X.A.jacDensity_eq i hV, ← ENNReal.ofReal_mul (X.prior_nonneg _),
    ← ENNReal.ofReal_mul (mul_nonneg (X.prior_nonneg _) (mul_nonneg (abs_nonneg _)
      (Finset.prod_nonneg fun j _ => pow_nonneg (abs_nonneg _) _)))]
  congr 1
  unfold ϕf NormalisedBox.wgt
  ring

/-- ★ **The pieces exhaust the prior measure** (the atlas's exact weighted transport). -/
theorem sum_coreMeasure : ∑ p : X.PIdx, X.coreMeasure p = X.priorMeasure := by
  unfold coreMeasure priorMeasure
  rw [Fintype.sum_sigma, ← X.A.weightedDomainTransport (a := fun w => ENNReal.ofReal (X.prior w))
    (ENNReal.measurable_ofReal.comp X.prior_m)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← map_finset_sum' _ _ (X.φ_smooth i).continuous.measurable]
  congr 1
  rw [← X.withDensity_sector_eq i, X.restrict_sector_eq i,
    ← Finset.sum_coe_sort (X.A.signs i) fun σ =>
      volume.restrict (WaterFilling.orthantBox σ X.a : Set (Fin d → ℝ)),
    ← Measure.sum_fintype fun σ : ↥(X.A.signs i) =>
      volume.restrict (WaterFilling.orthantBox σ.1 X.a : Set (Fin d → ℝ)),
    withDensity_sum, Measure.sum_fintype]

/-! ### The smooth core decomposition -/

/-- The enumeration of the pieces. -/
noncomputable def en : Fin (Fintype.card X.PIdx) ≃ X.PIdx := (Fintype.equivFin _).symm

/-- ★★★ **The smooth core decomposition of the population integral**: one smooth core presentation
per chart piece, no tail. -/
noncomputable def decomp : SmoothCoreDecomposition X.D (Fintype.card X.PIdx)
    (fun I => Base (X.act (X.en I).1) X.a) (fun I => X.da (X.en I)) where
  core I := X.coreMeasure (X.en I)
  tail := 0
  measure_eq := by
    rw [add_zero, X.D_μ, ← X.sum_coreMeasure]
    exact (Equiv.sum_comp X.en X.coreMeasure).symm
  δ₀ := 1
  δ₀_pos := one_pos
  gap := by simp
  chart I := X.piecePresentation (X.en I)

/-! ### The population integral is the partition function with insertions -/

theorem Z_eq_globalLaplace (N : ℝ) :
    X.D.Z N = globalLaplace X.A.W X.K (fun w => X.prior w * X.obs w) N := by
  unfold LocalisationData.Z LocalisationData.integrand globalLaplace
  rw [X.D_μ, X.D_obs, X.D_phase, priorMeasure]
  have hdens : (fun w => ENNReal.ofReal (X.prior w)) =
      fun w => ((X.prior w).toNNReal : ℝ≥0∞) := rfl
  rw [hdens, integral_withDensity_eq_integral_smul X.prior_m.real_toNNReal]
  refine setIntegral_congr_fun X.A.measurableSet_W fun w _ => ?_
  rw [NNReal.smul_def, Real.coe_toNNReal', max_eq_left (X.prior_nonneg w), smul_eq_mul]
  ring

/-- ★★★ **The smooth coordinate-free expansion of the partition function with insertions**, from a
weighted domain atlas with arbitrary smooth weights: for every `A`,
`∫_W prior·obs·e^{−NK} − ∑_{exponent ≤ A} coeff · N^{−α}(log N)^j = o(N^{−A})`, on the lattice
`commonQ⁻¹ℕ` with logarithmic degree `≤ commonD`. -/
theorem hasSmoothCoordFreeExpansion :
    HasSmoothCoordFreeExpansion (globalLaplace X.A.W X.K fun w => X.prior w * X.obs w)
      X.decomp.coeff X.decomp.commonQ X.decomp.commonD := by
  have h := X.decomp.hasSmoothCoordFreeExpansion
  have hZ : X.D.Z = globalLaplace X.A.W X.K fun w => X.prior w * X.obs w :=
    funext X.Z_eq_globalLaplace
  rwa [hZ] at h

/-- The scalar expansion certificate of the partition function with insertions. -/
noncomputable def certificate :
    SmoothExpansionCertificate (globalLaplace X.A.W X.K fun w => X.prior w * X.obs w) where
  Q := X.decomp.commonQ
  Q_pos := X.decomp.commonQ_pos
  D := X.decomp.commonD
  coeff := X.decomp.coeff
  coeff_support := X.decomp.toCertificate.coeff_support
  expansion := by
    have h := X.decomp.cutoffExpansion
    have hZ : X.D.Z = globalLaplace X.A.W X.K fun w => X.prior w * X.obs w :=
      funext X.Z_eq_globalLaplace
    rwa [hZ] at h

/-- ★★ **Intrinsic coefficients**: two smooth sheet inputs for the same domain, phase, prior and
observable (different atlases, weights, orthant selections, units) have the same coefficients. -/
theorem coeff_eq_of_inputs {Y : SmoothSheetInputs d} (hW : X.A.W = Y.A.W) (hK : X.K = Y.K)
    (hprior : X.prior = Y.prior) (hobs : X.obs = Y.obs) (μ : ℝ) (q : ℕ) :
    X.decomp.coeff μ q = Y.decomp.coeff μ q := by
  have hZ : (globalLaplace X.A.W X.K fun w => X.prior w * X.obs w) =
      globalLaplace Y.A.W Y.K fun w => Y.prior w * Y.obs w := by
    rw [hW, hK, hprior, hobs]
  exact SmoothExpansionCertificate.coeff_eq X.certificate
    { Q := Y.decomp.commonQ, Q_pos := Y.decomp.commonQ_pos, D := Y.decomp.commonD,
      coeff := Y.decomp.coeff, coeff_support := Y.decomp.toCertificate.coeff_support,
      expansion := by rw [hZ]; exact Y.certificate.expansion } μ q

end SmoothSheetInputs

end SmoothEngine

end Grammar
