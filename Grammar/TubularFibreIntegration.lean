/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.TubularJacobian
import Grammar.WeightedFibreIntegration

/-!
# Integration along the fibres of the tube

`TubularJacobian` computes the pull-back of the ambient Lebesgue density through the tube chart
`ψ (z, n) = emb z + J_i(emb z)ᵀ n` of a graph piece as the Jacobian density `tubeJac` on the
certified domain `Ω`. This file integrates it out along the fibres — the paper's
`eq:pushforward_local` and `eq:pushforward_char` for the tube of a compact analytic LCI stratum:

* `tubeDensity = 1_Ω · tubeJac` — the pulled-back density on `ℝ^{d−r} × ℝ^r` (measurable,
  nonnegative); the pulled-back measure is `omegaMeasure volume volume tubeDensity`
  (`MomentFunctional.lean`), with fibre measures `fibreMeasure volume tubeDensity z` on `ℝ^r`.
* `integrableOn_tubeJac_smul` — integrability transfers through the change of variables.
* `integral_tube_piece_fubini` — for `F` integrable on the tube piece,
  `∫_{U ∩ proj⁻¹V'} F dy = ∫_z ∫_n tubeDensity(z,n) F(ψ(z,n)) dn dz
   = ∫_z ∫ F(ψ(z,·)) dη_z dz`, and `= ∫ F ∘ ψ dΩ` against the pulled-back measure
  (`integral_tube_piece_eq_omega`).
* `lintegral_tube_piece` — the nonnegative version, with no integrability hypothesis.
* `integral_foot_eq_fibreMass` — **the pushforward density**: for a function of the foot,
  `∫_{U ∩ proj⁻¹V'} f(ft (proj y)) dy = ∫_z f(z) C(z) dz` with `C(z) = ∫_n tubeDensity(z, n) dn`
  the fibre mass — `τ_*(Φ^*|dy|) = C(z) |dz|`, the local form of `eq:pushforward_char`.

Scope: ambient Lebesgue density on one graph piece; for `|μ| = ρ |dy|` multiply the density by
`ρ ∘ ψ`. No manifold-level density pushforward and no gluing across pieces.
-/

open scoped Manifold ContDiff Matrix ENNReal
open Bundle Set Function StrucDual.Geometry TopologicalSpace Topology MeasureTheory Filter

namespace Grammar

section Density

variable {d r : ℕ} {S : Set (Fin d → ℝ)} {A : CompatibleAnalyticLCIAtlas r S} {s : Fin d → ℝ}

theorem tubeJac_nonneg (C : ModelGraphChart A s) (p : (Fin (d - r) → ℝ) × (Fin r → ℝ)) :
    0 ≤ tubeJac C p := abs_nonneg (fderiv ℝ (flatChart C) (C.concat p)).det

theorem measurable_tubeJac (C : ModelGraphChart A s) : Measurable (tubeJac C) := by
  have h1 : Measurable fun p : (Fin (d - r) → ℝ) × (Fin r → ℝ) =>
      fderiv ℝ (flatChart C) (C.concat p) :=
    (measurable_fderiv ℝ (flatChart C)).comp C.concat.continuous.measurable
  exact (continuous_abs.measurable.comp (ContinuousLinearMap.continuous_det.measurable.comp h1))

/-- **The pulled-back Lebesgue density** on `ℝ^{d−r} × ℝ^r`: `1_Ω · tubeJac`. -/
noncomputable def tubeDensity (T : NormalTubularChart A.normal S) (C : ModelGraphChart A s) :
    (Fin (d - r) → ℝ) × (Fin r → ℝ) → ℝ :=
  (tubeChartDom T C).indicator (tubeJac C)

theorem measurable_tubeDensity (T : NormalTubularChart A.normal S) (C : ModelGraphChart A s) :
    Measurable (tubeDensity T C) :=
  (measurable_tubeJac C).indicator (isOpen_tubeChartDom T C).measurableSet

theorem tubeDensity_nonneg (T : NormalTubularChart A.normal S) (C : ModelGraphChart A s)
    (p : (Fin (d - r) → ℝ) × (Fin r → ℝ)) : 0 ≤ tubeDensity T C p :=
  indicator_nonneg (fun q _ => tubeJac_nonneg C q) p

/-- The tube chart is continuous on the certified domain. -/
theorem continuousOn_tubeChart (T : NormalTubularChart A.normal S) (C : ModelGraphChart A s) :
    ContinuousOn (tubeChart C) (tubeChartDom T C) := fun p hp =>
  (contDiffAt_tubeChart C (n := 1) hp.1).continuousAt.continuousWithinAt

/-- **Integrability transfers through the tube chart**: if `F` is integrable on the tube piece,
`tubeJac • F ∘ ψ` is integrable on the certified domain. -/
theorem integrableOn_tubeJac_smul (T : NormalTubularChart A.normal S) (C : ModelGraphChart A s)
    {F : (Fin d → ℝ) → ℝ} (hF : IntegrableOn F (T.U ∩ T.proj ⁻¹' C.V')) :
    IntegrableOn (fun p => tubeJac C p • F (tubeChart C p)) (tubeChartDom T C) := by
  have hΩ : MeasurableSet (tubeChartDom T C) := (isOpen_tubeChartDom T C).measurableSet
  have h1 : IntegrableOn F (flatChart C '' (C.concat '' tubeChartDom T C)) := by
    rwa [image_flatChart_concat, image_tubeChart]
  rw [integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
    (C.measurableEmbedding_concat.measurableSet_image.2 hΩ)
    (hasFDerivWithinAt_flatChart C fun p hp => hp.1) (injOn_flatChart T C subset_rfl)] at h1
  have h2 := (C.measurePreserving_concat.integrableOn_comp_preimage
    C.measurableEmbedding_concat).2 h1
  rw [C.concat.injective.preimage_image] at h2
  refine h2.congr_fun (fun p _ => ?_) hΩ
  simp only [Function.comp, tubeJac, flatChart_concat]

end Density

section Fubini

variable {d r : ℕ} {S : Set (Fin d → ℝ)} {A : CompatibleAnalyticLCIAtlas r S} {s : Fin d → ℝ}
  (T : NormalTubularChart A.normal S) (C : ModelGraphChart A s)

/-- The tubular change of variables as an integral over the whole product space against the
pulled-back density. -/
theorem integral_tube_piece_eq_density (F : (Fin d → ℝ) → ℝ) :
    ∫ y in T.U ∩ T.proj ⁻¹' C.V', F y = ∫ p, tubeDensity T C p * F (tubeChart C p) := by
  rw [integral_tube_piece T C F, ← integral_indicator (isOpen_tubeChartDom T C).measurableSet]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  change _ = tubeDensity T C p * F (tubeChart C p)
  simp only [smul_eq_mul]
  exact indicator_mul_left _ _ _

/-- The density-weighted integrand is integrable on the product space. -/
theorem integrable_tubeDensity_mul {F : (Fin d → ℝ) → ℝ}
    (hF : IntegrableOn F (T.U ∩ T.proj ⁻¹' C.V')) :
    Integrable (fun p => tubeDensity T C p * F (tubeChart C p)) := by
  have h := (integrable_indicator_iff (isOpen_tubeChartDom T C).measurableSet).2
    (integrableOn_tubeJac_smul T C hF)
  refine h.congr (Eventually.of_forall fun p => ?_)
  change _ = tubeDensity T C p * F (tubeChart C p)
  simp only [smul_eq_mul]
  exact indicator_mul_left _ _ _

/-- **`eq:pushforward_local` for the tube, explicit form**: for `F` integrable on the tube piece,
`∫_{U ∩ proj⁻¹V'} F dy = ∫_z ∫_n tubeDensity(z, n) F(ψ(z, n)) dn dz`. -/
theorem integral_tube_piece_fubini {F : (Fin d → ℝ) → ℝ}
    (hF : IntegrableOn F (T.U ∩ T.proj ⁻¹' C.V')) :
    ∫ y in T.U ∩ T.proj ⁻¹' C.V', F y =
      ∫ z, ∫ n, tubeDensity T C (z, n) * F (tubeChart C (z, n)) := by
  rw [integral_tube_piece_eq_density T C F]
  have h := integrable_tubeDensity_mul T C hF
  rw [Measure.volume_eq_prod] at h ⊢
  exact integral_prod _ h

/-- **`eq:pushforward_local` for the tube, fibre-measure form**: `∫_{U ∩ proj⁻¹V'} F dy =
∫_z ∫ F(ψ(z, ·)) dη_z dz` with `η_z = tubeDensity(z, ·) dn` the fibre measure. -/
theorem integral_tube_piece_fibreMeasure {F : (Fin d → ℝ) → ℝ}
    (hF : IntegrableOn F (T.U ∩ T.proj ⁻¹' C.V')) :
    ∫ y in T.U ∩ T.proj ⁻¹' C.V', F y =
      ∫ z, ∫ n, F (tubeChart C (z, n)) ∂fibreMeasure volume (tubeDensity T C) z := by
  rw [integral_tube_piece_fubini T C hF]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  exact (integral_fibreMeasure volume (measurable_tubeDensity T C) (tubeDensity_nonneg T C) z
    _).symm

/-- **The pulled-back measure**: `∫_{U ∩ proj⁻¹V'} F dy = ∫ F ∘ ψ dΩ` with
`Ω = tubeDensity · dz dn`. -/
theorem integral_tube_piece_eq_omega (F : (Fin d → ℝ) → ℝ) :
    ∫ y in T.U ∩ T.proj ⁻¹' C.V', F y =
      ∫ p, F (tubeChart C p) ∂omegaMeasure volume volume (tubeDensity T C) := by
  rw [integral_tube_piece_eq_density T C F, omegaMeasure, ← Measure.volume_eq_prod,
    integral_withDensity_eq_integral_toReal_smul (measurable_tubeDensity T C).ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp only [ENNReal.toReal_ofReal (tubeDensity_nonneg T C p), smul_eq_mul]

/-- **The nonnegative version**, without integrability: for measurable `G : ℝ^d → [0, ∞]`,
`∫⁻_{U ∩ proj⁻¹V'} G dy = ∫⁻_z ∫⁻_n tubeDensity(z, n) G(ψ(z, n)) dn dz`. -/
theorem lintegral_tube_piece {G : (Fin d → ℝ) → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ y in T.U ∩ T.proj ⁻¹' C.V', G y =
      ∫⁻ z, ∫⁻ n, ENNReal.ofReal (tubeDensity T C (z, n)) * G (tubeChart C (z, n)) := by
  have hΩ : MeasurableSet (tubeChartDom T C) := (isOpen_tubeChartDom T C).measurableSet
  have hpt : ∀ p, (tubeChartDom T C).indicator (fun a =>
      ENNReal.ofReal |(fderiv ℝ (flatChart C) (C.concat a)).det| * G (flatChart C (C.concat a))) p =
      ENNReal.ofReal (tubeDensity T C p) * G (tubeChart C p) := by
    intro p
    by_cases hp : p ∈ tubeChartDom T C
    · simp only [indicator_of_mem hp, tubeDensity, tubeJac, flatChart_concat]
    · simp only [indicator_of_notMem hp, tubeDensity, ENNReal.ofReal_zero, zero_mul]
  have hae : AEMeasurable (fun p => ENNReal.ofReal (tubeDensity T C p) * G (tubeChart C p))
      volume := by
    have h1 : AEMeasurable ((tubeChartDom T C).indicator
        fun p => ENNReal.ofReal (tubeDensity T C p) * G (tubeChart C p)) volume := by
      rw [aemeasurable_indicator_iff hΩ]
      exact (measurable_tubeDensity T C).ennreal_ofReal.aemeasurable.mul
        (hG.comp_aemeasurable ((continuousOn_tubeChart T C).aemeasurable hΩ))
    refine h1.congr (Eventually.of_forall fun p => ?_)
    by_cases hp : p ∈ tubeChartDom T C
    · rw [indicator_of_mem hp]
    · rw [indicator_of_notMem hp]
      simp only [tubeDensity, indicator_of_notMem hp, ENNReal.ofReal_zero, zero_mul]
  rw [← image_tubeChart T C, ← image_flatChart_concat C,
    lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
      (C.measurableEmbedding_concat.measurableSet_image.2 hΩ)
      (hasFDerivWithinAt_flatChart C fun p hp => hp.1) (injOn_flatChart T C subset_rfl) G,
    ← C.measurePreserving_concat.setLIntegral_comp_emb C.measurableEmbedding_concat,
    ← lintegral_indicator hΩ, lintegral_congr hpt]
  rw [Measure.volume_eq_prod] at hae ⊢
  exact lintegral_prod _ hae

/-- **The pushforward density `τ_*(Φ^*|dy|) = C(z) |dz|`**: for a function `f` of the foot
coordinate, `∫_{U ∩ proj⁻¹V'} f(ft (proj y)) dy = ∫_z f(z) C(z) dz` with
`C(z) = ∫_n tubeDensity(z, n) dn` the fibre mass. -/
theorem integral_foot_eq_fibreMass {f : (Fin (d - r) → ℝ) → ℝ}
    (hf : IntegrableOn (fun y => f (C.ft (T.proj y))) (T.U ∩ T.proj ⁻¹' C.V')) :
    ∫ y in T.U ∩ T.proj ⁻¹' C.V', f (C.ft (T.proj y)) =
      ∫ z, f z * (fibreMass volume (tubeDensity T C) z).toReal := by
  rw [integral_tube_piece_fubini T C hf]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  have hpt : ∀ n, tubeDensity T C (z, n) * f (C.ft (T.proj (tubeChart C (z, n)))) =
      f z * tubeDensity T C (z, n) := by
    intro n
    by_cases hp : (z, n) ∈ tubeChartDom T C
    · rw [(tubeChart_mem T C hp).2.1, C.ft_emb _ hp.1, mul_comm]
    · simp only [tubeDensity, indicator_of_notMem hp, zero_mul, mul_zero]
  simp_rw [hpt]
  rw [integral_const_mul, fibreMass, ← integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall fun n => tubeDensity_nonneg T C (z, n))
    ((measurable_tubeDensity T C).comp measurable_prodMk_left).aestronglyMeasurable]

end Fubini

end Grammar
