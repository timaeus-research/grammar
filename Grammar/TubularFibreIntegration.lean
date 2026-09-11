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

/-- **A tube weight**: a nonnegative bounded measurable density factor on the ambient space (the
paper's `|μ_0| = b · (φ_prior∘π) |dy|`, cutoffs and cover weights) — carried by the fibre measures,
not differentiated. -/
structure TubeWeight (d : ℕ) where
  /-- The weight. -/
  w : (Fin d → ℝ) → ℝ
  measurable : Measurable w
  nonneg : ∀ y, 0 ≤ w y
  /-- A uniform bound. -/
  bound : ℝ
  le_bound : ∀ y, w y ≤ bound

namespace TubeWeight

/-- The trivial weight `1` (ambient Lebesgue density). -/
def one (d : ℕ) : TubeWeight d :=
  ⟨fun _ => 1, measurable_const, fun _ => zero_le_one, 1, fun _ => le_rfl⟩

@[simp] theorem one_w (d : ℕ) (y : Fin d → ℝ) : (one d).w y = 1 := rfl

theorem bound_nonneg {d : ℕ} (wt : TubeWeight d) : 0 ≤ wt.bound :=
  (wt.nonneg 0).trans (wt.le_bound 0)

/-- Restriction of a weight to a measurable set (multiplication by the indicator). -/
noncomputable def restrict {d : ℕ} (wt : TubeWeight d) (s : Set (Fin d → ℝ)) (hs : MeasurableSet s)
  :
    TubeWeight d :=
  ⟨s.indicator wt.w, wt.measurable.indicator hs, fun y => indicator_nonneg (fun y _ => wt.nonneg y)
    y,
    wt.bound, fun y => (indicator_le_self' (fun y _ => wt.nonneg y) y).trans (wt.le_bound y)⟩

@[simp] theorem restrict_w {d : ℕ} (wt : TubeWeight d) (s : Set (Fin d → ℝ)) (hs : MeasurableSet s)
    (y : Fin d → ℝ) : (wt.restrict s hs).w y = s.indicator wt.w y := rfl

end TubeWeight

open Classical in
/-- The tube chart extended measurably by `0` off the certified domain. -/
noncomputable def tubeChartM (T : NormalTubularChart A.normal S) (C : ModelGraphChart A s) :
    (Fin (d - r) → ℝ) × (Fin r → ℝ) → Fin d → ℝ :=
  (tubeChartDom T C).piecewise (tubeChart C) 0

/-- The tube chart is continuous on the certified domain. -/
theorem continuousOn_tubeChart (T : NormalTubularChart A.normal S) (C : ModelGraphChart A s) :
    ContinuousOn (tubeChart C) (tubeChartDom T C) := fun _ hp =>
  (contDiffAt_tubeChart C (n := 1) hp.1).continuousAt.continuousWithinAt

theorem measurable_tubeChartM (T : NormalTubularChart A.normal S) (C : ModelGraphChart A s) :
    Measurable (tubeChartM T C) := by
  classical
  exact ContinuousOn.measurable_piecewise (continuousOn_tubeChart T C) continuousOn_const
    (isOpen_tubeChartDom T C).measurableSet

theorem tubeChartM_of_mem (T : NormalTubularChart A.normal S) (C : ModelGraphChart A s)
    {p : (Fin (d - r) → ℝ) × (Fin r → ℝ)} (hp : p ∈ tubeChartDom T C) :
    tubeChartM T C p = tubeChart C p := by
  classical
  exact Set.piecewise_eq_of_mem _ _ _ hp

/-- **The pulled-back weighted density** on `ℝ^{d−r} × ℝ^r`: `1_Ω · tubeJac · (w ∘ ψ)`. -/
noncomputable def tubeDensity (T : NormalTubularChart A.normal S) (C : ModelGraphChart A s)
    (wt : TubeWeight d) : (Fin (d - r) → ℝ) × (Fin r → ℝ) → ℝ :=
  (tubeChartDom T C).indicator fun p => tubeJac C p * wt.w (tubeChartM T C p)

variable (T : NormalTubularChart A.normal S) (C : ModelGraphChart A s) (wt : TubeWeight d)

theorem tubeDensity_of_mem {p : (Fin (d - r) → ℝ) × (Fin r → ℝ)} (hp : p ∈ tubeChartDom T C) :
    tubeDensity T C wt p = tubeJac C p * wt.w (tubeChart C p) := by
  rw [tubeDensity, indicator_of_mem hp, tubeChartM_of_mem T C hp]

theorem tubeDensity_of_notMem {p : (Fin (d - r) → ℝ) × (Fin r → ℝ)}
    (hp : p ∉ tubeChartDom T C) : tubeDensity T C wt p = 0 :=
  indicator_of_notMem hp _

theorem measurable_tubeDensity : Measurable (tubeDensity T C wt) :=
  ((measurable_tubeJac C).mul (wt.measurable.comp (measurable_tubeChartM T C))).indicator
    (isOpen_tubeChartDom T C).measurableSet

theorem tubeDensity_nonneg (p : (Fin (d - r) → ℝ) × (Fin r → ℝ)) : 0 ≤ tubeDensity T C wt p :=
  indicator_nonneg (fun q _ => mul_nonneg (tubeJac_nonneg C q) (wt.nonneg _)) p

theorem tubeDensity_le (p : (Fin (d - r) → ℝ) × (Fin r → ℝ)) :
    tubeDensity T C wt p ≤ tubeJac C p * wt.bound := by
  by_cases hp : p ∈ tubeChartDom T C
  · rw [tubeDensity_of_mem T C wt hp]
    exact mul_le_mul_of_nonneg_left (wt.le_bound _) (tubeJac_nonneg C p)
  · rw [tubeDensity_of_notMem T C wt hp]
    exact mul_nonneg (tubeJac_nonneg C p) wt.bound_nonneg

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
  (T : NormalTubularChart A.normal S) (C : ModelGraphChart A s) (wt : TubeWeight d)

/-- The weighted tubular change of variables as an integral over the whole product space against
the pulled-back weighted density. -/
theorem integral_tube_piece_eq_density (F : (Fin d → ℝ) → ℝ) :
    ∫ y in T.U ∩ T.proj ⁻¹' C.V', wt.w y * F y = ∫ p, tubeDensity T C wt p * F (tubeChart C p) := by
  rw [integral_tube_piece T C (fun y => wt.w y * F y),
    ← integral_indicator (isOpen_tubeChartDom T C).measurableSet]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  beta_reduce
  by_cases hp : p ∈ tubeChartDom T C
  · rw [indicator_of_mem hp, tubeDensity_of_mem T C wt hp, smul_eq_mul, mul_assoc]
  · rw [indicator_of_notMem hp, tubeDensity_of_notMem T C wt hp, zero_mul]

/-- The density-weighted integrand is integrable on the product space. -/
theorem integrable_tubeDensity_mul {F : (Fin d → ℝ) → ℝ}
    (hF : IntegrableOn (fun y => wt.w y * F y) (T.U ∩ T.proj ⁻¹' C.V')) :
    Integrable (fun p => tubeDensity T C wt p * F (tubeChart C p)) := by
  have h := (integrable_indicator_iff (isOpen_tubeChartDom T C).measurableSet).2
    (integrableOn_tubeJac_smul T C hF)
  refine h.congr (Eventually.of_forall fun p => ?_)
  beta_reduce
  by_cases hp : p ∈ tubeChartDom T C
  · rw [indicator_of_mem hp, tubeDensity_of_mem T C wt hp, smul_eq_mul, mul_assoc]
  · rw [indicator_of_notMem hp, tubeDensity_of_notMem T C wt hp, zero_mul]

/-- **`eq:pushforward_local` for the tube, explicit form**: for `w·F` integrable on the tube
piece, `∫_{U ∩ proj⁻¹V'} w F dy = ∫_z ∫_n tubeDensity(z, n) F(ψ(z, n)) dn dz`. -/
theorem integral_tube_piece_fubini {F : (Fin d → ℝ) → ℝ}
    (hF : IntegrableOn (fun y => wt.w y * F y) (T.U ∩ T.proj ⁻¹' C.V')) :
    ∫ y in T.U ∩ T.proj ⁻¹' C.V', wt.w y * F y =
      ∫ z, ∫ n, tubeDensity T C wt (z, n) * F (tubeChart C (z, n)) := by
  rw [integral_tube_piece_eq_density T C wt F]
  have h := integrable_tubeDensity_mul T C wt hF
  rw [Measure.volume_eq_prod] at h ⊢
  exact integral_prod _ h

/-- **`eq:pushforward_local` for the tube, fibre-measure form**: `∫_{U ∩ proj⁻¹V'} w F dy =
∫_z ∫ F(ψ(z, ·)) dη_z dz` with `η_z = tubeDensity(z, ·) dn` the weighted fibre measure. -/
theorem integral_tube_piece_fibreMeasure {F : (Fin d → ℝ) → ℝ}
    (hF : IntegrableOn (fun y => wt.w y * F y) (T.U ∩ T.proj ⁻¹' C.V')) :
    ∫ y in T.U ∩ T.proj ⁻¹' C.V', wt.w y * F y =
      ∫ z, ∫ n, F (tubeChart C (z, n)) ∂fibreMeasure volume (tubeDensity T C wt) z := by
  rw [integral_tube_piece_fubini T C wt hF]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  exact (integral_fibreMeasure volume (measurable_tubeDensity T C wt) (tubeDensity_nonneg T C wt) z
    _).symm

/-- **The pulled-back measure**: `∫_{U ∩ proj⁻¹V'} w F dy = ∫ F ∘ ψ dΩ` with
`Ω = tubeDensity · dz dn`. -/
theorem integral_tube_piece_eq_omega (F : (Fin d → ℝ) → ℝ) :
    ∫ y in T.U ∩ T.proj ⁻¹' C.V', wt.w y * F y =
      ∫ p, F (tubeChart C p) ∂omegaMeasure volume volume (tubeDensity T C wt) := by
  rw [integral_tube_piece_eq_density T C wt F, omegaMeasure, ← Measure.volume_eq_prod,
    integral_withDensity_eq_integral_toReal_smul (measurable_tubeDensity T C wt).ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp only [ENNReal.toReal_ofReal (tubeDensity_nonneg T C wt p), smul_eq_mul]

/-- **The nonnegative version**, without integrability: for measurable `G : ℝ^d → [0, ∞]`,
`∫⁻_{U ∩ proj⁻¹V'} w G dy = ∫⁻_z ∫⁻_n tubeDensity(z, n) G(ψ(z, n)) dn dz`. -/
theorem lintegral_tube_piece {G : (Fin d → ℝ) → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ y in T.U ∩ T.proj ⁻¹' C.V', ENNReal.ofReal (wt.w y) * G y =
      ∫⁻ z, ∫⁻ n, ENNReal.ofReal (tubeDensity T C wt (z, n)) * G (tubeChart C (z, n)) := by
  have hΩ : MeasurableSet (tubeChartDom T C) := (isOpen_tubeChartDom T C).measurableSet
  have hG' : Measurable fun y => ENNReal.ofReal (wt.w y) * G y :=
    wt.measurable.ennreal_ofReal.mul hG
  have hpt : ∀ p, (tubeChartDom T C).indicator (fun a =>
      ENNReal.ofReal |(fderiv ℝ (flatChart C) (C.concat a)).det| *
        (ENNReal.ofReal (wt.w (flatChart C (C.concat a))) * G (flatChart C (C.concat a)))) p =
      ENNReal.ofReal (tubeDensity T C wt p) * G (tubeChart C p) := by
    intro p
    by_cases hp : p ∈ tubeChartDom T C
    · rw [indicator_of_mem hp, tubeDensity_of_mem T C wt hp,
        ENNReal.ofReal_mul (tubeJac_nonneg C p), mul_assoc]
      simp only [tubeJac, flatChart_concat]
    · rw [indicator_of_notMem hp, tubeDensity_of_notMem T C wt hp, ENNReal.ofReal_zero, zero_mul]
  have hae : AEMeasurable (fun p => ENNReal.ofReal (tubeDensity T C wt p) * G (tubeChart C p))
      volume := by
    have h1 : AEMeasurable ((tubeChartDom T C).indicator
        fun p => ENNReal.ofReal (tubeDensity T C wt p) * G (tubeChart C p)) volume := by
      rw [aemeasurable_indicator_iff hΩ]
      exact (measurable_tubeDensity T C wt).ennreal_ofReal.aemeasurable.mul
        (hG.comp_aemeasurable ((continuousOn_tubeChart T C).aemeasurable hΩ))
    refine h1.congr (Eventually.of_forall fun p => ?_)
    beta_reduce
    by_cases hp : p ∈ tubeChartDom T C
    · rw [indicator_of_mem hp]
    · rw [indicator_of_notMem hp, tubeDensity_of_notMem T C wt hp, ENNReal.ofReal_zero, zero_mul]
  rw [← image_tubeChart T C, ← image_flatChart_concat C,
    lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
      (C.measurableEmbedding_concat.measurableSet_image.2 hΩ)
      (hasFDerivWithinAt_flatChart C fun p hp => hp.1) (injOn_flatChart T C subset_rfl)
      (fun y => ENNReal.ofReal (wt.w y) * G y),
    ← C.measurePreserving_concat.setLIntegral_comp_emb C.measurableEmbedding_concat,
    ← lintegral_indicator hΩ, lintegral_congr hpt]
  rw [Measure.volume_eq_prod] at hae ⊢
  exact lintegral_prod _ hae

/-- **The pushforward density `τ_*(w |dy|) = C(z) |dz|`**: for a function `f` of the foot
coordinate, `∫_{U ∩ proj⁻¹V'} w f(ft (proj y)) dy = ∫_z f(z) C(z) dz` with
`C(z) = ∫_n tubeDensity(z, n) dn` the weighted fibre mass. -/
theorem integral_foot_eq_fibreMass {f : (Fin (d - r) → ℝ) → ℝ}
    (hf : IntegrableOn (fun y => wt.w y * f (C.ft (T.proj y))) (T.U ∩ T.proj ⁻¹' C.V')) :
    ∫ y in T.U ∩ T.proj ⁻¹' C.V', wt.w y * f (C.ft (T.proj y)) =
      ∫ z, f z * (fibreMass volume (tubeDensity T C wt) z).toReal := by
  rw [integral_tube_piece_fubini T C wt hf]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  have hpt : ∀ n, tubeDensity T C wt (z, n) * f (C.ft (T.proj (tubeChart C (z, n)))) =
      f z * tubeDensity T C wt (z, n) := by
    intro n
    by_cases hp : (z, n) ∈ tubeChartDom T C
    · rw [(tubeChart_mem T C hp).2.1, C.ft_emb _ hp.1, mul_comm]
    · simp only [tubeDensity_of_notMem T C wt hp, zero_mul, mul_zero]
  simp_rw [hpt]
  rw [integral_const_mul, fibreMass, ← integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall fun n => tubeDensity_nonneg T C wt (z, n))
    ((measurable_tubeDensity T C wt).comp measurable_prodMk_left).aestronglyMeasurable]

end Fubini

end Grammar
