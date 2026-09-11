/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.TubularCoordFree

/-!
# The pushforward form of the coordinate-free expansion

`TubularCoordFree` expands the tube integral over a graph piece as an integral over the chart
coordinate `z ∈ W` of the invariant contractions against the *unnormalised* fibre measures. The
paper's `eq:per_stratum_expansion_coordfree` integrates instead over the stratum against the
pushforward density `τ_*|μ|`, with the moments of the *normalised* fibre measures. This file proves
that form on strucdual's tube:

* `condTubeNormalMeasure` — the normalised fibre measures `κ_x = C(x)⁻¹ η_x` on the ambient
  normal spaces (finite moments `integrable_norm_pow_condTubeNormalMeasure`; equal to the
  pushed-forward `condFibre` when the mass is nonzero, `condTubeNormalMeasure_eq_map_condFibre`);
* `condContractionSeries F x = ∑_k ⟨D^k_⊥F(x), 𝖬^κ_k(x)⟩` — the paper's per-stratum integrand as a
  function on the stratum;
* `integral_foot_eq_tubeBase` — the pushforward measure `τ_*(dy|_{U'}) = map proj (dy|_{U'})` on
  the stratum piece: `∫_{U'} g(proj y) dy = ∫ g dτ_*` (`eq:pushforward_char` on the actual tube);
* `integral_tube_piece_eq_integral_condContraction` — **`eq:per_stratum_expansion_coordfree` on
  strucdual's tube**: `∫_{U'} F dy = ∫_{U'} (∑_k ⟨D^k_⊥F, 𝖬^κ_k⟩)(proj y) dy`, i.e. the tube
  integral is the integral over the stratum piece, against the pushforward of Lebesgue measure,
  of the contraction series with the normalised fibre moments — with no chart coordinate.

Non-claims: the radius/domination hypotheses are the paper's uniform-polydisc hypothesis; the
identity is exact (no `1/r!`: `rem:lean_per_stratum`); one graph piece; ambient Lebesgue density.
-/

open scoped Manifold ContDiff Matrix ENNReal NNReal
open Bundle Set Function StrucDual.Geometry TopologicalSpace Topology MeasureTheory Filter

namespace Grammar

section Mass

variable {d r : ℕ} {S : Set (Fin d → ℝ)} {A : CompatibleAnalyticLCIAtlas r S} {s : Fin d → ℝ}
  (T : NormalTubularChart A.normal S) (C : ModelGraphChart A s)

/-- The fibre masses are finite. -/
theorem fibreMass_tube_ne_top (z : Fin (d - r) → ℝ) :
    fibreMass volume (tubeDensity T C) z ≠ (⊤ : ℝ≥0∞) := by
  have h := integrable_norm_pow_tubeFibre T C z 0
  simp only [pow_zero] at h
  rw [← fibreMeasure_univ]
  have := (integrable_const_iff.1 h).resolve_left one_ne_zero
  exact measure_ne_top _ _

theorem measurable_fibreMass_tube : Measurable fun z => fibreMass volume (tubeDensity T C) z :=
  Measurable.lintegral_prod_right (f := fun z n => ENNReal.ofReal (tubeDensity T C (z, n)))
    (measurable_tubeDensity T C).ennreal_ofReal

/-- The fibre density is integrable along each fibre. -/
theorem integrable_tubeDensity_fibre (z : Fin (d - r) → ℝ) :
    Integrable (fun n : Fin r → ℝ => tubeDensity T C (z, n)) := by
  have h := integrable_norm_pow_tubeFibre T C z 0
  simp only [pow_zero] at h
  unfold fibreMeasure at h
  have hmeas : AEMeasurable (fun n : Fin r → ℝ => (tubeDensity T C (z, n)).toNNReal) volume :=
    ((measurable_tubeDensity T C).comp measurable_prodMk_left).real_toNNReal.aemeasurable
  rw [show (fun n : Fin r → ℝ => ENNReal.ofReal (tubeDensity T C (z, n))) =
      fun n => ((tubeDensity T C (z, n)).toNNReal : ℝ≥0∞) from rfl,
    integrable_withDensity_iff_integrable_coe_smul₀ hmeas] at h
  refine h.congr (Eventually.of_forall fun n => ?_)
  simp only [Real.coe_toNNReal _ (tubeDensity_nonneg T C _), smul_eq_mul, mul_one]

/-- The fibre integral of the density is the fibre mass. -/
theorem integral_tubeDensity_fibre (z : Fin (d - r) → ℝ) :
    ∫ n, tubeDensity T C (z, n) = (fibreMass volume (tubeDensity T C) z).toReal := by
  rw [fibreMass, ← integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall fun n => tubeDensity_nonneg T C (z, n))
    ((measurable_tubeDensity T C).comp measurable_prodMk_left).aestronglyMeasurable]

/-- Where the fibre mass vanishes, the fibre density vanishes almost everywhere. -/
theorem tubeDensity_ae_zero_of_mass_zero {z : Fin (d - r) → ℝ}
    (h0 : fibreMass volume (tubeDensity T C) z = 0) :
    (fun n => tubeDensity T C (z, n)) =ᵐ[volume] 0 := by
  have h := (lintegral_eq_zero_iff ((measurable_tubeDensity T C).comp
    measurable_prodMk_left).ennreal_ofReal).1 h0
  filter_upwards [h] with n hn
  simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at hn
  exact le_antisymm hn (tubeDensity_nonneg T C _)

end Mass

section Cond

variable {d r : ℕ} {S : Set (Fin d → ℝ)} {A : CompatibleAnalyticLCIAtlas r S} {s : Fin d → ℝ}
  (T : NormalTubularChart A.normal S) (C : ModelGraphChart A s)

/-- The normalisation factor `C(x)⁻¹` (as `ofReal (C.toReal⁻¹)`, so that it vanishes with `C`). -/
noncomputable def massInv (x : Fin d → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (fibreMass volume (tubeDensity T C) (C.ft x)).toReal⁻¹

theorem massInv_ne_top (x : Fin d → ℝ) : massInv T C x ≠ (⊤ : ℝ≥0∞) := ENNReal.ofReal_ne_top

theorem massInv_toReal (x : Fin d → ℝ) :
    (massInv T C x).toReal = (fibreMass volume (tubeDensity T C) (C.ft x)).toReal⁻¹ :=
  ENNReal.toReal_ofReal (inv_nonneg.2 ENNReal.toReal_nonneg)

/-- **The normalised fibre measures on the ambient normal spaces** `κ_x = C(x)⁻¹ η_x`. -/
noncomputable def condTubeNormalMeasure (x : Fin d → ℝ) : Measure ↥(A.normal x) :=
  massInv T C x • tubeNormalMeasure T C x

theorem integrable_norm_pow_condTubeNormalMeasure (k : ℕ) (x : Fin d → ℝ) :
    Integrable (fun ξ : ↥(A.normal x) => ‖ξ‖ ^ k) (condTubeNormalMeasure T C x) :=
  (integrable_norm_pow_tubeNormalMeasure T C k x).smul_measure (massInv_ne_top T C x)

/-- When the fibre mass is nonzero, the normalised measure is the pushed-forward conditional fibre
measure `condFibre` of `MomentFunctional`. -/
theorem condTubeNormalMeasure_eq_map_condFibre {x : Fin d → ℝ} (hx : x ∈ S ∩ C.V')
    (h0 : fibreMass volume (tubeDensity T C) (C.ft x) ≠ 0) :
    condTubeNormalMeasure T C x = (condFibre volume (tubeDensity T C) (C.ft x)).map
      (rowFrameEquiv A C.i hx.1 (C.mem_V_of_mem hx)) := by
  rw [condTubeNormalMeasure, tubeNormalMeasure_of_mem T C hx, condFibre_eq_smul_fibreMeasure,
    Measure.map_smul]
  congr 1
  rw [massInv, ← ENNReal.toReal_inv, ENNReal.ofReal_toReal (ENNReal.inv_ne_top.2 h0)]

/-- The contraction against a rescaled fibre-measure family rescales. -/
theorem normalContraction_smul_measure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] {M : Type*} (N : (Fin d → ℝ) → Submodule ℝ E)
    (η : ∀ x, Measure (N x)) (c : (Fin d → ℝ) → ℝ≥0∞) {k : ℕ}
    (hr : ∀ x, Integrable (fun ξ : N x => ‖ξ‖ ^ k) (η x))
    (hr' : ∀ x, Integrable (fun ξ : N x => ‖ξ‖ ^ k) (c x • η x)) (Φ : ∀ x, N x → M) (F : M → ℝ)
    (x : Fin d → ℝ) :
    normalContraction N (fun x => c x • η x) hr' Φ F x =
      (c x).toReal * normalContraction N η hr Φ F x := by
  unfold normalContraction normalMoment
  simp only [momentFunctional_apply]
  rw [integral_smul_measure, smul_eq_mul]

/-- **The paper's per-stratum integrand**: `x ↦ ∑_k ⟨D^k_⊥F(x), 𝖬^κ_k(x)⟩`, the contraction series
  of
the additive family's normal Taylor forms against the normalised fibre moments. -/
noncomputable def condContractionSeries (F : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ :=
  ∑' k, normalContraction A.normal (condTubeNormalMeasure T C)
    (integrable_norm_pow_condTubeNormalMeasure T C k) (additiveFamily A.normal) F x

end Cond

section Pushforward

variable {d r : ℕ} {S : Set (Fin d → ℝ)} {A : CompatibleAnalyticLCIAtlas r S} {s : Fin d → ℝ}
  (T : NormalTubularChart A.normal S) (C : ModelGraphChart A s)

/-- **The pushforward measure `τ_*(dy|_{U'})`** of Lebesgue measure on the tube piece to the
stratum: `∫_{U'} g(proj y) dy = ∫ g dτ_*` for measurable `g` (`eq:pushforward_char`). -/
theorem integral_foot_eq_tubeBase {g : (Fin d → ℝ) → ℝ} (hg : Measurable g) :
    ∫ y in T.U ∩ T.proj ⁻¹' C.V', g (T.proj y) =
      ∫ x, g x ∂(volume.restrict (T.U ∩ T.proj ⁻¹' C.V')).map T.proj := by
  have hU : MeasurableSet (T.U ∩ T.proj ⁻¹' C.V') := (restrictTube T C.V'
    C.isOpen_V').isOpen_U.measurableSet
  have hproj : AEMeasurable T.proj (volume.restrict (T.U ∩ T.proj ⁻¹' C.V')) :=
    (ContinuousOn.aemeasurable (fun y hy => (T.contDiffAt_proj
      hy.1).continuousAt.continuousWithinAt) hU)
  rw [integral_map hproj hg.aestronglyMeasurable]

/-- The fibre integral of `F ∘ ψ` against the fibre measure, as a function of `z`. -/
noncomputable def fibreIntegral (F : (Fin d → ℝ) → ℝ) (z : Fin (d - r) → ℝ) : ℝ :=
  ∫ n, tubeDensity T C (z, n) * F (tubeChart C (z, n))

theorem integrable_fibreIntegral {F : (Fin d → ℝ) → ℝ}
    (hF : IntegrableOn F (T.U ∩ T.proj ⁻¹' C.V')) : Integrable (fibreIntegral T C F) := by
  have h := integrable_tubeDensity_mul T C hF
  rw [Measure.volume_eq_prod] at h
  exact h.integral_prod_left

theorem fibreIntegral_eq_zero_of_mass_zero (F : (Fin d → ℝ) → ℝ) {z : Fin (d - r) → ℝ}
    (h0 : fibreMass volume (tubeDensity T C) z = 0) : fibreIntegral T C F z = 0 := by
  unfold fibreIntegral
  refine integral_eq_zero_of_ae ?_
  filter_upwards [tubeDensity_ae_zero_of_mass_zero T C h0] with n hn
  simp [hn]

/-- **The contraction series at a point of the graph piece** is the normalised fibre integral:
`∑_k ⟨D^k_⊥F(emb z), 𝖬^κ_k⟩ = C(z)⁻¹ ∫ F∘ψ_z dη_z`. -/
theorem condContractionSeries_emb {F : (Fin d → ℝ) → ℝ}
    {q : (Fin (d - r) → ℝ) → FormalMultilinearSeries ℝ (Fin r → ℝ) ℝ}
    {Rad : (Fin (d - r) → ℝ) → ℝ≥0∞}
    (hq : ∀ z ∈ C.W, HasFPowerSeriesOnBall (fun n => F (tubeChart C (z, n))) (q z) 0 (Rad z))
    (hη : ∀ z ∈ C.W, ∀ᵐ n ∂fibreMeasure volume (tubeDensity T C) z,
      n ∈ Metric.eball (0 : Fin r → ℝ) (Rad z))
    (hdom : ∀ z ∈ C.W, Summable fun k =>
      ‖q z k‖ * ∫ n, ‖n‖ ^ k ∂fibreMeasure volume (tubeDensity T C) z)
    {z : Fin (d - r) → ℝ} (hz : z ∈ C.W) :
    condContractionSeries T C F (C.emb z) =
      (fibreMass volume (tubeDensity T C) z).toReal⁻¹ * fibreIntegral T C F z := by
  unfold condContractionSeries
  have h1 : ∀ k, normalContraction A.normal (condTubeNormalMeasure T C)
      (integrable_norm_pow_condTubeNormalMeasure T C k) (additiveFamily A.normal) F (C.emb z) =
      (fibreMass volume (tubeDensity T C) z).toReal⁻¹ * ((k.factorial : ℝ)⁻¹ *
        momentFunctional (fibreMeasure volume (tubeDensity T C) z)
          (integrable_norm_pow_tubeFibre T C z k) (normalJet (fun n => F (tubeChart C (z, n))) k))
            := by
    intro k
    have h := normalContraction_smul_measure A.normal (tubeNormalMeasure T C) (massInv T C)
      (integrable_norm_pow_tubeNormalMeasure T C k)
      (integrable_norm_pow_condTubeNormalMeasure T C k) (additiveFamily A.normal) F (C.emb z)
    rw [massInv_toReal, C.ft_emb z hz, normalContraction_tube T C F hz k] at h
    exact h
  simp_rw [h1]
  rw [tsum_mul_left, ← integral_eq_tsum_moment (hq z hz) _ (hη z hz)
    (fun k => integrable_norm_pow_tubeFibre T C z k) (hdom z hz), fibreIntegral,
    integral_fibreMeasure volume (measurable_tubeDensity T C) (tubeDensity_nonneg T C) z]

/-- The normalised fibre integral `C(z)⁻¹ ∫ F∘ψ_z dη_z` as a function of `z`. -/
noncomputable def normFibreIntegral (F : (Fin d → ℝ) → ℝ) (z : Fin (d - r) → ℝ) : ℝ :=
  (fibreMass volume (tubeDensity T C) z).toReal⁻¹ * fibreIntegral T C F z

theorem aestronglyMeasurable_normFibreIntegral {F : (Fin d → ℝ) → ℝ}
    (hF : IntegrableOn F (T.U ∩ T.proj ⁻¹' C.V')) :
    AEStronglyMeasurable (normFibreIntegral T C F) volume :=
  ((measurable_fibreMass_tube T C).ennreal_toReal.inv.aestronglyMeasurable).mul
    (integrable_fibreIntegral T C hF).aestronglyMeasurable

/-- `tubeDensity(z,n) · (C(z)⁻¹ ∫ F∘ψ_z dη_z)` is integrable on the product space. -/
theorem integrable_tubeDensity_mul_normFibreIntegral {F : (Fin d → ℝ) → ℝ}
    (hF : IntegrableOn F (T.U ∩ T.proj ⁻¹' C.V')) :
    Integrable (fun p : (Fin (d - r) → ℝ) × (Fin r → ℝ) =>
      tubeDensity T C p * normFibreIntegral T C F p.1) := by
  have hfi : Integrable (fibreIntegral T C F) := integrable_fibreIntegral T C hF
  rw [Measure.volume_eq_prod]
  refine (integrable_prod_iff ?_).2 ⟨?_, ?_⟩
  · rw [← Measure.volume_eq_prod]
    exact (measurable_tubeDensity T C).aestronglyMeasurable.mul
      ((aestronglyMeasurable_normFibreIntegral T C hF).comp_quasiMeasurePreserving
        Measure.quasiMeasurePreserving_fst)
  · exact Eventually.of_forall fun z =>
      (integrable_tubeDensity_fibre T C z).mul_const (normFibreIntegral T C F z)
  · refine (hfi.norm).congr (Eventually.of_forall fun z => ?_)
    simp only
    have : ∀ n, ‖tubeDensity T C (z, n) * normFibreIntegral T C F z‖ =
        tubeDensity T C (z, n) * ‖normFibreIntegral T C F z‖ := fun n => by
      rw [norm_mul, Real.norm_of_nonneg (tubeDensity_nonneg T C _)]
    simp_rw [this]
    rw [integral_mul_const, integral_tubeDensity_fibre]
    by_cases h0 : fibreMass volume (tubeDensity T C) z = 0
    · rw [fibreIntegral_eq_zero_of_mass_zero T C F h0]
      simp [normFibreIntegral, h0]
    · have hne : (fibreMass volume (tubeDensity T C) z).toReal ≠ 0 :=
        ENNReal.toReal_ne_zero.2 ⟨h0, fibreMass_tube_ne_top T C z⟩
      rw [normFibreIntegral, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_inv,
        ENNReal.abs_toReal, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]

/-- The fibre integral against the fibre measure is the mass times the normalised fibre
integral. -/
theorem integral_fibreMeasure_eq_mass_mul_normFibreIntegral (F : (Fin d → ℝ) → ℝ)
    (z : Fin (d - r) → ℝ) :
    ∫ n, F (tubeChart C (z, n)) ∂fibreMeasure volume (tubeDensity T C) z =
      (fibreMass volume (tubeDensity T C) z).toReal * normFibreIntegral T C F z := by
  rw [integral_fibreMeasure volume (measurable_tubeDensity T C) (tubeDensity_nonneg T C) z]
  change fibreIntegral T C F z = _
  by_cases h0 : fibreMass volume (tubeDensity T C) z = 0
  · rw [fibreIntegral_eq_zero_of_mass_zero T C F h0]
    simp [h0]
  · have hne : (fibreMass volume (tubeDensity T C) z).toReal ≠ 0 :=
      ENNReal.toReal_ne_zero.2 ⟨h0, fibreMass_tube_ne_top T C z⟩
    rw [normFibreIntegral, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]

/-- On the certified domain the contraction series of the foot is the normalised fibre
integral of the base coordinate; off it both sides are annihilated by the density. -/
theorem tubeDensity_mul_condContractionSeries {F : (Fin d → ℝ) → ℝ}
    {q : (Fin (d - r) → ℝ) → FormalMultilinearSeries ℝ (Fin r → ℝ) ℝ}
    {Rad : (Fin (d - r) → ℝ) → ℝ≥0∞}
    (hq : ∀ z ∈ C.W, HasFPowerSeriesOnBall (fun n => F (tubeChart C (z, n))) (q z) 0 (Rad z))
    (hη : ∀ z ∈ C.W, ∀ᵐ n ∂fibreMeasure volume (tubeDensity T C) z,
      n ∈ Metric.eball (0 : Fin r → ℝ) (Rad z))
    (hdom : ∀ z ∈ C.W, Summable fun k =>
      ‖q z k‖ * ∫ n, ‖n‖ ^ k ∂fibreMeasure volume (tubeDensity T C) z)
    (p : (Fin (d - r) → ℝ) × (Fin r → ℝ)) :
    tubeDensity T C p * condContractionSeries T C F (T.proj (tubeChart C p)) =
      tubeDensity T C p * normFibreIntegral T C F p.1 := by
  by_cases hp : p ∈ tubeChartDom T C
  · rw [(tubeChart_mem T C hp).2.1, condContractionSeries_emb T C hq hη hdom hp.1]
    rfl
  · simp [tubeDensity, indicator_of_notMem hp]

/-- **The contraction series of the foot is integrable on the tube piece.** -/
theorem integrableOn_condContractionSeries_foot {F : (Fin d → ℝ) → ℝ}
    (hF : IntegrableOn F (T.U ∩ T.proj ⁻¹' C.V'))
    {q : (Fin (d - r) → ℝ) → FormalMultilinearSeries ℝ (Fin r → ℝ) ℝ}
    {Rad : (Fin (d - r) → ℝ) → ℝ≥0∞}
    (hq : ∀ z ∈ C.W, HasFPowerSeriesOnBall (fun n => F (tubeChart C (z, n))) (q z) 0 (Rad z))
    (hη : ∀ z ∈ C.W, ∀ᵐ n ∂fibreMeasure volume (tubeDensity T C) z,
      n ∈ Metric.eball (0 : Fin r → ℝ) (Rad z))
    (hdom : ∀ z ∈ C.W, Summable fun k =>
      ‖q z k‖ * ∫ n, ‖n‖ ^ k ∂fibreMeasure volume (tubeDensity T C) z) :
    IntegrableOn (fun y => condContractionSeries T C F (T.proj y)) (T.U ∩ T.proj ⁻¹' C.V') := by
  have hΩ : MeasurableSet (tubeChartDom T C) := (isOpen_tubeChartDom T C).measurableSet
  rw [← image_tubeChart T C, ← image_flatChart_concat C,
    integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
      (C.measurableEmbedding_concat.measurableSet_image.2 hΩ)
      (hasFDerivWithinAt_flatChart C fun p hp => hp.1) (injOn_flatChart T C subset_rfl),
    ← C.measurePreserving_concat.integrableOn_comp_preimage C.measurableEmbedding_concat,
    C.concat.injective.preimage_image]
  have h := integrable_tubeDensity_mul_normFibreIntegral T C hF
  refine (h.integrableOn.congr_fun (fun p hp => ?_) hΩ)
  simp only [Function.comp, flatChart_concat, smul_eq_mul]
  rw [← tubeDensity_mul_condContractionSeries T C hq hη hdom p, tubeDensity, indicator_of_mem hp]
  rfl

/-- **`eq:per_stratum_expansion_coordfree` on strucdual's tube**: for `F` integrable on the tube
piece whose fibre restrictions have power series carrying the fibre measures and dominating their
moments, `∫_{U'} F dy = ∫_{U'} (∑_k ⟨D^k_⊥F, 𝖬^κ_k⟩)(proj y) dy` — the integral over the stratum
piece, against the pushforward of Lebesgue measure through the foot, of the contraction series with
the normalised fibre moments. -/
theorem integral_tube_piece_eq_integral_condContraction {F : (Fin d → ℝ) → ℝ}
    (hF : IntegrableOn F (T.U ∩ T.proj ⁻¹' C.V'))
    {q : (Fin (d - r) → ℝ) → FormalMultilinearSeries ℝ (Fin r → ℝ) ℝ}
    {Rad : (Fin (d - r) → ℝ) → ℝ≥0∞}
    (hq : ∀ z ∈ C.W, HasFPowerSeriesOnBall (fun n => F (tubeChart C (z, n))) (q z) 0 (Rad z))
    (hη : ∀ z ∈ C.W, ∀ᵐ n ∂fibreMeasure volume (tubeDensity T C) z,
      n ∈ Metric.eball (0 : Fin r → ℝ) (Rad z))
    (hdom : ∀ z ∈ C.W, Summable fun k =>
      ‖q z k‖ * ∫ n, ‖n‖ ^ k ∂fibreMeasure volume (tubeDensity T C) z) :
    ∫ y in T.U ∩ T.proj ⁻¹' C.V', F y =
      ∫ y in T.U ∩ T.proj ⁻¹' C.V', condContractionSeries T C F (T.proj y) := by
  have hR : ∫ y in T.U ∩ T.proj ⁻¹' C.V', condContractionSeries T C F (T.proj y) =
      ∫ p, tubeDensity T C p * normFibreIntegral T C F p.1 := by
    rw [integral_tube_piece_eq_density T C]
    exact integral_congr_ae (Eventually.of_forall (tubeDensity_mul_condContractionSeries T C hq hη
      hdom))
  have hint := integrable_tubeDensity_mul_normFibreIntegral T C hF
  rw [hR, Measure.volume_eq_prod] at *
  rw [integral_prod _ hint, integral_tube_piece_fibreMeasure T C hF]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only
  rw [integral_mul_const, integral_tubeDensity_fibre,
    integral_fibreMeasure_eq_mass_mul_normFibreIntegral]

end Pushforward

end Grammar
