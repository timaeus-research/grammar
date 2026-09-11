/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.TubularFibreIntegration
import Grammar.CoordFreeTaylorMoment

/-!
# The Taylor–moment expansion on the actual tube

The coordinate-free Taylor–moment expansion of `CoordFreeTaylorMoment` (the corrected
`eq:per_stratum_expansion_coordfree` / `eq:tubular_expansion`) takes as input a fibre measure with
finite moments carried by the ball of convergence of the fibre restriction of the observable. This
file supplies those inputs on strucdual's tube over a graph piece, from the pulled-back Lebesgue
density of `TubularJacobian`/`TubularFibreIntegration`:

* the fibres of the certified domain are bounded (`norm_le_of_mem_tubeChartDom`), the Jacobian is
  continuous along each fibre (`continuous_tubeJac_fibre`), so **every fibre measure
  `η_z = tubeDensity(z,·) dn` has finite moments of all orders**
  (`integrable_norm_pow_tubeFibre`), and it vanishes off `W` (`fibreMeasure_eq_zero_of_notMem`);
* **the expansion of the tube integral**: for `F` integrable on the tube piece whose fibre
  restrictions `n ↦ F(ψ(z,n))` have power series at `0` carrying the fibre measures and dominating
  their moments, `∫_{U ∩ proj⁻¹V'} F dy = ∫_z ∑_k (k!)⁻¹ ⟨D^k(F∘ψ_z)(0), 𝖬_k(z)⟩ dz`
  (`integral_tube_piece_eq_tsum_moment`) and, in multi-index form,
  `= ∫_z ∑_k ∑_{|b|=k} (∂^b(F∘ψ_z)(0)/b!) M̃_b(z) dz` (`integral_tube_piece_eq_tsum_multiIndex`);
* **the derivative of the tube chart**
  `Dψ(z,n)(h,k) = D emb(z) h + (D(J^T∘emb)(z) h) n + J(emb z)^T k` (`hasFDerivAt_tubeChart`) and
  **the zero-section Jacobian**
  `g(z,0) = |det([D emb(z), J_i(emb z)^T] ∘ L⁻¹)|` (`tubeJac_zero`).

Non-claims: the domination/radius hypotheses are the paper's uniform-polydisc hypothesis and are
taken as hypotheses (they hold for analytic `F` on a shrunken tube but are not derived here); one
graph piece, ambient Lebesgue density.
-/

open scoped Manifold ContDiff Matrix ENNReal NNReal
open Bundle Set Function StrucDual.Geometry TopologicalSpace Topology MeasureTheory Filter

namespace Grammar

section Fibre

variable {d r : ℕ} {S : Set (Fin d → ℝ)} {A : CompatibleAnalyticLCIAtlas r S} {s : Fin d → ℝ}
  (T : NormalTubularChart A.normal S) (C : ModelGraphChart A s)

/-- The fibres of the certified domain are bounded: `‖n‖ ≤ ‖(J Jᵀ)⁻¹J‖ · ε`. -/
theorem norm_le_of_mem_tubeChartDom {z : Fin (d - r) → ℝ} (hz : z ∈ C.W) {n : Fin r → ℝ}
    (hn : (z, n) ∈ tubeChartDom T C) : ‖n‖ ≤ ‖rowCoframe A C.i (C.emb z)‖ * T.eps := by
  have h := rowCoframe_rowFrame A C.i (C.emb_mem_S hz) (C.emb_mem_V hz) n
  calc ‖n‖ = ‖rowCoframe A C.i (C.emb z) (rowFrame A C.i (C.emb z) n)‖ := by rw [h]
    _ ≤ ‖rowCoframe A C.i (C.emb z)‖ * ‖rowFrame A C.i (C.emb z) n‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖rowCoframe A C.i (C.emb z)‖ * T.eps :=
        mul_le_mul_of_nonneg_left hn.2.le (norm_nonneg _)

/-- The Jacobian density is continuous along each fibre over `W`. -/
theorem continuous_tubeJac_fibre {z : Fin (d - r) → ℝ} (hz : z ∈ C.W) :
    Continuous fun n : Fin r → ℝ => tubeJac C (z, n) := by
  refine continuous_iff_continuousAt.2 fun n => ?_
  have h : ContinuousAt (fderiv ℝ (flatChart C)) (C.concat (z, n)) :=
    (contDiffAt_flatChart C (n := ω) hz).continuousAt_fderiv (by simp)
  have h1 : ContinuousAt (fun n : Fin r → ℝ => C.concat (z, n)) n :=
    (C.concat.continuous.comp (continuous_const.prodMk continuous_id)).continuousAt
  have h2 : ContinuousAt (fun n : Fin r → ℝ => fderiv ℝ (flatChart C) (C.concat (z, n))) n :=
    ContinuousAt.comp (g := fderiv ℝ (flatChart C)) (f := fun n : Fin r → ℝ => C.concat (z, n)) h h1
  exact (continuous_abs.comp ContinuousLinearMap.continuous_det).continuousAt.comp h2

theorem tubeDensity_eq_zero_of_notMem {z : Fin (d - r) → ℝ} (hz : z ∉ C.W) (n : Fin r → ℝ) :
    tubeDensity T C (z, n) = 0 :=
  indicator_of_notMem (fun h => hz h.1) _

/-- The fibre measures vanish off `W`. -/
theorem fibreMeasure_eq_zero_of_notMem {z : Fin (d - r) → ℝ} (hz : z ∉ C.W) :
    fibreMeasure volume (tubeDensity T C) z = 0 := by
  unfold fibreMeasure
  have : (fun n => ENNReal.ofReal (tubeDensity T C (z, n))) = 0 := funext fun n => by
    simp [tubeDensity_eq_zero_of_notMem T C hz n]
  rw [this, withDensity_zero]

/-- **Every fibre measure of the tube has finite moments of all orders.** -/
theorem integrable_norm_pow_tubeFibre (z : Fin (d - r) → ℝ) (k : ℕ) :
    Integrable (fun n : Fin r → ℝ => ‖n‖ ^ k) (fibreMeasure volume (tubeDensity T C) z) := by
  by_cases hz : z ∈ C.W
  · unfold fibreMeasure
    have hmeas : AEMeasurable (fun n : Fin r → ℝ => (tubeDensity T C (z, n)).toNNReal) volume :=
      ((measurable_tubeDensity T C).comp measurable_prodMk_left).real_toNNReal.aemeasurable
    rw [show (fun n : Fin r → ℝ => ENNReal.ofReal (tubeDensity T C (z, n))) =
        fun n => ((tubeDensity T C (z, n)).toNNReal : ℝ≥0∞) from rfl,
      integrable_withDensity_iff_integrable_coe_smul₀ hmeas]
    set M := ‖rowCoframe A C.i (C.emb z)‖ * T.eps with hM
    obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : Fin r → ℝ) M).exists_bound_of_continuousOn
      (continuous_tubeJac_fibre C hz).continuousOn
    have hnot : ∀ n, n ∉ Metric.closedBall (0 : Fin r → ℝ) M → (z, n) ∉ tubeChartDom T C :=
      fun n hn h => hn (by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact norm_le_of_mem_tubeChartDom T C hz h)
    have hgm : AEStronglyMeasurable
        (fun n : Fin r → ℝ => ((tubeDensity T C (z, n)).toNNReal : ℝ≥0) • ‖n‖ ^ k) volume :=
      (hmeas.coe_nnreal_real.smul
        (continuous_norm.pow k).measurable.aemeasurable).aestronglyMeasurable
    have key : ∀ n ∈ Metric.closedBall (0 : Fin r → ℝ) M,
        ‖((tubeDensity T C (z, n)).toNNReal : ℝ≥0) • ‖n‖ ^ k‖ ≤ B * M ^ k := by
      intro n hn
      have hn' : ‖n‖ ≤ M := by rwa [Metric.mem_closedBall, dist_zero_right] at hn
      have hc : 0 ≤ tubeDensity T C (z, n) := tubeDensity_nonneg T C _
      have hcB : tubeDensity T C (z, n) ≤ B :=
        (indicator_le_self' (fun q _ => tubeJac_nonneg C q) _).trans
          ((le_abs_self _).trans (hB n hn))
      rw [NNReal.smul_def, Real.coe_toNNReal _ hc, smul_eq_mul, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg hc (pow_nonneg (norm_nonneg _) _))]
      exact mul_le_mul hcB (pow_le_pow_left₀ (norm_nonneg _) hn' k)
        (pow_nonneg (norm_nonneg _) _) (hc.trans hcB)
    have hbound : IntegrableOn
        (fun n : Fin r → ℝ => ((tubeDensity T C (z, n)).toNNReal : ℝ≥0) • ‖n‖ ^ k)
        (Metric.closedBall (0 : Fin r → ℝ) M) :=
      Measure.integrableOn_of_bounded measure_closedBall_lt_top.ne hgm
        (ae_restrict_of_forall_mem measurableSet_closedBall key)
    refine (hbound.integrable_indicator measurableSet_closedBall).congr
      (Eventually.of_forall fun n => ?_)
    by_cases hn : n ∈ Metric.closedBall (0 : Fin r → ℝ) M
    · rw [indicator_of_mem hn]
      rfl
    · rw [indicator_of_notMem hn]
      simp [tubeDensity, indicator_of_notMem (hnot n hn)]
  · rw [fibreMeasure_eq_zero_of_notMem T C hz]
    exact integrable_zero_measure

end Fibre

section Expansion

variable {d r : ℕ} {S : Set (Fin d → ℝ)} {A : CompatibleAnalyticLCIAtlas r S} {s : Fin d → ℝ}
  (T : NormalTubularChart A.normal S) (C : ModelGraphChart A s)

/-- **The Taylor–moment expansion of the tube integral**: for `F` integrable on the tube piece
whose fibre restrictions `F ∘ ψ_z` have power series at `0` carrying the fibre measures and
dominating their moments, `∫_{U ∩ proj⁻¹V'} F dy = ∫_z ∑_k (k!)⁻¹ ⟨D^k(F∘ψ_z)(0), 𝖬_k(z)⟩ dz`. -/
theorem integral_tube_piece_eq_tsum_moment {F : (Fin d → ℝ) → ℝ}
    (hF : IntegrableOn F (T.U ∩ T.proj ⁻¹' C.V'))
    {q : (Fin (d - r) → ℝ) → FormalMultilinearSeries ℝ (Fin r → ℝ) ℝ}
    {Rad : (Fin (d - r) → ℝ) → ℝ≥0∞}
    (hq : ∀ z ∈ C.W, HasFPowerSeriesOnBall (fun n => F (tubeChart C (z, n))) (q z) 0 (Rad z))
    (hη : ∀ z ∈ C.W, ∀ᵐ n ∂fibreMeasure volume (tubeDensity T C) z,
      n ∈ Metric.eball (0 : Fin r → ℝ) (Rad z))
    (hdom : ∀ z ∈ C.W, Summable fun k =>
      ‖q z k‖ * ∫ n, ‖n‖ ^ k ∂fibreMeasure volume (tubeDensity T C) z) :
    ∫ y in T.U ∩ T.proj ⁻¹' C.V', F y =
      ∫ z, (C.W : Set (Fin (d - r) → ℝ)).indicator (fun z => ∑' k, (k.factorial : ℝ)⁻¹ *
        momentFunctional (fibreMeasure volume (tubeDensity T C) z)
          (integrable_norm_pow_tubeFibre T C z k)
          (normalJet (fun n => F (tubeChart C (z, n))) k)) z := by
  rw [integral_tube_piece_fibreMeasure T C hF]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  by_cases hz : z ∈ C.W
  · rw [indicator_of_mem hz]
    exact integral_eq_tsum_moment (hq z hz) _ (hη z hz)
      (fun k => integrable_norm_pow_tubeFibre T C z k) (hdom z hz)
  · rw [indicator_of_notMem hz]
    change ∫ n, F (tubeChart C (z, n)) ∂fibreMeasure volume (tubeDensity T C) z = 0
    rw [fibreMeasure_eq_zero_of_notMem T C hz, integral_zero_measure]

/-- **The multi-index form**:
`∫_{U ∩ proj⁻¹V'} F dy = ∫_z ∑_k ∑_{|b|=k} (∂^b(F∘ψ_z)(0)/b!) M̃_b(z) dz` with the dressed
moments `M̃_b(z) = ∫ n^b dη_z`. -/
theorem integral_tube_piece_eq_tsum_multiIndex {F : (Fin d → ℝ) → ℝ}
    (hF : IntegrableOn F (T.U ∩ T.proj ⁻¹' C.V'))
    {q : (Fin (d - r) → ℝ) → FormalMultilinearSeries ℝ (Fin r → ℝ) ℝ}
    {Rad : (Fin (d - r) → ℝ) → ℝ≥0∞}
    (hq : ∀ z ∈ C.W, HasFPowerSeriesOnBall (fun n => F (tubeChart C (z, n))) (q z) 0 (Rad z))
    (hη : ∀ z ∈ C.W, ∀ᵐ n ∂fibreMeasure volume (tubeDensity T C) z,
      n ∈ Metric.eball (0 : Fin r → ℝ) (Rad z))
    (hdom : ∀ z ∈ C.W, Summable fun k =>
      ‖q z k‖ * ∫ n, ‖n‖ ^ k ∂fibreMeasure volume (tubeDensity T C) z) :
    ∫ y in T.U ∩ T.proj ⁻¹' C.V', F y =
      ∫ z, (C.W : Set (Fin (d - r) → ℝ)).indicator (fun z => ∑' k,
        ∑ b ∈ Finset.Nat.antidiagonalTuple r k, (∏ i, ((b i).factorial : ℝ))⁻¹ *
          weightComponent (normalJet (fun n => F (tubeChart C (z, n))) k) b *
          dressedMoment (fibreMeasure volume (tubeDensity T C) z) b) z := by
  rw [integral_tube_piece_fibreMeasure T C hF]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  by_cases hz : z ∈ C.W
  · rw [indicator_of_mem hz]
    exact integral_eq_tsum_multiIndex (hq z hz) _ (hη z hz)
      (fun k => integrable_norm_pow_tubeFibre T C z k) (hdom z hz)
  · rw [indicator_of_notMem hz]
    change ∫ n, F (tubeChart C (z, n)) ∂fibreMeasure volume (tubeDensity T C) z = 0
    rw [fibreMeasure_eq_zero_of_notMem T C hz, integral_zero_measure]

end Expansion

section Derivative

variable {d r : ℕ} {S : Set (Fin d → ℝ)} {A : CompatibleAnalyticLCIAtlas r S} {s : Fin d → ℝ}
  (C : ModelGraphChart A s)

/-- **The derivative of the tube chart**:
`Dψ(z,n) = D emb(z) ∘ fst + (J^T(emb z) ∘ snd + (D(J^T∘emb)(z) ∘ fst)ᵗ n)`. -/
theorem hasFDerivAt_tubeChart {z : Fin (d - r) → ℝ} (hz : z ∈ C.W) (n : Fin r → ℝ) :
    HasFDerivAt (tubeChart C)
      (fderiv ℝ C.emb z ∘L ContinuousLinearMap.fst ℝ (Fin (d - r) → ℝ) (Fin r → ℝ) +
        (rowFrame A C.i (C.emb z) ∘L ContinuousLinearMap.snd ℝ (Fin (d - r) → ℝ) (Fin r → ℝ) +
          (fderiv ℝ (rowFrame A C.i) (C.emb z) ∘L
            (fderiv ℝ C.emb z ∘L ContinuousLinearMap.fst ℝ (Fin (d - r) → ℝ) (Fin r → ℝ))).flip n))
      (z, n) := by
  have hemb : HasFDerivAt C.emb (fderiv ℝ C.emb z) z :=
    ((C.contDiffOn_emb.contDiffAt (C.W.isOpen.mem_nhds hz)).differentiableAt
      (by simp)).hasFDerivAt
  have h1 : HasFDerivAt (fun p : (Fin (d - r) → ℝ) × (Fin r → ℝ) => C.emb p.1)
      (fderiv ℝ C.emb z ∘L ContinuousLinearMap.fst ℝ (Fin (d - r) → ℝ) (Fin r → ℝ)) (z, n) :=
    hemb.comp (z, n) hasFDerivAt_fst
  have hR : HasFDerivAt (rowFrame A C.i) (fderiv ℝ (rowFrame A C.i) (C.emb z)) (C.emb z) :=
    ((contDiffAt_rowFrame A C.i (n := 1) _).differentiableAt one_ne_zero).hasFDerivAt
  have h2 := hR.comp (z, n) h1
  exact h1.add (h2.clm_apply hasFDerivAt_snd)

/-- At the zero section the derivative is `[D emb(z), J_i(emb z)^T]`. -/
theorem hasFDerivAt_tubeChart_zero {z : Fin (d - r) → ℝ} (hz : z ∈ C.W) :
    HasFDerivAt (tubeChart C) ((fderiv ℝ C.emb z).coprod (rowFrame A C.i (C.emb z))) (z, 0) := by
  refine (hasFDerivAt_tubeChart C hz 0).congr_fderiv ?_
  have h0 : (fderiv ℝ (rowFrame A C.i) (C.emb z) ∘L
      (fderiv ℝ C.emb z ∘L ContinuousLinearMap.fst ℝ (Fin (d - r) → ℝ) (Fin r → ℝ))).flip
        (0 : Fin r → ℝ) = 0 :=
    ContinuousLinearMap.ext fun p => by simp
  rw [h0, add_zero, ContinuousLinearMap.comp_fst_add_comp_snd]

theorem fderiv_flatChart_zero {z : Fin (d - r) → ℝ} (hz : z ∈ C.W) :
    fderiv ℝ (flatChart C) (C.concat (z, 0)) =
      (fderiv ℝ C.emb z).coprod (rowFrame A C.i (C.emb z)) ∘L
        (C.concat.symm : (Fin d → ℝ) →L[ℝ] (Fin (d - r) → ℝ) × (Fin r → ℝ)) := by
  have h : HasFDerivAt (tubeChart C) ((fderiv ℝ C.emb z).coprod (rowFrame A C.i (C.emb z)))
      (C.concat.symm (C.concat (z, 0))) := by
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact hasFDerivAt_tubeChart_zero C hz
  exact (h.comp (C.concat (z, 0)) C.concat.symm.hasFDerivAt).fderiv

/-- **The zero-section Jacobian**: `g(z, 0) = |det([D emb(z), J_i(emb z)^T] ∘ L⁻¹)|`. -/
theorem tubeJac_zero {z : Fin (d - r) → ℝ} (hz : z ∈ C.W) :
    tubeJac C (z, 0) = |((fderiv ℝ C.emb z).coprod (rowFrame A C.i (C.emb z)) ∘L
      (C.concat.symm : (Fin d → ℝ) →L[ℝ] (Fin (d - r) → ℝ) × (Fin r → ℝ))).det| := by
  unfold tubeJac
  rw [fderiv_flatChart_zero C hz]

end Derivative

end Grammar
