/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.TubularExpansion
import Grammar.ChartNormalFamily
import Grammar.StrucDualNormalFamily

/-!
# The coordinate-free expansion on the actual tube

`TubularExpansion` expands the tube integral over a graph piece in the row frame
`J_i(emb z)ᵀ : ℝ^r ≃ N_{emb z}`. This file removes the frame: the fibre measures are pushed
forward to **measures on the ambient normal spaces** `N_x = normal x` (`tubeNormalMeasure`), and
the terms become the invariant contractions `⟨D^k_⊥F(x), 𝖬_k(x)⟩` of `NormalFibreMoment` for the
additive normal family `Φ_x(n) = x + n` (`StrucDualNormalFamily`), whose Taylor forms are the
restricted ambient jets (`rawNormalJet_additive`):

* `rowFrameEquiv` — the row frame as a continuous linear equivalence `ℝ^r ≃L N_x` on the stratum
  in a chart domain (`rowFrameEquiv_apply_coe`);
* `tubeNormalMeasure` — the fibre measures of the pulled-back Lebesgue density on the normal
  spaces `N_x`, `x ∈ S ∩ V'`, with finite moments of all orders
  (`integrable_norm_pow_tubeNormalMeasure`);
* `normalContraction_tube` — frame removal termwise: `(k!)⁻¹ ⟨D^k(F∘ψ_z)(0), 𝖬_k(z)⟩ =
  ⟨D^k_⊥F(emb z), 𝖬_k(emb z)⟩`;
* `integral_tube_piece_eq_tsum_normalContraction` — **`eq:tubular_expansion` coordinate-free on
  strucdual's tube**: `∫_{U ∩ proj⁻¹V'} F dy = ∫_z 1_W(z) ∑_k ⟨D^k_⊥F(emb z), 𝖬_k(emb z)⟩ dz`.

Non-claims: the radius/domination hypotheses of the fibre power series are the paper's hypotheses;
the base integral is over the chart coordinate `z ∈ W ⊆ ℝ^{d−r}` (not yet against a density on the
manifold `Stratum A`); one graph piece.
-/

open scoped Manifold ContDiff Matrix ENNReal NNReal
open Bundle Set Function StrucDual.Geometry TopologicalSpace Topology MeasureTheory Filter

namespace Grammar

section FrameEquiv

variable {d r : ℕ} {S : Set (Fin d → ℝ)} (A : CompatibleAnalyticLCIAtlas r S) (i : A.ι)

/-- **The row frame as an equivalence** `ℝ^r ≃L N_x` on the stratum in the chart domain. -/
noncomputable def rowFrameEquiv {x : Fin d → ℝ} (hx : x ∈ S) (hxi : x ∈ A.V i) :
    (Fin r → ℝ) ≃L[ℝ] ↥(A.normal x) :=
  ((LinearEquiv.ofInjective (rowFrame A i x : (Fin r → ℝ) →ₗ[ℝ] (Fin d → ℝ))
    (rowFrame_injective A i hx hxi)).trans
      (LinearEquiv.ofEq _ _ (range_rowFrame A i hx hxi))).toContinuousLinearEquiv

theorem rowFrameEquiv_apply_coe {x : Fin d → ℝ} (hx : x ∈ S) (hxi : x ∈ A.V i) (v : Fin r → ℝ) :
    ((rowFrameEquiv A i hx hxi v : ↥(A.normal x)) : Fin d → ℝ) = rowFrame A i x v := by
  simp [rowFrameEquiv, LinearEquiv.coe_toContinuousLinearEquiv', LinearEquiv.trans_apply]

end FrameEquiv

section NormalMeasure

variable {d r : ℕ} {S : Set (Fin d → ℝ)} {A : CompatibleAnalyticLCIAtlas r S} {s : Fin d → ℝ}
  (T : NormalTubularChart A.normal S) (C : ModelGraphChart A s)

theorem ModelGraphChart.mem_V_of_mem (C : ModelGraphChart A s) {x : Fin d → ℝ}
    (hx : x ∈ S ∩ C.V') : x ∈ A.V C.i := C.V'_subset hx.2

open Classical in
/-- **The fibre measures on the ambient normal spaces**: at `x ∈ S ∩ V'`, the fibre measure of the
pulled-back Lebesgue density over `z = ft x`, pushed forward by the row frame to `N_x`. -/
noncomputable def tubeNormalMeasure (x : Fin d → ℝ) : Measure ↥(A.normal x) :=
  if hx : x ∈ S ∩ C.V' then
    (fibreMeasure volume (tubeDensity T C) (C.ft x)).map
      (rowFrameEquiv A C.i hx.1 (C.mem_V_of_mem hx))
  else 0

theorem tubeNormalMeasure_of_mem {x : Fin d → ℝ} (hx : x ∈ S ∩ C.V') :
    tubeNormalMeasure T C x = (fibreMeasure volume (tubeDensity T C) (C.ft x)).map
      (rowFrameEquiv A C.i hx.1 (C.mem_V_of_mem hx)) := by
  rw [tubeNormalMeasure, dif_pos hx]

/-- The pushed-forward fibre measures have finite moments of all orders. -/
theorem integrable_norm_pow_tubeNormalMeasure (k : ℕ) (x : Fin d → ℝ) :
    Integrable (fun ξ : ↥(A.normal x) => ‖ξ‖ ^ k) (tubeNormalMeasure T C x) := by
  unfold tubeNormalMeasure
  split_ifs with hx
  · exact integrable_norm_pow_map' (rowFrameEquiv A C.i hx.1 (C.mem_V_of_mem hx) :
      (Fin r → ℝ) →L[ℝ] ↥(A.normal x)) (integrable_norm_pow_tubeFibre T C (C.ft x) k)
  · exact integrable_zero_measure

theorem momentFunctional_congr_measure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [OpensMeasurableSpace E] {k : ℕ} {μ ν : Measure E} (h : μ = ν)
    (hμ : Integrable (fun u => ‖u‖ ^ k) μ) (hν : Integrable (fun u => ‖u‖ ^ k) ν)
    (α : JetForm E k) : momentFunctional μ hμ α = momentFunctional ν hν α := by
  subst h
  rfl

/-- **Frame removal, termwise**: in the row frame the invariant contraction at `emb z` is the
`k`-th Taylor–moment term of the fibre restriction `F ∘ ψ_z`. -/
theorem normalContraction_tube (F : (Fin d → ℝ) → ℝ) {z : Fin (d - r) → ℝ} (hz : z ∈ C.W)
    (k : ℕ) :
    normalContraction A.normal (tubeNormalMeasure T C)
        (integrable_norm_pow_tubeNormalMeasure T C k) (additiveFamily A.normal) F (C.emb z) =
      (k.factorial : ℝ)⁻¹ * momentFunctional (fibreMeasure volume (tubeDensity T C) z)
        (integrable_norm_pow_tubeFibre T C z k) (normalJet (fun n => F (tubeChart C (z, n))) k) :=
          by
  have hx : C.emb z ∈ S ∩ C.V' := C.emb_mem z hz
  set e := rowFrameEquiv A C.i hx.1 (C.mem_V_of_mem hx) with he
  rw [normalContraction_frame' A.normal (additiveFamily A.normal) F (C.emb z)
    (tubeNormalMeasure T C) (integrable_norm_pow_tubeNormalMeasure T C k) e]
  have hmeas : (tubeNormalMeasure T C (C.emb z)).map (e.symm : ↥(A.normal (C.emb z)) →L[ℝ] (Fin r →
    ℝ)) =
      fibreMeasure volume (tubeDensity T C) z := by
    rw [tubeNormalMeasure_of_mem T C hx, C.ft_emb _ hz, ← he, Measure.map_map
      (e.symm : ↥(A.normal (C.emb z)) →L[ℝ] (Fin r → ℝ)).continuous.measurable
        e.continuous.measurable]
    have : ⇑(e.symm : ↥(A.normal (C.emb z)) →L[ℝ] (Fin r → ℝ)) ∘ ⇑e = id := e.symm_comp_self
    rw [this, Measure.map_id]
  have hfun : (fun v : Fin r → ℝ => F (additiveFamily A.normal (C.emb z) (e v))) =
      fun n => F (tubeChart C (z, n)) := by
    funext v
    rw [additiveFamily_apply, he, rowFrameEquiv_apply_coe]
    rfl
  rw [momentFunctional_congr_measure hmeas _ (integrable_norm_pow_tubeFibre T C z k), hfun,
    map_smul, smul_eq_mul]
  rfl

/-- **`eq:tubular_expansion`, coordinate-free, on strucdual's tube**: for `F` integrable on the
tube piece whose fibre restrictions have power series at `0` carrying the fibre measures and
dominating their moments,
`∫_{U ∩ proj⁻¹V'} F dy = ∫_z 1_W(z) ∑_k ⟨D^k_⊥F(emb z), 𝖬_k(emb z)⟩ dz`, with `D^k_⊥F` the
normal Taylor form of the additive family (the restricted ambient jet) and `𝖬_k` the moments of
the pulled-back Lebesgue density on the ambient normal spaces. -/
theorem integral_tube_piece_eq_tsum_normalContraction {F : (Fin d → ℝ) → ℝ}
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
        normalContraction A.normal (tubeNormalMeasure T C)
          (integrable_norm_pow_tubeNormalMeasure T C k) (additiveFamily A.normal) F
          (C.emb z)) z := by
  rw [integral_tube_piece_eq_tsum_moment T C hF hq hη hdom]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  by_cases hz : z ∈ C.W
  · rw [indicator_of_mem hz, indicator_of_mem hz]
    exact tsum_congr fun k => (normalContraction_tube T C F hz k).symm
  · rw [indicator_of_notMem hz, indicator_of_notMem hz]

end NormalMeasure

end Grammar
