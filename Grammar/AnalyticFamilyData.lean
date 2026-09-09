/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.LpContinuity
import Grammar.PolyCoeffParam
import Grammar.PopulationDataBridge

/-!
# Analytic families of amplitudes are admissible tangential data (Programme Q, N3, unit 311)

The paper's chart amplitude after a tangential-only cutoff is `ρ_I(v) c(v,u) (φ∘π)(v,u)`: for each
tangential point `v` an analytic function of the normal variable `u`, jointly continuous in `(v,u)`.
This file turns such a family into the zero-noise tangential data of Programme S/P without any
geometric construction. Hypotheses on `F : X → (Fin d → ℂ) → ℂ` (radii `1 < r < R`):

* each `F x` is holomorphic on the open polydisc of radius `R`;
* `(x, w) ↦ F x w` is continuous on `X × closedPolydisc d r`;
* `‖F x w‖ ≤ M` on `X × closedPolydisc d r` (uniform bound; automatic from joint continuity when `X`
  is compact, but stated as a hypothesis).

Then `analyticDatum F x := ofFamilies 1 0 (polyRealCoeff d r (F x))` (zero phase, real Cauchy
coefficients at radius `r`) is a datum with `xiCoord = 0` and `etaCoord = polyRealCoeff d r (F x)`;
the map `x ↦ analyticDatum F x` is continuous into `DataSpace d` (`continuous_analyticDatum`, by the
ℓ¹ criterion with coordinatewise continuity and the geometric majorant `M r^{-|γ|}`, summable since
`r > 1`); and the represented amplitude is the real part of `F x` on the closed cube
(`dataAmplitude_analyticDatum`, reconstruction). For a compact `K` this gives
`analyticTangential F : TangentialData K d` with zero noise (`xiCoord_analyticTangential`).

This closes the non-claim "analytic admissibility of localised amplitudes" for the case the paper
uses (tangential-only cutoffs), given a common holomorphic neighbourhood with a strict radius gap;
it does not construct such a neighbourhood or the cutoff. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

open CoeffFamily

variable {X : Type*} [TopologicalSpace X] {d : ℕ}

/-- The zero-noise datum of an analytic amplitude: real Cauchy coefficients at radius `r`. -/
noncomputable def analyticDatum {r R : ℝ} (hr : 0 < r) (hrR : r < R) (h1r : 1 < r)
    (F : X → (Fin d → ℂ) → ℂ) (hF : ∀ x, DifferentiableOn ℂ (F x) (openPolydisc d R)) (x : X) :
    DataSpace d :=
  ofFamilies 1 one_pos 0 (polyRealCoeff d r (F x)) (absSummableAt_zero 1)
    (absSummableAt_polyRealCoeff hr hrR zero_le_one h1r (hF x))

omit [TopologicalSpace X] in
theorem analyticDatum_inl {r R : ℝ} (hr : 0 < r) (hrR : r < R) (h1r : 1 < r)
    (F : X → (Fin d → ℂ) → ℂ) (hF : ∀ x, DifferentiableOn ℂ (F x) (openPolydisc d R)) (x : X)
    (γ : Fin d → ℕ) : analyticDatum hr hrR h1r F hF x (Sum.inl γ) = 0 := by
  change (0 : CoeffFamily d) γ * (1 : ℝ) ^ (∑ i, γ i) = 0
  simp

omit [TopologicalSpace X] in
theorem analyticDatum_inr {r R : ℝ} (hr : 0 < r) (hrR : r < R) (h1r : 1 < r)
    (F : X → (Fin d → ℂ) → ℂ) (hF : ∀ x, DifferentiableOn ℂ (F x) (openPolydisc d R)) (x : X)
    (γ : Fin d → ℕ) :
    analyticDatum hr hrR h1r F hF x (Sum.inr γ) = (polyCoeff d r (F x) γ).re := by
  change polyRealCoeff d r (F x) γ * (1 : ℝ) ^ (∑ i, γ i) = _
  simp [polyRealCoeff]

omit [TopologicalSpace X] in
/-- **Zero noise.** -/
theorem xiCoord_analyticDatum {r R : ℝ} (hr : 0 < r) (hrR : r < R) (h1r : 1 < r)
    (F : X → (Fin d → ℂ) → ℂ) (hF : ∀ x, DifferentiableOn ℂ (F x) (openPolydisc d R)) (x : X) :
    xiCoord (analyticDatum hr hrR h1r F hF x) = 0 := by
  funext γ
  exact analyticDatum_inl hr hrR h1r F hF x γ

omit [TopologicalSpace X] in
theorem etaCoord_analyticDatum {r R : ℝ} (hr : 0 < r) (hrR : r < R) (h1r : 1 < r)
    (F : X → (Fin d → ℂ) → ℂ) (hF : ∀ x, DifferentiableOn ℂ (F x) (openPolydisc d R)) (x : X) :
    etaCoord (analyticDatum hr hrR h1r F hF x) = polyRealCoeff d r (F x) := by
  funext γ
  exact analyticDatum_inr hr hrR h1r F hF x γ

/-- The geometric majorant on the data index. -/
noncomputable def geomMajorant (d : ℕ) (r M : ℝ) : DataIdx d → ℝ :=
  Sum.elim (fun _ => 0) fun γ => M * r⁻¹ ^ (∑ i, γ i)

theorem summable_geomMajorant (d : ℕ) {r : ℝ} (h1r : 1 < r) (M : ℝ) :
    Summable (geomMajorant d r M) := by
  refine Summable.sum _ ?_ ?_
  · simp [geomMajorant]
  · have hq : Summable fun γ : Fin d → ℕ => ∏ i, r⁻¹ ^ γ i :=
      summable_prodGeom d (q := fun _ => r⁻¹) (fun _ => by positivity)
        (fun _ => inv_lt_one_of_one_lt₀ h1r)
    refine (hq.mul_left M).congr fun γ => ?_
    simp [geomMajorant, Finset.prod_pow_eq_pow_sum]

/-- **Continuity of the analytic datum** into the data space. -/
theorem continuous_analyticDatum {r R M : ℝ} (hr : 0 < r) (hrR : r < R) (h1r : 1 < r)
    (F : X → (Fin d → ℂ) → ℂ) (hF : ∀ x, DifferentiableOn ℂ (F x) (openPolydisc d R))
    (hFc : ContinuousOn (fun p : X × (Fin d → ℂ) => F p.1 p.2) (univ ×ˢ closedPolydisc d r))
    (hM : ∀ x, ∀ w ∈ closedPolydisc d r, ‖F x w‖ ≤ M) :
    Continuous (analyticDatum hr hrR h1r F hF) := by
  refine continuous_dataSpace_of_majorant _ ?_ (geomMajorant d r M) (summable_geomMajorant d h1r M)
    ?_
  · rintro (γ | γ)
    · simp only [analyticDatum_inl]
      exact continuous_const
    · simp only [analyticDatum_inr]
      exact continuous_polyRealCoeff_param hr hFc γ
  · rintro x (γ | γ)
    · simp [analyticDatum_inl, geomMajorant]
    · rw [analyticDatum_inr]
      simp only [geomMajorant, Sum.elim_inr]
      refine (Complex.abs_re_le_norm _).trans (norm_polyCoeff_le hr (fun w hw => ?_) γ)
      exact hM x w (torusSet_subset_closedPolydisc d r hw)

/-- Reconstruction of a holomorphic amplitude from its real Cauchy coefficients at any real point
of the open polydisc. -/
theorem evalF_polyRealCoeff_of_lt {R r : ℝ} (hr : 0 < r) (hrR : r < R) {F : (Fin d → ℂ) → ℂ}
    (hF : DifferentiableOn ℂ F (openPolydisc d R)) {u : Fin d → ℝ}
    (hu : ∀ i, ‖(u i : ℂ)‖ < r) :
    evalF (polyRealCoeff d r F) u = (F fun i => (u i : ℂ)).re := by
  obtain ⟨M, hM⟩ := exists_bound_closedPolydisc hrR hF
  have hslice := sliceHolo_of_differentiableOn d hr hrR hF
  have h := hasSum_polyCoeff d hr hslice hM (mem_openPolydisc.2 hu)
  have h2 := h.mapL Complex.reCLM
  unfold evalF polyRealCoeff
  refine (h2.congr_fun fun γ => ?_).tsum_eq
  simp only [Complex.reCLM_apply]
  rw [show (∏ i, ((u i : ℂ)) ^ γ i) = ((∏ i, u i ^ γ i : ℝ) : ℂ) by push_cast; rfl,
    Complex.re_mul_ofReal]
  rfl

/-- **Reconstruction**: the represented amplitude of the analytic datum is `Re (F x)` on the
closed cube. -/
theorem dataAmplitude_analyticDatum {r R : ℝ} (hr : 0 < r) (hrR : r < R) (h1r : 1 < r)
    (F : X → (Fin d → ℂ) → ℂ) (hF : ∀ x, DifferentiableOn ℂ (F x) (openPolydisc d R)) (x : X)
    {u : Fin d → ℝ} (hu : u ∈ closedCube d) :
    dataAmplitude (analyticDatum hr hrR h1r F hF x) u = (F x fun i => (u i : ℂ)).re := by
  rw [dataAmplitude_eq_of_mem _ hu, etaCoord_analyticDatum]
  refine evalF_polyRealCoeff_of_lt hr hrR (hF x) fun i => ?_
  have hi := Set.mem_univ_pi.1 hu i
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hi.1]
  exact lt_of_le_of_lt hi.2 h1r

variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K] [MeasurableSpace K]
  [OpensMeasurableSpace K]

/-- **The tangential data of an analytic family** on a compact tangential space. -/
noncomputable def analyticTangential {r R M : ℝ} (hr : 0 < r) (hrR : r < R) (h1r : 1 < r)
    (F : K → (Fin d → ℂ) → ℂ) (hF : ∀ v, DifferentiableOn ℂ (F v) (openPolydisc d R))
    (hFc : ContinuousOn (fun p : K × (Fin d → ℂ) => F p.1 p.2) (univ ×ˢ closedPolydisc d r))
    (hM : ∀ v, ∀ w ∈ closedPolydisc d r, ‖F v w‖ ≤ M) : TangentialData K d :=
  ⟨analyticDatum hr hrR h1r F hF, continuous_analyticDatum hr hrR h1r F hF hFc hM⟩

omit [CompactSpace K] [T2Space K] [MeasurableSpace K] [OpensMeasurableSpace K] in
theorem analyticTangential_apply {r R M : ℝ} (hr : 0 < r) (hrR : r < R) (h1r : 1 < r)
    (F : K → (Fin d → ℂ) → ℂ) (hF : ∀ v, DifferentiableOn ℂ (F v) (openPolydisc d R))
    (hFc : ContinuousOn (fun p : K × (Fin d → ℂ) => F p.1 p.2) (univ ×ˢ closedPolydisc d r))
    (hM : ∀ v, ∀ w ∈ closedPolydisc d r, ‖F v w‖ ≤ M) (v : K) :
    analyticTangential hr hrR h1r F hF hFc hM v = analyticDatum hr hrR h1r F hF v := rfl

omit [CompactSpace K] [T2Space K] [MeasurableSpace K] [OpensMeasurableSpace K] in
/-- The analytic tangential data have zero noise. -/
theorem xiCoord_analyticTangential {r R M : ℝ} (hr : 0 < r) (hrR : r < R) (h1r : 1 < r)
    (F : K → (Fin d → ℂ) → ℂ) (hF : ∀ v, DifferentiableOn ℂ (F v) (openPolydisc d R))
    (hFc : ContinuousOn (fun p : K × (Fin d → ℂ) => F p.1 p.2) (univ ×ˢ closedPolydisc d r))
    (hM : ∀ v, ∀ w ∈ closedPolydisc d r, ‖F v w‖ ≤ M) (v : K) :
    xiCoord (analyticTangential hr hrR h1r F hF hFc hM v) = 0 :=
  xiCoord_analyticDatum hr hrR h1r F hF v

end Grammar
