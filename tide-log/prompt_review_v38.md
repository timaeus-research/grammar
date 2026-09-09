# Fidelity review v38 — units 309–312 (Programme Q, N3: analytic amplitude families are admissible tangential data)

Context: your #38 design and review v37 (N1 PASS; GO N3 with the eight-unit list: ℓ¹ continuity criterion; continuity of Cauchy coefficients in the parameter; uniform geometric majorant; continuous coefficient-family map; reconstruction; zero-noise `ofFamilies`/`TangentialData` wrapper; multiplication by a continuous tangential factor; public bridge — "units 2–4 must use the actual weighted coordinates of `DataSpace`", "reconstruction is essential", "a strict radius gap", no construction of the cutoff or the common neighbourhood). N3 is implemented in four units (309–312). Everything compiles (branch `tide/programme-q`, no `sorry`, no added `axiom`).

Frozen interfaces:
```lean
abbrev DataIdx (d : ℕ) : Type := (Fin d → ℕ) ⊕ (Fin d → ℕ);  abbrev DataSpace (d : ℕ) : Type := lp (fun _ : DataIdx d => ℝ) 1
theorem dataNorm_eq_tsum_abs (x : DataSpace d) : ‖x‖ = ∑' i, |x i|;   theorem summable_abs_coord (x : DataSpace d) : Summable fun i => |x i|
noncomputable def ofFamilies (b : ℝ) (hb : 0 < b) (cξ cη : CoeffFamily d) (hξ : AbsSummableAt cξ b) (hη : AbsSummableAt cη b) : DataSpace d :=
  ⟨Sum.elim (fun γ => cξ γ * b ^ (∑ i, γ i)) (fun γ => cη γ * b ^ (∑ i, γ i)), _⟩
def xiCoord (x : DataSpace d) : CoeffFamily d := fun γ => x (Sum.inl γ);  def etaCoord … := fun γ => x (Sum.inr γ)
noncomputable def polyCoeff (d : ℕ) (r : ℝ) (F : (Fin d → ℂ) → ℂ) (γ : Fin d → ℕ) : ℂ := iterOp d r fun w => F w * ∏ i, (w i)⁻¹ ^ γ i
theorem norm_polyCoeff_le {d : ℕ} {r M : ℝ} (hr : 0 < r) {F} (hF : ∀ w ∈ torusSet d r, ‖F w‖ ≤ M) (γ) : ‖polyCoeff d r F γ‖ ≤ M * r⁻¹ ^ (∑ i, γ i)
theorem hasSum_polyCoeff : ∀ (d : ℕ) {r M : ℝ}, 0 < r → ∀ {F}, SliceHolo d r F → (∀ w ∈ closedPolydisc d r, ‖F w‖ ≤ M) → ∀ {z}, z ∈ openPolydisc d r → HasSum (fun γ => polyCoeff d r F γ * ∏ i, z i ^ γ i) (F z)
theorem sliceHolo_of_differentiableOn : ∀ (d : ℕ) {r R : ℝ}, 0 < r → r < R → ∀ {F}, DifferentiableOn ℂ F (openPolydisc d R) → SliceHolo d r F
theorem exists_bound_closedPolydisc {d} {R r} (hrR : r < R) {F} (hF : DifferentiableOn ℂ F (openPolydisc d R)) : ∃ M, ∀ w ∈ closedPolydisc d r, ‖F w‖ ≤ M
noncomputable def polyRealCoeff (d : ℕ) (r : ℝ) (F : (Fin d → ℂ) → ℂ) : CoeffFamily d := fun γ => (polyCoeff d r F γ).re
theorem absSummableAt_polyRealCoeff {d} {R r b : ℝ} (hr : 0 < r) (hrR : r < R) (hb : 0 ≤ b) (hbr : b < r) {F} (hF : DifferentiableOn ℂ F (openPolydisc d R)) : AbsSummableAt (polyRealCoeff d r F) b
theorem continuousOn_iterOp_param : ∀ (d : ℕ) {X} [TopologicalSpace X] {r : ℝ}, 0 < r → ∀ {G : X → (Fin d → ℂ) → ℂ} {S : Set X}, ContinuousOn (fun p : X × (Fin d → ℂ) => G p.1 p.2) (S ×ˢ torusSet d r) → ContinuousOn (fun x => iterOp d r (G x)) S
theorem summable_prodGeom : ∀ (d : ℕ) {q : Fin d → ℝ}, (∀ i, 0 ≤ q i) → (∀ i, q i < 1) → Summable fun γ : Fin d → ℕ => ∏ i, q i ^ γ i
def torusSet (d : ℕ) (r : ℝ) : Set (Fin d → ℂ) := Set.pi univ fun _ => Metric.sphere 0 r;  closedPolydisc/openPolydisc likewise with closedBall/ball; mem_openPolydisc : z ∈ openPolydisc d r ↔ ∀ i, ‖z i‖ < r
abbrev TangentialData (K) (d : ℕ) := C(K, DataSpace d);  tanIntegral ν n h k β N b x = ∫ v, dataBoxIntegral n h k β N b (x v) ∂ν
-- unit 299: dataBoxIntegral_population (hx : xiCoord x = 0) : dataBoxIntegral n h k β N 1 x = origPhaseIntegral n h k β N 1 (fun _ => 0) (dataAmplitude x);  dataAmplitude x u = evalF (etaCoord x) (cubeClamp u);  dataAmplitude_eq_of_mem (hu : u ∈ closedCube d) : dataAmplitude x u = evalF (etaCoord x) u
-- unit 300: tanIntegral_population_tendsto (x : TangentialData K (n+1)) (hx : ∀ v, xiCoord (x v) = 0) … : Tendsto (fun N => tanIntegral ν n h k β N 1 x / (N^(-l) * log N^(m-1))) atTop (𝓝 (∫ v, amplitudeCoeff h k l β (dataAmplitude (x v)) ∂ν))
-- unit 307: isEquivalent_of_tendsto_remainder (ht : Tendsto (fun N => Z N / (N^(-μ) * log N^j)) atTop (𝓝 c)) (hc : c ≠ 0) : Z ~[atTop] fun N => c * (N^(-μ) * log N^j)
theorem faceProj_mapsTo {d} (h k) (l) : MapsTo (faceProj h k l) (unitBox d) (closedCube d)
```

## The four units (complete files)

### Grammar/LpContinuity.lean
```lean
/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.StochasticData

/-!
# Continuity into weighted ℓ¹ from coordinatewise continuity and a summable majorant
(Programme Q, N3, unit 309)

The tangential-data interface of Programme S represents a chart datum as an element of the ℓ¹ data
space, and a tangential family as a *continuous* map `K → DataSpace d`. Coefficientwise continuity
does not give ℓ¹ continuity; a common summable majorant does:
```
(∀ i, Continuous (fun x => F x i))  ∧  (∀ x i, |F x i| ≤ B i)  ∧  Summable B   ⇒   Continuous F
```
(`continuous_dataSpace_of_majorant`). Proof: `‖F x − F x₀‖ = ∑ᵢ |F x i − F x₀ i|`; split at a finite
set `s` whose complementary tail of `B` is small (`tendsto_tsum_compl_atTop_zero`); the head is a
finite sum of continuous functions vanishing at `x₀`, the tail is bounded by `2 ∑_{i∉s} B i`. This
is
the generic criterion Astra #38/review v37 asked for; the analytic-family application (Cauchy
coefficients with the geometric majorant `M (b/r)^{|γ|}`) follows in the next units.
Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

/-- **ℓ¹ continuity from a summable majorant**: coordinatewise continuous, uniformly dominated by a
summable `B`, hence continuous into the data space. -/
theorem continuous_dataSpace_of_majorant {X : Type*} [TopologicalSpace X] {d : ℕ}
    (F : X → DataSpace d) (hcoord : ∀ i, Continuous fun x => F x i) (B : DataIdx d → ℝ)
    (hB : Summable B) (hbound : ∀ x i, |F x i| ≤ B i) : Continuous F := by
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  -- a finite set outside which the majorant's tail is small
  have htail := tendsto_tsum_compl_atTop_zero B
  obtain ⟨s, hs⟩ := (htail.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 4))).exists
  -- the head tends to zero
  have hhead : Tendsto (fun x => ∑ i ∈ s, |F x i - F x₀ i|) (𝓝 x₀) (𝓝 0) := by
    have : Tendsto (fun x => ∑ i ∈ s, |F x i - F x₀ i|) (𝓝 x₀)
        (𝓝 (∑ i ∈ s, |F x₀ i - F x₀ i|)) :=
      tendsto_finsetSum _ fun i _ => (((hcoord i).tendsto x₀).sub_const _).abs
    simpa using this
  filter_upwards [hhead.eventually (gt_mem_nhds (half_pos hε))] with x hx
  rw [dist_eq_norm, dataNorm_eq_tsum_abs]
  have hsum : Summable fun i => |(F x - F x₀) i| := summable_abs_coord _
  have hcoe : ∀ i, (F x - F x₀) i = F x i - F x₀ i := fun i => by
    rw [lp.coeFn_sub, Pi.sub_apply]
  simp only [hcoe] at hsum ⊢
  rw [← hsum.sum_add_tsum_compl (s := s)]
  have hle : ∀ i, |F x i - F x₀ i| ≤ 2 * B i := fun i =>
    (abs_sub _ _).trans (by linarith [hbound x i, hbound x₀ i])
  have htail_le : ∑' i : ↑(↑s : Set (DataIdx d))ᶜ, |F x i - F x₀ i| ≤
      ∑' i : ↑(↑s : Set (DataIdx d))ᶜ, 2 * B i :=
    Summable.tsum_le_tsum (fun i => hle i) (hsum.subtype _) ((hB.mul_left 2).subtype _)
  rw [tsum_mul_left] at htail_le
  have hs' : ∑' i : ↑(↑s : Set (DataIdx d))ᶜ, B i < ε / 4 := hs
  linarith

end Grammar
```

### Grammar/PolyCoeffParam.lean
```lean
/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.CircleOpParam
import Grammar.PolydiscCoeff

/-!
# Cauchy coefficients depend continuously on a parameter (Programme Q, N3, unit 310)

For a family `F : X → (Fin d → ℂ) → ℂ` jointly continuous on `X × (closed polydisc of radius r)`,
each Cauchy coefficient `polyCoeff d r (F x) γ = A_r^{[d]}(w ↦ F x w ∏ wᵢ^{-γᵢ})` is a continuous
function of `x` (`continuous_polyCoeff_param`): the integrand is jointly continuous on
`X × torus`, where every `wᵢ` has modulus `r > 0`, and the iterated circle operator is continuous in
parameters (`continuousOn_iterOp_param`). With the uniform Cauchy estimate
`‖polyCoeff d r (F x) γ‖ ≤ M r^{-|γ|}` (`norm_polyCoeff_le`) this is the coordinatewise input to
the ℓ¹ criterion of unit 309. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

/-- The monomial factor `w ↦ ∏ wᵢ^{-γᵢ}` is continuous on the torus. -/
theorem continuousOn_torus_monomial_inv {d : ℕ} {r : ℝ} (hr : 0 < r) (γ : Fin d → ℕ) :
    ContinuousOn (fun w : Fin d → ℂ => ∏ i, (w i)⁻¹ ^ γ i) (torusSet d r) := by
  refine continuousOn_finsetProd _ fun i _ => ?_
  refine ((continuous_apply i).continuousOn.inv₀ fun w hw => ?_).pow _
  have := (mem_torusSet.1 hw) i
  intro h0
  rw [h0, norm_zero] at this
  linarith

/-- **Parametric continuity of the Cauchy coefficients**: for `F` jointly continuous on
`X × closedPolydisc d r`, `x ↦ polyCoeff d r (F x) γ` is continuous. -/
theorem continuous_polyCoeff_param {X : Type*} [TopologicalSpace X] {d : ℕ} {r : ℝ} (hr : 0 < r)
    {F : X → (Fin d → ℂ) → ℂ}
    (hF : ContinuousOn (fun p : X × (Fin d → ℂ) => F p.1 p.2) (univ ×ˢ closedPolydisc d r))
    (γ : Fin d → ℕ) : Continuous fun x => polyCoeff d r (F x) γ := by
  rw [← continuousOn_univ]
  unfold polyCoeff
  refine continuousOn_iterOp_param d hr (G := fun x w => F x w * ∏ i, (w i)⁻¹ ^ γ i) (S := univ) ?_
  have hsub : (univ : Set X) ×ˢ torusSet d r ⊆ univ ×ˢ closedPolydisc d r :=
    Set.prod_mono le_rfl (torusSet_subset_closedPolydisc d r)
  refine (hF.mono hsub).mul ?_
  exact (continuousOn_torus_monomial_inv hr γ).comp continuousOn_snd fun p hp => hp.2

/-- The real parts of the Cauchy coefficients are continuous in the parameter. -/
theorem continuous_polyRealCoeff_param {X : Type*} [TopologicalSpace X] {d : ℕ} {r : ℝ}
    (hr : 0 < r) {F : X → (Fin d → ℂ) → ℂ}
    (hF : ContinuousOn (fun p : X × (Fin d → ℂ) => F p.1 p.2) (univ ×ˢ closedPolydisc d r))
    (γ : Fin d → ℕ) : Continuous fun x => (polyCoeff d r (F x) γ).re :=
  Complex.continuous_re.comp (continuous_polyCoeff_param hr hF γ)

end Grammar
```

### Grammar/AnalyticFamilyData.lean
```lean
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
```

### Grammar/AnalyticFamilyBridge.lean
```lean
/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.AnalyticFamilyData
import Grammar.PopulationTangential
import Grammar.FirstNonzeroAsymptotic

/-!
# The public bridge: analytic amplitude families in the stratum theorems (Programme Q, N3, u312)

For an analytic family `F : K → (Fin (n+1) → ℂ) → ℂ` on a compact tangential space (hypotheses of
unit 311: holomorphic on the polydisc of radius `R`, jointly continuous and bounded by `M` on
`K × closedPolydisc r`, `1 < r < R`), the tangential integral of the analytic data is the paper's
stratum integral of the chart population integrals of the real amplitudes `Re F_v`
(`tanIntegral_analyticTangential`), and Theorem A(c) with tangential integration reads
```
∫_K ∫ (Re F_v)(u) u^h e^{-βN u^{2k}} du dν(v) / (N^{-λ}(log N)^{m−1})
      → ∫_K amplitudeCoeff h k λ β (Re F_v) dν(v)              (tanIntegral_analytic_tendsto)
```
with asymptotic equivalence when the integrated face functional is nonzero. A continuous
tangential factor `ρ ∈ C(K, ℝ)` (the paper's cutoff, constant in the normal directions) preserves
the hypotheses (`analyticFamily_smul_*`), with `Re(ρ(v) F_v) = ρ(v) Re F_v`. Only amplitude values
on the closed cube matter (`amplitudeCoeff_congr_closedCube`, `origPhaseIntegral_congr_box`).

Not established: existence of the common holomorphic neighbourhood or of the cutoff; the geometric
origin of `F_v` (chart maps, Jacobians) is external. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology Asymptotics

namespace Grammar

/-- Two amplitudes agreeing on the closed cube have the same face functional. -/
theorem amplitudeCoeff_congr_closedCube {d : ℕ} (h k : Fin d → ℕ) (l β : ℝ)
    {η₁ η₂ : (Fin d → ℝ) → ℝ} (hη : ∀ u ∈ closedCube d, η₁ u = η₂ u) :
    amplitudeCoeff h k l β η₁ = amplitudeCoeff h k l β η₂ := by
  unfold amplitudeCoeff
  congr 1
  refine setIntegral_congr_fun (measurableSet_unitBox d) fun u hu => ?_
  rw [hη _ (faceProj_mapsTo h k l hu)]

/-- Two amplitudes agreeing on the unit box have the same population integral. -/
theorem origPhaseIntegral_congr_box (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N : ℝ)
    {η₁ η₂ : (Fin (n + 1) → ℝ) → ℝ} (hη : ∀ u ∈ unitBox (n + 1), η₁ u = η₂ u) :
    origPhaseIntegral n h k β N 1 (fun _ => 0) η₁ = origPhaseIntegral n h k β N 1 (fun _ => 0) η₂
:= by
  unfold origPhaseIntegral
  have hset : piBox (n + 1) (Ioc (0 : ℝ) 1) = unitBox (n + 1) := rfl
  rw [hset]
  refine setIntegral_congr_fun (measurableSet_unitBox _) fun u hu => ?_
  rw [hη u hu]

variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K] [MeasurableSpace K]
  [OpensMeasurableSpace K] (ν : Measure K) [IsFiniteMeasure ν]

/-- The real amplitude of an analytic family. -/
noncomputable def realAmp {d : ℕ} (F : K → (Fin d → ℂ) → ℂ) (v : K) (u : Fin d → ℝ) : ℝ :=
  (F v fun i => (u i : ℂ)).re

omit [CompactSpace K] [T2Space K] [OpensMeasurableSpace K] [IsFiniteMeasure ν] in
/-- **The tangential integral of analytic data is the stratum integral of the chart population
integrals of `Re F_v`.** -/
theorem tanIntegral_analyticTangential (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N : ℝ) {r R M : ℝ}
    (hr : 0 < r) (hrR : r < R) (h1r : 1 < r) (F : K → (Fin (n + 1) → ℂ) → ℂ)
    (hF : ∀ v, DifferentiableOn ℂ (F v) (openPolydisc (n + 1) R))
    (hFc : ContinuousOn (fun p : K × (Fin (n + 1) → ℂ) => F p.1 p.2)
      (univ ×ˢ closedPolydisc (n + 1) r))
    (hM : ∀ v, ∀ w ∈ closedPolydisc (n + 1) r, ‖F v w‖ ≤ M) :
    tanIntegral ν n h k β N 1 (analyticTangential hr hrR h1r F hF hFc hM) =
      ∫ v, origPhaseIntegral n h k β N 1 (fun _ => 0) (realAmp F v) ∂ν := by
  unfold tanIntegral
  congr 1
  funext v
  rw [analyticTangential_apply, dataBoxIntegral_population n h k β N _
    (xiCoord_analyticDatum hr hrR h1r F hF v)]
  refine origPhaseIntegral_congr_box n h k β N fun u hu => ?_
  exact dataAmplitude_analyticDatum hr hrR h1r F hF v (unitBox_subset_closedCube _ hu)

/-- **Theorem A(c) for an analytic amplitude family on a stratum.** -/
theorem tanIntegral_analytic_tendsto (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (β : ℝ) (hβ : 0 < β) {r R M : ℝ} (hr : 0 < r) (hrR : r < R) (h1r : 1 < r)
    (F : K → (Fin (n + 1) → ℂ) → ℂ) (hF : ∀ v, DifferentiableOn ℂ (F v) (openPolydisc (n + 1) R))
    (hFc : ContinuousOn (fun p : K × (Fin (n + 1) → ℂ) => F p.1 p.2)
      (univ ×ˢ closedPolydisc (n + 1) r))
    (hM : ∀ v, ∀ w ∈ closedPolydisc (n + 1) r, ‖F v w‖ ≤ M) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l) :
    Tendsto (fun N => (∫ v, origPhaseIntegral n h k β N 1 (fun _ => 0) (realAmp F v) ∂ν) /
        (N ^ (-l) * Real.log N ^ (multCount (ratioExp h k) l - 1))) atTop
      (𝓝 (∫ v, amplitudeCoeff h k l β (realAmp F v) ∂ν)) := by
  have hT := tanIntegral_population_tendsto ν n h k hk β hβ
    (analyticTangential hr hrR h1r F hF hFc hM) (xiCoord_analyticTangential hr hrR h1r F hF hFc hM)
    hmin hatt
  have hamp : ∀ v, amplitudeCoeff h k l β (dataAmplitude (analyticTangential hr hrR h1r F hF hFc hM
v)) =
      amplitudeCoeff h k l β (realAmp F v) := fun v =>
    amplitudeCoeff_congr_closedCube h k l β fun u hu => by
      rw [analyticTangential_apply]
      exact dataAmplitude_analyticDatum hr hrR h1r F hF v hu
  simp only [hamp] at hT
  refine hT.congr' (Eventually.of_forall fun N => ?_)
  rw [tanIntegral_analyticTangential ν n h k β N hr hrR h1r F hF hFc hM]

/-- Asymptotic equivalence when the integrated face functional is nonzero. -/
theorem tanIntegral_analytic_isEquivalent (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (β : ℝ) (hβ : 0 < β) {r R M : ℝ} (hr : 0 < r) (hrR : r < R) (h1r : 1 < r)
    (F : K → (Fin (n + 1) → ℂ) → ℂ) (hF : ∀ v, DifferentiableOn ℂ (F v) (openPolydisc (n + 1) R))
    (hFc : ContinuousOn (fun p : K × (Fin (n + 1) → ℂ) => F p.1 p.2)
      (univ ×ˢ closedPolydisc (n + 1) r))
    (hM : ∀ v, ∀ w ∈ closedPolydisc (n + 1) r, ‖F v w‖ ≤ M) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (hA : (∫ v, amplitudeCoeff h k l β (realAmp F v) ∂ν) ≠ 0) :
    (fun N => ∫ v, origPhaseIntegral n h k β N 1 (fun _ => 0) (realAmp F v) ∂ν) ~[atTop]
      fun N => (∫ v, amplitudeCoeff h k l β (realAmp F v) ∂ν) *
        (N ^ (-l) * Real.log N ^ (multCount (ratioExp h k) l - 1)) :=
  isEquivalent_of_tendsto_remainder
    (tanIntegral_analytic_tendsto ν n h k hk β hβ hr hrR h1r F hF hFc hM hmin hatt) hA

omit [CompactSpace K] [T2Space K] [MeasurableSpace K] [OpensMeasurableSpace K] in
/-- **A continuous tangential factor preserves the hypotheses**: holomorphy… -/
theorem analyticFamily_smul_differentiableOn {d : ℕ} {R : ℝ} (ρ : C(K, ℝ))
    (F : K → (Fin d → ℂ) → ℂ) (hF : ∀ v, DifferentiableOn ℂ (F v) (openPolydisc d R)) (v : K) :
    DifferentiableOn ℂ (fun w => ((ρ v : ℝ) : ℂ) * F v w) (openPolydisc d R) :=
  (hF v).const_mul _

omit [CompactSpace K] [T2Space K] [MeasurableSpace K] [OpensMeasurableSpace K] in
/-- …joint continuity… -/
theorem analyticFamily_smul_continuousOn {d : ℕ} {r : ℝ} (ρ : C(K, ℝ))
    (F : K → (Fin d → ℂ) → ℂ)
    (hFc : ContinuousOn (fun p : K × (Fin d → ℂ) => F p.1 p.2) (univ ×ˢ closedPolydisc d r)) :
    ContinuousOn (fun p : K × (Fin d → ℂ) => ((ρ p.1 : ℝ) : ℂ) * F p.1 p.2)
      (univ ×ˢ closedPolydisc d r) :=
  ((Complex.continuous_ofReal.comp (ρ.continuous.comp continuous_fst)).continuousOn).mul hFc

omit [T2Space K] [MeasurableSpace K] [OpensMeasurableSpace K] in
/-- …and the uniform bound (with `‖ρ‖` the sup norm). -/
theorem analyticFamily_smul_bound {d : ℕ} {r M : ℝ} (ρ : C(K, ℝ)) (F : K → (Fin d → ℂ) → ℂ)
    (hM : ∀ v, ∀ w ∈ closedPolydisc d r, ‖F v w‖ ≤ M) (v : K) (w : Fin d → ℂ)
    (hw : w ∈ closedPolydisc d r) : ‖((ρ v : ℝ) : ℂ) * F v w‖ ≤ ‖ρ‖ * M := by
  rw [norm_mul, Complex.norm_real]
  exact mul_le_mul (ρ.norm_coe_le_norm v) (hM v w hw) (norm_nonneg _) (norm_nonneg _)

omit [CompactSpace K] [T2Space K] [MeasurableSpace K] [OpensMeasurableSpace K] in
/-- The real amplitude of the scaled family is the scaled real amplitude. -/
theorem realAmp_smul {d : ℕ} (ρ : C(K, ℝ)) (F : K → (Fin d → ℂ) → ℂ) (v : K) (u : Fin d → ℝ) :
    realAmp (fun v w => ((ρ v : ℝ) : ℂ) * F v w) v u = ρ v * realAmp F v u := by
  simp [realAmp]

end Grammar
```

## Questions
1. u309: is the ℓ¹ criterion correctly proved (head/tail split via `Summable.sum_add_tsum_compl`, tail `≤ 2·tail(B) < ε/2`, head `→ 0`)? Is the coercion subtlety between `{x // x ∉ s}` and `↑(↑s)ᶜ` handled honestly (`hs' : … := hs` is a defeq cast)?
2. u310: is the joint-continuity hypothesis on `X × closedPolydisc d r` the right one, and the torus invertibility argument sound?
3. u311: does `analyticDatum` use the ACTUAL weighted coordinates (`ofFamilies 1 …`, so the encoding weight is `1^{|γ|} = 1` and the geometric majorant is `M r^{-|γ|}`, summable only because `r > 1` — is the strict gap `1 < r` correctly placed and essential)? Are `xiCoord_analyticDatum`/`etaCoord_analyticDatum` correct (the `change` steps unfold `ofFamilies` coordinates)? Is the reconstruction `dataAmplitude_analyticDatum` faithful (real Cauchy coefficients at radius `r` reconstruct `Re F` at real points of norm `< r`, in particular on the closed cube)? Is the bound hypothesis `hM` stated on the closed polydisc but used only on the torus legitimate?
4. u312: is the public bridge what N3 promised — the tangential integral of the analytic data equals the stratum integral of the chart population integrals of `Re F_v`, and Theorem A(c) transfers with the face functional of `Re F_v`? Are the `ρ`-lemmas an adequate rendering of "multiplication by a continuous tangential factor" (hypotheses preserved; `Re(ρ F) = ρ Re F`), given no theorem here instantiates the whole bridge for `ρ · F` (the user instantiates u311/u312 with the scaled family)?
5. Non-claims for N3; blocking/nonblocking fixes; and the N2 gate design. For N2 I found a clean coefficient route: with `M(μ,i) := fluctMoment β 0 0 μ i = ∫₀^∞ t^{μ−1}(−log t)^i e^{−βt} dt`, integration by parts gives `M(μ+1, i) = (μ M(μ,i) − i M(μ,i−1))/β`; the shifted state density `ρ_{h+2k+γ}(t) = t·ρ_{h+γ}(t)` (all exponents shift by one, coefficients unchanged: `stateDensityRep n (w+1) = shift 1 (stateDensityRep n w)` from `monoWeights (h+2k) k = monoWeights h k + 1`); hence in `kernelS` (`∑_{q=j}^{n} coeffAt(ρ_{h+γ}, μ, q) C(q,j) M(μ, q−j)`) the shifted coefficient is `C_K(μ+1, j) = (μ C(μ,j) − (j+1) C(μ,j+1))/β` for EVERY μ, j (using `C(q,j)(q−j) = (j+1) C(q,j+1)`). At `j = m−1` this recovers `A_K = (λ/β)A` (u304, since `C(λ,m) = 0`); at `j = m−2` it gives `B_K = (λB − (m−1)A)/β` — your Route B target. Do you agree this identity is the right N2 gate deliverable (unit 314) alongside the exact derivative identity (unit 313), and that the two-term quotient (unit 315) then needs only: the population `CutoffExpansion` at cutoff `λ + 1/Q` with the isolated exponent (u293's `spectralSum_isolated`) to get `Z = N^{-λ}(A log^{m−1} + B log^{m−2} + lower) + O(N^{-L})`, i.e. `Z/(N^{-λ} log^{m−2}) − A log N → B`? Any subtlety with `m = 1` (no `B` term; then `Z_K/Z = λ/(βN) + o(1/(N log N))` needs the remainder `o(N^{-λ}/log N)` which the cutoff expansion gives)?

Verdict per unit (PASS / qualified / FAIL), blocking fixes, nonblocking should-fixes. The files above are complete, not extractor output.
