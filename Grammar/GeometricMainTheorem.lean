/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.ChartTaylorMoment

/-!
# The conditional geometric main theorem

Assembly of the geometric bridge (Headlines CVII–CXII) into the paper's main expansion theorem,
conditional on a certified resolution presentation:

* `cutoffExpansion_of_exp_small`: an exponentially small residual is a cutoff expansion with zero
  coefficients; hence (`AdaptedStrataData.cutoffExpansion`, `expansion`) the population integral
  `Z(N) = ∫ F e^{−NK} dμ` of a localisation datum with adapted strata data has, for every cutoff
  `L`, the quantitative power–log expansion `|Z(N) − ∑_{μ<L} N^{−μ} ∑_j gCoeff_{μ,j} log^j N| ≤
  K N^{−L}(1+log N)^D` — `thm:expectation_expansion` with the assembled canonical coefficients.
* `NormalMomentPresentation`: for one chart, analyticity of the observable in the normal fibre
  (`obs ∘ Φ(v,·)` has a power series on a ball containing the box) and boundedness of the density;
  the **raw fibre measure** `|μ|_v = c(v,u) u^h e^{−βN u^{2k}} du` (`fibreMeasure`, raw-moment
  convention with outer measure `ν`); the chart integral is `∫_K ∑_r (1/r!) ⟨Moment_{|μ|_{v,N},r},
  D^r(obs∘Φ_v)(0)⟩ dν(v)` (`tanIntegral_eq_moment_series`), and the assembled integral is the finite
  sum of these plus the exponentially small tail (`AdaptedStrataData.Z_eq_moment_series`); the
  moment series has the canonical coefficients (`momentSeries_cutoffExpansion`).
* `moment_pairing_invariant_of_series`: the moment–jet contraction is invariant under fibre-linear
  frame changes with transported measure, for analytic observables (no global smoothness needed).
* `expectation_expansion_of_adaptedStrataData`: the package.

Non-claims: Hironaka / existence of the presentation; the adapted partition of unity; global
tubular neighbourhoods; canonical higher normal derivatives beyond fibre-linear covariance; removal
of phase units; an asymptotic ordering by normal Taylor degree.
-/

open MeasureTheory Set Filter Topology Asymptotics
open scoped ENNReal NNReal

namespace Grammar

open MonoRep CoeffFamily

/-! ### Exponentially small residuals are cutoff expansions with zero coefficients -/

theorem absSpectralSum_zero (Q D : ℕ) (L N : ℝ) : absSpectralSum Q D (fun _ _ => 0) L N = 0 := by
  simp [absSpectralSum]

theorem cutoffExpansion_of_exp_small (Q D : ℕ) {E : ℝ → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hE : Tendsto (fun N => E N * Real.exp (ε * N)) atTop (𝓝 0)) :
    CutoffExpansion Q D E fun _ _ => 0 := by
  intro L _
  refine ⟨1, ?_⟩
  have h1 := tendsto_div_rpow_of_exp E hε hE L
  filter_upwards [Metric.tendsto_nhds.1 h1 1 one_pos, eventually_ge_atTop (1 : ℝ)] with N hN hN1
  rw [Real.dist_eq, sub_zero] at hN
  have hpos : 0 < N ^ (-L) := Real.rpow_pos_of_pos (by linarith) _
  have hlog : 1 ≤ (1 + Real.log N) ^ D := one_le_pow₀ (by linarith [Real.log_nonneg hN1])
  have habs : |E N| ≤ N ^ (-L) := by
    have := hN.le
    rwa [abs_div, abs_of_pos hpos, div_le_one hpos] at this
  rw [absSpectralSum_zero, sub_zero, one_mul]
  calc |E N| ≤ N ^ (-L) * 1 := by rw [mul_one]; exact habs
    _ ≤ N ^ (-L) * (1 + Real.log N) ^ D := mul_le_mul_of_nonneg_left hlog hpos.le

/-! ### Fibre-linear invariance for analytic observables -/

section Invariance

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : E → ℝ}
  {p : FormalMultilinearSeries ℝ E ℝ} {R : ℝ≥0∞}

theorem normalJet_diag (F : E → ℝ) (r : ℕ) (u : E) :
    normalJet F r (fun _ => u) = (r.factorial : ℝ) * homogeneousTaylor F r u := by
  unfold homogeneousTaylor
  rw [mul_inv_cancel_left₀ (by positivity)]

/-- Covariance of the homogeneous Taylor terms under a linear equivalence, for analytic `F`
(no global smoothness): `T_r(F ∘ L⁻¹)(u) = T_r F (L⁻¹ u)`. -/
theorem homogeneousTaylor_comp_symm_of_series (hp : HasFPowerSeriesOnBall F p 0 R)
    (L : E ≃L[ℝ] E) (r : ℕ) (u : E) :
    homogeneousTaylor (F ∘ L.symm) r u = homogeneousTaylor F r (L.symm u) := by
  have hp' : HasFPowerSeriesOnBall F p ((L.symm : E →L[ℝ] E) 0) R := by rwa [map_zero]
  have hq := hp'.compContinuousLinearMap
  change homogeneousTaylor (F ∘ ⇑(L.symm : E →L[ℝ] E)) r u = _
  rw [homogeneousTaylor_eq_series hq r u, homogeneousTaylor_eq_series hp r (L.symm u),
    FormalMultilinearSeries.compContinuousLinearMap_apply]
  rfl

variable [MeasurableSpace E] [OpensMeasurableSpace E] [BorelSpace E]

/-- **Invariance of the moment–jet pairing for analytic observables**: with `η' = L_*η` and
`F' = F ∘ L⁻¹`, `⟨Moment_{η'}, D^r F'(0)⟩ = ⟨Moment_η, D^r F(0)⟩`. -/
theorem moment_pairing_invariant_of_series (hp : HasFPowerSeriesOnBall F p 0 R) (L : E ≃L[ℝ] E)
    {η : Measure E} {r : ℕ} (hr : Integrable (fun u => ‖u‖ ^ r) η) :
    momentFunctional (η.map (L : E →L[ℝ] E)) (integrable_norm_pow_map (L : E →L[ℝ] E) hr)
        (normalJet (F ∘ L.symm) r) =
      momentFunctional η hr (normalJet F r) := by
  simp only [momentFunctional_apply]
  rw [integral_map (L : E →L[ℝ] E).continuous.measurable.aemeasurable
    (continuous_diagEval _).aestronglyMeasurable]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  dsimp only
  rw [normalJet_diag, normalJet_diag, homogeneousTaylor_comp_symm_of_series hp L]
  simp

end Invariance

/-! ### Normal-moment presentations of a chart -/

namespace ChartPresentation

variable {U : Type*} [MeasurableSpace U] {D : LocalisationData U} {ρ : U → ℝ} {K : Type*}
  [TopologicalSpace K] [MeasurableSpace K] {n : ℕ} {β : ℝ} (C : ChartPresentation D ρ K n β)

/-- The observable in the normal fibre over `v`: `u ↦ F(Φ(v,u))`. -/
def obsFibre (v : K) (u : Fin (n + 1) → ℝ) : ℝ := D.obs (C.Φ (v, u))

/-- The raw fibre measure `|μ|_{v,N} = c(v,u) u^h e^{−βN u^{2k}} du` on the normal box. -/
noncomputable def fibreMeasure (v : K) (N : ℝ) : Measure (Fin (n + 1) → ℝ) :=
  (dressedMeasure n C.h C.k β N C.b).withDensity fun u => ENNReal.ofReal (C.c (v, u))

theorem fibreMeasure_ac (v : K) (N : ℝ) :
    C.fibreMeasure v N ≪ dressedMeasure n C.h C.k β N C.b :=
  withDensity_absolutelyContinuous _ _

theorem fibreMeasure_ae_norm_le (v : K) (N : ℝ) : ∀ᵐ u ∂C.fibreMeasure v N, ‖u‖ ≤ C.b :=
  (C.fibreMeasure_ac v N).ae_le (dressedMeasure_ae_norm_le n C.h C.k β N C.b C.b_pos)

end ChartPresentation

/-- A normal-moment presentation of a chart: the observable is analytic in the normal fibre on a
ball containing the box, and the density factor is bounded. -/
structure NormalMomentPresentation {U : Type*} [MeasurableSpace U] {D : LocalisationData U}
    {ρ : U → ℝ} {K : Type*} [TopologicalSpace K] [MeasurableSpace K] {n : ℕ} {β : ℝ}
    (C : ChartPresentation D ρ K n β) where
  /-- the fibre power series of the observable -/
  p : K → FormalMultilinearSeries ℝ (Fin (n + 1) → ℝ) ℝ
  /-- the fibre radii -/
  R : K → ℝ≥0∞
  analytic : ∀ v, HasFPowerSeriesOnBall (C.obsFibre v) (p v) 0 (R v)
  radius : ∀ v, ENNReal.ofReal C.b < R v
  /-- a bound for the density factor -/
  cBound : ℝ
  c_le : ∀ q, C.c q ≤ cBound

namespace NormalMomentPresentation

variable {U : Type*} [MeasurableSpace U] {D : LocalisationData U} {ρ : U → ℝ} {K : Type*}
  [TopologicalSpace K] [MeasurableSpace K] {n : ℕ} {β : ℝ} {C : ChartPresentation D ρ K n β}
  (T : NormalMomentPresentation C)
include T

theorem isFiniteMeasure_fibreMeasure (hβ : 0 ≤ β) {N : ℝ} (hN : 0 ≤ N) (v : K) :
    IsFiniteMeasure (C.fibreMeasure v N) := by
  have := isFiniteMeasure_dressedMeasure n C.h C.k β N C.b hβ hN
  unfold ChartPresentation.fibreMeasure
  refine isFiniteMeasure_withDensity (ne_top_of_le_ne_top ?_
    (lintegral_mono fun u => ENNReal.ofReal_le_ofReal (T.c_le (v, u))))
  rw [lintegral_const]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)

theorem integrable_norm_pow_fibre (hβ : 0 ≤ β) {N : ℝ} (hN : 0 ≤ N) (v : K) (r : ℕ) :
    Integrable (fun u => ‖u‖ ^ r) (C.fibreMeasure v N) :=
  haveI := T.isFiniteMeasure_fibreMeasure hβ hN v
  integrable_norm_pow_of_ae_le _ (C.fibreMeasure_ae_norm_le v N) r

/-- The fibre integral of the observable against the raw fibre measure is its Taylor–moment
series. -/
theorem integral_obsFibre_eq_tsum (hβ : 0 ≤ β) {N : ℝ} (hN : 0 ≤ N) (v : K) :
    ∫ u, C.obsFibre v u ∂C.fibreMeasure v N = ∑' r, (r.factorial : ℝ)⁻¹ *
      ∫ u, normalJet (C.obsFibre v) r (fun _ => u) ∂C.fibreMeasure v N := by
  have := T.isFiniteMeasure_fibreMeasure hβ hN v
  exact integral_eq_tsum_moment (T.analytic v) _
    ((C.fibreMeasure_ac v N).ae_le (dressedMeasure_ae_mem_eball C.b_pos (T.radius v)))
    (T.integrable_norm_pow_fibre hβ hN v)
    (summable_norm_mul_integral_of_ae_le _
      ((C.fibreMeasure_ac v N).ae_le (dressedMeasure_ae_norm_le_toNNReal C.b_pos))
      (lt_of_lt_of_le (T.radius v) (T.analytic v).r_le))

/-- **The chart integral as a base integral of fibre Taylor–moment series**:
`𝒵(N) = ∫_K ∑_r (1/r!) ⟨Moment_{|μ|_{v,N},r}, D^r(F∘Φ_v)(0)⟩ dν(v)` for `N ≥ 0`. -/
theorem tanIntegral_eq_moment_series (hβ : 0 ≤ β) {N : ℝ} (hN : 0 ≤ N) :
    tanIntegral C.ν n C.h C.k β N C.b C.x = ∫ v, ∑' r, (r.factorial : ℝ)⁻¹ *
      ∫ u, normalJet (C.obsFibre v) r (fun _ => u) ∂C.fibreMeasure v N ∂C.ν := by
  unfold tanIntegral
  have hA := Measure.ae_ae_of_ae_prod (μ := C.ν)
    (ν := volume.restrict (piBox (n + 1) (Ioc 0 C.b))) C.amplitude_eq
  have hc := Measure.ae_ae_of_ae_prod (μ := C.ν)
    (ν := volume.restrict (piBox (n + 1) (Ioc 0 C.b))) C.nonneg_c
  refine integral_congr_ae ?_
  filter_upwards [hA, hc] with v hAv hcv
  have hac : dressedMeasure n C.h C.k β N C.b ≪ volume.restrict (piBox (n + 1) (Ioc 0 C.b)) :=
    withDensity_absolutelyContinuous _ _
  have hmv : Measurable fun u : Fin (n + 1) → ℝ => ENNReal.ofReal (C.c (v, u)) :=
    (C.measurable_c.comp measurable_prodMk_left).ennreal_ofReal
  rw [dataBoxIntegral_eq_integral_dressed n C.h C.k β N C.b (C.x v) (C.fluct_zero v),
    ← T.integral_obsFibre_eq_tsum hβ hN v]
  unfold ChartPresentation.fibreMeasure
  rw [integral_withDensity_eq_integral_toReal_smul hmv
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae ?_
  filter_upwards [hac.ae_le hAv, hac.ae_le hcv] with u hu1 hu2
  rw [hu1, ENNReal.toReal_ofReal hu2, smul_eq_mul]
  rfl

/-- Invariance of the fibre contractions under a fibrewise linear change of normal frame with
transported fibre measure. -/
theorem contraction_invariant (hβ : 0 ≤ β) {N : ℝ} (hN : 0 ≤ N) (v : K)
    (L : (Fin (n + 1) → ℝ) ≃L[ℝ] (Fin (n + 1) → ℝ)) (r : ℕ) :
    momentFunctional ((C.fibreMeasure v N).map (L : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ)))
        (integrable_norm_pow_map _ (T.integrable_norm_pow_fibre hβ hN v r))
        (normalJet (C.obsFibre v ∘ L.symm) r) =
      momentFunctional (C.fibreMeasure v N) (T.integrable_norm_pow_fibre hβ hN v r)
        (normalJet (C.obsFibre v) r) :=
  moment_pairing_invariant_of_series (T.analytic v) L _

end NormalMomentPresentation

/-! ### The assembled statements -/

namespace AdaptedStrataData

variable {U : Type*} [MeasurableSpace U] {D : LocalisationData U} {M : ℕ} {K : Fin M → Type*}
  [∀ I, TopologicalSpace (K I)] [∀ I, MeasurableSpace (K I)] {n : Fin M → ℕ} {β : ℝ}
  (A : AdaptedStrataData D M K n β)

/-- **The resolved integral as a sum of base integrals of fibre Taylor–moment series** plus the
exponentially small tail, for `N ≥ 0`. -/
theorem Z_eq_moment_series (T : ∀ I, NormalMomentPresentation (A.chart I)) (hβ : 0 ≤ β) {N : ℝ}
    (hN : 0 ≤ N) :
    D.Z N = ∑ I, (∫ v, ∑' r, (r.factorial : ℝ)⁻¹ *
      ∫ u, normalJet ((A.chart I).obsFibre v) r (fun _ => u) ∂(A.chart I).fibreMeasure v N
        ∂(A.chart I).ν) + A.tail N := by
  rw [A.Z_eq N]
  congr 1
  unfold gInt
  exact Finset.sum_congr rfl fun I _ => (T I).tanIntegral_eq_moment_series hβ hN

variable [∀ I, CompactSpace (K I)] [∀ I, T2Space (K I)] [∀ I, OpensMeasurableSpace (K I)]

/-- **The resolved population integral is a cutoff expansion with the assembled canonical
coefficients.** -/
theorem cutoffExpansion (hβ : 0 < β) :
    CutoffExpansion (commonQ A.k) (commonD n) D.Z (gCoeff A.ν A.h A.k β A.b A.x) := by
  have h := (cutoffExpansion_gInt A.ν A.h A.k β A.b A.k_pos hβ A.b_pos A.x).add
    (cutoffExpansion_of_exp_small (commonQ A.k) (commonD n) (half_pos D.δ_pos)
      (A.tail_tendsto (by linarith [D.δ_pos])))
  have hZ : (fun N => gInt A.ν A.h A.k β A.b A.x N + A.tail N) = D.Z :=
    funext fun N => (A.Z_eq N).symm
  have hc : (fun μ j => gCoeff A.ν A.h A.k β A.b A.x μ j + 0) = gCoeff A.ν A.h A.k β A.b A.x :=
    funext fun μ => funext fun j => add_zero _
  rwa [hZ, hc] at h

/-- **`thm:expectation_expansion`, conditional form**: for every cutoff `L > 0` there is `K` with
`|Z(N) − ∑_{μ < L} N^{−μ} ∑_{j ≤ D} gCoeff_{μ,j} log^j N| ≤ K N^{−L} (1 + log N)^D` for all large
`N`. -/
theorem expansion (hβ : 0 < β) (L : ℝ) (hL : 0 < L) : ∃ Kc : ℝ, ∀ᶠ N in atTop,
    |D.Z N - absSpectralSum (commonQ A.k) (commonD n) (gCoeff A.ν A.h A.k β A.b A.x) L N| ≤
      Kc * (N ^ (-L) * (1 + Real.log N) ^ commonD n) :=
  A.cutoffExpansion hβ L hL

/-- **Canonical compatibility**: the moment series has the assembled canonical coefficients. -/
theorem momentSeries_cutoffExpansion (T : ∀ I, NormalMomentPresentation (A.chart I)) (hβ : 0 < β) :
    CutoffExpansion (commonQ A.k) (commonD n) (fun N => ∑ I, ∫ v, ∑' r, (r.factorial : ℝ)⁻¹ *
      ∫ u, normalJet ((A.chart I).obsFibre v) r (fun _ => u) ∂(A.chart I).fibreMeasure v N
        ∂(A.chart I).ν) (gCoeff A.ν A.h A.k β A.b A.x) := by
  refine (cutoffExpansion_gInt A.ν A.h A.k β A.b A.k_pos hβ A.b_pos A.x).congr_eventually ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with N hN
  have := A.Z_eq_moment_series T hβ.le hN
  rw [A.Z_eq N] at this
  linarith

/-- **The conditional geometric main theorem**: a localisation datum with adapted strata data and
normal-moment presentations has (i) the quantitative power–log expansion with the assembled
canonical coefficients, (ii) an exponentially small residual, (iii) the Taylor–moment
representation of its resolved integral, and (iv) the moment series carries the same canonical
coefficients. -/
theorem expectation_expansion_of_adaptedStrataData
    (T : ∀ I, NormalMomentPresentation (A.chart I)) (hβ : 0 < β) :
    CutoffExpansion (commonQ A.k) (commonD n) D.Z (gCoeff A.ν A.h A.k β A.b A.x) ∧
    (∀ N, 0 ≤ N → |A.tail N| ≤ (∫ z, |D.obs z| ∂D.μ) * Real.exp (-D.δ * N)) ∧
    (∀ N, 0 ≤ N → D.Z N = ∑ I, (∫ v, ∑' r, (r.factorial : ℝ)⁻¹ *
      ∫ u, normalJet ((A.chart I).obsFibre v) r (fun _ => u) ∂(A.chart I).fibreMeasure v N
        ∂(A.chart I).ν) + A.tail N) ∧
    CutoffExpansion (commonQ A.k) (commonD n) (fun N => ∑ I, ∫ v, ∑' r, (r.factorial : ℝ)⁻¹ *
      ∫ u, normalJet ((A.chart I).obsFibre v) r (fun _ => u) ∂(A.chart I).fibreMeasure v N
        ∂(A.chart I).ν) (gCoeff A.ν A.h A.k β A.b A.x) :=
  ⟨A.cutoffExpansion hβ, fun _ hN => A.tail_bound hN, fun _ hN => A.Z_eq_moment_series T hβ.le hN,
    A.momentSeries_cutoffExpansion T hβ⟩

end AdaptedStrataData

end Grammar
