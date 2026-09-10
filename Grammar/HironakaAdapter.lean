/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.DominantExponentPair
import Grammar.ResolutionTransport
import Monomialize.VolumeScaling.PartialResolution
import Monomialize.Analytic.Readout.E5

/-!
# The adapter to `timaeus-research/hironaka`

`hironaka` (a lake dependency, pinned) formalises Bierstone–Milman's chart form of resolution of
singularities and its read-outs for singular learning theory: the sublevel asymptotics
`HasLLCExponentsOn volume K f λ θ` (`sublevelVol volume K f ε ≍ ε^λ (−log ε)^{θ−1}` as `ε → 0⁺`)
and the partial resolutions `PartialResolution n F K` with monomial charts.  This file is the
fieldwise adapter to grammar's interfaces.

* `SublevelTheta.of_hasLLCExponentsOn`: hironaka's sublevel asymptotics on `K` are grammar's
  `SublevelTheta` for the restricted measure, with log degree `q = θ − 1`; hence
  `LaplaceTheta.of_hasLLCExponentsOn`, the two-sided Laplace growth of `∫_K e^{−N f}`.
* `laplaceTheta_of_analyticOnNhd_nonneg_of_Q`: **the population Laplace exponent pair of a
  real-analytic nonnegative phase**, conditional on hironaka's `Q n` (Bierstone–Milman Theorem 3.2
  in chart form, which hironaka proves leaf-wise; only declarations taking `Q n` as an explicit
  hypothesis are consumed here, so this file adds no axioms): on every small closed cube around a
  zero of `K`,
  `∫ e^{−N K} dx ≍ N^{−λ}(log N)^{θ−1}` with `λ ∈ ℚ_{>0}`, `1 ≤ θ ≤ n`.
* `ResolutionChart.ofPartialResolution`, `ResolutionCover.ofPartialResolution`: the chart data of a
  partial resolution as grammar's resolution charts, whose images cover `K` almost everywhere
  (`ResolutionCover.ae_mem_iUnion_image_ofPartialResolution`), so the exact assembled transport
  `ResolutionCover.sum_map_eq` and the partition `LocalisationData.partitionOfCover` apply.
-/

open MeasureTheory Filter Topology Asymptotics Set
open Monomialize.VolumeScaling

namespace Grammar

/-! ### Sublevel asymptotics -/

section Sublevel

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {K : Set X} {f : X → ℝ} {lam : ℝ} {q : ℕ}

theorem sublevelMass_restrict (hf : Measurable f) (t : ℝ) :
    sublevelMass (μ.restrict K) f t = sublevelVol μ K f t := by
  unfold sublevelMass sublevelVol
  rw [Measure.restrict_apply (measurableSet_le hf measurable_const), inter_comm]

theorem sublevelScale_eq_llcScale (lam : ℝ) (q : ℕ) (t : ℝ) :
    sublevelScale lam q t = llcScale lam (q + 1 : ℕ) t := by
  unfold sublevelScale llcScale
  rw [show ((q + 1 : ℕ) : ℝ) - 1 = (q : ℝ) by push_cast; ring, Real.rpow_natCast]

/-- **hironaka's sublevel asymptotics are grammar's `SublevelTheta`** for the restricted measure,
with log degree `q = θ − 1`. -/
theorem SublevelTheta.of_hasLLCExponentsOn (hf : Measurable f)
    (h : HasLLCExponentsOn μ K f lam (q + 1 : ℕ)) : SublevelTheta (μ.restrict K) f lam q := by
  unfold SublevelTheta
  have h1 : sublevelMass (μ.restrict K) f = sublevelVol μ K f := funext (sublevelMass_restrict hf)
  have h2 : sublevelScale lam q = llcScale lam (q + 1 : ℕ) :=
    funext (sublevelScale_eq_llcScale lam q)
  rw [h1, h2]
  exact h

/-- **Two-sided Laplace growth from hironaka's sublevel asymptotics**:
`∫_K e^{−N f} dμ ≍ N^{−λ} (log N)^{θ−1}`. -/
theorem LaplaceTheta.of_hasLLCExponentsOn [IsFiniteMeasure (μ.restrict K)] (hf : Measurable f)
    (hf0 : 0 ≤ᵐ[μ.restrict K] f) (h : HasLLCExponentsOn μ K f lam (q + 1 : ℕ)) :
    LaplaceTheta (μ.restrict K) f lam q :=
  (SublevelTheta.of_hasLLCExponentsOn hf h).laplaceTheta hf hf0

end Sublevel

/-! ### Restriction to a set depends only on the values on the set -/

section Congr

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {B : Set X} {f g : X → ℝ} {lam : ℝ} {q : ℕ}

theorem LaplaceTheta.congr_eqOn (hB : MeasurableSet B) (hfg : EqOn f g B)
    (h : LaplaceTheta (μ.restrict B) f lam q) : LaplaceTheta (μ.restrict B) g lam q := by
  unfold LaplaceTheta at h ⊢
  have : (fun N => ∫ x, Real.exp (-N * f x) ∂μ.restrict B) =
      fun N => ∫ x, Real.exp (-N * g x) ∂μ.restrict B :=
    funext fun N => setIntegral_congr_fun hB fun x hx => by simp only [hfg hx]
  rwa [this] at h

end Congr

/-! ### The population Laplace exponent pair of an analytic nonnegative phase -/

section Analytic

variable {n : ℕ}

open scoped Classical in
/-- A measurable modification of `K` agreeing with it on the closed cube. -/
noncomputable def cubeModification (K : (Fin n → ℝ) → ℝ) (w : Fin n → ℝ) (r : ℝ) :
    (Fin n → ℝ) → ℝ := (Metric.closedBall w r).piecewise K 0

open scoped Classical in
theorem cubeModification_eqOn (K : (Fin n → ℝ) → ℝ) (w : Fin n → ℝ) (r : ℝ) :
    EqOn (cubeModification K w r) K (Metric.closedBall w r) := fun _ hx => by
  unfold cubeModification
  exact piecewise_eq_of_mem _ _ _ hx

open scoped Classical in
theorem measurable_cubeModification {K : (Fin n → ℝ) → ℝ} {w : Fin n → ℝ} {r : ℝ}
    (hK : ContinuousOn K (Metric.closedBall w r)) : Measurable (cubeModification K w r) := by
  refine measurable_of_restrict_of_restrict_compl (s := Metric.closedBall w r)
    Metric.isClosed_closedBall.measurableSet ?_ ?_
  · have h : (Metric.closedBall w r).domRestrict (cubeModification K w r) =
        (Metric.closedBall w r).domRestrict K :=
      funext fun x => cubeModification_eqOn K w r x.2
    rw [h]
    exact (continuousOn_iff_continuous_domRestrict.1 hK).measurable
  · have h : (Metric.closedBall w r)ᶜ.domRestrict (cubeModification K w r) = fun _ => (0 : ℝ) := by
      funext x
      unfold cubeModification
      exact piecewise_eq_of_notMem _ _ _ x.2
    rw [h]
    exact measurable_const

instance isFiniteMeasure_restrict_closedBall (w : Fin n → ℝ) (r : ℝ) :
    IsFiniteMeasure ((volume : Measure (Fin n → ℝ)).restrict (Metric.closedBall w r)) :=
  ⟨by rw [Measure.restrict_apply_univ]; exact measure_closedBall_lt_top⟩

/-- **The population Laplace exponent pair of a real-analytic nonnegative phase**, conditional on
hironaka's `Q n`: for `K` real-analytic on an open `U`, `K w = 0`, `K` not identically zero near `w`
and `K ≥ 0` near `w`, there are `λ ∈ ℚ_{>0}`, `θ ∈ {1, …, n}` and `r₀ > 0` such that on every closed
cube `closedBall w r`, `0 < r ≤ r₀`, `∫ e^{−N K} dx ≍ N^{−λ} (log N)^{θ−1}` as `N → ∞`. -/
theorem laplaceTheta_of_analyticOnNhd_nonneg_of_Q (hQ : Monomialize.Analytic.Q n)
    {U : Set (Fin n → ℝ)} (hU : IsOpen U) {K : (Fin n → ℝ) → ℝ} (hK : AnalyticOnNhd ℝ K U)
    {w : Fin n → ℝ} (hw : w ∈ U) (h0 : K w = 0) (hne : ¬ ∀ᶠ x in 𝓝 w, K x = 0)
    (hK0 : ∀ᶠ x in 𝓝 w, 0 ≤ K x) :
    ∃ (lam : ℚ) (theta : ℕ) (r₀ : ℝ), 0 < lam ∧ 1 ≤ theta ∧ theta ≤ n ∧ 0 < r₀ ∧
      ∀ r : ℝ, 0 < r → r ≤ r₀ →
        LaplaceTheta ((volume : Measure (Fin n → ℝ)).restrict (Metric.closedBall w r)) K
          (lam : ℝ) (theta - 1) := by
  obtain ⟨lam, theta, r₀, hlam, h1, hn, hr₀, hE5⟩ :=
    Monomialize.Analytic.exists_hasLLCExponentsOn_of_analyticOnNhd_nonneg_of_Q hQ hU hK hw h0 hne
      hK0
  obtain ⟨ε, hε, hpos⟩ := Metric.eventually_nhds_iff.mp hK0
  obtain ⟨ε', hε', hU'⟩ := Metric.isOpen_iff.mp hU w hw
  refine ⟨lam, theta, min r₀ (min (ε / 2) (ε' / 2)), hlam, h1, hn, ?_, fun r hr hrle => ?_⟩
  · exact lt_min hr₀ (lt_min (half_pos hε) (half_pos hε'))
  have hrr₀ : r ≤ r₀ := hrle.trans (min_le_left _ _)
  have hrε : r < ε := lt_of_le_of_lt (hrle.trans ((min_le_right _ _).trans (min_le_left _ _)))
    (half_lt_self hε)
  have hrε' : r < ε' := lt_of_le_of_lt (hrle.trans ((min_le_right _ _).trans (min_le_right _ _)))
    (half_lt_self hε')
  have hball : Metric.closedBall w r ⊆ Metric.ball w ε := Metric.closedBall_subset_ball hrε
  have hballU : Metric.closedBall w r ⊆ U := (Metric.closedBall_subset_ball hrε').trans hU'
  have hcont : ContinuousOn K (Metric.closedBall w r) := hK.continuousOn.mono hballU
  set K' := cubeModification K w r with hK'
  have hKm : Measurable K' := measurable_cubeModification hcont
  have heq : EqOn K' K (Metric.closedBall w r) := cubeModification_eqOn K w r
  have hB : MeasurableSet (Metric.closedBall w r) := Metric.isClosed_closedBall.measurableSet
  -- hironaka's exponents transfer to the modification
  have hLLC : HasLLCExponentsOn volume (Metric.closedBall w r) K' (lam : ℝ) (theta : ℝ) :=
    (hasLLCExponentsOn_congr_eqOn fun x hx => (heq hx).symm).mp (hE5 r hr hrr₀)
  obtain ⟨q, hq⟩ : ∃ q : ℕ, theta = q + 1 := ⟨theta - 1, by omega⟩
  have hq' : ((theta : ℝ) - 1) = q := by rw [hq]; push_cast; ring
  have hLLC' : HasLLCExponentsOn volume (Metric.closedBall w r) K' (lam : ℝ) (q + 1 : ℕ) := by
    rw [hq] at hLLC; exact_mod_cast hLLC
  have hnn : 0 ≤ᵐ[(volume : Measure (Fin n → ℝ)).restrict (Metric.closedBall w r)] K' := by
    rw [Filter.EventuallyLE, ae_restrict_iff' hB]
    refine Eventually.of_forall fun x hx => ?_
    rw [Pi.zero_apply, heq hx]
    exact hpos (Metric.mem_ball.mp (hball hx))
  have hL : LaplaceTheta ((volume : Measure (Fin n → ℝ)).restrict (Metric.closedBall w r)) K'
      (lam : ℝ) q := LaplaceTheta.of_hasLLCExponentsOn hKm hnn hLLC'
  rw [show theta - 1 = q by omega]
  exact hL.congr_eqOn hB heq

end Analytic

/-! ### Partial resolutions as resolution covers -/

namespace ResolutionChart

variable {n : ℕ} {F : (Fin n → ℝ) → ℝ} {K : Set (Fin n → ℝ)}

/-- **A chart of a partial resolution as a resolution chart.** -/
noncomputable def ofPartialResolution (R : PartialResolution n F K) (i : R.ι) :
    ResolutionChart n where
  dom := R.dom i
  dom_compact := R.dom_compact i
  φ := R.φ i
  U := (R.smooth i).choose
  U_open := (R.smooth i).choose_spec.1
  dom_subset := (R.smooth i).choose_spec.2.1
  smooth := (R.smooth i).choose_spec.2.2.of_le (by exact_mod_cast le_top)
  E := R.E i
  E_subset := R.E_subset i
  E_closed := R.E_closed i
  E_null := R.E_null i
  inj := R.inj i

@[simp] theorem ofPartialResolution_dom (R : PartialResolution n F K) (i : R.ι) :
    (ofPartialResolution R i).dom = R.dom i := rfl

@[simp] theorem ofPartialResolution_φ (R : PartialResolution n F K) (i : R.ι) :
    (ofPartialResolution R i).φ = R.φ i := rfl

end ResolutionChart

namespace ResolutionCover

variable {n : ℕ} {F : (Fin n → ℝ) → ℝ} {K : Set (Fin n → ℝ)}

/-- **A partial resolution as a resolution cover.** -/
noncomputable def ofPartialResolution (R : PartialResolution n F K) : ResolutionCover n R.ι where
  chart := ResolutionChart.ofPartialResolution R

/-- The chart images of a partial resolution cover `K` almost everywhere. -/
theorem ae_mem_iUnion_image_ofPartialResolution (R : PartialResolution n F K) :
    ∀ᵐ z ∂(volume : Measure (Fin n → ℝ)).restrict K, z ∈ ⋃ i, (ofPartialResolution R).image i := by
  rw [ae_restrict_iff' R.K_compact.isClosed.measurableSet]
  have h := R.cover
  rw [← compl_mem_ae_iff] at h
  filter_upwards [h] with z hz hzK
  by_contra hcon
  exact hz ⟨hzK, hcon⟩

end ResolutionCover

end Grammar
