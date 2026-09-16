/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.Fluctuation
import Grammar.Asymptotic
import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Integrability of the Mellin integrand of the frozen partition function (§20, item 1)

The hypotheses of the fluctuation zeta identity — absolute integrability of the double integral
`∫∫ N^{s−1} obs e^{−NK+√N Ξ} dN dν` on the strip, local integrability of the frozen partition
function on `(0,∞)` and its boundedness near `0` — are derived here from the structural facts of
the standard form: `Ξ = √K ψ` with `ψ` bounded (`|Ξ| ≤ C_ψ √K`), a bounded observable, and the
convergence of the population zeta integral `∫ K^{−σ} dν` at `σ = Re s`.

* `exp_tilt_le`: `e^{−NK+√N H} ≤ e^{H²/(2K)} e^{−NK/2}` (AM–GM), whence
  `integrableOn_rpow_mul_exp_tilt` (the Mellin integrand is integrable on `(0,∞)` for `σ > 0`);
* `integral_rpow_mul_exp_tilt_scaled`: `∫_0^∞ N^{σ−1} e^{−NK + √N a√K} dN = K^{−σ} S_σ(a)`;
* ★★ `integrable_mellinIntegrand_of_bounded_std`: the Fubini hypothesis `hint` of the zeta
  identity on `0 < Re s`, given `|Ξ| ≤ C_ψ √K`, a bounded observable and `∫ K^{−Re s} dν < ∞`;
* ★ `continuousOn_integral_tilt`, `locallyIntegrableOn_integral_tilt`,
  `integral_tilt_isBigO_one`: for a bounded field and observable and a finite `ν`, the frozen
  partition function `N ↦ ∫ obs e^{−NK+√N Ξ} dν` is continuous on `(0,∞)`, hence locally
  integrable there, and bounded near `0` — the hypotheses `hE`, `hE0`.

Zero `sorry`/`axiom`.
-/

open MeasureTheory Filter Topology Set Asymptotics

namespace Grammar

/-- AM–GM for the tilt: `e^{−NK+√N H} ≤ e^{H²/(2K)} e^{−NK/2}`. -/
theorem exp_tilt_le {K : ℝ} (hK : 0 < K) (H : ℝ) {N : ℝ} (hN : 0 ≤ N) :
    Real.exp (-N * K + Real.sqrt N * H) ≤
      Real.exp (H ^ 2 / (2 * K)) * Real.exp (-(K / 2) * N) := by
  rw [← Real.exp_add, Real.exp_le_exp]
  have hsK : Real.sqrt K ≠ 0 := (Real.sqrt_pos.2 hK).ne'
  have hK' : K ≠ 0 := hK.ne'
  have h1 := two_mul_le_add_sq (Real.sqrt N * Real.sqrt K) (|H| / Real.sqrt K)
  have h2 : Real.sqrt N * Real.sqrt K * (|H| / Real.sqrt K) = Real.sqrt N * |H| := by
    field_simp
  have h3 : (Real.sqrt N * Real.sqrt K) ^ 2 = N * K := by
    rw [mul_pow, Real.sq_sqrt hN, Real.sq_sqrt hK.le]
  have h4 : (|H| / Real.sqrt K) ^ 2 = 2 * (H ^ 2 / (2 * K)) := by
    rw [div_pow, sq_abs, Real.sq_sqrt hK.le]
    field_simp
  have h1' : 2 * (Real.sqrt N * |H|) ≤ N * K + 2 * (H ^ 2 / (2 * K)) := by
    rw [← h2, ← h3, ← h4]
    linarith [h1]
  have h5 : Real.sqrt N * H ≤ Real.sqrt N * |H| :=
    mul_le_mul_of_nonneg_left (le_abs_self H) (Real.sqrt_nonneg N)
  linarith

/-- The Mellin integrand of the tilted exponential is integrable on `(0,∞)` for `σ > 0`. -/
theorem integrableOn_rpow_mul_exp_tilt {K : ℝ} (hK : 0 < K) (H : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    IntegrableOn (fun N : ℝ => N ^ (σ - 1) * Real.exp (-N * K + Real.sqrt N * H)) (Ioi 0) := by
  have hmaj : IntegrableOn (fun N : ℝ => Real.exp (H ^ 2 / (2 * K)) *
      (N ^ (σ - 1) * Real.exp (-(K / 2) * N))) (Ioi 0) := by
    have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := σ - 1) (b := K / 2)
      (by linarith) one_pos (by linarith)
    simp only [Real.rpow_one] at this
    exact this.const_mul _
  refine Integrable.mono' hmaj ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine ContinuousOn.mul (fun x hx => ?_) (Continuous.continuousOn (by fun_prop))
    exact (Real.continuousAt_rpow_const _ _ (Or.inl (ne_of_gt hx))).continuousWithinAt
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun N hN => ?_)
    have hN0 : (0 : ℝ) < N := hN
    have hr : 0 ≤ N ^ (σ - 1) := Real.rpow_nonneg hN0.le _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hr (Real.exp_pos _).le)]
    calc N ^ (σ - 1) * Real.exp (-N * K + Real.sqrt N * H)
        ≤ N ^ (σ - 1) * (Real.exp (H ^ 2 / (2 * K)) * Real.exp (-(K / 2) * N)) :=
          mul_le_mul_of_nonneg_left (exp_tilt_le hK H hN0.le) hr
      _ = Real.exp (H ^ 2 / (2 * K)) * (N ^ (σ - 1) * Real.exp (-(K / 2) * N)) := by ring

/-- The norm of the complex Mellin integrand. -/
theorem norm_cpow_mul_ofReal {N : ℝ} (hN : 0 < N) (s : ℂ) (r : ℝ) :
    ‖(N : ℂ) ^ (s - 1) * (r : ℂ)‖ = N ^ (s.re - 1) * |r| := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hN, Complex.sub_re, Complex.one_re,
    Complex.norm_real, Real.norm_eq_abs]

/-- ★ **The scaled Mellin integral**: `∫_0^∞ N^{σ−1} e^{−NK + √N a√K} dN = K^{−σ} S_σ(a)`. -/
theorem integral_rpow_mul_exp_tilt_scaled {K : ℝ} (hK : 0 < K) (a σ : ℝ) :
    ∫ N in Ioi (0 : ℝ), N ^ (σ - 1) * Real.exp (-N * K + Real.sqrt N * (a * Real.sqrt K)) =
      K ^ (-σ) * fluctuation 1 σ a := by
  have hK1 : K ^ (1 - σ) * K ^ (σ - 1) = 1 := by
    rw [← Real.rpow_add hK, show (1 - σ) + (σ - 1) = 0 by ring, Real.rpow_zero]
  have hg : ∀ N : ℝ, 0 < N →
      N ^ (σ - 1) * Real.exp (-N * K + Real.sqrt N * (a * Real.sqrt K)) =
      K ^ (1 - σ) *
        ((K * N) ^ (σ - 1) * Real.exp (-1 * (K * N) + 1 * a * Real.sqrt (K * N))) := by
    intro N hN
    have hexp : Real.exp (-N * K + Real.sqrt N * (a * Real.sqrt K)) =
        Real.exp (-1 * (K * N) + 1 * a * Real.sqrt (K * N)) := by
      rw [Real.sqrt_mul hK.le]
      congr 1
      ring
    rw [Real.mul_rpow hK.le hN.le, hexp]
    calc N ^ (σ - 1) * Real.exp (-1 * (K * N) + 1 * a * Real.sqrt (K * N))
        = (K ^ (1 - σ) * K ^ (σ - 1)) *
          (N ^ (σ - 1) * Real.exp (-1 * (K * N) + 1 * a * Real.sqrt (K * N))) := by
          rw [hK1]
          ring
      _ = _ := by ring
  rw [setIntegral_congr_fun measurableSet_Ioi fun N hN => hg N hN, integral_const_mul,
    integral_comp_mul_left_Ioi
      (fun t : ℝ => t ^ (σ - 1) * Real.exp (-1 * t + 1 * a * Real.sqrt t)) 0 hK,
    mul_zero, smul_eq_mul]
  unfold fluctuation
  rw [← mul_assoc]
  congr 1
  rw [show K⁻¹ = K ^ (-(1 : ℝ)) by rw [Real.rpow_neg hK.le, Real.rpow_one], ← Real.rpow_add hK]
  congr 1
  ring

variable {α : Type*} [MeasurableSpace α] {ν : Measure α} {K Ξ obs : α → ℝ}

/-- ★★ **Absolute integrability of the Mellin double integral on the strip `Re s > 0`**, for a
field `Ξ = √K ψ` with `|ψ| ≤ C_ψ`, a bounded observable, and a convergent population zeta
integral `∫ K^{−Re s} dν`.  This is the hypothesis `hint` of the fluctuation zeta identity. -/
theorem integrable_mellinIntegrand_of_bounded_std [SFinite ν] (hKm : Measurable K)
    (hΞm : Measurable Ξ) (hobsm : Measurable obs) (hK : ∀ᵐ w ∂ν, 0 < K w) {Cobs : ℝ}
    (hobsB : ∀ w, |obs w| ≤ Cobs) {Cψ : ℝ} (hΞ : ∀ w, |Ξ w| ≤ Cψ * Real.sqrt (K w)) {s : ℂ}
    (hs : 0 < s.re) (hKint : Integrable (fun w => K w ^ (-s.re)) ν) :
    Integrable (fun p : ℝ × α => (p.1 : ℂ) ^ (s - 1) *
      ((obs p.2 * Real.exp (-p.1 * K p.2 + Real.sqrt p.1 * Ξ p.2) : ℝ) : ℂ))
      ((volume.restrict (Ioi 0)).prod ν) := by
  have hmeas : AEStronglyMeasurable (fun p : ℝ × α => (p.1 : ℂ) ^ (s - 1) *
      ((obs p.2 * Real.exp (-p.1 * K p.2 + Real.sqrt p.1 * Ξ p.2) : ℝ) : ℂ))
      ((volume.restrict (Ioi 0)).prod ν) := by
    have h1 : AEStronglyMeasurable (fun N : ℝ => (N : ℂ) ^ (s - 1))
        (volume.restrict (Ioi 0)) := by
      refine ContinuousOn.aestronglyMeasurable (fun N hN => ?_) measurableSet_Ioi
      exact (Complex.continuousAt_ofReal_cpow_const _ _
        (Or.inr (ne_of_gt hN))).continuousWithinAt
    have h2 : Measurable fun p : ℝ × α =>
        ((obs p.2 * Real.exp (-p.1 * K p.2 + Real.sqrt p.1 * Ξ p.2) : ℝ) : ℂ) := by
      fun_prop
    exact h1.comp_fst.mul h2.aestronglyMeasurable
  refine (integrable_prod_iff' hmeas).2 ⟨?_, ?_⟩
  · filter_upwards [hK] with w hw
    have hreal := (integrableOn_rpow_mul_exp_tilt hw (Ξ w) hs).const_mul |obs w|
    refine Integrable.mono' hreal ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable (fun N hN => ?_) measurableSet_Ioi
      refine ContinuousWithinAt.mul ?_ (Continuous.continuousWithinAt (by fun_prop))
      exact (Complex.continuousAt_ofReal_cpow_const _ _
        (Or.inr (ne_of_gt hN))).continuousWithinAt
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun N hN => ?_)
      rw [norm_cpow_mul_ofReal hN, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact le_of_eq (by ring)
  · have hS : 0 ≤ fluctuation 1 s.re Cψ := (fluctuation_pos 1 s.re Cψ one_pos hs).le
    refine Integrable.mono' (hKint.const_mul (Cobs * fluctuation 1 s.re Cψ)) ?_ ?_
    · exact hmeas.norm.prod_swap.integral_prod_right'
    · filter_upwards [hK] with w hw
      have hnn : 0 ≤ ∫ N in Ioi (0 : ℝ), ‖(N : ℂ) ^ (s - 1) *
          ((obs w * Real.exp (-N * K w + Real.sqrt N * Ξ w) : ℝ) : ℂ)‖ :=
        integral_nonneg fun _ => norm_nonneg _
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      have hint1 := integrableOn_rpow_mul_exp_tilt hw (Ξ w) hs
      have hint2 := integrableOn_rpow_mul_exp_tilt hw (Cψ * Real.sqrt (K w)) hs
      calc ∫ N in Ioi (0 : ℝ), ‖(N : ℂ) ^ (s - 1) *
            ((obs w * Real.exp (-N * K w + Real.sqrt N * Ξ w) : ℝ) : ℂ)‖
          = ∫ N in Ioi (0 : ℝ), |obs w| *
              (N ^ (s.re - 1) * Real.exp (-N * K w + Real.sqrt N * Ξ w)) := by
            refine setIntegral_congr_fun measurableSet_Ioi fun N hN => ?_
            rw [norm_cpow_mul_ofReal hN, abs_mul, abs_of_pos (Real.exp_pos _)]
            ring
        _ ≤ ∫ N in Ioi (0 : ℝ), Cobs *
              (N ^ (s.re - 1) * Real.exp (-N * K w + Real.sqrt N * (Cψ * Real.sqrt (K w)))) := by
            refine setIntegral_mono_on (hint1.const_mul _) (hint2.const_mul _) measurableSet_Ioi
              fun N hN => ?_
            have hN0 : (0 : ℝ) < N := hN
            have hr : 0 ≤ N ^ (s.re - 1) := Real.rpow_nonneg hN0.le _
            have he : Real.exp (-N * K w + Real.sqrt N * Ξ w) ≤
                Real.exp (-N * K w + Real.sqrt N * (Cψ * Real.sqrt (K w))) := by
              rw [Real.exp_le_exp]
              have := mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) (hΞ w))
                (Real.sqrt_nonneg N)
              linarith
            exact mul_le_mul (hobsB w) (mul_le_mul_of_nonneg_left he hr)
              (mul_nonneg hr (Real.exp_pos _).le) (le_trans (abs_nonneg _) (hobsB w))
        _ = Cobs * fluctuation 1 s.re Cψ * K w ^ (-s.re) := by
            rw [integral_const_mul, integral_rpow_mul_exp_tilt_scaled hw Cψ s.re]
            ring

omit [MeasurableSpace α] in
/-- On `0 ≤ N ≤ N₁`, with `K ≥ 0`, `|Ξ| ≤ C_Ξ`, `|obs| ≤ C_obs`, the tilted integrand is bounded
by `C_obs e^{√N₁ C_Ξ}`. -/
theorem abs_tilt_integrand_le {w : α} (hK : 0 ≤ K w) {CΞ Cobs : ℝ} (hΞ : |Ξ w| ≤ CΞ)
    (hobs : |obs w| ≤ Cobs) {N N₁ : ℝ} (hN : 0 ≤ N) (hN₁ : N ≤ N₁) :
    |obs w * Real.exp (-N * K w + Real.sqrt N * Ξ w)| ≤ Cobs * Real.exp (Real.sqrt N₁ * CΞ) := by
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  have hCΞ : 0 ≤ CΞ := le_trans (abs_nonneg _) hΞ
  refine mul_le_mul hobs ?_ (Real.exp_pos _).le (le_trans (abs_nonneg _) hobs)
  rw [Real.exp_le_exp]
  have h1 : 0 ≤ N * K w := mul_nonneg hN hK
  have h2 : Real.sqrt N * Ξ w ≤ Real.sqrt N * CΞ :=
    mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) hΞ) (Real.sqrt_nonneg N)
  have h3 : Real.sqrt N * CΞ ≤ Real.sqrt N₁ * CΞ :=
    mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hN₁) hCΞ
  linarith

/-- The frozen partition function of a bounded field and observable is bounded on `[0, N₁]`. -/
theorem abs_integral_tilt_le [IsFiniteMeasure ν] (hK : ∀ᵐ w ∂ν, 0 ≤ K w) {CΞ Cobs : ℝ}
    (hΞ : ∀ w, |Ξ w| ≤ CΞ) (hobs : ∀ w, |obs w| ≤ Cobs) {N N₁ : ℝ} (hN : 0 ≤ N) (hN₁ : N ≤ N₁) :
    |∫ w, obs w * Real.exp (-N * K w + Real.sqrt N * Ξ w) ∂ν| ≤
      Cobs * Real.exp (Real.sqrt N₁ * CΞ) * ν.real univ := by
  rw [← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le_const ?_
  filter_upwards [hK] with w hw
  rw [Real.norm_eq_abs]
  exact abs_tilt_integrand_le hw (hΞ w) (hobs w) hN hN₁

/-- ★ **Continuity of the frozen partition function on `(0,∞)`** for a bounded field and
observable and a finite `ν` (dominated convergence). -/
theorem continuousOn_integral_tilt [IsFiniteMeasure ν] (hKm : Measurable K) (hΞm : Measurable Ξ)
    (hobsm : Measurable obs) (hK : ∀ᵐ w ∂ν, 0 ≤ K w) {CΞ Cobs : ℝ} (hΞ : ∀ w, |Ξ w| ≤ CΞ)
    (hobs : ∀ w, |obs w| ≤ Cobs) :
    ContinuousOn (fun N => ∫ w, obs w * Real.exp (-N * K w + Real.sqrt N * Ξ w) ∂ν) (Ioi 0) := by
  intro N₀ hN₀
  have hN₀' : (0 : ℝ) < N₀ := hN₀
  refine ContinuousAt.continuousWithinAt ?_
  refine continuousAt_of_dominated (bound := fun _ => Cobs * Real.exp (Real.sqrt (N₀ + 1) * CΞ))
    ?_ ?_ (integrable_const _) ?_
  · refine Eventually.of_forall fun N => Measurable.aestronglyMeasurable ?_
    fun_prop
  · filter_upwards [Ioo_mem_nhds hN₀' (lt_add_one N₀)] with N hN
    filter_upwards [hK] with w hw
    rw [Real.norm_eq_abs]
    exact abs_tilt_integrand_le hw (hΞ w) (hobs w) hN.1.le hN.2.le
  · exact Eventually.of_forall fun w => Continuous.continuousAt (by fun_prop)

/-- ★ **Local integrability of the frozen partition function on `(0,∞)`** (the hypothesis `hE`
of the fluctuation zeta identity). -/
theorem locallyIntegrableOn_integral_tilt [IsFiniteMeasure ν] (hKm : Measurable K)
    (hΞm : Measurable Ξ) (hobsm : Measurable obs) (hK : ∀ᵐ w ∂ν, 0 ≤ K w) {CΞ Cobs : ℝ}
    (hΞ : ∀ w, |Ξ w| ≤ CΞ) (hobs : ∀ w, |obs w| ≤ Cobs) :
    LocallyIntegrableOn
      (fun N => ((∫ w, obs w * Real.exp (-N * K w + Real.sqrt N * Ξ w) ∂ν : ℝ) : ℂ)) (Ioi 0) :=
  (Complex.continuous_ofReal.comp_continuousOn
    (continuousOn_integral_tilt hKm hΞm hobsm hK hΞ hobs)).locallyIntegrableOn measurableSet_Ioi

/-- ★ **Boundedness of the frozen partition function near `0`** (the hypothesis `hE0` of the
fluctuation zeta identity). -/
theorem integral_tilt_isBigO_one [IsFiniteMeasure ν] (hK : ∀ᵐ w ∂ν, 0 ≤ K w) {CΞ Cobs : ℝ}
    (hΞ : ∀ w, |Ξ w| ≤ CΞ) (hobs : ∀ w, |obs w| ≤ Cobs) :
    (fun N => ((∫ w, obs w * Real.exp (-N * K w + Real.sqrt N * Ξ w) ∂ν : ℝ) : ℂ))
      =O[𝓝[>] 0] fun _ : ℝ => (1 : ℂ) := by
  refine IsBigO.of_bound (Cobs * Real.exp (Real.sqrt 1 * CΞ) * ν.real univ) ?_
  filter_upwards [eventually_mem_nhdsWithin,
    (eventually_lt_nhds one_pos).filter_mono nhdsWithin_le_nhds] with N hN hN1
  rw [norm_one, mul_one, Complex.norm_real, Real.norm_eq_abs]
  exact abs_integral_tilt_le hK hΞ hobs (le_of_lt hN) hN1.le

omit [MeasurableSpace α] in
/-- A field of the standard form `|Ξ| ≤ C_ψ √K` with `K ≤ C_K` is bounded. -/
theorem abs_le_of_abs_le_sqrt {w : α} {Cψ CK : ℝ} (hCψ : 0 ≤ Cψ) (hKB : K w ≤ CK)
    (hΞ : |Ξ w| ≤ Cψ * Real.sqrt (K w)) : |Ξ w| ≤ Cψ * Real.sqrt CK :=
  hΞ.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hKB) hCψ)

end Grammar
