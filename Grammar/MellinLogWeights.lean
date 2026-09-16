/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.EmpiricalMellinJet
import Grammar.EmpiricalInnerTwoRegime

/-!
# The lower logarithmic Mellin weights are `ν`-derivatives of the fluctuation function
(§20, consult #145 (2))

The coefficients of the empirical expansion below the top logarithmic power involve the
log-weighted Mellin moments `mellinMom G μ ℓ = ∫₀^∞ s^{μ−1} (−log s)^ℓ G(√s) e^{−s} ds`. On the
jet families `G(τ) = τ^r e^{aτ}` these are derivatives of the fluctuation function in its index:
★★ `mellinMom_pow_mul_exp_eq_iteratedDeriv`:
`mellinMom (τ^r e^{aτ}) μ ℓ = (−1)^ℓ · ∂_ν^ℓ S_ν(a) |_{ν = μ + r/2}` (`S_ν = fluctuation 1 ν`).
Route: `fluctuationLog ν a ℓ = ∫ t^{ν−1} (log t)^ℓ e^{−t + a√t} dt` is integrable for `ν > 0`
(the envelope of `EmpiricalInnerTwoRegime`), differentiable in `ν` under the integral with
derivative `fluctuationLog ν a (ℓ+1)` (★ `hasDerivAt_fluctuationLog`, dominated on a ball by
`(t^{ν/2−1} + t^{3ν/2−1}) |log t|^{ℓ+1} e^{−t+a√t}`), hence `iteratedDeriv ℓ S_·(a) ν =
fluctuationLog ν a ℓ` for `ν > 0` (`iteratedDeriv_fluctuation_eq`); and the moment kernel of the
jet is exactly `(−1)^ℓ` times the `fluctuationLog` integrand at the shifted index
(`mellinMom_pow_mul_exp`). The normalisation is that of the development's `momKernel`
(`s^{μ−1}(−log s)^ℓ`, no factors of `2`; consult #145). Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

namespace SmoothEngine

/-- The log-weighted fluctuation integral `∫₀^∞ t^{ν−1} (log t)^ℓ e^{−t + a√t} dt`. -/
noncomputable def fluctuationLog (ν a : ℝ) (ℓ : ℕ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), t ^ (ν - 1) * Real.log t ^ ℓ * exp (-t + a * Real.sqrt t)

theorem fluctuationLog_zero (ν a : ℝ) : fluctuationLog ν a 0 = fluctuation 1 ν a := by
  unfold fluctuationLog fluctuation
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [pow_zero, mul_one, neg_one_mul, one_mul]

theorem continuousOn_fluctuationLog_integrand (ν a : ℝ) (ℓ : ℕ) :
    ContinuousOn (fun t : ℝ => t ^ (ν - 1) * Real.log t ^ ℓ * exp (-t + a * Real.sqrt t))
      (Ioi 0) := by
  refine ((continuousOn_id.rpow_const fun t ht => Or.inl (ne_of_gt ht)).mul
    ((Real.continuousOn_log.mono fun t ht => ne_of_gt ht).pow ℓ)).mul ?_
  exact (continuous_exp.comp (by fun_prop)).continuousOn

/-- The absolute-log integrand is the `m = 0` envelope. -/
theorem integrableOn_abs_log_integrand {ν : ℝ} (hν : 0 < ν) (a : ℝ) (ℓ : ℕ) :
    IntegrableOn (fun t : ℝ => t ^ (ν - 1) * |Real.log t| ^ ℓ * exp (-t + a * Real.sqrt t))
      (Ioi 0) := by
  refine (integrableOn_envelope 0 a hν ℓ).congr_fun (fun t _ => ?_) measurableSet_Ioi
  beta_reduce
  rw [pow_zero, one_mul, ← Real.exp_add]
  ring_nf

theorem integrableOn_fluctuationLog_integrand {ν : ℝ} (hν : 0 < ν) (a : ℝ) (ℓ : ℕ) :
    IntegrableOn (fun t : ℝ => t ^ (ν - 1) * Real.log t ^ ℓ * exp (-t + a * Real.sqrt t))
      (Ioi 0) := by
  refine Integrable.mono' (integrableOn_abs_log_integrand hν a ℓ)
    ((continuousOn_fluctuationLog_integrand ν a ℓ).aestronglyMeasurable measurableSet_Ioi) ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  filter_upwards with t ht
  have ht0 : (0 : ℝ) < t := ht
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg ht0.le _), abs_pow,
    abs_of_pos (exp_pos _)]

/-- ★ **Differentiation under the integral in the index**:
`∂_ν fluctuationLog ν a ℓ = fluctuationLog ν a (ℓ+1)` for `ν > 0`. -/
theorem hasDerivAt_fluctuationLog {ν : ℝ} (hν : 0 < ν) (a : ℝ) (ℓ : ℕ) :
    HasDerivAt (fun ν => fluctuationLog ν a ℓ) (fluctuationLog ν a (ℓ + 1)) ν := by
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  let F : ℝ → ℝ → ℝ := fun x t => t ^ (x - 1) * Real.log t ^ ℓ * exp (-t + a * Real.sqrt t)
  let D : ℝ → ℝ → ℝ := fun x t => t ^ (x - 1) * Real.log t ^ (ℓ + 1) * exp (-t + a * Real.sqrt t)
  let bound : ℝ → ℝ := fun t =>
    (t ^ (ν / 2 - 1) + t ^ (3 * ν / 2 - 1)) * |Real.log t| ^ (ℓ + 1) * exp (-t + a * Real.sqrt t)
  have hFi : ∀ x, 0 < x → Integrable (F x) μ := fun x hx =>
    integrableOn_fluctuationLog_integrand hx a ℓ
  have hDi : ∀ x, 0 < x → Integrable (D x) μ := fun x hx =>
    integrableOn_fluctuationLog_integrand hx a (ℓ + 1)
  have hbi : Integrable bound μ := by
    have h1 := integrableOn_abs_log_integrand (by linarith : 0 < ν / 2) a (ℓ + 1)
    have h2 := integrableOn_abs_log_integrand (by linarith : 0 < 3 * ν / 2) a (ℓ + 1)
    have heq : bound = fun t =>
        t ^ (ν / 2 - 1) * |Real.log t| ^ (ℓ + 1) * exp (-t + a * Real.sqrt t) +
          t ^ (3 * ν / 2 - 1) * |Real.log t| ^ (ℓ + 1) * exp (-t + a * Real.sqrt t) := by
      funext t
      simp only [bound]
      ring
    rw [heq]
    exact h1.add h2
  have hball : ∀ x ∈ Metric.ball ν (ν / 2), 0 < x ∧ ν / 2 - 1 ≤ x - 1 ∧ x - 1 ≤ 3 * ν / 2 - 1 := by
    intro x hx
    have habs : |x - ν| < ν / 2 := by simpa only [Metric.mem_ball, Real.dist_eq] using hx
    obtain ⟨h1, h2⟩ := abs_lt.mp habs
    exact ⟨by linarith, by linarith, by linarith⟩
  have hpos : ∀ᵐ t ∂μ, 0 < t := ae_restrict_mem measurableSet_Ioi
  have hpoint : ∀ t, 0 < t → ∀ x, HasDerivAt (fun x => F x t) (D x t) x := by
    intro t ht x
    have hpow : HasDerivAt (fun x : ℝ => t ^ (x - 1)) (t ^ (x - 1) * Real.log t) x := by
      refine (((hasDerivAt_id x).sub_const 1).const_rpow ht).congr_deriv ?_
      simp only [id, mul_one]
      ring
    have h := (hpow.mul_const (Real.log t ^ ℓ)).mul_const (exp (-t + a * Real.sqrt t))
    refine h.congr_deriv ?_
    simp only [D]
    ring
  have hFmeas : ∀ᶠ x in 𝓝 ν, AEStronglyMeasurable (F x) μ :=
    eventually_of_mem (Ioi_mem_nhds hν) fun x hx => (hFi x hx).aestronglyMeasurable
  have hbound : ∀ᵐ t ∂μ, ∀ x ∈ Metric.ball ν (ν / 2), ‖D x t‖ ≤ bound t := by
    filter_upwards [hpos] with t ht x hx
    obtain ⟨hx0, hx1, hx2⟩ := hball x hx
    have hrpow : t ^ (x - 1) ≤ t ^ (ν / 2 - 1) + t ^ (3 * ν / 2 - 1) := by
      rcases le_or_gt t 1 with ht1 | ht1
      · exact (Real.rpow_le_rpow_of_exponent_ge ht ht1 hx1).trans
          (le_add_of_nonneg_right (Real.rpow_nonneg ht.le _))
      · exact (Real.rpow_le_rpow_of_exponent_le ht1.le hx2).trans
          (le_add_of_nonneg_left (Real.rpow_nonneg ht.le _))
    simp only [D, bound]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg ht.le _), abs_pow,
      abs_of_pos (exp_pos _)]
    gcongr
  have hdiff : ∀ᵐ t ∂μ, ∀ x ∈ Metric.ball ν (ν / 2), HasDerivAt (fun x => F x t) (D x t) x := by
    filter_upwards [hpos] with t ht x _
    exact hpoint t ht x
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (F := F) (F' := D)
    (x₀ := ν) (bound := bound) (s := Metric.ball ν (ν / 2))
    (Metric.ball_mem_nhds ν (by linarith)) hFmeas (hFi ν hν)
    (hDi ν hν).aestronglyMeasurable hbound hbi hdiff
  exact h.2

/-- ★ **The `ν`-derivatives of the fluctuation function** are the log-weighted integrals. -/
theorem iteratedDeriv_fluctuation_eq {ν : ℝ} (hν : 0 < ν) (a : ℝ) (ℓ : ℕ) :
    iteratedDeriv ℓ (fun ν => fluctuation 1 ν a) ν = fluctuationLog ν a ℓ := by
  induction ℓ generalizing ν with
  | zero => rw [iteratedDeriv_zero, fluctuationLog_zero]
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv n (fun ν => fluctuation 1 ν a) =ᶠ[𝓝 ν]
        fun x => fluctuationLog x a n :=
      eventually_of_mem (Ioi_mem_nhds hν) fun x hx => ih hx
    rw [hev.deriv_eq]
    exact (hasDerivAt_fluctuationLog hν a n).deriv

/-- The log-weighted Mellin moment of the jet `τ^r e^{aτ}` is `(−1)^ℓ` times the log-weighted
fluctuation integral at the shifted index `μ + r/2`. -/
theorem mellinMom_pow_mul_exp {μ a : ℝ} (r ℓ : ℕ) :
    mellinMom (fun τ => τ ^ r * exp (a * τ)) μ ℓ = (-1) ^ ℓ * fluctuationLog (μ + r / 2) a ℓ := by
  unfold mellinMom momKernel fluctuationLog
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
  beta_reduce
  have hs0 : (0 : ℝ) < s := hs
  have h1 : Real.sqrt s ^ r = s ^ ((r : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hs0.le]
    congr 1
    ring
  have h2 : s ^ (μ + r / 2 - 1) = s ^ (μ - 1) * s ^ ((r : ℝ) / 2) := by
    rw [← Real.rpow_add hs0]
    congr 1
    ring
  rw [neg_pow, h1, h2, Real.exp_add]
  ring

/-- ★★ **The lower logarithmic Mellin weights are index derivatives of the fluctuation
function**: `mellinMom (τ^r e^{aτ}) μ ℓ = (−1)^ℓ ∂_ν^ℓ S_ν(a) |_{ν = μ + r/2}`. -/
theorem mellinMom_pow_mul_exp_eq_iteratedDeriv {μ a : ℝ} (hμ : 0 < μ) (r ℓ : ℕ) :
    mellinMom (fun τ => τ ^ r * exp (a * τ)) μ ℓ =
      (-1) ^ ℓ * iteratedDeriv ℓ (fun ν => fluctuation 1 ν a) (μ + r / 2) := by
  rw [mellinMom_pow_mul_exp r ℓ, iteratedDeriv_fluctuation_eq (by positivity) a ℓ]

end SmoothEngine

end Grammar
