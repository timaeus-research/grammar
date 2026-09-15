/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.Fluctuation
import Grammar.Asymptotic

/-!
# Positivity, monotonicity and Lipschitz bounds of the fluctuation function

`S_λ(a) = ∫₀^∞ t^{λ−1} e^{−βt + βa√t} dt` (positive: `fluctuation_pos`) is increasing in `a` and
locally Lipschitz with constant `β S_{λ+1/2}(M)` on `[−M, M]` (`abs_fluctuation_sub_le`). The
normalised
**fluctuation density** `fluctDensity μ a = S_μ(a)/Γ(μ)` at temperature one equals `1` at `a = 0`
and is the density of the empirical stratum measure with respect to the population one
(`EmpiricalStratumMeasure`). Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set

namespace Grammar

theorem differentiable_fluctuation (β lam : ℝ) (hβ : 0 < β) (hlam : 0 < lam) :
    Differentiable ℝ (fluctuation β lam) := fun a =>
  (hasDerivAt_fluctuation β lam hβ hlam a).differentiableAt

theorem monotone_fluctuation (β lam : ℝ) (hβ : 0 < β) (hlam : 0 < lam) :
    Monotone (fluctuation β lam) :=
  monotone_of_deriv_nonneg (differentiable_fluctuation β lam hβ hlam) fun a => by
    rw [(hasDerivAt_fluctuation β lam hβ hlam a).deriv]
    exact (mul_pos hβ (fluctuation_pos β (lam + 1 / 2) a hβ (by linarith))).le

theorem fluctuation_mono_of_abs_le (β lam : ℝ) (hβ : 0 < β) (hlam : 0 < lam) {M a : ℝ}
    (ha : |a| ≤ M) : fluctuation β lam a ≤ fluctuation β lam M :=
  monotone_fluctuation β lam hβ hlam ((le_abs_self a).trans ha)

/-- **Local Lipschitz bound**: `|S_λ(a) − S_λ(b)| ≤ β S_{λ+1/2}(M) |a − b|` for `|a|, |b| ≤ M`. -/
theorem abs_fluctuation_sub_le (β lam : ℝ) (hβ : 0 < β) (hlam : 0 < lam) {M a b : ℝ}
    (ha : |a| ≤ M) (hb : |b| ≤ M) :
    |fluctuation β lam a - fluctuation β lam b| ≤
      β * fluctuation β (lam + 1 / 2) M * |a - b| := by
  have hbound : ∀ x ∈ Icc (-M) M, ‖deriv (fluctuation β lam) x‖ ≤
      β * fluctuation β (lam + 1 / 2) M := fun x hx => by
    rw [(hasDerivAt_fluctuation β lam hβ hlam x).deriv, Real.norm_eq_abs,
      abs_of_pos (mul_pos hβ (fluctuation_pos β _ x hβ (by linarith)))]
    exact mul_le_mul_of_nonneg_left
      (monotone_fluctuation β _ hβ (by linarith) hx.2) hβ.le
  have := (convex_Icc (-M) M).norm_image_sub_le_of_norm_deriv_le
    (fun x _ => differentiable_fluctuation β lam hβ hlam x) hbound (abs_le.1 hb) (abs_le.1 ha)
  simpa [Real.norm_eq_abs] using this

/-! ### The normalised fluctuation density at temperature one -/

/-- The fluctuation density `S_μ(a)/Γ(μ)` (temperature one): the density of the empirical
stratum measure with respect to the population one; equals `1` at `a = 0`. -/
noncomputable def fluctDensity (μ a : ℝ) : ℝ := fluctuation 1 μ a / Real.Gamma μ

/-- The Lipschitz constant of the fluctuation density on `[−M, M]`: `S_{μ+1/2}(M)/Γ(μ)`. -/
noncomputable def fluctLip (μ M : ℝ) : ℝ := fluctuation 1 (μ + 1 / 2) M / Real.Gamma μ

theorem fluctDensity_zero {μ : ℝ} (hμ : 0 < μ) : fluctDensity μ 0 = 1 := by
  rw [fluctDensity, fluctuation_zero 1 μ one_pos hμ, Real.one_rpow, one_mul,
    div_self (Real.Gamma_pos_of_pos hμ).ne']

theorem fluctDensity_pos {μ : ℝ} (hμ : 0 < μ) (a : ℝ) : 0 < fluctDensity μ a :=
  div_pos (fluctuation_pos 1 μ a one_pos hμ) (Real.Gamma_pos_of_pos hμ)

theorem continuous_fluctDensity {μ : ℝ} (hμ : 0 < μ) : Continuous (fluctDensity μ) :=
  (differentiable_fluctuation 1 μ one_pos hμ).continuous.div_const _

theorem fluctDensity_le_of_abs_le {μ : ℝ} (hμ : 0 < μ) {M a : ℝ} (ha : |a| ≤ M) :
    fluctDensity μ a ≤ fluctDensity μ M :=
  div_le_div_of_nonneg_right (fluctuation_mono_of_abs_le 1 μ one_pos hμ ha)
    (Real.Gamma_pos_of_pos hμ).le

theorem abs_fluctDensity_sub_le {μ : ℝ} (hμ : 0 < μ) {M a b : ℝ} (ha : |a| ≤ M) (hb : |b| ≤ M) :
    |fluctDensity μ a - fluctDensity μ b| ≤ fluctLip μ M * |a - b| := by
  unfold fluctDensity fluctLip
  rw [← sub_div, abs_div, abs_of_pos (Real.Gamma_pos_of_pos hμ), div_mul_eq_mul_div]
  refine div_le_div_of_nonneg_right ?_ (Real.Gamma_pos_of_pos hμ).le
  have := abs_fluctuation_sub_le 1 μ one_pos hμ ha hb
  rwa [one_mul] at this

end Grammar
