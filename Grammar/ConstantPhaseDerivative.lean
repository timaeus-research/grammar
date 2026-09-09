/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.SmoothSeries
import Grammar.ConstantPhaseTransport
import Grammar.UniformCutoffConst

/-!
# The phase derivative of the constant-phase coefficient (unit 335)

Passing `∂_a` through the monomial sum: on `|a − a₀| < 1` the half-shifted kernels are dominated by
`|f_γ| β D M_{μ+1/2}(|a₀|+1)` (the phase log moment is monotone in the phase), so Mathlib's
derivative-of-series theorem gives `∂_a T(μ,j;a) = β H(μ,j;a)` for the summed kernel functional
(`hasDerivAt_kernelFunctional_phase`), hence for the constant-phase coefficient itself
(`hasDerivAt_constPhase_coeff`), and the transport identity of `ConstantPhaseTransport` takes the
paper-style form
```
C_K(μ+1, j; a) = (μ C(μ,j;a) − (j+1) C(μ,j+1;a) + (a/2) ∂_a C(μ,j;a))/β
```
(`population_coeff_add_two_k_phase_deriv`). Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

open CoeffFamily

/-- **The kernel functional is differentiable in the constant phase**, with derivative
`β` times the half-shifted kernel functional. -/
theorem hasDerivAt_kernelFunctional_phase (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    {β : ℝ} (hβ : 0 < β) {μ : ℝ} (hμ : 0 < μ) (j : ℕ) {f : CoeffFamily (n + 1)}
    (hf : AbsSummable f) (a₀ : ℝ) :
    HasDerivAt (fun a => kernelFunctional n h k β a 0 μ j f)
      (β * kernelFunctionalHalf n h k β a₀ μ j f) a₀ := by
  have hμ' : 0 < μ + 1 / 2 := by linarith
  set B : ℝ := kernelBudget n k * phaseLogMoment β (|a₀| + 1) (μ + 1 / 2) n 0 with hB
  have hsum := hasDerivAt_tsum_of_isPreconnected (𝕜 := ℝ) (F := ℝ)
    (u := fun γ => |f γ| * (β * B)) (t := Metric.ball a₀ 1)
    (g := fun γ a => f γ * kernelS n h k β a 0 μ j γ)
    (g' := fun γ a => f γ * (β * kernelSHalf n h k β a μ j γ)) (y₀ := a₀) (y := a₀)
    (hf.mul_right _) Metric.isOpen_ball (convex_ball a₀ 1).isPreconnected
    (fun γ a _ => (hasDerivAt_kernelS_phase n h k hβ hμ j γ a).const_mul (f γ))
    (fun γ a ha => ?_) (Metric.mem_ball_self one_pos) ?_ (Metric.mem_ball_self one_pos)
  · unfold kernelFunctional kernelFunctionalHalf
    have hg' : (fun a => ∑' γ, f γ * (β * kernelSHalf n h k β a μ j γ)) =
        fun a => β * ∑' γ, f γ * kernelSHalf n h k β a μ j γ := by
      funext a
      rw [← tsum_mul_left]
      congr 1
      funext γ
      ring
    have := hsum.const_mul (∏ i, 1 / (2 * (k i : ℝ)))
    refine this.congr_deriv ?_
    have e : ∑' γ, f γ * (β * kernelSHalf n h k β a₀ μ j γ) =
        β * ∑' γ, f γ * kernelSHalf n h k β a₀ μ j γ := congrFun hg' a₀
    rw [e]
    ring
  · -- the derivative bound on the ball
    have ha' : a ≤ |a₀| + 1 := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt] at ha
      linarith [le_abs_self a₀]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hβ]
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hβ.le) (abs_nonneg _)
    refine (abs_kernelSHalf_le n h k hk β a hβ hμ j γ).trans ?_
    exact mul_le_mul_of_nonneg_left (phaseLogMoment_mono β hβ ha' hμ' n 0)
      (kernelBudget_nonneg n k)
  · -- summability at the centre
    refine Summable.of_norm ?_
    simpa [Real.norm_eq_abs, abs_mul] using summable_kernel_term n h k hk β a₀ hβ 0 hμ j hf

/-- **The constant-phase coefficient is differentiable in the phase**, with derivative
`β H(μ,j;a)`. -/
theorem hasDerivAt_constPhase_coeff (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {β : ℝ}
    (hβ : 0 < β) {cη : CoeffFamily (n + 1)} (hη : AbsSummable cη) {μ : ℝ} (hμ : 0 < μ) (j : ℕ)
    (a₀ : ℝ) :
    HasDerivAt (fun a => familySpectralCoeff n h k β (constFamily a) cη μ j)
      (β * kernelFunctionalHalf n h k β a₀ μ j cη) a₀ := by
  have e : (fun a => familySpectralCoeff n h k β (constFamily a) cη μ j) =
      fun a => kernelFunctional n h k β a 0 μ j cη :=
    funext fun a => familySpectralCoeff_constPhase n h k hk hβ a hη hμ j
  rw [e]
  exact hasDerivAt_kernelFunctional_phase n h k hk hβ hμ j hη a₀

/-- **Constant-phase transport in derivative form**:
`C_K(μ+1,j;a) = (μ C(μ,j;a) − (j+1) C(μ,j+1;a) + (a/2) ∂_a C(μ,j;a))/β`. -/
theorem population_coeff_add_two_k_phase_deriv (n : ℕ) (h k : Fin (n + 1) → ℕ)
    (hk : ∀ i, 0 < k i) {β : ℝ} (hβ : 0 < β) (a : ℝ) {cη : CoeffFamily (n + 1)}
    (hη : AbsSummable cη) {μ : ℝ} (hμ : 0 < μ) (j : ℕ) :
    familySpectralCoeff n (fun i => h i + 2 * k i) k β (constFamily a) cη (μ + 1) j =
      (μ * familySpectralCoeff n h k β (constFamily a) cη μ j -
        ((j : ℝ) + 1) * familySpectralCoeff n h k β (constFamily a) cη μ (j + 1) +
        a / 2 * deriv (fun a => familySpectralCoeff n h k β (constFamily a) cη μ j) a) / β := by
  rw [population_coeff_add_two_k_phase n h k hk hβ a hη hμ j,
    (hasDerivAt_constPhase_coeff n h k hk hβ hη hμ j a).deriv]
  field_simp

end Grammar
