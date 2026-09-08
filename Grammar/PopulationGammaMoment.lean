/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.MonomialPhaseTail
import Grammar.GammaLogAsymptotic

/-!
# The zero-phase, zero-log fluctuation moment is the Gamma integral (Astra #37 P1, unit 292)

The kernel moments of the Taylor tree are `fluctMoment β a p μ i = ∫₀^∞ t^{μ-1} (−log t)^i (√t)^p
e^{−βt + β√t a} dt`. At zero phase (`a = 0`) and zero fluctuation order (`p = 0`) they are the
Mellin moments `∫₀^∞ t^{μ-1} (−log t)^i e^{−βt} dt` of the pure exponential; for `i = 0` this is
the Gamma integral `Γ(μ) β^{−μ}` (`μ > 0`, `β > 0`). This is the analytic constant of the paper's
bare normal moments (`eq:a_minus_m_explicit` with the Tauberian factor `Γ(λ)`), now identified
inside the Taylor-tree coefficient kernel `S_0(μ,j;γ)` at `q = j`. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

/-- At zero phase and zero fluctuation order the kernel is the pure exponential. -/
theorem phaseKernel_zero_zero (β t : ℝ) : phaseKernel β 0 0 t = Real.exp (-(β * t)) := by
  simp [phaseKernel]

/-- **Zero-phase, zero-log Mellin moment**: `fluctMoment β 0 0 μ 0 = Γ(μ) β^{−μ}` for `μ > 0`,
`β > 0`. -/
theorem fluctMoment_population_zero_log (β μ : ℝ) (hβ : 0 < β) (hμ : 0 < μ) :
    fluctMoment β 0 0 μ 0 = Real.Gamma μ * β ^ (-μ) := by
  unfold fluctMoment
  rw [← integral_rpow_mul_exp_neg_mul μ β hμ hβ]
  congr 1
  funext t
  rw [phaseKernel_zero_zero]
  simp

/-- The zero-phase, zero-log moment is strictly positive. -/
theorem fluctMoment_population_zero_log_pos (β μ : ℝ) (hβ : 0 < β) (hμ : 0 < μ) :
    0 < fluctMoment β 0 0 μ 0 := by
  rw [fluctMoment_population_zero_log β μ hβ hμ]
  exact mul_pos (Real.Gamma_pos_of_pos hμ) (Real.rpow_pos_of_pos hβ _)

end Grammar
