/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.PolyCoeffParam
import Grammar.AnalyticTaylorTree
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Cauchy coefficients are measurable in a parameter

For a family `G : 𝓧 → (Fin d → ℂ) → ℂ` that is jointly measurable in `(x, w)`, the iterated
circle average `x ↦ iterOp d r (G x)` is measurable (`measurable_iterOp_param`), hence so are the
several-variable Cauchy coefficients `x ↦ polyCoeff d r (G x) γ` (`measurable_polyCoeff_param`) and
their real parts (`measurable_polyRealCoeff_param`).  The proof is an induction on the number of
variables with the remaining circle variables kept inside the measurable parameter: each circle
average is a Bochner integral over the angle, and integrals of jointly measurable functions are
measurable in the parameter (`StronglyMeasurable.integral_prod_right'`).

No continuity or integrability is needed for measurability (the Bochner integral is totalised); the
identities of the coefficients with genuine Cauchy integrals are proved elsewhere under continuity.
-/

open MeasureTheory Set Real Filter Topology
open scoped Interval

namespace Grammar

variable {𝓧 : Type*} [MeasurableSpace 𝓧]

/-- The parametric circle average `x ↦ circleOp r (g x)` is measurable when `(x, w) ↦ g x w` is. -/
theorem measurable_circleOp_param {r : ℝ} {g : 𝓧 → ℂ → ℂ}
    (hg : Measurable fun p : 𝓧 × ℂ => g p.1 p.2) : Measurable fun x => circleOp r (g x) := by
  unfold circleOp circleIntegral
  refine Measurable.const_mul ?_ _
  have hle : (0 : ℝ) ≤ 2 * π := by positivity
  simp_rw [intervalIntegral.integral_of_le hle]
  have hF : Measurable fun p : 𝓧 × ℝ =>
      deriv (circleMap 0 r) p.2 • ((circleMap 0 r p.2)⁻¹ * g p.1 (circleMap 0 r p.2)) := by
    simp_rw [deriv_circleMap]
    have h1 : Measurable fun p : 𝓧 × ℝ => circleMap 0 r p.2 :=
      (continuous_circleMap 0 r).measurable.comp measurable_snd
    exact (h1.mul measurable_const).smul (h1.inv.mul (hg.comp (measurable_fst.prodMk h1)))
  exact (hF.stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Ioc 0 (2 * π)))).measurable

/-- **Measurability of the iterated circle average in a parameter.** -/
theorem measurable_iterOp_param : ∀ (d : ℕ) {𝓧 : Type*} [MeasurableSpace 𝓧] (r : ℝ)
    {G : 𝓧 → (Fin d → ℂ) → ℂ}, Measurable (fun p : 𝓧 × (Fin d → ℂ) => G p.1 p.2) →
    Measurable fun x => iterOp d r (G x)
  | 0, 𝓧, _, r, G, hG => by
    simp only [iterOp]
    exact hG.comp (measurable_id.prodMk measurable_const)
  | d + 1, 𝓧, _, r, G, hG => by
    simp only [iterOp]
    -- the inner operator with the first circle variable absorbed into the parameter
    have hinner : Measurable fun p : 𝓧 × ℂ =>
        iterOp d r fun w' => G p.1 (Fin.cons p.2 w') := by
      refine measurable_iterOp_param d r (G := fun p : 𝓧 × ℂ => fun w' => G p.1 (Fin.cons p.2 w'))
        ?_
      have hcons : Measurable fun q : (𝓧 × ℂ) × (Fin d → ℂ) =>
          (Fin.cons q.1.2 q.2 : Fin (d + 1) → ℂ) := by
        refine measurable_pi_lambda _ fun i => ?_
        refine Fin.cases ?_ (fun j => ?_) i
        · simp only [Fin.cons_zero]; exact measurable_snd.comp measurable_fst
        · simp only [Fin.cons_succ]; exact (measurable_pi_apply j).comp measurable_snd
      exact hG.comp ((measurable_fst.comp measurable_fst).prodMk hcons)
    exact measurable_circleOp_param (g := fun x w => iterOp d r fun w' => G x (Fin.cons w w'))
      hinner

/-- **Cauchy coefficients are measurable in the parameter.** -/
theorem measurable_polyCoeff_param {d : ℕ} (r : ℝ) {a : 𝓧 → (Fin d → ℂ) → ℂ}
    (ha : Measurable fun p : 𝓧 × (Fin d → ℂ) => a p.1 p.2) (γ : Fin d → ℕ) :
    Measurable fun x => polyCoeff d r (a x) γ := by
  unfold polyCoeff
  refine measurable_iterOp_param d r (G := fun x w => a x w * ∏ i, (w i)⁻¹ ^ γ i) ?_
  refine ha.mul ?_
  exact Finset.measurable_prod _ fun i _ =>
    ((measurable_pi_apply i).comp measurable_snd).inv.pow_const _

theorem measurable_polyRealCoeff_param {d : ℕ} (r : ℝ) {a : 𝓧 → (Fin d → ℂ) → ℂ}
    (ha : Measurable fun p : 𝓧 × (Fin d → ℂ) => a p.1 p.2) (γ : Fin d → ℕ) :
    Measurable fun x => polyRealCoeff d r (a x) γ :=
  Complex.measurable_re.comp (measurable_polyCoeff_param r ha γ)

end Grammar
