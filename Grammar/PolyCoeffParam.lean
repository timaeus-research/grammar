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
