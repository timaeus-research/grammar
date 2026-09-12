/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.AnalyticFamilyData
import Grammar.ParameterisedSeriesDatum

/-!
# Arbitrary-radius analytic uniform series (CCCXXVIII; phase 3, unit P1)

Consult #98 §2. For a family `F : X → (Fin m → ℂ) → ℂ` of holomorphic functions on the open polydisc
of radius `R`, jointly continuous and uniformly bounded by `M` on the closed polydisc of radius
`r < R`, the real Cauchy coefficients at radius `r` form a `UniformSeriesFamily X m ρ` for every
`0 < ρ < r` (`analyticUniformSeries`): the coefficients are continuous in the parameter
(`continuous_polyRealCoeff_param`), dominated by `M r^{-|γ|}` (`norm_polyCoeff_le`), and the
majorant is `ρ`-summable because `Σ_γ M (ρ/r)^{|γ|} = Σ_γ M ∏_i (ρ/r)^{γ_i}` converges
(`summable_cauchyMajorant_weight`, the multivariate geometric series `summable_prodGeom`).
The represented function is the real part of `F x` on the real ball of radius `r`
(`evalF_analyticUniformSeries`, from `evalF_polyRealCoeff_of_lt`). Unlike `analyticDatum` (scale 1)
this works at every radius in the ORIGINAL normal variables. Zero `sorry`/`axiom`.
-/

open Set Filter Topology

namespace Grammar

open CoeffFamily

/-- The Cauchy majorant `M r^{-|γ|}` is summable against the weight `ρ^{|γ|}` for `0 ≤ ρ < r`. -/
theorem summable_cauchyMajorant_weight (m : ℕ) {ρ r : ℝ} (hρ : 0 ≤ ρ) (hρr : ρ < r) (M : ℝ) :
    Summable fun γ : Fin m → ℕ => |M * r⁻¹ ^ (∑ i, γ i)| * ρ ^ (∑ i, γ i) := by
  have hr : 0 < r := hρ.trans_lt hρr
  have hq0 : 0 ≤ ρ / r := div_nonneg hρ hr.le
  have hq1 : ρ / r < 1 := (div_lt_one hr).2 hρr
  refine ((summable_prodGeom m (q := fun _ => ρ / r) (fun _ => hq0) fun _ => hq1).mul_left
    |M|).congr fun γ => ?_
  rw [Finset.prod_pow_eq_pow_sum, abs_mul, abs_pow, abs_inv, abs_of_pos hr, div_pow, mul_assoc,
    inv_pow, ← div_eq_inv_mul, mul_div_assoc']

variable {X : Type*} [TopologicalSpace X] {m : ℕ} {ρ r R M : ℝ}

/-- ★ **Analytic uniform series at an arbitrary radius**: the real Cauchy coefficients at radius `r`
of a family jointly continuous and bounded by `M` on the closed polydisc of radius `r` form a
`ρ`-summable uniform series family for every `ρ < r`. (Holomorphicity is not needed for the family
itself; it enters only in the reconstruction `evalF_analyticUniformSeries`.) -/
noncomputable def analyticUniformSeries (hρ : 0 < ρ) (hρr : ρ < r) (F : X → (Fin m → ℂ) → ℂ)
    (hcont : ContinuousOn (fun p : X × (Fin m → ℂ) => F p.1 p.2) (univ ×ˢ closedPolydisc m r))
    (hbound : ∀ x, ∀ z ∈ closedPolydisc m r, ‖F x z‖ ≤ M) : UniformSeriesFamily X m ρ where
  f x := polyRealCoeff m r (F x)
  M γ := M * r⁻¹ ^ (∑ i, γ i)
  continuous_coeff γ := continuous_polyRealCoeff_param (hρ.trans hρr) hcont γ
  abs_le x γ := by
    refine (Complex.abs_re_le_norm _).trans (norm_polyCoeff_le (hρ.trans hρr) ?_ γ)
    exact fun w hw => hbound x w (torusSet_subset_closedPolydisc m r hw)
  M_abs := summable_cauchyMajorant_weight m hρ.le hρr M

theorem analyticUniformSeries_f (hρ : 0 < ρ) (hρr : ρ < r) (F : X → (Fin m → ℂ) → ℂ)
    (hcont : ContinuousOn (fun p : X × (Fin m → ℂ) => F p.1 p.2) (univ ×ˢ closedPolydisc m r))
    (hbound : ∀ x, ∀ z ∈ closedPolydisc m r, ‖F x z‖ ≤ M) (x : X) :
    (analyticUniformSeries hρ hρr F hcont hbound).f x = polyRealCoeff m r (F x) := rfl

/-- Reconstruction on the real ball of radius `r`: the series represents `Re (F x)`. -/
theorem evalF_analyticUniformSeries (hρ : 0 < ρ) (hρr : ρ < r) (hrR : r < R)
    (F : X → (Fin m → ℂ) → ℂ) (hhol : ∀ x, DifferentiableOn ℂ (F x) (openPolydisc m R))
    (hcont : ContinuousOn (fun p : X × (Fin m → ℂ) => F p.1 p.2) (univ ×ˢ closedPolydisc m r))
    (hbound : ∀ x, ∀ z ∈ closedPolydisc m r, ‖F x z‖ ≤ M) (x : X) {u : Fin m → ℝ}
    (hu : ‖u‖ < r) :
    evalF ((analyticUniformSeries hρ hρr F hcont hbound).f x) u = (F x fun i => (u i : ℂ)).re := by
  rw [analyticUniformSeries_f]
  refine evalF_polyRealCoeff_of_lt (hρ.trans hρr) hrR (hhol x) fun i => ?_
  rw [Complex.norm_real]
  exact (norm_le_pi_norm u i).trans_lt hu

/-- Reconstruction on the series ball `‖u‖ < ρ`. -/
theorem evalF_analyticUniformSeries_of_lt (hρ : 0 < ρ) (hρr : ρ < r) (hrR : r < R)
    (F : X → (Fin m → ℂ) → ℂ) (hhol : ∀ x, DifferentiableOn ℂ (F x) (openPolydisc m R))
    (hcont : ContinuousOn (fun p : X × (Fin m → ℂ) => F p.1 p.2) (univ ×ˢ closedPolydisc m r))
    (hbound : ∀ x, ∀ z ∈ closedPolydisc m r, ‖F x z‖ ≤ M) (x : X) {u : Fin m → ℝ}
    (hu : ‖u‖ < ρ) :
    evalF ((analyticUniformSeries hρ hρr F hcont hbound).f x) u = (F x fun i => (u i : ℂ)).re :=
  evalF_analyticUniformSeries hρ hρr hrR F hhol hcont hbound x (hu.trans hρr)

end Grammar
