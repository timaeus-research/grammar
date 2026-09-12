/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The abstract perturbation transfer for reweighted posteriors (CCLXXXVII)

The first unit of the statistical-transfer programme (consult #86, C1; the population/empirical
guardrail). For a probability measure `μ` (the population posterior), a nonnegative integrable
reweighting `R` (the empirical-to-population density ratio) and a positive scalar `A`, the
**tilted expectation** `μ̂(φ) = ∫ φ R dμ / ∫ R dμ` is compared with `μ(φ)` through the single number
`δ = ∫ |R/A − 1| dμ`:

* `abs_integral_div_sub_one_le`: `|∫ R dμ / A − 1| ≤ δ`;
* ★ `abs_tiltedExpectation_sub_le`: for `|φ| ≤ M` and `δ < 1`,
  `|μ̂(φ) − μ(φ)| ≤ 2 M δ / (1 − δ)`;
* `tendsto_tiltedExpectation_sub`: along a sequence with `δ_n → 0`, `μ̂_n(φ) − μ_n(φ) → 0`.

The hypothesis `δ_n → 0` is substantial — it is NOT a consequence of an ordinary uniform law of
large numbers (the empirical fluctuation survives at order one on the shrinking neighbourhoods of
the zero set; consult #86's Gaussian example `m(a,b) = (a, ab)`), and the theorem says nothing about
when it holds. It is the clean interface through which any such transfer must pass.
-/

open MeasureTheory Filter Topology

namespace Grammar

section Tilted

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

/-- **The tilted expectation** `μ̂(φ) = ∫ φ R dμ / ∫ R dμ`. -/
noncomputable def tiltedExpectation (R φ : Ω → ℝ) : ℝ := (∫ x, φ x * R x ∂μ) / ∫ x, R x ∂μ

variable [IsProbabilityMeasure μ] {R : Ω → ℝ} (hR : Integrable R μ) {A : ℝ} (hA : 0 < A)

include hR hA in
/-- `|∫ R dμ / A − 1| ≤ ∫ |R/A − 1| dμ`. -/
theorem abs_integral_div_sub_one_le :
    |(∫ x, R x ∂μ) / A - 1| ≤ ∫ x, |R x / A - 1| ∂μ := by
  have h1 : (∫ x, R x ∂μ) / A - 1 = ∫ x, (R x / A - 1) ∂μ := by
    rw [integral_sub (hR.div_const A) (integrable_const 1), integral_div, integral_const]
    simp
  rw [h1]
  exact abs_integral_le_integral_abs

include hR hA in
/-- ★ **The perturbation bound**: for `|φ| ≤ M` and `δ = ∫ |R/A − 1| dμ < 1`,
`|μ̂(φ) − μ(φ)| ≤ 2 M δ / (1 − δ)`. -/
theorem abs_tiltedExpectation_sub_le {φ : Ω → ℝ} (hφ : AEStronglyMeasurable φ μ) {M : ℝ}
    (hM : ∀ x, |φ x| ≤ M) (hδ : ∫ x, |R x / A - 1| ∂μ < 1) :
    |tiltedExpectation μ R φ - ∫ x, φ x ∂μ| ≤
      2 * M * (∫ x, |R x / A - 1| ∂μ) / (1 - ∫ x, |R x / A - 1| ∂μ) := by
  set δ := ∫ x, |R x / A - 1| ∂μ with hδdef
  obtain ⟨x₀, -⟩ : (Set.univ : Set Ω).Nonempty :=
    nonempty_of_measure_ne_zero (μ := μ) (by rw [measure_univ]; exact one_ne_zero)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM x₀)
  have hδ0 : 0 ≤ δ := integral_nonneg fun x => abs_nonneg _
  -- the normalised reweighting
  set g : Ω → ℝ := fun x => R x / A with hgdef
  have hg : Integrable g μ := hR.div_const A
  have hg1 : Integrable (fun x => g x - 1) μ := hg.sub (integrable_const 1)
  have hφint : Integrable φ μ := (integrable_const M).mono' hφ (Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs]; exact hM x)
  have hφg : Integrable (fun x => φ x * (g x - 1)) μ :=
    hg1.bdd_mul (c := M) hφ (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hM x)
  have hD : |(∫ x, g x ∂μ) - 1| ≤ δ := by
    have := abs_integral_div_sub_one_le μ hR hA
    rwa [← integral_div] at this
  have hDpos : 1 - δ ≤ ∫ x, g x ∂μ := by
    have := (abs_le.1 hD).1
    linarith
  have hDpos' : 0 < ∫ x, g x ∂μ := lt_of_lt_of_le (by linarith) hDpos
  -- the tilted expectation in terms of `g`
  have e1 : ∫ x, φ x * g x ∂μ = (∫ x, φ x * R x ∂μ) / A := by
    rw [← integral_div]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hgdef]
    ring
  have e2 : ∫ x, g x ∂μ = (∫ x, R x ∂μ) / A := by
    rw [← integral_div]
  have htilt : tiltedExpectation μ R φ = (∫ x, φ x * g x ∂μ) / ∫ x, g x ∂μ := by
    unfold tiltedExpectation
    rw [e1, e2, div_div_div_cancel_right₀ hA.ne']
  -- the numerator identity
  have hφg' : Integrable (fun x => φ x * g x) μ :=
    hg.bdd_mul (c := M) hφ (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hM x)
  have hnum : (∫ x, φ x * g x ∂μ) - (∫ x, φ x ∂μ) * ∫ x, g x ∂μ =
      (∫ x, φ x * (g x - 1) ∂μ) - (∫ x, φ x ∂μ) * ((∫ x, g x ∂μ) - 1) := by
    have : (∫ x, φ x * (g x - 1) ∂μ) = (∫ x, φ x * g x ∂μ) - ∫ x, φ x ∂μ := by
      rw [← integral_sub hφg' hφint]
      congr 1
      funext x
      ring
    rw [this]
    ring
  -- the bounds on the two numerator terms
  have hb1 : |∫ x, φ x * (g x - 1) ∂μ| ≤ M * δ := by
    have := norm_integral_le_of_norm_le (f := fun x => φ x * (g x - 1)) (hg1.norm.const_mul M)
      (Eventually.of_forall fun x => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (by rw [Real.norm_eq_abs]; exact hM x) (norm_nonneg _))
    rw [Real.norm_eq_abs, integral_const_mul] at this
    simp only [Real.norm_eq_abs] at this
    exact this
  have hb2 : |∫ x, φ x ∂μ| ≤ M := by
    have := norm_integral_le_of_norm_le_const (μ := μ) (f := φ) (C := M)
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hM x)
    rwa [Real.norm_eq_abs, measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] at this
  -- assemble
  have hdiff : tiltedExpectation μ R φ - ∫ x, φ x ∂μ =
      ((∫ x, φ x * (g x - 1) ∂μ) - (∫ x, φ x ∂μ) * ((∫ x, g x ∂μ) - 1)) / ∫ x, g x ∂μ := by
    rw [htilt, ← hnum, sub_div, mul_div_assoc, div_self hDpos'.ne', mul_one]
  rw [hdiff, abs_div, abs_of_pos hDpos']
  calc |(∫ x, φ x * (g x - 1) ∂μ) - (∫ x, φ x ∂μ) * ((∫ x, g x ∂μ) - 1)| / ∫ x, g x ∂μ
      ≤ (M * δ + M * δ) / ∫ x, g x ∂μ := by
        gcongr
        calc |(∫ x, φ x * (g x - 1) ∂μ) - (∫ x, φ x ∂μ) * ((∫ x, g x ∂μ) - 1)|
            ≤ |∫ x, φ x * (g x - 1) ∂μ| + |(∫ x, φ x ∂μ) * ((∫ x, g x ∂μ) - 1)| := abs_sub _ _
          _ ≤ M * δ + M * δ := by
            rw [abs_mul]
            exact add_le_add hb1 (mul_le_mul hb2 hD (abs_nonneg _) hM0)
    _ ≤ (M * δ + M * δ) / (1 - δ) :=
        div_le_div_of_nonneg_left (by positivity) (by linarith) hDpos
    _ = 2 * M * δ / (1 - δ) := by ring

end Tilted

/-! ### The transfer along a sequence -/

section Sequence

variable {Ω : Type*} [MeasurableSpace Ω] (μ : ℕ → Measure Ω) [∀ n, IsProbabilityMeasure (μ n)]
  (R : ℕ → Ω → ℝ) (hR : ∀ n, Integrable (R n) (μ n)) (A : ℕ → ℝ) (hA : ∀ n, 0 < A n)

include hR hA in
/-- **The transfer**: if `δ_n = ∫ |R_n/A_n − 1| dμ_n → 0`, the tilted and the reference expectations
of a uniformly bounded observable have the same limit behaviour: their difference tends to `0`. -/
theorem tendsto_tiltedExpectation_sub {φ : Ω → ℝ} (hφ : ∀ n, AEStronglyMeasurable φ (μ n)) {M : ℝ}
    (hM : ∀ x, |φ x| ≤ M)
    (hδ : Tendsto (fun n => ∫ x, |R n x / A n - 1| ∂(μ n)) atTop (𝓝 0)) :
    Tendsto (fun n => tiltedExpectation (μ n) (R n) φ - ∫ x, φ x ∂(μ n)) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n => 2 * M * (∫ x, |R n x / A n - 1| ∂(μ n)) /
      (1 - ∫ x, |R n x / A n - 1| ∂(μ n))) atTop (𝓝 0) := by
    have h := (hδ.const_mul (2 * M)).div (tendsto_const_nhds.sub hδ)
      (by norm_num : (1 : ℝ) - 0 ≠ 0)
    rw [show (2 * M * 0 / (1 - 0) : ℝ) = 0 by simp] at h
    exact h
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [hδ.eventually (eventually_lt_nhds one_pos)] with n hn
  rw [Real.norm_eq_abs]
  exact abs_tiltedExpectation_sub_le (μ n) (hR n) (hA n) (hφ n) hM hn

end Sequence

end Grammar
