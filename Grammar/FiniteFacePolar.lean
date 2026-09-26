/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.ChartZetaPolar

/-!
# The polar part of a finite face sum (route B, unit B7)

The polar theorem of unit 5 (`chartZetaAtDepth_sub_polarPart_isBigO_one`) is an instance of a
statement about an arbitrary finite family: for weights `w x`, pole orders `c x ≤ D + 1` and
functions `f x` holomorphic near `μ`, the sum `Σ_x w x · (μ − s)^{−c x} · f x s` minus the
principal part built from the Taylor coefficients of the `f x`,

  `finiteFacePolarCoeff X w c f μ q
     = Σ_{x : c x ≥ q+1} w x · (−1)^{c x} · f x^{(c x − 1 − q)}(μ) / (c x − 1 − q)!`

(the coefficient of `(s − μ)^{−(q+1)}`), is bounded on a punctured neighbourhood of `μ`
(★ `finiteFaceSum_sub_polarPart_isBigO_one`).  Unit 5's `chartPolarCoeff` is the instance with
`w = faceW · resConst`, `c = poleOrder`, `f = faceHolo` (`chartPolarCoeff_eq_finiteFacePolarCoeff`);
the empirical continuation of unit B12 is the instance with the coupled face zeta functions.
-/

open Filter Topology Finset Asymptotics
open scoped Nat

namespace Grammar

section FiniteFace

variable {α : Type*}

/-- The polar coefficients of the finite face sum `Σ_x w x (μ − s)^{−c x} f x s`: the coefficient
of `(s − μ)^{−(q+1)}`. -/
noncomputable def finiteFacePolarCoeff (X : Finset α) (w : α → ℂ) (c : α → ℕ) (f : α → ℂ → ℂ)
    (μ : ℂ) (q : ℕ) : ℂ :=
  ∑ x ∈ X.filter (fun x => q + 1 ≤ c x),
    w x * ((-1) ^ c x * iteratedDeriv (c x - 1 - q) (f x) μ / ((c x - 1 - q)! : ℂ))

theorem finiteFacePolarCoeff_eq_zero (X : Finset α) (w : α → ℂ) (c : α → ℕ) (f : α → ℂ → ℂ)
    (μ : ℂ) {q : ℕ} (hq : ∀ x ∈ X, c x < q + 1) :
    finiteFacePolarCoeff X w c f μ q = 0 := by
  unfold finiteFacePolarCoeff
  rw [Finset.filter_false_of_mem fun x hx => not_le.2 (hq x hx)]
  simp

/-- The principal part rearranged as a sum over the family. -/
theorem polarPart_finiteFacePolarCoeff_eq (X : Finset α) (w : α → ℂ) (c : α → ℕ) (f : α → ℂ → ℂ)
    (μ : ℂ) {D : ℕ} (hD : ∀ x ∈ X, c x ≤ D + 1) (s : ℂ) :
    polarPart D (finiteFacePolarCoeff X w c f μ) μ s = ∑ x ∈ X, w x *
      ∑ q ∈ range (c x),
        (-1) ^ c x * iteratedDeriv (c x - 1 - q) (f x) μ / ((c x - 1 - q)! : ℂ) /
          (s - μ) ^ (q + 1) := by
  unfold polarPart finiteFacePolarCoeff
  simp_rw [Finset.sum_div, Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Finset.mul_sum, ← Finset.sum_filter]
  have hrange : (range (D + 1)).filter (fun q => q + 1 ≤ c x) = range (c x) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_range]
    have := hD x hx
    omega
  rw [hrange]
  refine Finset.sum_congr rfl fun q _ => ?_
  ring

/-- ★ **The polar part of a finite face sum.**  For `f x` holomorphic on a neighbourhood of `μ`
and pole orders `c x ≤ D + 1`, the difference
`Σ_x w x (μ − s)^{−c x} f x s − polarPart D (finiteFacePolarCoeff …) μ` is bounded on a punctured
neighbourhood of `μ`. -/
theorem finiteFaceSum_sub_polarPart_isBigO_one (X : Finset α) (w : α → ℂ) (c : α → ℕ)
    (f : α → ℂ → ℂ) (μ : ℂ) (hf : ∀ x ∈ X, ∃ U ∈ 𝓝 μ, DifferentiableOn ℂ (f x) U) {D : ℕ}
    (hD : ∀ x ∈ X, c x ≤ D + 1) :
    (fun s : ℂ => (∑ x ∈ X, w x * ((μ - s)⁻¹ ^ c x * f x s)) -
      polarPart D (finiteFacePolarCoeff X w c f μ) μ s) =O[𝓝[≠] μ] fun _ => (1 : ℂ) := by
  have hrw : ∀ s : ℂ, (∑ x ∈ X, w x * ((μ - s)⁻¹ ^ c x * f x s)) -
      polarPart D (finiteFacePolarCoeff X w c f μ) μ s =
      ∑ x ∈ X, w x * ((μ - s)⁻¹ ^ c x * f x s - ∑ q ∈ range (c x),
        (-1) ^ c x * iteratedDeriv (c x - 1 - q) (f x) μ / ((c x - 1 - q)! : ℂ) /
          (s - μ) ^ (q + 1)) := by
    intro s
    rw [polarPart_finiteFacePolarCoeff_eq X w c f μ hD s, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  have key : (∑ x ∈ X, fun s : ℂ => w x * ((μ - s)⁻¹ ^ c x * f x s - ∑ q ∈ range (c x),
      (-1) ^ c x * iteratedDeriv (c x - 1 - q) (f x) μ / ((c x - 1 - q)! : ℂ) /
        (s - μ) ^ (q + 1))) =O[𝓝[≠] μ] fun _ => (1 : ℂ) := by
    refine IsBigO.sum fun x hx => ?_
    obtain ⟨U, hU, hfx⟩ := hf x hx
    exact (pole_taylor_isBigO_one hU hfx (c x)).const_mul_left _
  refine key.congr_left fun s => ?_
  rw [Finset.sum_apply, hrw]

/-- Unit 5's chart polar coefficients are the instance with weights `faceW · resConst`, orders
`poleOrder` and holomorphic factors `faceHolo`. -/
theorem chartPolarCoeff_eq_finiteFacePolarCoeff {d : ℕ} (p : Fin d → ℕ) (F : (Fin d → ℝ) → ℝ)
    (h k : Fin d → ℕ) (μ : ℝ) (q : ℕ) :
    chartPolarCoeff p F h k μ q = finiteFacePolarCoeff (SmoothEngine.faceIndex p)
      (fun x => ((SmoothEngine.faceW x.1 x.2 : ℝ) : ℂ) * resConst h k x.1 x.2 μ)
      (fun x => poleOrder h k x.1 x.2 μ) (fun x => faceHolo p F h k x.1 x.2 μ) (μ : ℂ) q :=
  rfl

end FiniteFace

end Grammar
