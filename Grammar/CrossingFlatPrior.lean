/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.NaiveBayesDensity

/-!
# The crossing `x²y²` with the flat prior: the one-dimensional state density

For the flat prior on `[−1, 1]²` the law of the product `t = w₁w₂` has density `2 log(1/|t|)` on
`0 < |t| < 1` (the product-of-uniforms density of `Grammar.NaiveBayesDensity` at the unit square),
so every integral of a function of the product — the partition function of the deep linear
network of depth two with zero target, `K = t²/2`, with or without the regression field
`√N ξ t` — is a one-dimensional integral against this state density (the pushforward of the prior; the paper's polar distribution is its Mellin data)
(★★ `lintegral_crossing_flat`, `lintegral_crossing_flat_field`; examples_slop §2).
Zero `sorry`/`axiom`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Grammar

/-- The product density of the unit square is `2 log(1/|t|)` on `0 < |t| < 1` and `0` outside. -/
theorem prodDensity_unit (t : ℝ) :
    prodDensity 1 1 1 1 t =
      if 0 < |t| ∧ |t| < 1 then ENNReal.ofReal (2 * Real.log (1 / |t|)) else 0 := by
  have key : ∀ s : ℝ, 0 < s →
      ENNReal.ofReal (max (Real.log (1 * 1 / s)) 0) +
        ENNReal.ofReal (max (Real.log (1 * 1 / s)) 0) =
        if 0 < s ∧ s < 1 then ENNReal.ofReal (2 * Real.log (1 / s)) else 0 := by
    intro s hs
    rw [one_mul]
    rcases lt_or_ge s 1 with h | h
    · have hl : 0 ≤ Real.log (1 / s) := Real.log_nonneg ((one_le_div hs).mpr h.le)
      rw [if_pos ⟨hs, h⟩, max_eq_left hl, ← ENNReal.ofReal_add hl hl]
      congr 1; ring
    · have hl : Real.log (1 / s) ≤ 0 :=
        Real.log_nonpos (by positivity) ((div_le_one hs).mpr h)
      rw [if_neg (fun hh => absurd hh.2 (not_lt.mpr h)), max_eq_right hl, ENNReal.ofReal_zero,
        add_zero]
  unfold prodDensity
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · rw [if_neg (not_lt.mpr ht.le), if_pos ht, abs_of_neg ht, key (-t) (neg_pos.mpr ht)]
  · simp
  · rw [if_pos ht, abs_of_pos ht, key t ht]

/-- ★★ The flat prior on the square pushed forward along the product: for every measurable
`Ψ ≥ 0`, `∫_{[−1,1]²} Ψ(w₁w₂) dw = ∫_{−1}^{1} Ψ(t) · 2 log(1/|t|) dt`. -/
theorem lintegral_crossing_flat {Ψ : ℝ → ℝ≥0∞} (hΨ : Measurable Ψ) :
    ∫⁻ w in Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1, Ψ (w.1 * w.2) =
      ∫⁻ t in Ioo (-1 : ℝ) 1, Ψ t * ENNReal.ofReal (2 * Real.log (1 / |t|)) := by
  rw [lintegral_rect_prod (α := 1) (β := 1) (γ := 1) (δ := 1) one_pos one_pos one_pos one_pos hΨ]
  have e : ∀ t : ℝ, Ψ t * prodDensity 1 1 1 1 t =
      (Ioo (-1 : ℝ) 1).indicator (fun t => Ψ t * ENNReal.ofReal (2 * Real.log (1 / |t|))) t := by
    intro t
    rw [prodDensity_unit, indicator_apply]
    by_cases h : 0 < |t| ∧ |t| < 1
    · have hmem : t ∈ Ioo (-1 : ℝ) 1 := by rw [mem_Ioo, ← abs_lt]; exact h.2
      rw [if_pos h, if_pos hmem]
    · rw [if_neg h, mul_zero]
      by_cases ht : t = 0
      · subst ht
        simp
      · have hnot : t ∉ Ioo (-1 : ℝ) 1 := by
          intro hmem
          exact h ⟨abs_pos.mpr ht, abs_lt.mpr hmem⟩
        rw [if_neg hnot]
  simp_rw [e]
  rw [lintegral_indicator measurableSet_Ioo]

/-- The depth-two deep linear network with zero target, flat prior on `[−1, 1]²` and frozen
regression field `ξ`: the partition function with an insertion `f(w₁w₂)` is the one-dimensional
integral against the state density `2 log(1/|t|)`. -/
theorem lintegral_crossing_flat_field (N ξ : ℝ) {f : ℝ → ℝ} (hf : Measurable f) :
    ∫⁻ w in Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1,
        ENNReal.ofReal (f (w.1 * w.2) *
          Real.exp (-N * (w.1 * w.2) ^ 2 / 2 + Real.sqrt N * ξ * (w.1 * w.2))) =
      ∫⁻ t in Ioo (-1 : ℝ) 1,
        ENNReal.ofReal (f t * Real.exp (-N * t ^ 2 / 2 + Real.sqrt N * ξ * t)) *
          ENNReal.ofReal (2 * Real.log (1 / |t|)) :=
  lintegral_crossing_flat (Ψ := fun t => ENNReal.ofReal
    (f t * Real.exp (-N * t ^ 2 / 2 + Real.sqrt N * ξ * t))) (by fun_prop)

end Grammar
