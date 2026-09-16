/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.EmpiricalRectContinuity

/-!
# The top cube coefficient is Lipschitz on bounded jets

For a cube `[0,b]^d`, exponents `h k`, a smooth cutoff amplitude `η` vanishing near the deep set
(relative to the closed box) and an index `(μ, c)`, the coefficient of `N^{−μ} (log N)^{c−1}` of the
cube expansion with field `ζ` is Lipschitz in the `C^R` jets of `ζ` on the closed box, uniformly on
sets of fields with bounded jets, where `R = ∑ᵢ depthOf h k (cutoffOf h μ) i` is the canonical
order. This is the bounded-jet estimate behind the continuous extension of the coefficient to the
closed realizable cube jets (consult #151).
-/

open Filter Topology Set
open scoped ContDiff

namespace Grammar

namespace SmoothEngine

variable {d : ℕ} {η : (Fin d → ℝ) → ℝ} {h k : Fin d → ℕ}

/-- **Bounded-jet Lipschitz estimate for the top cube coefficient.** -/
theorem exists_empCoeffRect_top_bound (hη : ContDiff ℝ ∞ η) (hk : ∀ i, 0 < k i) {b : ℝ}
    (hb : 0 < b) {μ : ℝ} (hμ : 0 < μ) {c : ℕ} (hc : 1 ≤ c) (hdeep : DeepVanishing η b c) {B : ℝ}
    (hB : 0 ≤ B) :
    ∃ K, 0 ≤ K ∧ ∀ ζ₁ ζ₂ : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ ζ₁ → ContDiff ℝ ∞ ζ₂ →
      JetBoundOn (∑ i, depthOf h k (cutoffOf h μ) i) (closedBox d b) ζ₂ B → ∀ ε, 0 ≤ ε → ε ≤ 1 →
      JetClose (∑ i, depthOf h k (cutoffOf h μ) i) (closedBox d b) ζ₁ ζ₂ ε →
      |empCoeffRect η ζ₁ h k (fun _ => b) μ (c - 1) -
        empCoeffRect η ζ₂ h k (fun _ => b) μ (c - 1)| ≤ K * ε := by
  obtain ⟨C, hC0, hrep⟩ := exists_jetClose_replaced hη hμ (∑ i, depthOf h k (cutoffOf h μ) i) b hB
  refine ⟨coeffBoundConstant h k (depthOf h k (cutoffOf h μ)) 1 b μ (c - 1) * C,
    mul_nonneg (coeffBoundConstant_nonneg _ _ _ _ _ _ _) hC0,
    fun ζ₁ ζ₂ hζ₁ hζ₂ hbound ε hε0 hε1 hclose => ?_⟩
  rw [empCoeffRect_top_eq_smoothCoeff hη hζ₁ hk hb hμ hc hdeep,
    empCoeffRect_top_eq_smoothCoeff hη hζ₂ hk hb hμ hc hdeep]
  have hF₁ := (contDiff_mul_fluctuation hη hζ₁ hμ).div_const (Real.Gamma μ)
  have hF₂ := (contDiff_mul_fluctuation hη hζ₂ hμ).div_const (Real.Gamma μ)
  have hrb := rectBound_of_jetClose hF₁ hF₂ (depthOf h k (cutoffOf h μ))
    (hrep ζ₁ ζ₂ hζ₁ hζ₂ hbound ε hε0 hε1 hclose)
  calc |smoothCoeff (fun v => η v * fluctuation 1 μ (ζ₁ v) / Real.Gamma μ) h k 1 b μ (c - 1) -
        smoothCoeff (fun v => η v * fluctuation 1 μ (ζ₂ v) / Real.Gamma μ) h k 1 b μ (c - 1)|
      ≤ coeffBoundConstant h k (depthOf h k (cutoffOf h μ)) 1 b μ (c - 1) * (C * ε) :=
        abs_smoothCoeff_sub_le hF₁ hF₂ hk one_pos hb hrb (c - 1)
    _ = coeffBoundConstant h k (depthOf h k (cutoffOf h μ)) 1 b μ (c - 1) * C * ε := by ring

end SmoothEngine

end Grammar
