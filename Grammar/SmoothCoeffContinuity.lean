/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothCoeffBound
import Grammar.CoordinateFrechetBridge
import Grammar.SmoothCoefficientLinearity

/-!
# Continuity of the canonical population coefficients in the amplitude (§20, consult #144 A)

The canonical coefficients `smoothCoeff F h k β b μ q` of `∫_{(0,b]^d} F v^h e^{−βN v^{2k}} dv` are
linear in the amplitude (`smoothCoeff_add`, `smoothCoeff_sub`, `smoothCoeff_const_mul`, by
uniqueness of cutoff expansions), so the quantitative bound `abs_smoothCoeff_le` at the canonical
depth `p = 2k·cutoffOf h μ − h` controls DIFFERENCES: ★ `abs_smoothCoeff_sub_le`. Consequently
the coefficient at a fixed index `(μ, q)` is continuous for convergence of the amplitude jets of
order `≤ p` on the closed box, uniformly (★★ `tendsto_smoothCoeff`), and a fortiori for
convergence in the `C^{|p|}` topology on the closed box measured by `iteratedFDeriv` norms
(`rectBound_of_iteratedFDeriv`, ★★ `tendsto_smoothCoeff_of_iteratedFDeriv`): a finite-order
statement at fixed `(μ, q)`, with the order `|p| = Σ (2kᵢ·cutoffOf h μ − hᵢ)` explicit. No single
order serves all coefficients. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology Finset
open scoped ContDiff

namespace Grammar

namespace SmoothEngine

variable {d : ℕ} {F G : (Fin d → ℝ) → ℝ} {h k : Fin d → ℕ} {β b : ℝ}

/-! ### Linearity in the amplitude -/

theorem integrableOn_smoothIntegrand (hF : ContDiff ℝ ∞ F) (h k : Fin d → ℕ) (β b N : ℝ) :
    IntegrableOn (fun v => F v * mono h v * exp (-(N * β) * mono (fun i => 2 * k i) v))
      (box (Fin d) b) := by
  have hc : Continuous fun v : Fin d → ℝ =>
      F v * mono h v * exp (-(N * β) * mono (fun i => 2 * k i) v) :=
    (hF.continuous.mul (continuous_mono h)).mul
      (continuous_exp.comp (continuous_const.mul (continuous_mono _)))
  exact (hc.continuousOn.integrableOn_compact (isCompact_closedBox b)).mono_set
    (box_subset_closedBox b)

theorem smoothIntegral_add (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (h k : Fin d → ℕ)
    (β b N : ℝ) :
    smoothIntegral (fun v => F v + G v) h k β b N =
      smoothIntegral F h k β b N + smoothIntegral G h k β b N := by
  unfold smoothIntegral
  rw [← integral_add (integrableOn_smoothIntegrand hF h k β b N)
    (integrableOn_smoothIntegrand hG h k β b N)]
  refine setIntegral_congr_fun (measurableSet_box (ι := Fin d) b) fun v _ => ?_
  ring

theorem smoothIntegral_sub (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (h k : Fin d → ℕ)
    (β b N : ℝ) :
    smoothIntegral (fun v => F v - G v) h k β b N =
      smoothIntegral F h k β b N - smoothIntegral G h k β b N := by
  unfold smoothIntegral
  rw [← integral_sub (integrableOn_smoothIntegrand hF h k β b N)
    (integrableOn_smoothIntegrand hG h k β b N)]
  refine setIntegral_congr_fun (measurableSet_box (ι := Fin d) b) fun v _ => ?_
  ring

theorem smoothIntegral_const_mul (r : ℝ) (F : (Fin d → ℝ) → ℝ) (h k : Fin d → ℕ) (β b N : ℝ) :
    smoothIntegral (fun v => r * F v) h k β b N = r * smoothIntegral F h k β b N := by
  unfold smoothIntegral
  rw [← integral_const_mul]
  refine setIntegral_congr_fun (measurableSet_box (ι := Fin d) b) fun v _ => ?_
  ring

/-- Two coefficient systems agreeing on the lattice below the degree, both vanishing off it,
agree everywhere; used to pass from expansion uniqueness to a full identity. -/
theorem smoothCoeff_eq_of_cutoffExpansion (hF : ContDiff ℝ ∞ F) (hk : ∀ i, 0 < k i) (hβ : 0 < β)
    (hb : 0 < b) (c : ℝ → ℕ → ℝ)
    (hc : CutoffExpansion (Qamb k) (d - 1) (smoothIntegral F h k β b) c)
    (hc0 : ∀ μ, (∀ m : ℕ, μ ≠ (m : ℝ) / Qamb k) → ∀ q, c μ q = 0)
    (hcD : ∀ μ q, d - 1 < q → c μ q = 0) (μ : ℝ) (q : ℕ) : smoothCoeff F h k β b μ q = c μ q := by
  have hQ := Qamb_pos k hk
  by_cases hμ : ∃ m : ℕ, μ = (m : ℝ) / Qamb k
  · by_cases hq : q ≤ d - 1
    · exact CutoffExpansion.coeff_unique hQ (smooth_cutoffExpansion hF hk hβ hb) hc hμ hq
    · have hq' := not_le.1 hq
      rw [smoothCoeff_eq_zero_of_degree_gt hq', hcD μ q hq']
  · have hμ' : ∀ m : ℕ, μ ≠ (m : ℝ) / Qamb k := fun m hm => hμ ⟨m, hm⟩
    rw [smoothCoeff_eq_zero_of_not_lattice hk hβ hb hμ' q, hc0 μ hμ' q]

/-- ★ **Additivity of the canonical coefficients in the amplitude.** -/
theorem smoothCoeff_add (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (hk : ∀ i, 0 < k i)
    (hβ : 0 < β) (hb : 0 < b) (μ : ℝ) (q : ℕ) :
    smoothCoeff (fun v => F v + G v) h k β b μ q =
      smoothCoeff F h k β b μ q + smoothCoeff G h k β b μ q := by
  refine smoothCoeff_eq_of_cutoffExpansion (hF.add hG) hk hβ hb
    (fun ν j => smoothCoeff F h k β b ν j + smoothCoeff G h k β b ν j) ?_ ?_ ?_ μ q
  · have hexp := (smooth_cutoffExpansion hF hk hβ hb (h := h)).add
      (smooth_cutoffExpansion hG hk hβ hb (h := h))
    have hfun : (fun N => smoothIntegral F h k β b N + smoothIntegral G h k β b N) =
        smoothIntegral (fun v => F v + G v) h k β b :=
      funext fun N => (smoothIntegral_add hF hG h k β b N).symm
    rwa [hfun] at hexp
  · intro ν hν j
    rw [smoothCoeff_eq_zero_of_not_lattice hk hβ hb hν j,
      smoothCoeff_eq_zero_of_not_lattice hk hβ hb hν j, add_zero]
  · intro ν j hj
    rw [smoothCoeff_eq_zero_of_degree_gt hj, smoothCoeff_eq_zero_of_degree_gt hj, add_zero]

/-- ★ **The canonical coefficients of a difference.** -/
theorem smoothCoeff_sub (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (hk : ∀ i, 0 < k i)
    (hβ : 0 < β) (hb : 0 < b) (μ : ℝ) (q : ℕ) :
    smoothCoeff (fun v => F v - G v) h k β b μ q =
      smoothCoeff F h k β b μ q - smoothCoeff G h k β b μ q := by
  refine smoothCoeff_eq_of_cutoffExpansion (hF.sub hG) hk hβ hb
    (fun ν j => smoothCoeff F h k β b ν j - smoothCoeff G h k β b ν j) ?_ ?_ ?_ μ q
  · have hexp := (smooth_cutoffExpansion hF hk hβ hb (h := h)).sub
      (smooth_cutoffExpansion hG hk hβ hb (h := h))
    have hfun : (fun N => smoothIntegral F h k β b N - smoothIntegral G h k β b N) =
        smoothIntegral (fun v => F v - G v) h k β b :=
      funext fun N => (smoothIntegral_sub hF hG h k β b N).symm
    rwa [hfun] at hexp
  · intro ν hν j
    rw [smoothCoeff_eq_zero_of_not_lattice hk hβ hb hν j,
      smoothCoeff_eq_zero_of_not_lattice hk hβ hb hν j, sub_zero]
  · intro ν j hj
    rw [smoothCoeff_eq_zero_of_degree_gt hj, smoothCoeff_eq_zero_of_degree_gt hj, sub_zero]

/-- ★ **Homogeneity of the canonical coefficients in the amplitude.** -/
theorem smoothCoeff_const_mul (hF : ContDiff ℝ ∞ F) (hk : ∀ i, 0 < k i) (hβ : 0 < β) (hb : 0 < b)
    (r μ : ℝ) (q : ℕ) :
    smoothCoeff (fun v => r * F v) h k β b μ q = r * smoothCoeff F h k β b μ q := by
  refine smoothCoeff_eq_of_cutoffExpansion (contDiff_const.mul hF) hk hβ hb
    (fun ν j => r * smoothCoeff F h k β b ν j) ?_ ?_ ?_ μ q
  · have hexp := CutoffExpansion.const_mul r (smooth_cutoffExpansion hF hk hβ hb (h := h))
    have hfun : (fun N => r * smoothIntegral F h k β b N) =
        smoothIntegral (fun v => r * F v) h k β b :=
      funext fun N => (smoothIntegral_const_mul r F h k β b N).symm
    rwa [hfun] at hexp
  · intro ν hν j
    rw [smoothCoeff_eq_zero_of_not_lattice hk hβ hb hν j, mul_zero]
  · intro ν j hj
    rw [smoothCoeff_eq_zero_of_degree_gt hj, mul_zero]

/-! ### The bound on differences and continuity -/

/-- ★ **Differences of canonical coefficients are controlled by the canonical-depth rectangular
bound of the difference of the amplitudes.** -/
theorem abs_smoothCoeff_sub_le (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (hk : ∀ i, 0 < k i)
    (hβ : 0 < β) (hb : 0 < b) {μ : ℝ} {M : ℝ}
    (hM : RectBound (fun v => F v - G v) (depthOf h k (cutoffOf h μ)) b M) (q : ℕ) :
    |smoothCoeff F h k β b μ q - smoothCoeff G h k β b μ q| ≤
      coeffBoundConstant h k (depthOf h k (cutoffOf h μ)) β b μ q * M := by
  rw [← smoothCoeff_sub hF hG hk hβ hb μ q]
  exact abs_smoothCoeff_le (hF.sub hG) hk hb hM q

/-- ★★ **Continuity of a canonical coefficient in the amplitude**: if the jets of order
`≤ p = 2k·cutoffOf h μ − h` of `Fₙ − G` are bounded on `[0,b]^d` by `Mₙ → 0`, then
`smoothCoeff Fₙ … μ q → smoothCoeff G … μ q`. -/
theorem tendsto_smoothCoeff {F : ℕ → (Fin d → ℝ) → ℝ} (hF : ∀ n, ContDiff ℝ ∞ (F n))
    (hG : ContDiff ℝ ∞ G) (hk : ∀ i, 0 < k i) (hβ : 0 < β) (hb : 0 < b) {μ : ℝ} {M : ℕ → ℝ}
    (hM : ∀ n, RectBound (fun v => F n v - G v) (depthOf h k (cutoffOf h μ)) b (M n))
    (hM0 : Tendsto M atTop (𝓝 0)) (q : ℕ) :
    Tendsto (fun n => smoothCoeff (F n) h k β b μ q) atTop (𝓝 (smoothCoeff G h k β b μ q)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero
    (g := fun n => coeffBoundConstant h k (depthOf h k (cutoffOf h μ)) β b μ q * M n)
    (fun n => norm_nonneg _) (fun n => ?_) ?_
  · rw [Real.norm_eq_abs]
    exact abs_smoothCoeff_sub_le (hF n) hG hk hβ hb (hM n) q
  · simpa using hM0.const_mul (coeffBoundConstant h k (depthOf h k (cutoffOf h μ)) β b μ q)

/-! ### From `iteratedFDeriv` bounds to rectangular bounds -/

/-- A uniform bound on the `iteratedFDeriv` norms of orders `≤ Σ p` on the closed box gives the
rectangular jet bound at depth `p`. -/
theorem rectBound_of_iteratedFDeriv (hF : ContDiff ℝ ∞ F) (p : Fin d → ℕ) {b M : ℝ}
    (hM : ∀ r ≤ ∑ i, p i, ∀ v ∈ closedBox d b, ‖iteratedFDeriv ℝ r F v‖ ≤ M) :
    RectBound F p b M := by
  intro m hm v hv
  refine (abs_pdMulti_le_norm_iteratedFDeriv_of_mem isOpen_univ hF.contDiffOn m _
    (mem_univ v)).trans ?_
  rw [wordLen_finRange]
  exact hM _ (Finset.sum_le_sum fun i _ => hm i) v (mem_closedBox.2 hv)

/-- ★★ **Continuity of a canonical coefficient for `C^{|p|}` convergence on the closed box**,
`|p| = Σ (2kᵢ·cutoffOf h μ − hᵢ)`. -/
theorem tendsto_smoothCoeff_of_iteratedFDeriv {F : ℕ → (Fin d → ℝ) → ℝ}
    (hF : ∀ n, ContDiff ℝ ∞ (F n)) (hG : ContDiff ℝ ∞ G) (hk : ∀ i, 0 < k i) (hβ : 0 < β)
    (hb : 0 < b) {μ : ℝ} {M : ℕ → ℝ}
    (hM : ∀ n, ∀ r ≤ ∑ i, depthOf h k (cutoffOf h μ) i, ∀ v ∈ closedBox d b,
      ‖iteratedFDeriv ℝ r (fun v => F n v - G v) v‖ ≤ M n)
    (hM0 : Tendsto M atTop (𝓝 0)) (q : ℕ) :
    Tendsto (fun n => smoothCoeff (F n) h k β b μ q) atTop (𝓝 (smoothCoeff G h k β b μ q)) :=
  tendsto_smoothCoeff hF hG hk hβ hb
    (fun n => rectBound_of_iteratedFDeriv ((hF n).sub hG) _ (hM n)) hM0 q

end SmoothEngine

end Grammar
