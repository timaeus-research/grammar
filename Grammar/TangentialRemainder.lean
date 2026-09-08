/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.TangentialData

/-!
# The integrated ordered remainder: continuity and uniform convergence (Stage S10)

Unit 279 (Astra #34, unit 2 of tranche A3). The integrated canonical coefficients
`𝒞_{μ,j}(x) = ∫_K C_{μ,j}(x v) dν` and, for fixed `N ≥ 0`, the integrated integral
`𝒵(N; x)` are Lipschitz on sup-norm balls of `C(K, DataSpace)` with constants
`ν(K) · dataLipConst`, resp. `ν(K) ·` (the ballwise constant of unit 274), hence continuous and
Borel measurable (`continuous_tanCoeff`, `continuous_tanIntegral`). The integrated ordered
normalised remainder is the integral of the pointwise one,
`ℛ_N^{μ,j}(x) − 𝒞_{μ,j}(x) = ∫_K (R_N^{μ,j}(x v) − C_{μ,j}(x v)) dν` (`tanRemainder_sub_tanCoeff`),
so on the sup-norm ball of radius `R`, `|ℛ_N^{μ,j}(x) − 𝒞_{μ,j}(x)| ≤ ν(K) · remainderMajorant N`
(`abs_tanRemainder_sub_le`) and `ℛ_N^{μ,j} → 𝒞_{μ,j}` uniformly on the ball
(`tendstoUniformlyOn_tanRemainder`). This is the deterministic `lemma:AsymInt` in ordered-remainder
form, with explicit domination.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

open CoeffFamily

variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K] [MeasurableSpace K]
  [OpensMeasurableSpace K] (ν : Measure K) [IsFiniteMeasure ν]

/-! ### Lipschitz continuity of the integrated functionals -/

theorem abs_tanCoeff_sub_le (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {b : ℝ} (hb : 0 < b) {R : ℝ} {x y : TangentialData K (n + 1)} (hx : ‖x‖ ≤ R)
    (hy : ‖y‖ ≤ R) (μ : ℝ) (j : ℕ) :
    |tanCoeff ν n h k β b y μ j - tanCoeff ν n h k β b x μ j| ≤
      (ν univ).toReal * dataLipConst n h k β b μ j R * ‖y - x‖ := by
  unfold tanCoeff
  rw [← integral_sub (integrable_dataBoxCoeff_tan ν n h k hk β hβ hb y μ j)
    (integrable_dataBoxCoeff_tan ν n h k hk β hβ hb x μ j)]
  have hbound : ∀ v, ‖dataBoxCoeff n h k β b (y v) μ j - dataBoxCoeff n h k β b (x v) μ j‖ ≤
      dataLipConst n h k β b μ j R * ‖y - x‖ := by
    intro v
    rw [Real.norm_eq_abs]
    refine (abs_dataBoxCoeff_sub_le n h k hk β hβ hb ((norm_tan_apply_le x v).trans hx)
      ((norm_tan_apply_le y v).trans hy) μ j).trans ?_
    exact mul_le_mul_of_nonneg_left (norm_tan_apply_sub_le y x v)
      (dataLipConst_nonneg n h k β hβ hb μ j ((norm_nonneg x).trans hx))
  have := norm_integral_le_of_norm_le_const (μ := ν) (Eventually.of_forall hbound)
  rw [Real.norm_eq_abs] at this
  refine this.trans (le_of_eq ?_)
  rw [measureReal_def]; ring

/-- The integrated coefficient is continuous on `C(K, DataSpace)`. -/
theorem continuous_tanCoeff (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {b : ℝ} (hb : 0 < b) (μ : ℝ) (j : ℕ) :
    Continuous fun x : TangentialData K (n + 1) => tanCoeff ν n h k β b x μ j := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  set R := ‖x‖ + 1 with hR
  have hmem : Metric.closedBall (0 : TangentialData K (n + 1)) R ∈ 𝓝 x :=
    Metric.closedBall_mem_nhds_of_mem (by simp [hR])
  have hR0 : 0 ≤ R := by rw [hR]; positivity
  have hC0 : 0 ≤ (ν univ).toReal * dataLipConst n h k β b μ j R :=
    mul_nonneg ENNReal.toReal_nonneg (dataLipConst_nonneg n h k β hβ hb μ j hR0)
  have hlip : LipschitzOnWith (Real.toNNReal ((ν univ).toReal * dataLipConst n h k β b μ j R))
      (fun x : TangentialData K (n + 1) => tanCoeff ν n h k β b x μ j)
      (Metric.closedBall 0 R) := by
    refine LipschitzOnWith.of_dist_le_mul fun y hy z hz => ?_
    have hy' : ‖y‖ ≤ R := by simpa using hy
    have hz' : ‖z‖ ≤ R := by simpa using hz
    rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ hC0]
    exact abs_tanCoeff_sub_le ν n h k hk β hβ hb hz' hy' μ j
  exact hlip.continuousOn.continuousAt hmem

theorem measurable_tanCoeff (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {b : ℝ} (hb : 0 < b) (μ : ℝ) (j : ℕ) :
    Measurable fun x : TangentialData K (n + 1) => tanCoeff ν n h k β b x μ j :=
  (continuous_tanCoeff ν n h k hk β hβ hb μ j).measurable

theorem abs_tanIntegral_sub_le (n : ℕ) (h k : Fin (n + 1) → ℕ) {β N b : ℝ} (hβ : 0 ≤ β)
    (hN : 0 ≤ N) (hb : 0 < b) {R : ℝ} {x y : TangentialData K (n + 1)} (hx : ‖x‖ ≤ R)
    (hy : ‖y‖ ≤ R) :
    |tanIntegral ν n h k β N b y - tanIntegral ν n h k β N b x| ≤
      (ν univ).toReal * (b ^ (∑ i, h i + (n + 1)) *
        (Real.exp (β * Real.sqrt (boxScale k b N) * R) *
          (1 + R * (β * Real.sqrt (boxScale k b N))))) * ‖y - x‖ := by
  unfold tanIntegral
  rw [← integral_sub (integrable_dataBoxIntegral_tan ν n h k hβ hN hb y)
    (integrable_dataBoxIntegral_tan ν n h k hβ hN hb x)]
  have hK0 : 0 ≤ b ^ (∑ i, h i + (n + 1)) * (Real.exp (β * Real.sqrt (boxScale k b N) * R) *
      (1 + R * (β * Real.sqrt (boxScale k b N)))) := by
    have hR0 : 0 ≤ R := (norm_nonneg x).trans hx
    have := Real.sqrt_nonneg (boxScale k b N)
    have := Real.exp_pos (β * Real.sqrt (boxScale k b N) * R)
    positivity
  have hbound : ∀ v, ‖dataBoxIntegral n h k β N b (y v) - dataBoxIntegral n h k β N b (x v)‖ ≤
      b ^ (∑ i, h i + (n + 1)) * (Real.exp (β * Real.sqrt (boxScale k b N) * R) *
        (1 + R * (β * Real.sqrt (boxScale k b N)))) * ‖y - x‖ := by
    intro v
    rw [Real.norm_eq_abs]
    refine (abs_dataBoxIntegral_sub_le n h k hβ hN hb ((norm_tan_apply_le x v).trans hx)
      ((norm_tan_apply_le y v).trans hy)).trans ?_
    exact mul_le_mul_of_nonneg_left (norm_tan_apply_sub_le y x v) hK0
  have := norm_integral_le_of_norm_le_const (μ := ν) (Eventually.of_forall hbound)
  rw [Real.norm_eq_abs] at this
  refine this.trans (le_of_eq ?_)
  rw [measureReal_def]; ring

/-- The integrated integral is continuous on `C(K, DataSpace)` (fixed `N ≥ 0`). -/
theorem continuous_tanIntegral (n : ℕ) (h k : Fin (n + 1) → ℕ) {β N b : ℝ} (hβ : 0 ≤ β)
    (hN : 0 ≤ N) (hb : 0 < b) :
    Continuous fun x : TangentialData K (n + 1) => tanIntegral ν n h k β N b x := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  set R := ‖x‖ + 1 with hR
  have hmem : Metric.closedBall (0 : TangentialData K (n + 1)) R ∈ 𝓝 x :=
    Metric.closedBall_mem_nhds_of_mem (by simp [hR])
  have hR0 : 0 ≤ R := by rw [hR]; positivity
  set C := (ν univ).toReal * (b ^ (∑ i, h i + (n + 1)) *
    (Real.exp (β * Real.sqrt (boxScale k b N) * R) *
      (1 + R * (β * Real.sqrt (boxScale k b N))))) with hC
  have hC0 : 0 ≤ C := by
    have := Real.sqrt_nonneg (boxScale k b N)
    have := Real.exp_pos (β * Real.sqrt (boxScale k b N) * R)
    have := ENNReal.toReal_nonneg (a := ν univ)
    positivity
  have hlip : LipschitzOnWith (Real.toNNReal C)
      (fun x : TangentialData K (n + 1) => tanIntegral ν n h k β N b x)
      (Metric.closedBall 0 R) := by
    refine LipschitzOnWith.of_dist_le_mul fun y hy z hz => ?_
    have hy' : ‖y‖ ≤ R := by simpa using hy
    have hz' : ‖z‖ ≤ R := by simpa using hz
    rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ hC0]
    exact abs_tanIntegral_sub_le ν n h k hβ hN hb hz' hy'
  exact hlip.continuousOn.continuousAt hmem

theorem measurable_tanIntegral (n : ℕ) (h k : Fin (n + 1) → ℕ) {β N b : ℝ} (hβ : 0 ≤ β)
    (hN : 0 ≤ N) (hb : 0 < b) :
    Measurable fun x : TangentialData K (n + 1) => tanIntegral ν n h k β N b x :=
  (continuous_tanIntegral ν n h k hβ hN hb).measurable

/-! ### The integrated ordered remainder -/

/-- The integrated ordered remainder minus the integrated coefficient is the integral of the
pointwise difference (`N ≥ 0`). -/
theorem tanRemainder_sub_tanCoeff (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {b : ℝ} (hb : 0 < b) (x : TangentialData K (n + 1)) (μ : ℝ) (j : ℕ) {N : ℝ}
    (hN : 0 ≤ N) :
    tanRemainder ν n h k β b x μ j N - tanCoeff ν n h k β b x μ j =
      ∫ v, (orderedRemainder n h k β b (x v) μ j N - dataBoxCoeff n h k β b (x v) μ j) ∂ν := by
  have hC := integrable_dataBoxCoeff_tan ν n h k hk β hβ hb x μ j
  have hZ := integrable_dataBoxIntegral_tan ν n h k hβ.le hN hb x
  have hP : Integrable (fun v => predSum n h k β b (x v) μ j N) ν := by
    unfold predSum expTerm
    exact integrable_finset_sum _ fun p _ =>
      (integrable_dataBoxCoeff_tan ν n h k hk β hβ hb x p.1 p.2).mul_const _
  have hR : Integrable (fun v => orderedRemainder n h k β b (x v) μ j N) ν := by
    unfold orderedRemainder
    exact (hZ.sub hP).div_const _
  rw [integral_sub hR hC]
  congr 1
  unfold tanRemainder orderedRemainder tanIntegral tanPredSum tanCoeff
  rw [integral_div, integral_sub hZ hP]
  congr 2
  unfold predSum expTerm
  rw [integral_finset_sum _ fun p _ =>
    (integrable_dataBoxCoeff_tan ν n h k hk β hβ hb x p.1 p.2).mul_const _]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [integral_mul_const]

/-- **The integrated majorant estimate** (`lemma:AsymInt` in ordered-remainder form): on the
sup-norm ball of radius `R`, for `N ≥ e` and `N b^{2|k|} ≥ 1`,
`|ℛ_N^{μ,j}(x) − 𝒞_{μ,j}(x)| ≤ ν(K) · remainderMajorant n h k β b μ j R N`. -/
theorem abs_tanRemainder_sub_le (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {b : ℝ} (hb : 0 < b) {μ : ℝ} (hμ : ∃ m : ℕ, μ = (m : ℝ) / latticeQ k) {j : ℕ}
    (hj : j ≤ n) {R : ℝ} {x : TangentialData K (n + 1)} (hx : ‖x‖ ≤ R) {N : ℝ}
    (hNe : Real.exp 1 ≤ N) (hNb : 1 ≤ boxScale k b N) :
    |tanRemainder ν n h k β b x μ j N - tanCoeff ν n h k β b x μ j| ≤
      (ν univ).toReal * remainderMajorant n h k β b μ j R N := by
  have hN0 : 0 ≤ N := le_trans (Real.exp_pos 1).le hNe
  rw [tanRemainder_sub_tanCoeff ν n h k hk β hβ hb x μ j hN0]
  have hbound : ∀ v, ‖orderedRemainder n h k β b (x v) μ j N - dataBoxCoeff n h k β b (x v) μ j‖ ≤
      remainderMajorant n h k β b μ j R N := by
    intro v
    rw [Real.norm_eq_abs]
    exact abs_orderedRemainder_sub_le n h k hk β hβ hb hμ hj ((norm_tan_apply_le x v).trans hx)
      hNe hNb
  have := norm_integral_le_of_norm_le_const (μ := ν) (Eventually.of_forall hbound)
  rw [Real.norm_eq_abs] at this
  refine this.trans (le_of_eq ?_)
  rw [measureReal_def]; ring

/-- **Integrated ordered remainders converge uniformly on sup-norm balls.** -/
theorem tendstoUniformlyOn_tanRemainder (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (β : ℝ) (hβ : 0 < β) {b : ℝ} (hb : 0 < b) {μ : ℝ} (hμ : ∃ m : ℕ, μ = (m : ℝ) / latticeQ k)
    {j : ℕ} (hj : j ≤ n) (R : ℝ) :
    TendstoUniformlyOn (fun N x => tanRemainder ν n h k β b x μ j N)
      (fun x => tanCoeff ν n h k β b x μ j) atTop (Metric.closedBall 0 R) := by
  set c : ℝ := b ^ (2 * ∑ i, k i) with hc
  have hc0 : 0 < c := by positivity
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hmaj := (tendsto_remainderMajorant n h k β b μ j R).const_mul (ν univ).toReal
  rw [mul_zero] at hmaj
  have hev : ∀ᶠ N in atTop, (ν univ).toReal * remainderMajorant n h k β b μ j R N < ε :=
    hmaj.eventually (gt_mem_nhds hε)
  filter_upwards [hev, eventually_ge_atTop (Real.exp 1), eventually_ge_atTop (1 / c)] with N hNε hNe
    hNc x hx
  have hx' : ‖x‖ ≤ R := by simpa using hx
  have hscale : 1 ≤ boxScale k b N := by
    unfold boxScale; rw [← hc]
    rwa [div_le_iff₀ hc0] at hNc
  rw [Real.dist_eq, abs_sub_comm]
  exact lt_of_le_of_lt (abs_tanRemainder_sub_le ν n h k hk β hβ hb hμ hj hx' hNe hscale) hNε

end Grammar
