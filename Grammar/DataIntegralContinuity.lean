/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.DataCutoff

/-!
# Continuity and measurability of the standard integral in the data (Stage S5)

Unit 274 (review v27 should-fix 3). For fixed sample size `N ≥ 0`, the original box integral
`Z(N; ·) = dataBoxIntegral n h k β N b` is Lipschitz on every ball of the data space
(`abs_dataBoxIntegral_sub_le`), hence continuous (`continuous_dataBoxIntegral`) and Borel
measurable (`measurable_dataBoxIntegral`). Ingredients: on the closed unit cube the evaluation
`u ↦ evalF c u` is continuous (Weierstrass M-test with majorant `|c_γ|`, `continuousOn_evalF`) and
linear in `c` (`evalF_sub`), so the unit-box integrand is continuous in `u`, integrable on the
unit box, bounded by `mass cη · e^{β√N mass cξ}`, and Lipschitz in the data with constant
`e^{β√N R}(1 + β√N R)` on the ball of radius `R`; the unit box has volume one. The box integral is
the rescaled unit-box integral (`familyPhaseIntegralBox_eq`, `scale_toXi`). Together with the
measurability of the coefficients (Headline XXXIV) this makes every normalised remainder of A2 a
random variable.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

open CoeffFamily

variable {d : ℕ}

/-- The evaluation of an absolutely summable family is continuous on the closed unit cube. -/
theorem continuousOn_evalF {c : CoeffFamily d} (hc : AbsSummable c) :
    ContinuousOn (evalF c) (closedCube d) := by
  unfold evalF
  refine continuousOn_tsum (fun γ => ?_) hc fun γ u hu => ?_
  · exact (continuous_const.mul (continuous_finsetProd _ fun i _ =>
      (continuous_apply i).pow _)).continuousOn
  · rw [Real.norm_eq_abs]; exact abs_term_le hu γ

theorem evalF_sub {c c' : CoeffFamily d} (hc : AbsSummable c) (hc' : AbsSummable c')
    {u : Fin d → ℝ} (hu : u ∈ closedCube d) : evalF (c - c') u = evalF c u - evalF c' u := by
  unfold evalF
  rw [← (summable_term hc hu).tsum_sub (summable_term hc' hu)]
  refine tsum_congr fun γ => ?_
  simp only [Pi.sub_apply]; ring

/-- The unit-box integrand of the standard integral. -/
noncomputable def boxIntegrand (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N : ℝ)
    (cξ cη : CoeffFamily (n + 1)) (u : Fin (n + 1) → ℝ) : ℝ :=
  evalF cη u * (∏ i, u i ^ h i) *
    Real.exp (-(β * N * ∏ i, u i ^ (2 * k i)) + β * (Real.sqrt N * ∏ i, u i ^ k i) * evalF cξ u)

theorem familyPhaseIntegral_eq_integral_boxIntegrand (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N : ℝ)
    (cξ cη : CoeffFamily (n + 1)) :
    familyPhaseIntegral n h k β N cξ cη = ∫ u in unitBox (n + 1), boxIntegrand n h k β N cξ cη u :=
  rfl

theorem continuousOn_boxIntegrand (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N : ℝ)
    {cξ cη : CoeffFamily (n + 1)} (hξ : AbsSummable cξ) (hη : AbsSummable cη) :
    ContinuousOn (boxIntegrand n h k β N cξ cη) (closedCube (n + 1)) := by
  unfold boxIntegrand
  have hp : ∀ e : Fin (n + 1) → ℕ, Continuous fun u : Fin (n + 1) → ℝ => ∏ i, u i ^ e i :=
    fun e => continuous_finsetProd _ fun i _ => (continuous_apply i).pow _
  refine ((continuousOn_evalF hη).mul (hp h).continuousOn).mul
    (Real.continuous_exp.comp_continuousOn ?_)
  exact ((continuous_const.mul (hp _)).neg.continuousOn).add
    ((continuous_const.mul (continuous_const.mul (hp k))).continuousOn.mul (continuousOn_evalF hξ))

theorem integrableOn_boxIntegrand (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N : ℝ)
    {cξ cη : CoeffFamily (n + 1)} (hξ : AbsSummable cξ) (hη : AbsSummable cη) :
    IntegrableOn (boxIntegrand n h k β N cξ cη) (unitBox (n + 1)) :=
  ((continuousOn_boxIntegrand n h k β N hξ hη).integrableOn_compact
    (isCompact_closedCube _)).mono_set (unitBox_subset_closedCube _)

/-- On the unit box, `|Δ integrand| ≤ e^{β√N R} (mass Δη + R β √N mass Δξ)` for data of mass
`≤ R` (`β ≥ 0`, `N ≥ 0`). -/
theorem abs_boxIntegrand_sub_le (n : ℕ) (h k : Fin (n + 1) → ℕ) {β N : ℝ} (hβ : 0 ≤ β)
    (hN : 0 ≤ N) {cξ cξ' cη cη' : CoeffFamily (n + 1)} (hξ : AbsSummable cξ)
    (hξ' : AbsSummable cξ') (hη : AbsSummable cη) (hη' : AbsSummable cη') {R : ℝ}
    (hRξ : mass cξ ≤ R) (hRξ' : mass cξ' ≤ R) (hRη : mass cη ≤ R) {u : Fin (n + 1) → ℝ}
    (hu : u ∈ unitBox (n + 1)) :
    |boxIntegrand n h k β N cξ' cη' u - boxIntegrand n h k β N cξ cη u| ≤
      Real.exp (β * Real.sqrt N * R) *
        (mass (cη' - cη) + R * (β * Real.sqrt N) * mass (cξ' - cξ)) := by
  have hu' : u ∈ closedCube (n + 1) := unitBox_subset_closedCube _ hu
  have hR0 : 0 ≤ R := (mass_nonneg cξ).trans hRξ
  have hτ := prod_pow_mem_Icc (fun i => 2 * k i) hu
  have hh := prod_pow_mem_Icc h hu
  have hK := prod_pow_mem_Icc k hu
  set s : ℝ := β * (Real.sqrt N * ∏ i, u i ^ k i) with hs
  have hs0 : 0 ≤ s := by have := Real.sqrt_nonneg N; have := hK.1; positivity
  have hs1 : s ≤ β * Real.sqrt N := by
    rw [hs]
    have : Real.sqrt N * ∏ i, u i ^ k i ≤ Real.sqrt N * 1 :=
      mul_le_mul_of_nonneg_left hK.2 (Real.sqrt_nonneg N)
    nlinarith [Real.sqrt_nonneg N]
  set A : ℝ := -(β * N * ∏ i, u i ^ (2 * k i)) with hA
  have hA0 : A ≤ 0 := by
    rw [hA]
    have h0 := hτ.1
    have : 0 ≤ β * N * ∏ i, u i ^ (2 * k i) := by positivity
    linarith
  have heξ : |evalF cξ u| ≤ R := (abs_evalF_le hξ hu').trans hRξ
  have heξ' : |evalF cξ' u| ≤ R := (abs_evalF_le hξ' hu').trans hRξ'
  have heη : |evalF cη u| ≤ R := (abs_evalF_le hη hu').trans hRη
  have hexp_le : ∀ c : CoeffFamily (n + 1), AbsSummable c → mass c ≤ R →
      Real.exp (A + s * evalF c u) ≤ Real.exp (β * Real.sqrt N * R) := by
    intro c hc hcR
    refine Real.exp_le_exp.2 ?_
    have h1 : s * evalF c u ≤ s * R :=
      mul_le_mul_of_nonneg_left ((le_abs_self _).trans ((abs_evalF_le hc hu').trans hcR)) hs0
    nlinarith
  -- the exponential difference
  have hexp_sub : |Real.exp (A + s * evalF cξ' u) - Real.exp (A + s * evalF cξ u)| ≤
      Real.exp (β * Real.sqrt N * R) * (β * Real.sqrt N) * |evalF cξ' u - evalF cξ u| := by
    -- `|e^x − e^y| ≤ e^{max x y} |x − y|` via the mean value theorem
    have key : ∀ x y : ℝ, x ≤ y → |Real.exp y - Real.exp x| ≤ Real.exp y * |y - x| := by
      intro x y hxy
      rw [abs_of_nonneg (sub_nonneg.2 (Real.exp_le_exp.2 hxy)), abs_of_nonneg (sub_nonneg.2 hxy)]
      have := Real.add_one_le_exp (x - y)
      have hey : 0 < Real.exp y := Real.exp_pos y
      have hxy' : Real.exp x = Real.exp y * Real.exp (x - y) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [hxy']
      nlinarith [Real.exp_pos (x - y)]
    have hM : ∀ c : CoeffFamily (n + 1), AbsSummable c → mass c ≤ R →
        A + s * evalF c u ≤ β * Real.sqrt N * R := fun c hc hcR =>
      Real.exp_le_exp.1 (hexp_le c hc hcR)
    rcases le_total (A + s * evalF cξ u) (A + s * evalF cξ' u) with hle | hle
    · refine (key _ _ hle).trans ?_
      have h1 := hexp_le cξ' hξ' hRξ'
      have h2 : |A + s * evalF cξ' u - (A + s * evalF cξ u)| = s * |evalF cξ' u - evalF cξ u| := by
        rw [show A + s * evalF cξ' u - (A + s * evalF cξ u) = s * (evalF cξ' u - evalF cξ u) by
          ring, abs_mul, abs_of_nonneg hs0]
      rw [h2]
      have h3 : s * |evalF cξ' u - evalF cξ u| ≤ β * Real.sqrt N * |evalF cξ' u - evalF cξ u| :=
        mul_le_mul_of_nonneg_right hs1 (abs_nonneg _)
      calc Real.exp (A + s * evalF cξ' u) * (s * |evalF cξ' u - evalF cξ u|)
          ≤ Real.exp (β * Real.sqrt N * R) * (β * Real.sqrt N * |evalF cξ' u - evalF cξ u|) :=
            mul_le_mul h1 h3 (by positivity) (Real.exp_pos _).le
        _ = _ := by ring
    · rw [abs_sub_comm]
      refine (key _ _ hle).trans ?_
      have h1 := hexp_le cξ hξ hRξ
      have h2 : |A + s * evalF cξ u - (A + s * evalF cξ' u)| = s * |evalF cξ' u - evalF cξ u| := by
        rw [show A + s * evalF cξ u - (A + s * evalF cξ' u) = s * (evalF cξ u - evalF cξ' u) by
          ring, abs_mul, abs_of_nonneg hs0, abs_sub_comm]
      rw [h2]
      have h3 : s * |evalF cξ' u - evalF cξ u| ≤ β * Real.sqrt N * |evalF cξ' u - evalF cξ u| :=
        mul_le_mul_of_nonneg_right hs1 (abs_nonneg _)
      calc Real.exp (A + s * evalF cξ u) * (s * |evalF cξ' u - evalF cξ u|)
          ≤ Real.exp (β * Real.sqrt N * R) * (β * Real.sqrt N * |evalF cξ' u - evalF cξ u|) :=
            mul_le_mul h1 h3 (by positivity) (Real.exp_pos _).le
        _ = _ := by ring
  have hdξ : |evalF cξ' u - evalF cξ u| ≤ mass (cξ' - cξ) := by
    rw [← evalF_sub hξ' hξ hu']; exact abs_evalF_le (hξ'.sub hξ) hu'
  have hdη : |evalF cη' u - evalF cη u| ≤ mass (cη' - cη) := by
    rw [← evalF_sub hη' hη hu']; exact abs_evalF_le (hη'.sub hη) hu'
  -- assemble: F' G' − F G = (F' − F) G' + F (G' − G) with `F = evalF cη · u^h`, `G = exp(…)`
  unfold boxIntegrand
  have hmono : |∏ i, u i ^ h i| ≤ 1 := by rw [abs_of_nonneg hh.1]; exact hh.2
  set E := Real.exp (β * Real.sqrt N * R) with hE
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hG' : |Real.exp (A + s * evalF cξ' u)| ≤ E := by
    rw [abs_of_pos (Real.exp_pos _)]; exact hexp_le cξ' hξ' hRξ'
  have hsplit : evalF cη' u * (∏ i, u i ^ h i) * Real.exp (A + s * evalF cξ' u) -
      evalF cη u * (∏ i, u i ^ h i) * Real.exp (A + s * evalF cξ u) =
      (evalF cη' u - evalF cη u) * (∏ i, u i ^ h i) * Real.exp (A + s * evalF cξ' u) +
        evalF cη u * (∏ i, u i ^ h i) *
          (Real.exp (A + s * evalF cξ' u) - Real.exp (A + s * evalF cξ u)) := by ring
  rw [hsplit]
  refine (abs_add_le _ _).trans ?_
  have h1 : |(evalF cη' u - evalF cη u) * (∏ i, u i ^ h i) * Real.exp (A + s * evalF cξ' u)| ≤
      mass (cη' - cη) * E := by
    rw [abs_mul, abs_mul]
    have := mul_le_mul (mul_le_mul hdη hmono (abs_nonneg _) (mass_nonneg _)) hG' (abs_nonneg _)
      (mul_nonneg (mass_nonneg _) zero_le_one)
    simpa using this
  have h2 : |evalF cη u * (∏ i, u i ^ h i) *
      (Real.exp (A + s * evalF cξ' u) - Real.exp (A + s * evalF cξ u))| ≤
      R * 1 * (E * (β * Real.sqrt N) * mass (cξ' - cξ)) := by
    rw [abs_mul, abs_mul]
    refine mul_le_mul (mul_le_mul heη hmono (abs_nonneg _) hR0) (hexp_sub.trans ?_)
      (abs_nonneg _) (by positivity)
    exact mul_le_mul_of_nonneg_left hdξ (by positivity)
  calc _ ≤ mass (cη' - cη) * E + R * 1 * (E * (β * Real.sqrt N) * mass (cξ' - cξ)) :=
        add_le_add h1 h2
    _ = _ := by ring

/-- **Lipschitz continuity of the unit-box family integral in the data**, on data balls. -/
theorem abs_familyPhaseIntegral_coord_sub_le (n : ℕ) (h k : Fin (n + 1) → ℕ) {β N : ℝ}
    (hβ : 0 ≤ β) (hN : 0 ≤ N) {R : ℝ} {x y : DataSpace (n + 1)} (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) :
    |familyPhaseIntegral n h k β N (xiCoord y) (etaCoord y) -
        familyPhaseIntegral n h k β N (xiCoord x) (etaCoord x)| ≤
      Real.exp (β * Real.sqrt N * R) * (1 + R * (β * Real.sqrt N)) * ‖y - x‖ := by
  have hR0 : 0 ≤ R := (norm_nonneg x).trans hx
  rw [familyPhaseIntegral_eq_integral_boxIntegrand, familyPhaseIntegral_eq_integral_boxIntegrand,
    ← integral_sub (integrableOn_boxIntegrand n h k β N (absSummable_xiCoord y)
      (absSummable_etaCoord y)) (integrableOn_boxIntegrand n h k β N (absSummable_xiCoord x)
      (absSummable_etaCoord x))]
  have hvol : volume (unitBox (n + 1)) < ⊤ := by rw [volume_unitBox]; exact ENNReal.one_lt_top
  have hbound : ∀ u ∈ unitBox (n + 1),
      ‖boxIntegrand n h k β N (xiCoord y) (etaCoord y) u -
        boxIntegrand n h k β N (xiCoord x) (etaCoord x) u‖ ≤
      Real.exp (β * Real.sqrt N * R) * (1 + R * (β * Real.sqrt N)) * ‖y - x‖ := by
    intro u hu
    rw [Real.norm_eq_abs]
    refine (abs_boxIntegrand_sub_le n h k hβ hN (absSummable_xiCoord x) (absSummable_xiCoord y)
      (absSummable_etaCoord x) (absSummable_etaCoord y) ((mass_xiCoord_le x).trans hx)
      ((mass_xiCoord_le y).trans hy) ((mass_etaCoord_le x).trans hx) hu).trans ?_
    have h1 : mass (xiCoord y - xiCoord x) ≤ ‖y - x‖ := by
      have := mass_xiCoord_sub_le y x; simpa [Pi.sub_def] using this
    have h2 : mass (etaCoord y - etaCoord x) ≤ ‖y - x‖ := by
      have := mass_etaCoord_sub_le y x; simpa [Pi.sub_def] using this
    have hE0 : 0 ≤ Real.exp (β * Real.sqrt N * R) := (Real.exp_pos _).le
    have hc : 0 ≤ R * (β * Real.sqrt N) := by have := Real.sqrt_nonneg N; positivity
    calc Real.exp (β * Real.sqrt N * R) *
          (mass (etaCoord y - etaCoord x) + R * (β * Real.sqrt N) * mass (xiCoord y - xiCoord x))
        ≤ Real.exp (β * Real.sqrt N * R) * (‖y - x‖ + R * (β * Real.sqrt N) * ‖y - x‖) :=
          mul_le_mul_of_nonneg_left (add_le_add h2 (mul_le_mul_of_nonneg_left h1 hc)) hE0
      _ = _ := by ring
  have := norm_setIntegral_le_of_norm_le_const hvol hbound
  rw [Real.norm_eq_abs] at this
  simpa [MeasureTheory.measureReal_def, volume_unitBox] using this

/-- The box integral is the rescaled unit-box integral of the raw coordinates. -/
theorem dataBoxIntegral_eq (n : ℕ) (h k : Fin (n + 1) → ℕ) (β : ℝ) {N b : ℝ} (hN : 0 ≤ N)
    (hb : 0 < b) (x : DataSpace (n + 1)) :
    dataBoxIntegral n h k β N b x = b ^ (∑ i, h i + (n + 1)) *
      familyPhaseIntegral n h k β (boxScale k b N) (xiCoord x) (etaCoord x) := by
  unfold dataBoxIntegral
  rw [familyPhaseIntegralBox_eq n h k β hN hb, scale_toXi hb.ne', scale_toEta hb.ne']
  rfl

/-- **Lipschitz continuity of the standard integral in the data**, on data balls (fixed
`N ≥ 0`). -/
theorem abs_dataBoxIntegral_sub_le (n : ℕ) (h k : Fin (n + 1) → ℕ) {β N b : ℝ} (hβ : 0 ≤ β)
    (hN : 0 ≤ N) (hb : 0 < b) {R : ℝ} {x y : DataSpace (n + 1)} (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) :
    |dataBoxIntegral n h k β N b y - dataBoxIntegral n h k β N b x| ≤
      b ^ (∑ i, h i + (n + 1)) * (Real.exp (β * Real.sqrt (boxScale k b N) * R) *
        (1 + R * (β * Real.sqrt (boxScale k b N)))) * ‖y - x‖ := by
  rw [dataBoxIntegral_eq n h k β hN hb, dataBoxIntegral_eq n h k β hN hb, ← mul_sub, abs_mul,
    abs_of_nonneg (pow_nonneg hb.le _), mul_assoc]
  have hN' : 0 ≤ boxScale k b N := by unfold boxScale; positivity
  exact mul_le_mul_of_nonneg_left (abs_familyPhaseIntegral_coord_sub_le n h k hβ hN' hx hy)
    (pow_nonneg hb.le _)

/-- **The standard integral is continuous in the data** (fixed `N ≥ 0`). -/
theorem continuous_dataBoxIntegral (n : ℕ) (h k : Fin (n + 1) → ℕ) {β N b : ℝ} (hβ : 0 ≤ β)
    (hN : 0 ≤ N) (hb : 0 < b) :
    Continuous fun x : DataSpace (n + 1) => dataBoxIntegral n h k β N b x := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  set R := ‖x‖ + 1 with hR
  have hmem : Metric.closedBall (0 : DataSpace (n + 1)) R ∈ 𝓝 x :=
    Metric.closedBall_mem_nhds_of_mem (by simp [hR])
  set C := b ^ (∑ i, h i + (n + 1)) * (Real.exp (β * Real.sqrt (boxScale k b N) * R) *
    (1 + R * (β * Real.sqrt (boxScale k b N)))) with hC
  have hC0 : 0 ≤ C := by
    have := Real.sqrt_nonneg (boxScale k b N)
    have := Real.exp_pos (β * Real.sqrt (boxScale k b N) * R)
    have : 0 ≤ R := by rw [hR]; positivity
    positivity
  have hlip : LipschitzOnWith (Real.toNNReal C)
      (fun x : DataSpace (n + 1) => dataBoxIntegral n h k β N b x) (Metric.closedBall 0 R) := by
    refine LipschitzOnWith.of_dist_le_mul fun y hy z hz => ?_
    have hy' : ‖y‖ ≤ R := by simpa using hy
    have hz' : ‖z‖ ≤ R := by simpa using hz
    rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ hC0]
    exact abs_dataBoxIntegral_sub_le n h k hβ hN hb hz' hy'
  exact hlip.continuousOn.continuousAt hmem

theorem measurable_dataBoxIntegral (n : ℕ) (h k : Fin (n + 1) → ℕ) {β N b : ℝ} (hβ : 0 ≤ β)
    (hN : 0 ≤ N) (hb : 0 < b) :
    Measurable fun x : DataSpace (n + 1) => dataBoxIntegral n h k β N b x :=
  (continuous_dataBoxIntegral n h k hβ hN hb).measurable

end Grammar
