/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.BlowUpLaplaceExpansion
import Grammar.GammaOneLogMoments

/-!
# The frozen quartic amplitude: the linear term of `J_∞(ε) = ∫₀^∞ 2e^{−u⁴/2}/√(u² + ε) du`

Beyond DCXIV's two-term expansion `J_a(ε) = log(4/ε) + R_a + O(ε log(1/ε))`, the frozen blow-up
amplitude `a_∞(u) = e^{−u⁴/2}` has a genuine linear term and no `ε log(1/ε)` term:

  ★★★ `quarticJ_linear_remainder :
    |J_∞(ε) − (log(4/ε) + R_∞ + ½√(π/2)·ε)| ≤ 2ε²(log(1/ε) + 1)`  for `0 < ε ≤ 1`,

with `R_∞ = (log 2 − γ)/2` (DCXIV).  The mechanism: the kernel gap is
`2/√(u²+ε) − 2/u = −ε/u³ + r(u,ε)` with `0 ≤ r ≤ (3/4)ε²/u⁵` (`kernel_second_order`, from
`(1+x)^{−1/2} = 1 − x/2 + O(x²)`); the inner remainder `∫₀¹ (a−1) r` is split at `u = √ε`
(`≤ ε²/2` below, `≤ (3/16)ε² log(1/ε)` above, since `1 − a ≤ u⁴/2`); the outer remainder is
`≤ (3/16)ε²`; the elementary integral is `log(4/ε) + ε/2 + O(ε²)`; and the linear coefficient
`−∫₀¹(a−1)/u³ − ∫₁^∞ a/u³ + ½ = ∫₀^∞ (1−a)/u³ = ∫₀^∞ u e^{−u⁴/2} du = ½√(π/2)` by parts
(`quarticLinear_eq`).  Examples_slop §4; Astra round 29 target (vi), first half (the moving
amplitude's cancellation and the `N^{−3/2} log N` coefficient `√(2π)/32` are the second half).
Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

/-! ### The kernel gap to second order -/

/-- `0 ≤ 2/√(u²+ε) − 2/u + ε/u³ ≤ (3/4) ε²/u⁵`. -/
theorem kernel_second_order {ε u : ℝ} (hε : 0 < ε) (hu : 0 < u) :
    0 ≤ 2 / Real.sqrt (u ^ 2 + ε) - 2 / u + ε / u ^ 3 ∧
      2 / Real.sqrt (u ^ 2 + ε) - 2 / u + ε / u ^ 3 ≤ 3 / 4 * ε ^ 2 / u ^ 5 := by
  have hpos : 0 < u ^ 2 + ε := by positivity
  set s := Real.sqrt (u ^ 2 + ε) with hs
  have hs2 : s ^ 2 = u ^ 2 + ε := Real.sq_sqrt hpos.le
  have hsu : u < s := Real.lt_sqrt hu.le |>.2 (by linarith)
  have hs0 : 0 < s := by linarith
  have hε' : ε = s ^ 2 - u ^ 2 := by linarith
  have e : 2 / s - 2 / u + ε / u ^ 3 = (s - u) ^ 2 * (s + 2 * u) / (s * u ^ 3) := by
    rw [hε']
    field_simp
    ring
  rw [e]
  constructor
  · positivity
  · rw [div_le_div_iff₀ (by positivity) (by positivity), hε']
    have h1 : 0 ≤ s - u := by linarith
    have h2 : 0 ≤ (s - u) ^ 2 := sq_nonneg _
    have key : (s + 2 * u) * u ^ 2 ≤ 3 / 4 * (s + u) ^ 2 * s := by
      nlinarith [mul_nonneg h1
        (by positivity : (0 : ℝ) ≤ 3 / 4 * s ^ 2 + 9 / 4 * s * u + 2 * u ^ 2)]
    have : (s - u) ^ 2 * (s + 2 * u) * u ^ 5 ≤
        3 / 4 * ((s - u) ^ 2 * (s + u) ^ 2) * (s * u ^ 3) := by
      have := mul_le_mul_of_nonneg_left key (mul_nonneg h2 (by positivity : (0 : ℝ) ≤ u ^ 3))
      nlinarith [this]
    calc (s - u) ^ 2 * (s + 2 * u) * u ^ 5
        ≤ 3 / 4 * ((s - u) ^ 2 * (s + u) ^ 2) * (s * u ^ 3) := this
      _ = 3 / 4 * (s ^ 2 - u ^ 2) ^ 2 * (s * u ^ 3) := by ring

/-! ### The quartic amplitude near `0` -/

theorem one_sub_blowAmpInf_nonneg (u : ℝ) : 0 ≤ 1 - blowAmpInf u := by
  unfold blowAmpInf
  linarith [Real.exp_le_one_iff.2 (by nlinarith [pow_nonneg (sq_nonneg u) 2] : -u ^ 4 / 2 ≤ 0)]

theorem one_sub_blowAmpInf_le (u : ℝ) : 1 - blowAmpInf u ≤ u ^ 4 / 2 := by
  unfold blowAmpInf
  linarith [Real.add_one_le_exp (-u ^ 4 / 2)]

/-! ### The inner remainder `∫₀¹ (a − 1)(2/√(u²+ε) − 2/u + ε/u³)` -/

/-- The remainder integrand. -/
noncomputable def quarticRem (ε u : ℝ) : ℝ :=
  (blowAmpInf u - 1) * (2 / Real.sqrt (u ^ 2 + ε) - 2 / u + ε / u ^ 3)

theorem measurable_quarticRem (ε : ℝ) : Measurable (quarticRem ε) := by
  unfold quarticRem blowAmpInf
  fun_prop

theorem abs_quarticRem_le_low {ε u : ℝ} (hε : 0 < ε) (hu : 0 < u) :
    |quarticRem ε u| ≤ u ^ 3 + ε * u / 2 := by
  unfold quarticRem
  have h1 := one_sub_blowAmpInf_nonneg u
  have h2 := one_sub_blowAmpInf_le u
  obtain ⟨g1, g2⟩ := gap_bounds hε hu
  have hgap : |2 / Real.sqrt (u ^ 2 + ε) - 2 / u + ε / u ^ 3| ≤ 2 / u + ε / u ^ 3 := by
    rw [abs_le]
    constructor
    · have : 0 ≤ 2 / Real.sqrt (u ^ 2 + ε) := by positivity
      have : 0 ≤ ε / u ^ 3 := by positivity
      linarith
    · have : 0 ≤ 2 / u := by positivity
      linarith
  rw [abs_mul, abs_of_nonpos (by linarith)]
  calc -(blowAmpInf u - 1) * |2 / Real.sqrt (u ^ 2 + ε) - 2 / u + ε / u ^ 3|
      ≤ u ^ 4 / 2 * (2 / u + ε / u ^ 3) :=
        mul_le_mul (by linarith) hgap (abs_nonneg _) (by positivity)
    _ = u ^ 3 + ε * u / 2 := by field_simp

theorem abs_quarticRem_le_high {ε u : ℝ} (hε : 0 < ε) (hu : 0 < u) :
    |quarticRem ε u| ≤ 3 / 8 * ε ^ 2 / u := by
  unfold quarticRem
  have h1 := one_sub_blowAmpInf_nonneg u
  have h2 := one_sub_blowAmpInf_le u
  obtain ⟨k1, k2⟩ := kernel_second_order hε hu
  rw [abs_mul, abs_of_nonpos (by linarith), abs_of_nonneg k1]
  calc -(blowAmpInf u - 1) * (2 / Real.sqrt (u ^ 2 + ε) - 2 / u + ε / u ^ 3)
      ≤ u ^ 4 / 2 * (3 / 4 * ε ^ 2 / u ^ 5) := mul_le_mul (by linarith) k2 k1 (by positivity)
    _ = 3 / 8 * ε ^ 2 / u := by field_simp; ring

theorem integrableOn_quarticRem {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    IntegrableOn (quarticRem ε) (Ioc 0 1) := by
  refine Measure.integrableOn_of_bounded (M := 2)
    (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
    (measurable_quarticRem ε).aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioc]
  refine Eventually.of_forall fun u hu => ?_
  rw [Real.norm_eq_abs]
  have hu0 : 0 < u := hu.1
  have hu1 : u ≤ 1 := hu.2
  refine (abs_quarticRem_le_low hε hu0).trans ?_
  nlinarith [pow_le_one₀ hu0.le hu1 (n := 3), mul_le_mul hε1 hu1 hu0.le zero_le_one]

/-- `|∫₀¹ quarticRem| ≤ ε²/2 + (3/16)ε² log(1/ε)`. -/
theorem abs_integral_quarticRem_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    |∫ u in Ioc (0 : ℝ) 1, quarticRem ε u| ≤ ε ^ 2 / 2 + 3 / 16 * ε ^ 2 * Real.log (1 / ε) := by
  have hsε : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have hsε1 : Real.sqrt ε ≤ 1 := by
    rw [Real.sqrt_le_one]
    exact hε1
  have hint := integrableOn_quarticRem hε hε1
  have hsplit : Ioc (0 : ℝ) 1 = Ioc 0 (Real.sqrt ε) ∪ Ioc (Real.sqrt ε) 1 :=
    (Ioc_union_Ioc_eq_Ioc hsε.le hsε1).symm
  have hlow : IntegrableOn (quarticRem ε) (Ioc 0 (Real.sqrt ε)) :=
    hint.mono_set (Ioc_subset_Ioc_right hsε1)
  have hhigh : IntegrableOn (quarticRem ε) (Ioc (Real.sqrt ε) 1) :=
    hint.mono_set (Ioc_subset_Ioc_left hsε.le)
  have hdisj : Disjoint (Ioc (0 : ℝ) (Real.sqrt ε)) (Ioc (Real.sqrt ε) 1) :=
    Set.disjoint_left.2 fun u h1 h2 => absurd h2.1 (not_lt.2 h1.2)
  rw [hsplit, setIntegral_union hdisj measurableSet_Ioc hlow hhigh]
  -- the low piece
  have hmajL : IntegrableOn (fun u : ℝ => u ^ 3 + ε * u / 2) (Ioc 0 (Real.sqrt ε)) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hsε.le]
    exact (by fun_prop : Continuous fun u : ℝ => u ^ 3 + ε * u / 2).intervalIntegrable _ _
  have hL := norm_integral_le_of_norm_le (μ := volume.restrict (Ioc 0 (Real.sqrt ε)))
    (f := quarticRem ε) hmajL (by
      rw [ae_restrict_iff' measurableSet_Ioc]
      exact Eventually.of_forall fun u hu => by
        rw [Real.norm_eq_abs]; exact abs_quarticRem_le_low hε hu.1)
  have hLval : ∫ u in Ioc (0 : ℝ) (Real.sqrt ε), (u ^ 3 + ε * u / 2) = ε ^ 2 / 2 := by
    rw [← intervalIntegral.integral_of_le hsε.le, intervalIntegral.integral_add
      ((by fun_prop : Continuous fun u : ℝ => u ^ 3).intervalIntegrable 0 (Real.sqrt ε))
      ((by fun_prop : Continuous fun u : ℝ => ε * u / 2).intervalIntegrable 0 (Real.sqrt ε))]
    have e1 : ∫ u in (0 : ℝ)..Real.sqrt ε, u ^ 3 = Real.sqrt ε ^ 4 / 4 := by
      rw [integral_pow]; norm_num
    have e2 : ∫ u in (0 : ℝ)..Real.sqrt ε, ε * u / 2 = ε * Real.sqrt ε ^ 2 / 4 := by
      have : (fun u : ℝ => ε * u / 2) = fun u => (ε / 2) * u ^ 1 := by funext u; ring
      rw [this, intervalIntegral.integral_const_mul, integral_pow]; norm_num; ring
    rw [e1, e2, show Real.sqrt ε ^ 4 = (Real.sqrt ε ^ 2) ^ 2 by ring, Real.sq_sqrt hε.le]
    ring
  -- the high piece
  have hmajH : IntegrableOn (fun u : ℝ => 3 / 8 * ε ^ 2 / u) (Ioc (Real.sqrt ε) 1) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hsε1]
    refine ContinuousOn.intervalIntegrable ?_
    refine (continuousOn_const.div continuousOn_id fun u hu => ?_)
    rw [uIcc_of_le hsε1] at hu
    exact (lt_of_lt_of_le hsε hu.1).ne'
  have hH := norm_integral_le_of_norm_le (μ := volume.restrict (Ioc (Real.sqrt ε) 1))
    (f := quarticRem ε) hmajH (by
      rw [ae_restrict_iff' measurableSet_Ioc]
      exact Eventually.of_forall fun u hu => by
        rw [Real.norm_eq_abs]; exact abs_quarticRem_le_high hε (lt_trans hsε hu.1))
  have hHval : ∫ u in Ioc (Real.sqrt ε) 1, 3 / 8 * ε ^ 2 / u =
      3 / 16 * ε ^ 2 * Real.log (1 / ε) := by
    rw [← intervalIntegral.integral_of_le hsε1]
    have : (fun u : ℝ => 3 / 8 * ε ^ 2 / u) = fun u => (3 / 8 * ε ^ 2) * (1 / u) := by
      funext u; ring
    rw [this, intervalIntegral.integral_const_mul, integral_one_div_of_pos hsε one_pos]
    simp only [one_div, Real.log_inv]
    rw [Real.log_sqrt hε.le]
    ring
  rw [Real.norm_eq_abs] at hL hH
  rw [hLval] at hL
  rw [hHval] at hH
  calc |(∫ u in Ioc (0 : ℝ) (Real.sqrt ε), quarticRem ε u) +
        ∫ u in Ioc (Real.sqrt ε) 1, quarticRem ε u|
      ≤ |∫ u in Ioc (0 : ℝ) (Real.sqrt ε), quarticRem ε u| +
        |∫ u in Ioc (Real.sqrt ε) 1, quarticRem ε u| := abs_add_le _ _
    _ ≤ ε ^ 2 / 2 + 3 / 16 * ε ^ 2 * Real.log (1 / ε) := add_le_add hL hH

/-! ### The outer remainder `∫₁^∞ a (2/√(u²+ε) − 2/u + ε/u³)` -/

theorem integrableOn_rpow_neg_five : IntegrableOn (fun u : ℝ => u ^ (-5 : ℝ)) (Ioi 1) :=
  integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos

theorem integral_rpow_neg_five : ∫ u in Ioi (1 : ℝ), u ^ (-5 : ℝ) = 1 / 4 := by
  rw [integral_Ioi_rpow_of_lt (by norm_num) one_pos]
  norm_num

theorem integrableOn_blowAmpInf_div_cube :
    IntegrableOn (fun u : ℝ => blowAmpInf u / u ^ 3) (Ioi 1) := by
  have hmaj : IntegrableOn (fun u : ℝ => u ^ (-3 : ℝ)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos
  refine hmaj.mono' ((by unfold blowAmpInf; fun_prop : Measurable fun u : ℝ =>
    blowAmpInf u / u ^ 3).aestronglyMeasurable) ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Eventually.of_forall fun u hu => ?_
  have hu : (1 : ℝ) < u := hu
  have hu0 : 0 < u := by linarith
  have ha0 : 0 ≤ blowAmpInf u := by unfold blowAmpInf; positivity
  have ha1 : blowAmpInf u ≤ 1 := by linarith [one_sub_blowAmpInf_nonneg u]
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.rpow_neg hu0.le,
    show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, ← one_div,
    div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [pow_pos hu0 3]

/-- The outer remainder integrand. -/
noncomputable def quarticOuter (ε u : ℝ) : ℝ :=
  blowAmpInf u * (2 / Real.sqrt (u ^ 2 + ε) - 2 / u + ε / u ^ 3)

theorem abs_quarticOuter_le {ε u : ℝ} (hε : 0 < ε) (hu : 0 < u) :
    |quarticOuter ε u| ≤ 3 / 4 * ε ^ 2 * u ^ (-5 : ℝ) := by
  unfold quarticOuter
  obtain ⟨k1, k2⟩ := kernel_second_order hε hu
  have ha0 : 0 ≤ blowAmpInf u := by unfold blowAmpInf; positivity
  have ha1 : blowAmpInf u ≤ 1 := by linarith [one_sub_blowAmpInf_nonneg u]
  rw [abs_of_nonneg (mul_nonneg ha0 k1), Real.rpow_neg hu.le,
    show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  calc blowAmpInf u * (2 / Real.sqrt (u ^ 2 + ε) - 2 / u + ε / u ^ 3)
      ≤ 1 * (3 / 4 * ε ^ 2 / u ^ 5) := mul_le_mul ha1 k2 k1 zero_le_one
    _ = 3 / 4 * ε ^ 2 * (u ^ 5)⁻¹ := by ring

theorem integrableOn_quarticOuter {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (quarticOuter ε) (Ioi 1) := by
  refine (integrableOn_rpow_neg_five.const_mul (3 / 4 * ε ^ 2)).mono'
    ((by unfold quarticOuter blowAmpInf; fun_prop :
      Measurable (quarticOuter ε)).aestronglyMeasurable) ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Eventually.of_forall fun u hu => ?_
  have hu : (1 : ℝ) < u := hu
  rw [Real.norm_eq_abs]
  exact abs_quarticOuter_le hε (by linarith)

/-- `|∫₁^∞ quarticOuter| ≤ (3/16) ε²`. -/
theorem abs_integral_quarticOuter_le {ε : ℝ} (hε : 0 < ε) :
    |∫ u in Ioi (1 : ℝ), quarticOuter ε u| ≤ 3 / 16 * ε ^ 2 := by
  have hb := norm_integral_le_of_norm_le (μ := volume.restrict (Ioi (1 : ℝ)))
    (f := quarticOuter ε) (integrableOn_rpow_neg_five.const_mul (3 / 4 * ε ^ 2)) (by
      rw [ae_restrict_iff' measurableSet_Ioi]
      exact Eventually.of_forall fun u hu => by
        rw [Real.norm_eq_abs]
        exact abs_quarticOuter_le hε (by linarith [show (1 : ℝ) < u from hu]))
  rw [Real.norm_eq_abs, integral_const_mul, integral_rpow_neg_five] at hb
  linarith

/-! ### The elementary integral to second order -/

/-- `|2 log((1 + √(1+ε))/√ε) − log(4/ε) − ε/2| ≤ ε²/4` for `0 < ε ≤ 1`. -/
theorem elem_second_order {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    |2 * Real.log ((1 + Real.sqrt (1 + ε)) / Real.sqrt ε) - Real.log (4 / ε) - ε / 2| ≤
      ε ^ 2 / 4 := by
  have hsε : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  set s := Real.sqrt (1 + ε) with hs
  have h1 : 1 ≤ s := Real.one_le_sqrt.2 (by linarith)
  have h2 : s ≤ 1 + ε / 2 := Real.sqrt_one_add_le (by linarith)
  have h3 : 1 + ε / 2 - ε ^ 2 / 8 ≤ s := by
    have hy : (0 : ℝ) ≤ 1 + ε / 2 - ε ^ 2 / 8 := by nlinarith
    rw [hs, Real.le_sqrt hy (by linarith)]
    nlinarith [pow_nonneg hε.le 3, pow_nonneg hε.le 4]
  have hlog : 2 * Real.log ((1 + s) / Real.sqrt ε) - Real.log (4 / ε) =
      2 * Real.log (1 + (s - 1) / 2) := by
    rw [Real.log_div (by linarith) hsε.ne', Real.log_div (by norm_num) hε.ne',
      Real.log_sqrt hε.le, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow,
      show (1 : ℝ) + (s - 1) / 2 = (1 + s) / 2 by ring, Real.log_div (by linarith) (by norm_num)]
    push_cast
    ring
  rw [hlog]
  set x := (s - 1) / 2 with hx
  have hx0 : 0 ≤ x := by rw [hx]; linarith
  have hxu : x ≤ ε / 4 := by rw [hx]; linarith
  have hxl : ε / 4 - ε ^ 2 / 16 ≤ x := by rw [hx]; linarith
  have hup : Real.log (1 + x) ≤ x := by
    linarith [Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + x)]
  have hlo : x - x ^ 2 ≤ Real.log (1 + x) := by
    have h := Real.one_sub_inv_le_log_of_pos (by linarith : 0 < 1 + x)
    have e : 1 - (1 + x)⁻¹ = x / (1 + x) := by
      field_simp
      ring
    have : x - x ^ 2 ≤ 1 - (1 + x)⁻¹ := by
      rw [e, le_div_iff₀ (by linarith)]
      nlinarith [pow_nonneg hx0 3]
    linarith
  have hx2 : x ^ 2 ≤ ε ^ 2 / 16 := by nlinarith
  rw [abs_le]
  constructor <;> nlinarith

/-! ### The linear coefficient `∫₀^∞ (1 − a)/u³ = ½√(π/2)` -/

/-- The linear coefficient `κ = ∫₀^∞ (1 − e^{−u⁴/2})/u³ du`. -/
noncomputable def quarticLinear : ℝ := ∫ u in Ioi (0 : ℝ), (1 - blowAmpInf u) / u ^ 3

theorem integrableOn_one_sub_blowAmpInf_div_cube_inner :
    IntegrableOn (fun u : ℝ => (1 - blowAmpInf u) / u ^ 3) (Ioc 0 1) := by
  refine Measure.integrableOn_of_bounded (M := 1 / 2)
    (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
    ((by unfold blowAmpInf; fun_prop : Measurable fun u : ℝ => (1 - blowAmpInf u) / u ^ 3)
      |>.aestronglyMeasurable) ?_
  rw [ae_restrict_iff' measurableSet_Ioc]
  refine Eventually.of_forall fun u hu => ?_
  have hu0 : 0 < u := hu.1
  have h1 := one_sub_blowAmpInf_nonneg u
  have h2 := one_sub_blowAmpInf_le u
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_iff₀ (by positivity)]
  have hu4 : u ^ 4 ≤ u ^ 3 := by
    have := pow_pos hu0 3
    nlinarith [hu.2]
  linarith

theorem integrableOn_one_sub_blowAmpInf_div_cube_outer :
    IntegrableOn (fun u : ℝ => (1 - blowAmpInf u) / u ^ 3) (Ioi 1) := by
  have hmaj : IntegrableOn (fun u : ℝ => u ^ (-3 : ℝ)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos
  refine hmaj.mono' ((by unfold blowAmpInf; fun_prop : Measurable fun u : ℝ =>
    (1 - blowAmpInf u) / u ^ 3).aestronglyMeasurable) ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Eventually.of_forall fun u hu => ?_
  have hu : (1 : ℝ) < u := hu
  have hu0 : 0 < u := by linarith
  have h1 := one_sub_blowAmpInf_nonneg u
  have ha0 : 0 ≤ blowAmpInf u := by unfold blowAmpInf; positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.rpow_neg hu0.le,
    show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, ← one_div,
    div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [pow_pos hu0 3]

theorem integrableOn_one_sub_blowAmpInf_div_cube :
    IntegrableOn (fun u : ℝ => (1 - blowAmpInf u) / u ^ 3) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  exact integrableOn_one_sub_blowAmpInf_div_cube_inner.union
    integrableOn_one_sub_blowAmpInf_div_cube_outer

theorem integrableOn_mul_exp_neg_quartic :
    IntegrableOn (fun u : ℝ => u * Real.exp (-u ^ 4 / 2)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1) (p := 4) (b := 1 / 2) (by norm_num)
    (by norm_num) (by norm_num)
  refine h.congr_fun (fun u hu => ?_) measurableSet_Ioi
  have hu : (0 : ℝ) < u := hu
  simp only
  rw [Real.rpow_one, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  congr 1
  ring

/-- `∫₀^∞ u e^{−u⁴/2} du = ½√(π/2)`. -/
theorem integral_mul_exp_neg_quartic :
    ∫ u in Ioi (0 : ℝ), u * Real.exp (-u ^ 4 / 2) = Real.sqrt (Real.pi / 2) / 2 := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 4) (q := 1) (b := 1 / 2) (by norm_num)
    (by norm_num) (by norm_num)
  rw [setIntegral_congr_fun (g := fun u : ℝ => u ^ (1 : ℝ) * Real.exp (-(1 / 2) * u ^ (4 : ℝ)))
    measurableSet_Ioi (fun u (hu : (0 : ℝ) < u) => by
    beta_reduce
    rw [Real.rpow_one, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    congr 1
    ring), h]
  rw [show ((1 : ℝ) + 1) / 4 = 1 / 2 by norm_num, Real.Gamma_one_half_eq,
    show (-((1 : ℝ) + 1) / 4) = -(1 / 2 : ℝ) by norm_num, Real.rpow_neg (by norm_num),
    ← Real.sqrt_eq_rpow, Real.sqrt_div (by norm_num) 2, Real.sqrt_div Real.pi_pos.le 2]
  have h2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hpi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  field_simp
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-- ★★ **The linear coefficient**: `∫₀^∞ (1 − e^{−u⁴/2})/u³ du = ½√(π/2)`, by parts. -/
theorem quarticLinear_eq : quarticLinear = Real.sqrt (Real.pi / 2) / 2 := by
  unfold quarticLinear
  have hu : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun x : ℝ => 1 - blowAmpInf x)
      (2 * x ^ 3 * Real.exp (-x ^ 4 / 2)) x := by
    intro x _
    unfold blowAmpInf
    have h := (((hasDerivAt_pow 4 x).neg).div_const 2).exp
    refine (h.const_sub 1).congr_deriv ?_
    norm_num
    ring
  have hv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun x : ℝ => -1 / (2 * x ^ 2)) (1 / x ^ 3) x := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    have h := (hasDerivAt_const x (-1 : ℝ)).div ((hasDerivAt_pow 2 x).const_mul 2)
      (by positivity)
    refine h.congr_deriv ?_
    norm_num
    field_simp
  have huv' : IntegrableOn ((fun x : ℝ => 1 - blowAmpInf x) * fun x => 1 / x ^ 3) (Ioi 0) := by
    refine integrableOn_one_sub_blowAmpInf_div_cube.congr_fun (fun x _ => ?_) measurableSet_Ioi
    simp only [Pi.mul_apply]
    ring
  have hu'v : IntegrableOn ((fun x : ℝ => 2 * x ^ 3 * Real.exp (-x ^ 4 / 2)) *
      fun x => -1 / (2 * x ^ 2)) (Ioi 0) := by
    refine (integrableOn_mul_exp_neg_quartic.neg).congr_fun (fun x hx => ?_) measurableSet_Ioi
    have hx0 : (0 : ℝ) < x := hx
    simp only [Pi.mul_apply, Pi.neg_apply]
    field_simp
  have h_zero : Tendsto ((fun x : ℝ => 1 - blowAmpInf x) * fun x => -1 / (2 * x ^ 2)) (𝓝[>] 0)
      (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun x : ℝ => x ^ 2 / 4) ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with x hx
      have hx0 : (0 : ℝ) < x := hx
      simp only [Pi.mul_apply]
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (one_sub_blowAmpInf_nonneg x), abs_div,
        abs_neg, abs_one, abs_of_pos (by positivity : (0 : ℝ) < 2 * x ^ 2)]
      calc (1 - blowAmpInf x) * (1 / (2 * x ^ 2)) ≤ x ^ 4 / 2 * (1 / (2 * x ^ 2)) :=
            mul_le_mul_of_nonneg_right (one_sub_blowAmpInf_le x) (by positivity)
        _ = x ^ 2 / 4 := by field_simp; ring
    · have : Tendsto (fun x : ℝ => x ^ 2 / 4) (𝓝 0) (𝓝 ((0 : ℝ) ^ 2 / 4)) :=
        ((continuous_pow 2).div_const 4).tendsto 0
      simpa using this.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  have h_infty : Tendsto ((fun x : ℝ => 1 - blowAmpInf x) * fun x => -1 / (2 * x ^ 2)) atTop
      (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun x : ℝ => (1 / 2 : ℝ) * (x ^ 2)⁻¹) ?_ ?_
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      simp only [Pi.mul_apply]
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (one_sub_blowAmpInf_nonneg x), abs_div,
        abs_neg, abs_one, abs_of_pos (by positivity : (0 : ℝ) < 2 * x ^ 2)]
      have ha0 : 0 ≤ blowAmpInf x := by unfold blowAmpInf; positivity
      calc (1 - blowAmpInf x) * (1 / (2 * x ^ 2)) ≤ 1 * (1 / (2 * x ^ 2)) :=
            mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ = (1 / 2) * (x ^ 2)⁻¹ := by ring
    · have : Tendsto (fun x : ℝ => (1 / 2 : ℝ) * (x ^ 2)⁻¹) atTop (𝓝 ((1 / 2) * 0)) :=
        (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop two_ne_zero)).const_mul (1 / 2)
      simpa using this
  have key := integral_Ioi_mul_deriv_eq_deriv_mul hu hv huv' hu'v h_zero h_infty
  rw [sub_zero, zero_sub] at key
  rw [setIntegral_congr_fun measurableSet_Ioi (fun x _ => div_eq_mul_one_div (1 - blowAmpInf x)
    (x ^ 3)), key, ← integral_neg]
  rw [setIntegral_congr_fun measurableSet_Ioi (fun x (hx : (0 : ℝ) < x) => by
    change -(2 * x ^ 3 * Real.exp (-x ^ 4 / 2) * (-1 / (2 * x ^ 2))) = x * Real.exp (-x ^ 4 / 2)
    field_simp)]
  exact integral_mul_exp_neg_quartic

/-! ### The assembly -/

theorem integral_inv_cube_Ioi_one : ∫ u in Ioi (1 : ℝ), blowAmpInf u / u ^ 3 =
    1 / 2 - ∫ u in Ioi (1 : ℝ), (1 - blowAmpInf u) / u ^ 3 := by
  have hmaj : IntegrableOn (fun u : ℝ => u ^ (-3 : ℝ)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos
  have hval : ∫ u in Ioi (1 : ℝ), u ^ (-3 : ℝ) = 1 / 2 := by
    rw [integral_Ioi_rpow_of_lt (by norm_num) one_pos]
    norm_num
  have hsum : ∫ u in Ioi (1 : ℝ), (blowAmpInf u / u ^ 3 + (1 - blowAmpInf u) / u ^ 3) =
      ∫ u in Ioi (1 : ℝ), u ^ (-3 : ℝ) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    have hu0 : (0 : ℝ) < u := by linarith [show (1 : ℝ) < u from hu]
    rw [Real.rpow_neg hu0.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    field_simp
    ring
  rw [integral_add integrableOn_blowAmpInf_div_cube integrableOn_one_sub_blowAmpInf_div_cube_outer,
    hval] at hsum
  linarith

/-- ★★★ **The frozen quartic amplitude to second order**:
`|J_∞(ε) − (log(4/ε) + R_∞ + ½√(π/2)·ε)| ≤ 2ε²(log(1/ε) + 1)` for `0 < ε ≤ 1`. -/
theorem quarticJ_linear_remainder {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    |ampJ blowAmpInf ε - (Real.log (4 / ε) + ampRenorm blowAmpInf +
      Real.sqrt (Real.pi / 2) / 2 * ε)| ≤ 2 * ε ^ 2 * (Real.log (1 / ε) + 1) := by
  have h := blowAmpInf_ampData
  have hA1 := integrableOn_ampJ_inner h hε
  have hA2 := integrableOn_ampJ_outer h hε
  have hp1 := integrableOn_elem hε
  have hq1 : IntegrableOn (fun u : ℝ => (blowAmpInf u - 1) * (2 / u)) (Ioc 0 1) :=
    (integrableOn_ampRenorm_inner h).congr_fun (fun w hw => by
      simp only; rw [indicator_of_mem hw, Pi.one_apply]) measurableSet_Ioc
  have hq2 : IntegrableOn (fun u : ℝ => blowAmpInf u * (2 / u)) (Ioi 1) :=
    (integrableOn_ampRenorm_outer h).congr_fun (fun w hw => by
      simp only; rw [indicator_of_notMem (fun hm => absurd hm.2 (not_le.2 hw)), sub_zero])
      measurableSet_Ioi
  have hJ : ampJ blowAmpInf ε = (∫ u in Ioc (0 : ℝ) 1, 2 * blowAmpInf u / Real.sqrt (u ^ 2 + ε)) +
      ∫ u in Ioi (1 : ℝ), 2 * blowAmpInf u / Real.sqrt (u ^ 2 + ε) := by
    unfold ampJ
    rw [← Ioc_union_Ioi_eq_Ioi zero_le_one,
      setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hA1 hA2]
  have hE : ∫ u in Ioc (0 : ℝ) 1, 2 / Real.sqrt (u ^ 2 + ε) =
      2 * Real.log ((1 + Real.sqrt (1 + ε)) / Real.sqrt ε) := by
    rw [← intervalIntegral.integral_of_le zero_le_one, integral_elem hε]
  -- inner decomposition
  have hin := integrableOn_one_sub_blowAmpInf_div_cube_inner
  have hqR := integrableOn_quarticRem hε hε1
  have hR1 : ∫ u in Ioc (0 : ℝ) 1, 2 * blowAmpInf u / Real.sqrt (u ^ 2 + ε) =
      (∫ u in Ioc (0 : ℝ) 1, 2 / Real.sqrt (u ^ 2 + ε)) +
        (∫ u in Ioc (0 : ℝ) 1, (blowAmpInf u - 1) * (2 / u)) +
        (∫ u in Ioc (0 : ℝ) 1, quarticRem ε u) +
        ε * ∫ u in Ioc (0 : ℝ) 1, (1 - blowAmpInf u) / u ^ 3 := by
    have e : ∀ u ∈ Ioc (0 : ℝ) 1, 2 * blowAmpInf u / Real.sqrt (u ^ 2 + ε) =
        2 / Real.sqrt (u ^ 2 + ε) + (blowAmpInf u - 1) * (2 / u) + quarticRem ε u +
          ε * ((1 - blowAmpInf u) / u ^ 3) := by
      intro u hu
      have hu0 : 0 < u := hu.1
      unfold quarticRem
      field_simp
      ring
    have hI1 : IntegrableOn (fun u : ℝ => 2 / Real.sqrt (u ^ 2 + ε) +
        (blowAmpInf u - 1) * (2 / u)) (Ioc 0 1) := hp1.add hq1
    have hI2 : IntegrableOn (fun u : ℝ => 2 / Real.sqrt (u ^ 2 + ε) +
        (blowAmpInf u - 1) * (2 / u) + quarticRem ε u) (Ioc 0 1) := hI1.add hqR
    have hI3 : IntegrableOn (fun u : ℝ => ε * ((1 - blowAmpInf u) / u ^ 3)) (Ioc 0 1) :=
      hin.const_mul ε
    rw [setIntegral_congr_fun measurableSet_Ioc e, integral_add hI2 hI3, integral_add hI1 hqR,
      integral_add hp1 hq1, integral_const_mul]
  -- outer decomposition
  have hout := integrableOn_blowAmpInf_div_cube
  have hqO := integrableOn_quarticOuter hε
  have hR2 : ∫ u in Ioi (1 : ℝ), 2 * blowAmpInf u / Real.sqrt (u ^ 2 + ε) =
      (∫ u in Ioi (1 : ℝ), blowAmpInf u * (2 / u)) + (∫ u in Ioi (1 : ℝ), quarticOuter ε u) -
        ε * ∫ u in Ioi (1 : ℝ), blowAmpInf u / u ^ 3 := by
    have e : ∀ u ∈ Ioi (1 : ℝ), 2 * blowAmpInf u / Real.sqrt (u ^ 2 + ε) =
        blowAmpInf u * (2 / u) + quarticOuter ε u - ε * (blowAmpInf u / u ^ 3) := by
      intro u hu
      have hu0 : 0 < u := by linarith [show (1 : ℝ) < u from hu]
      unfold quarticOuter
      field_simp
      ring
    have hO1 : IntegrableOn (fun u : ℝ => blowAmpInf u * (2 / u) + quarticOuter ε u) (Ioi 1) :=
      hq2.add hqO
    have hO2 : IntegrableOn (fun u : ℝ => ε * (blowAmpInf u / u ^ 3)) (Ioi 1) := hout.const_mul ε
    rw [setIntegral_congr_fun measurableSet_Ioi e, integral_sub hO1 hO2, integral_add hq2 hqO,
      integral_const_mul]
  have hκ : quarticLinear = (∫ u in Ioc (0 : ℝ) 1, (1 - blowAmpInf u) / u ^ 3) +
      ∫ u in Ioi (1 : ℝ), (1 - blowAmpInf u) / u ^ 3 := by
    unfold quarticLinear
    rw [← Ioc_union_Ioi_eq_Ioi zero_le_one, setIntegral_union Ioc_disjoint_Ioi_same
      measurableSet_Ioi hin integrableOn_one_sub_blowAmpInf_div_cube_outer]
  have hb1 := elem_second_order hε hε1
  have hb2 := abs_integral_quarticRem_le hε hε1
  have hb3 := abs_integral_quarticOuter_le hε
  have hsplit := ampRenorm_split h
  have hlog : 0 ≤ Real.log (1 / ε) := Real.log_nonneg (by rw [le_div_iff₀ hε]; linarith)
  rw [hJ, hR1, hR2, hE, hsplit, ← quarticLinear_eq, hκ, integral_inv_cube_Ioi_one]
  rw [abs_le] at hb1 hb2 hb3 ⊢
  constructor <;> nlinarith [sq_nonneg ε, mul_nonneg (sq_nonneg ε) hlog]


end Grammar
