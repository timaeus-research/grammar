/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.GaussianDepthFiveConst
import Grammar.GaussianResidualCutoffBounds

/-!
# The depth-five polynomial with the linear-log rate

`|√N Z₅ − A₅ℓ⁴ − B₅ℓ³ − C₅ℓ² − D₅ℓ − E₅| ≤ K(1 + ℓ)/√N` for `N ≥ 1`
(★★★ `gaussLaplaceL_five_constant_rate`): DCLVI's exact remainder identity with the generic
residual bound (`residual_term_bound_of_le`, `|q₄| ≤ K₄(1 + 2 log v)/v²` from DCLIV) and the
cutoff moments with the extra `√a` (`abs_integral_gaussH_log_pow_Ioc_le_sqrt`), so that the
cutoff products of the cubic `P₄` cost `(1 + ℓ)³ N^{−3/4} ≤ 81(1 + ℓ)/√N` (`1 + log N ≤ 9N^{1/8}`).
The logarithmic exponent `m = 1` is preserved from depth four to depth five — the invariant of the
all-depth engine (Astra round 18).  Examples_slop §2.
Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

/-- `log N ≤ 8 N^{1/8}` for `N > 0`. -/
theorem log_le_eight_mul_rpow {N : ℝ} (hN : 0 < N) : Real.log N ≤ 8 * N ^ (1 / 8 : ℝ) := by
  have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hN (1 / 8))
  rw [Real.log_rpow hN] at h
  have h1 : 0 < N ^ (1 / 8 : ℝ) := Real.rpow_pos_of_pos hN _
  linarith

/-- `1 + log N ≤ 9 N^{1/8}` for `N ≥ 1`. -/
theorem one_add_log_le_nine_mul_rpow {N : ℝ} (hN : 1 ≤ N) :
    1 + Real.log N ≤ 9 * N ^ (1 / 8 : ℝ) := by
  have h1 : 1 ≤ N ^ (1 / 8 : ℝ) := Real.one_le_rpow hN (by norm_num)
  linarith [log_le_eight_mul_rpow (by linarith : (0 : ℝ) < N)]

/-- `√N = (N^{1/8})⁴`. -/
theorem sqrt_eq_rpow_eighth_pow {N : ℝ} (hN : 0 ≤ N) :
    Real.sqrt N = (N ^ (1 / 8 : ℝ)) ^ 4 := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hN]; norm_num

set_option maxHeartbeats 1600000 in
-- the exact remainder identity and the long chain of bounds exceed the default budget
/-- ★★★ **The depth-five polynomial with the linear-log rate**: there is `K ≥ 0` with
`|√N Z₅ − A₅ℓ⁴ − B₅ℓ³ − C₅ℓ² − D₅ℓ − E₅| ≤ K(1 + ℓ)/√N` for all `N ≥ 1`. -/
theorem gaussLaplaceL_five_constant_rate :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℝ, 1 ≤ N →
      |Real.sqrt N * gaussLaplaceL 5 N - gaussCoeffA 1 * (Real.log N) ^ 4 -
        gaussCoeffB 1 * (Real.log N) ^ 3 - thirdCoeff 1 * (Real.log N) ^ 2 -
        depthFiveLinCoeff * Real.log N - depthFiveConst| ≤
        K * (1 + Real.log N) / Real.sqrt N := by
  obtain ⟨K₄, hK₄0, hK₄⟩ := depthFiveQ_outer_le
  set s := Real.sqrt (2 * Real.pi) with hs_def
  have hs : 0 < s := Real.sqrt_pos.2 (by positivity)
  set A₄ : ℝ := gaussCoeffA 0 with hA₄
  set B₄ : ℝ := gaussCoeffB 0 with hB₄
  set C₄ : ℝ := thirdCoeff 0 with hC₄
  set D₄ : ℝ := depthFourConst with hD₄
  have hA₄0 : 0 < A₄ := by rw [hA₄]; unfold gaussCoeffA; positivity
  have hB0 : 0 ≤ |B₄| := abs_nonneg _
  have hC0 : 0 ≤ |C₄| := abs_nonneg _
  have hD0 : 0 ≤ |D₄| := abs_nonneg _
  set M : ℝ := (A₄ + |B₄| + |C₄| + |D₄|) * (1 / 3) + (6 * A₄ + 4 * |B₄| + 2 * |C₄|) * (2 / 3) +
    (12 * A₄ + 4 * |B₄|) * (16 / 3) + 8 * A₄ * 72 with hM
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  refine ⟨2 / s * (1 / 2 + K₄ / 2 + 3 * K₄ + 81 * M), by positivity, fun N hN => ?_⟩
  have hN0 : 0 < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have hsN1 : 1 ≤ Real.sqrt N := Real.one_le_sqrt.2 hN
  have hℓ : 0 ≤ Real.log N := Real.log_nonneg hN
  set ℓ := Real.log N with hℓdef
  -- the eighth root
  set y : ℝ := N ^ (1 / 8 : ℝ) with hy
  have hy1 : 1 ≤ y := Real.one_le_rpow hN (by norm_num)
  have hy0 : 0 < y := by linarith
  have hsqrt : Real.sqrt N = y ^ 4 := sqrt_eq_rpow_eighth_pow hN0.le
  have hℓy : 1 + ℓ ≤ 9 * y := one_add_log_le_nine_mul_rpow hN
  set a : ℝ := 1 / Real.sqrt N with ha_def
  have ha0 : 0 < a := by positivity
  have ha1 : a ≤ 1 := by rw [ha_def, div_le_one hsN]; exact hsN1
  have hasqrt : a * Real.sqrt a = 1 / y ^ 6 := by
    have h1 : a = (1 / y ^ 2) ^ 2 := by rw [ha_def, hsqrt]; field_simp
    have h2 : Real.sqrt a = 1 / y ^ 2 := by rw [h1]; exact Real.sqrt_sq (by positivity)
    rw [h2, ha_def, hsqrt]; field_simp
  set X : ℝ := (1 + ℓ) / Real.sqrt N with hX
  have hX0 : 0 < X := by positivity
  have hpow : (1 + ℓ) ^ 3 * (a * Real.sqrt a) ≤ 81 * X := by
    rw [hasqrt, hX, hsqrt]
    have hsq : (1 + ℓ) ^ 2 ≤ 81 * y ^ 2 := by
      have := pow_le_pow_left₀ (by linarith) hℓy 2
      rw [mul_pow] at this; linarith
    have hℓ1 : 0 ≤ 1 + ℓ := by linarith
    rw [show (1 + ℓ) ^ 3 * (1 / y ^ 6) = (1 + ℓ) ^ 3 / y ^ 6 by ring,
      show 81 * ((1 + ℓ) / y ^ 4) = 81 * (1 + ℓ) / y ^ 4 by ring,
      div_le_div_iff₀ (by positivity) (by positivity)]
    have := mul_le_mul_of_nonneg_right hsq (by positivity : (0 : ℝ) ≤ (1 + ℓ) * y ^ 4)
    nlinarith [this]
  -- the residual term
  have hin : ∀ v ∈ Ioc (0 : ℝ) 1, |depthFiveQ v| ≤ 1 := by
    intro v hv
    rw [depthFiveQ_inner hv, abs_of_nonneg (gaussLaplaceL_nonneg 4 _)]
    exact gaussLaplaceL_le_one 4 (sq_nonneg _)
  have hres := residual_term_bound_of_le measurable_depthFiveQ hK₄0 hin hK₄ hN
  have hres' : |2 * (∫ v in Ioi (0 : ℝ), gaussDensity (v / Real.sqrt N) * depthFiveQ v) -
      2 / s * depthFiveQint| ≤ 2 / s * (1 / 2 + K₄ / 2 + 3 * K₄) * X := by
    unfold depthFiveQint
    refine hres.trans ?_
    have h1 : 1 / (2 * N) ≤ 1 / 2 * X := by
      rw [hX]
      have hNs : Real.sqrt N ≤ N := by nlinarith [Real.sq_sqrt hN0.le]
      have h1' : 1 / N ≤ 1 / Real.sqrt N := one_div_le_one_div_of_le hsN hNs
      have h1'' : 1 / Real.sqrt N ≤ (1 + ℓ) / Real.sqrt N :=
        div_le_div_of_nonneg_right (by linarith) hsN.le
      have := h1'.trans h1''
      calc 1 / (2 * N) = 1 / 2 * (1 / N) := by ring
        _ ≤ 1 / 2 * ((1 + ℓ) / Real.sqrt N) := by linarith
    have h2 : K₄ * (1 + ℓ) / (2 * Real.sqrt N) = K₄ / 2 * X := by rw [hX]; ring
    have h3 : K₄ * (3 + ℓ) / Real.sqrt N ≤ 3 * K₄ * X := by
      rw [hX, ← mul_div_assoc]
      refine div_le_div_of_nonneg_right ?_ hsN.le
      nlinarith
    calc 2 / s * (1 / (2 * N) + K₄ * (1 + ℓ) / (2 * Real.sqrt N) + K₄ * (3 + ℓ) / Real.sqrt N)
        ≤ 2 / s * (1 / 2 * X + K₄ / 2 * X + 3 * K₄ * X) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          linarith [h1, h2, h3]
      _ = 2 / s * (1 / 2 + K₄ / 2 + 3 * K₄) * X := by ring
  -- the cutoff moments
  have he0 : |∫ x in Ioc (0 : ℝ) a, gaussH x / x| ≤ 1 / 3 * (a * Real.sqrt a) := by
    have := abs_integral_gaussH_log_pow_Ioc_le_sqrt 0 ha0 ha1
    simp only [pow_zero, mul_one] at this
    convert this using 2
    try norm_num
  have he1 : |∫ x in Ioc (0 : ℝ) a, gaussH x * Real.log x / x| ≤ 2 / 3 * (a * Real.sqrt a) := by
    have := abs_integral_gaussH_log_pow_Ioc_le_sqrt 1 ha0 ha1
    simp only [pow_one] at this
    convert this using 2
    try norm_num
  have he2 : |∫ x in Ioc (0 : ℝ) a, gaussH x * Real.log x ^ 2 / x| ≤
      16 / 3 * (a * Real.sqrt a) := by
    have := abs_integral_gaussH_log_pow_Ioc_le_sqrt 2 ha0 ha1
    convert this using 2
    try norm_num
  have he3 : |∫ x in Ioc (0 : ℝ) a, gaussH x * Real.log x ^ 3 / x| ≤ 72 * (a * Real.sqrt a) := by
    have := abs_integral_gaussH_log_pow_Ioc_le_sqrt 3 ha0 ha1
    convert this using 2
    try norm_num
  -- the coefficient bounds
  have hℓ1 : 1 ≤ 1 + ℓ := by linarith
  have hp0 : 1 ≤ (1 + ℓ) ^ 3 := one_le_pow₀ hℓ1
  have hp1 : ℓ ≤ (1 + ℓ) ^ 3 := (by linarith : ℓ ≤ 1 + ℓ).trans (le_self_pow₀ hℓ1 (by norm_num))
  have hp2 : ℓ ^ 2 ≤ (1 + ℓ) ^ 3 :=
    (pow_le_pow_left₀ hℓ (by linarith) 2).trans (pow_le_pow_right₀ hℓ1 (by norm_num))
  have hp3 : ℓ ^ 3 ≤ (1 + ℓ) ^ 3 := pow_le_pow_left₀ hℓ (by linarith) 3
  have h4 : |(4 : ℝ)| = 4 := abs_of_pos (by norm_num)
  have h6 : |(6 : ℝ)| = 6 := abs_of_pos (by norm_num)
  have h12 : |(12 : ℝ)| = 12 := abs_of_pos (by norm_num)
  have hL0 : 0 ≤ (1 + ℓ) ^ 3 := by positivity
  set L3 := (1 + ℓ) ^ 3 with hL3
  have hc0 : |A₄ * ℓ ^ 3 + B₄ * ℓ ^ 2 + C₄ * ℓ + D₄| ≤ (A₄ + |B₄| + |C₄| + |D₄|) * L3 := by
    calc |A₄ * ℓ ^ 3 + B₄ * ℓ ^ 2 + C₄ * ℓ + D₄|
        ≤ |A₄ * ℓ ^ 3 + B₄ * ℓ ^ 2 + C₄ * ℓ| + |D₄| := abs_add_le _ _
      _ ≤ |A₄ * ℓ ^ 3 + B₄ * ℓ ^ 2| + |C₄ * ℓ| + |D₄| := by gcongr; exact abs_add_le _ _
      _ ≤ |A₄ * ℓ ^ 3| + |B₄ * ℓ ^ 2| + |C₄ * ℓ| + |D₄| := by gcongr; exact abs_add_le _ _
      _ = A₄ * ℓ ^ 3 + |B₄| * ℓ ^ 2 + |C₄| * ℓ + |D₄| := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_pos hA₄0, abs_pow, abs_pow, abs_of_nonneg hℓ]
      _ ≤ A₄ * L3 + |B₄| * L3 + |C₄| * L3 + |D₄| * L3 := by
          have := mul_le_mul_of_nonneg_left hp3 hA₄0.le
          have := mul_le_mul_of_nonneg_left hp2 hB0
          have := mul_le_mul_of_nonneg_left hp1 hC0
          have := mul_le_mul_of_nonneg_left hp0 hD0
          linarith
      _ = (A₄ + |B₄| + |C₄| + |D₄|) * L3 := by ring
  have hc1 : |6 * A₄ * ℓ ^ 2 + 4 * B₄ * ℓ + 2 * C₄| ≤ (6 * A₄ + 4 * |B₄| + 2 * |C₄|) * L3 := by
    calc |6 * A₄ * ℓ ^ 2 + 4 * B₄ * ℓ + 2 * C₄|
        ≤ |6 * A₄ * ℓ ^ 2 + 4 * B₄ * ℓ| + |2 * C₄| := abs_add_le _ _
      _ ≤ |6 * A₄ * ℓ ^ 2| + |4 * B₄ * ℓ| + |2 * C₄| := by gcongr; exact abs_add_le _ _
      _ = 6 * A₄ * ℓ ^ 2 + 4 * |B₄| * ℓ + 2 * |C₄| := by
          simp only [abs_mul, abs_pow, abs_of_nonneg hℓ, abs_of_pos hA₄0, abs_two, h4, h6]
      _ ≤ 6 * A₄ * L3 + 4 * |B₄| * L3 + 2 * |C₄| * L3 := by
          have := mul_le_mul_of_nonneg_left hp2 (by positivity : (0 : ℝ) ≤ 6 * A₄)
          have := mul_le_mul_of_nonneg_left hp1 (by positivity : (0 : ℝ) ≤ 4 * |B₄|)
          have := mul_le_mul_of_nonneg_left hp0 (by positivity : (0 : ℝ) ≤ 2 * |C₄|)
          linarith
      _ = (6 * A₄ + 4 * |B₄| + 2 * |C₄|) * L3 := by ring
  have hc2 : |12 * A₄ * ℓ + 4 * B₄| ≤ (12 * A₄ + 4 * |B₄|) * L3 := by
    calc |12 * A₄ * ℓ + 4 * B₄| ≤ |12 * A₄ * ℓ| + |4 * B₄| := abs_add_le _ _
      _ = 12 * A₄ * ℓ + 4 * |B₄| := by
          simp only [abs_mul, abs_of_nonneg hℓ, abs_of_pos hA₄0, h4, h12]
      _ ≤ 12 * A₄ * L3 + 4 * |B₄| * L3 := by
          have := mul_le_mul_of_nonneg_left hp1 (by positivity : (0 : ℝ) ≤ 12 * A₄)
          have := mul_le_mul_of_nonneg_left hp0 (by positivity : (0 : ℝ) ≤ 4 * |B₄|)
          linarith
      _ = (12 * A₄ + 4 * |B₄|) * L3 := by ring
  have hc3 : |8 * A₄| ≤ 8 * A₄ * L3 := by
    rw [abs_of_pos (by positivity : (0 : ℝ) < 8 * A₄)]
    exact le_mul_of_one_le_right (by positivity) hp0
  -- assemble
  have hid := sqrt_mul_gaussLaplaceL_five_sub_eq hN
  rw [← hℓdef, ← ha_def] at hid
  set Q := ∫ v in Ioi (0 : ℝ), gaussDensity (v / Real.sqrt N) * depthFiveQ v with hQ
  set E0 := ∫ x in Ioc (0 : ℝ) a, gaussH x / x with hE0
  set E1 := ∫ x in Ioc (0 : ℝ) a, gaussH x * Real.log x / x with hE1
  set E2 := ∫ x in Ioc (0 : ℝ) a, gaussH x * Real.log x ^ 2 / x with hE2
  set E3 := ∫ x in Ioc (0 : ℝ) a, gaussH x * Real.log x ^ 3 / x with hE3
  have hX' : Real.sqrt N * gaussLaplaceL 5 N - gaussCoeffA 1 * ℓ ^ 4 - gaussCoeffB 1 * ℓ ^ 3 -
      thirdCoeff 1 * ℓ ^ 2 - depthFiveLinCoeff * ℓ - depthFiveConst =
      (2 * Q - 2 / s * depthFiveQint) +
        2 / s * (-((A₄ * ℓ ^ 3 + B₄ * ℓ ^ 2 + C₄ * ℓ + D₄) * E0) -
          (6 * A₄ * ℓ ^ 2 + 4 * B₄ * ℓ + 2 * C₄) * E1 - (12 * A₄ * ℓ + 4 * B₄) * E2 -
          8 * A₄ * E3) := by
    rw [hid]
    unfold depthFiveConst
    simp only [hA₄, hB₄, hC₄, hD₄, hs_def]
    ring
  rw [hX']
  have hcut : |-((A₄ * ℓ ^ 3 + B₄ * ℓ ^ 2 + C₄ * ℓ + D₄) * E0) -
      (6 * A₄ * ℓ ^ 2 + 4 * B₄ * ℓ + 2 * C₄) * E1 - (12 * A₄ * ℓ + 4 * B₄) * E2 -
      8 * A₄ * E3| ≤ M * (L3 * (a * Real.sqrt a)) := by
    have h0 : |(A₄ * ℓ ^ 3 + B₄ * ℓ ^ 2 + C₄ * ℓ + D₄) * E0| ≤
        (A₄ + |B₄| + |C₄| + |D₄|) * L3 * (1 / 3 * (a * Real.sqrt a)) := by
      rw [abs_mul]; exact mul_le_mul hc0 he0 (abs_nonneg _) (by positivity)
    have h1 : |(6 * A₄ * ℓ ^ 2 + 4 * B₄ * ℓ + 2 * C₄) * E1| ≤
        (6 * A₄ + 4 * |B₄| + 2 * |C₄|) * L3 * (2 / 3 * (a * Real.sqrt a)) := by
      rw [abs_mul]; exact mul_le_mul hc1 he1 (abs_nonneg _) (by positivity)
    have h2 : |(12 * A₄ * ℓ + 4 * B₄) * E2| ≤
        (12 * A₄ + 4 * |B₄|) * L3 * (16 / 3 * (a * Real.sqrt a)) := by
      rw [abs_mul]; exact mul_le_mul hc2 he2 (abs_nonneg _) (by positivity)
    have h3 : |8 * A₄ * E3| ≤ 8 * A₄ * L3 * (72 * (a * Real.sqrt a)) := by
      rw [abs_mul]; exact mul_le_mul hc3 he3 (abs_nonneg _) (by positivity)
    calc |-((A₄ * ℓ ^ 3 + B₄ * ℓ ^ 2 + C₄ * ℓ + D₄) * E0) -
          (6 * A₄ * ℓ ^ 2 + 4 * B₄ * ℓ + 2 * C₄) * E1 - (12 * A₄ * ℓ + 4 * B₄) * E2 -
          8 * A₄ * E3|
        ≤ |-((A₄ * ℓ ^ 3 + B₄ * ℓ ^ 2 + C₄ * ℓ + D₄) * E0) -
            (6 * A₄ * ℓ ^ 2 + 4 * B₄ * ℓ + 2 * C₄) * E1 - (12 * A₄ * ℓ + 4 * B₄) * E2| +
          |8 * A₄ * E3| := abs_sub _ _
      _ ≤ |-((A₄ * ℓ ^ 3 + B₄ * ℓ ^ 2 + C₄ * ℓ + D₄) * E0) -
            (6 * A₄ * ℓ ^ 2 + 4 * B₄ * ℓ + 2 * C₄) * E1| + |(12 * A₄ * ℓ + 4 * B₄) * E2| +
          |8 * A₄ * E3| := by gcongr; exact abs_sub _ _
      _ ≤ |-((A₄ * ℓ ^ 3 + B₄ * ℓ ^ 2 + C₄ * ℓ + D₄) * E0)| +
            |(6 * A₄ * ℓ ^ 2 + 4 * B₄ * ℓ + 2 * C₄) * E1| + |(12 * A₄ * ℓ + 4 * B₄) * E2| +
          |8 * A₄ * E3| := by gcongr; exact abs_sub _ _
      _ = |(A₄ * ℓ ^ 3 + B₄ * ℓ ^ 2 + C₄ * ℓ + D₄) * E0| +
            |(6 * A₄ * ℓ ^ 2 + 4 * B₄ * ℓ + 2 * C₄) * E1| + |(12 * A₄ * ℓ + 4 * B₄) * E2| +
          |8 * A₄ * E3| := by rw [abs_neg]
      _ ≤ (A₄ + |B₄| + |C₄| + |D₄|) * L3 * (1 / 3 * (a * Real.sqrt a)) +
            (6 * A₄ + 4 * |B₄| + 2 * |C₄|) * L3 * (2 / 3 * (a * Real.sqrt a)) +
            (12 * A₄ + 4 * |B₄|) * L3 * (16 / 3 * (a * Real.sqrt a)) +
          8 * A₄ * L3 * (72 * (a * Real.sqrt a)) := by gcongr
      _ = M * (L3 * (a * Real.sqrt a)) := by rw [hM]; ring
  have hcut' : |-((A₄ * ℓ ^ 3 + B₄ * ℓ ^ 2 + C₄ * ℓ + D₄) * E0) -
      (6 * A₄ * ℓ ^ 2 + 4 * B₄ * ℓ + 2 * C₄) * E1 - (12 * A₄ * ℓ + 4 * B₄) * E2 -
      8 * A₄ * E3| ≤ M * (81 * X) :=
    hcut.trans (mul_le_mul_of_nonneg_left (by rw [hL3]; exact hpow) hM0)
  calc |(2 * Q - 2 / s * depthFiveQint) +
        2 / s * (-((A₄ * ℓ ^ 3 + B₄ * ℓ ^ 2 + C₄ * ℓ + D₄) * E0) -
          (6 * A₄ * ℓ ^ 2 + 4 * B₄ * ℓ + 2 * C₄) * E1 - (12 * A₄ * ℓ + 4 * B₄) * E2 -
          8 * A₄ * E3)|
      ≤ |2 * Q - 2 / s * depthFiveQint| +
        2 / s * |-((A₄ * ℓ ^ 3 + B₄ * ℓ ^ 2 + C₄ * ℓ + D₄) * E0) -
          (6 * A₄ * ℓ ^ 2 + 4 * B₄ * ℓ + 2 * C₄) * E1 - (12 * A₄ * ℓ + 4 * B₄) * E2 -
          8 * A₄ * E3| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 / s)]
    _ ≤ 2 / s * (1 / 2 + K₄ / 2 + 3 * K₄) * X + 2 / s * (M * (81 * X)) := by
        gcongr
    _ = 2 / s * (1 / 2 + K₄ / 2 + 3 * K₄ + 81 * M) * X := by ring
    _ = 2 / s * (1 / 2 + K₄ / 2 + 3 * K₄ + 81 * M) * (1 + ℓ) / Real.sqrt N := by
        rw [hX]; ring

end Grammar
