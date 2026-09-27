/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.GaussianDepthAllThreeTerm

/-!
# The Gaussian DLN at every depth: the third logarithmic coefficient

The three-term engine of `GaussianDepthAllThreeTerm` is started at depth four from the depth-three
rate `|√t Z_3(t) − (A₃ ℓ² + B₃ ℓ + C₃)| ≤ 8(1 + ℓ)/√t` (DCXXXIV): one hand-made Gaussian step with
the input shape `8(1 + ℓ)/t` gives three-term data of `Z_4` with a bounded residual
(★★ `threeTermData_four`), and the induction through `threeTermStep_bound` gives, at every depth
`L = m + 4` (★★★ `gaussLaplaceL_three_term_bound`, `gaussLaplaceL_third_coeff`),

  `√N Z_L(N) = A_L ℓ^{L−1} + B_L ℓ^{L−2} + C_L ℓ^{L−3} + O((1 + ℓ)^{L−4})`,

`A_L = 1/((L−1)! s^{L−1})`, `B_L = ((L+1) log 2 − (L−1)γ)/((L−2)! s^{L−1})` (DCXXIV, DCXXVI) and
the third coefficient by the recursion (`thirdCoeff`)

  `C₄ = (C₃ + 2 B₃ R₀ + 8 A₃ J)/s`,  `C_{L+1} = (C_L/(L−2) + 2 B_L R₀ + 4(L−1) A_L J)/s`,

`R₀ = (log 2 − γ)/2`, `J = ∫₀^∞ h log x/x` (`gaussJlog`), `C₃ = depthThreeConst` — the
coefficient of `(log N)^{L−3}` in the polynomial `P_{L−1}` of examples_slop eq. (dln_gauss) at
every depth, in terms of
the two integral-defined constants `J` and `Q` of DCXXXI (Astra round-11 target 3).
Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

/-! ### The base: from depth three to depth four -/

/-- `∫₁^W (1 + 2 log w)/w² dw ≤ 3` for `W ≥ 1` (primitive `−(3 + 2 log w)/w`). -/
theorem integral_one_add_two_log_div_sq_le {W : ℝ} (hW : 1 ≤ W) :
    ∫ w in (1 : ℝ)..W, (1 + 2 * Real.log w) / w ^ 2 ≤ 3 := by
  have hderiv : ∀ w ∈ uIcc (1 : ℝ) W,
      HasDerivAt (fun w => -((3 + 2 * Real.log w) / w)) ((1 + 2 * Real.log w) / w ^ 2) w := by
    intro w hw
    rw [uIcc_of_le hW] at hw
    have hw0 : 0 < w := lt_of_lt_of_le one_pos hw.1
    have h1 : HasDerivAt (fun w : ℝ => 3 + 2 * Real.log w) (2 * w⁻¹) w := by
      have := (Real.hasDerivAt_log hw0.ne').const_mul 2
      exact this.const_add 3
    have h2 := (h1.div (hasDerivAt_id' w) hw0.ne').neg
    refine h2.congr_deriv ?_
    field_simp
    ring
  have hint : IntervalIntegrable (fun w : ℝ => (1 + 2 * Real.log w) / w ^ 2) volume 1 W := by
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.div (continuousOn_const.add (continuousOn_const.mul
      (Real.continuousOn_log.mono fun w hw => ?_))) (by fun_prop) fun w hw => ?_
    · rw [uIcc_of_le hW] at hw
      exact mem_compl_singleton_iff.2 (ne_of_gt (lt_of_lt_of_le one_pos hw.1))
    · rw [uIcc_of_le hW] at hw
      have : 0 < w := lt_of_lt_of_le one_pos hw.1
      positivity
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have hlogW : 0 ≤ Real.log W := Real.log_nonneg hW
  have hW0 : 0 < W := by linarith
  simp only [Real.log_one, mul_zero, add_zero, div_one]
  have : 0 ≤ (3 + 2 * Real.log W) / W := by positivity
  linarith

variable {A B C : ℝ}

/-- The base flat main term:
`∫_a^1 (A q² + B q + C)/(√(2π)√N x) = (Aℓ³/6 + Bℓ²/4 + Cℓ/2)/(√(2π)√N)`. -/
theorem base_flat_main (A B C : ℝ) {N : ℝ} (hN : 1 ≤ N) :
    ∫ x in Ioc (1 / Real.sqrt N) 1, 1 / Real.sqrt (2 * Real.pi) *
      ((A * (Real.log N + 2 * Real.log x) ^ 2 + B * (Real.log N + 2 * Real.log x) + C) /
        (Real.sqrt N * x)) =
      1 / (Real.sqrt (2 * Real.pi) * Real.sqrt N) *
        (A * (Real.log N) ^ 3 / 6 + B * (Real.log N) ^ 2 / 4 + C * Real.log N / 2) := by
  have hN0 : 0 < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have ha0 : 0 < 1 / Real.sqrt N := by positivity
  have ha1 : 1 / Real.sqrt N ≤ 1 := by rw [div_le_one hsN]; exact Real.one_le_sqrt.2 hN
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have e : ∀ x ∈ Ioc (1 / Real.sqrt N) 1, 1 / Real.sqrt (2 * Real.pi) *
      ((A * (Real.log N + 2 * Real.log x) ^ 2 + B * (Real.log N + 2 * Real.log x) + C) /
        (Real.sqrt N * x)) =
      A / (Real.sqrt (2 * Real.pi) * Real.sqrt N) * ((Real.log N + 2 * Real.log x) ^ 2 / x) +
        B / (Real.sqrt (2 * Real.pi) * Real.sqrt N) * ((Real.log N + 2 * Real.log x) ^ 1 / x) +
        C / (Real.sqrt (2 * Real.pi) * Real.sqrt N) * ((Real.log N + 2 * Real.log x) ^ 0 / x) := by
    intro x hx
    have hx0 : 0 < x := lt_trans ha0 hx.1
    field_simp
  have h2 := (intervalIntegrable_iff_integrableOn_Ioc_of_le ha1).1
    (intervalIntegrable_pow_log_div (Real.log N) 2 ha0 ha1)
  have h1 := (intervalIntegrable_iff_integrableOn_Ioc_of_le ha1).1
    (intervalIntegrable_pow_log_div (Real.log N) 1 ha0 ha1)
  have h0 := (intervalIntegrable_iff_integrableOn_Ioc_of_le ha1).1
    (intervalIntegrable_pow_log_div (Real.log N) 0 ha0 ha1)
  have h21 : IntegrableOn (fun x : ℝ =>
      A / (Real.sqrt (2 * Real.pi) * Real.sqrt N) * ((Real.log N + 2 * Real.log x) ^ 2 / x) +
      B / (Real.sqrt (2 * Real.pi) * Real.sqrt N) * ((Real.log N + 2 * Real.log x) ^ 1 / x))
      (Ioc (1 / Real.sqrt N) 1) := (h2.const_mul _).add (h1.const_mul _)
  rw [setIntegral_congr_fun measurableSet_Ioc e, integral_add h21 (h0.const_mul _),
    integral_add (h2.const_mul _) (h1.const_mul _),
    integral_const_mul, integral_const_mul, integral_const_mul, integral_pow_log_div _ _ ha0 ha1,
    integral_pow_log_div _ _ ha0 ha1, integral_pow_log_div _ _ ha0 ha1]
  have hloga : Real.log (1 / Real.sqrt N) = -(Real.log N / 2) := by
    rw [one_div, Real.log_inv, Real.log_sqrt hN0.le]
  rw [hloga, show Real.log N + 2 * -(Real.log N / 2) = 0 by ring]
  push_cast
  field_simp
  ring

/-- The base `h`-part:
`∫_a^∞ h (A q² + B q + C)/(√(2π)√N x) = (A ℓ² R₀ + 4 A ℓ J + B ℓ R₀ + C R₀ + rest)/(√(2π)√N)`,
`|rest| ≤ A (K₂_0 + 6) + |B| (K_0 + 1) + |C|/2`. -/
theorem base_h_main (A B C : ℝ) {N : ℝ} (hN : 1 ≤ N) (hA : 0 ≤ A) :
    |(∫ x in Ioi (1 / Real.sqrt N), 1 / Real.sqrt (2 * Real.pi) *
      (gaussH x * (A * (Real.log N + 2 * Real.log x) ^ 2 + B * (Real.log N + 2 * Real.log x) + C) /
        (Real.sqrt N * x))) -
      1 / (Real.sqrt (2 * Real.pi) * Real.sqrt N) * (A * (Real.log N) ^ 2 * gaussR₀ +
        4 * A * Real.log N * gaussJlog + B * Real.log N * gaussR₀ + C * gaussR₀)| ≤
      1 / (Real.sqrt (2 * Real.pi) * Real.sqrt N) *
        (A * (threeTermK 0 + 6) + |B| * (twoTermK 0 + 1) + |C| / 2) := by
  have hN0 : 0 < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have ha0 : 0 < 1 / Real.sqrt N := by positivity
  have ha1 : 1 / Real.sqrt N ≤ 1 := by rw [div_le_one hsN]; exact Real.one_le_sqrt.2 hN
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hℓ : 0 ≤ Real.log N := Real.log_nonneg hN
  have hℓN : Real.log N ≤ 2 * N := by
    have := Real.log_le_sub_one_of_pos hN0; linarith
  have hℓs : Real.log N ≤ 2 * Real.sqrt N := log_le_two_sqrt hN0
  have hℓ2 : (Real.log N) ^ 2 ≤ 4 * N := by
    have := Real.sq_sqrt hN0.le
    nlinarith
  have e : ∀ x ∈ Ioi (1 / Real.sqrt N), 1 / Real.sqrt (2 * Real.pi) *
      (gaussH x * (A * (Real.log N + 2 * Real.log x) ^ 2 + B * (Real.log N + 2 * Real.log x) + C) /
        (Real.sqrt N * x)) =
      1 / (Real.sqrt (2 * Real.pi) * Real.sqrt N) *
        (A * (gaussH x * (Real.log N + 2 * Real.log x) ^ 2 / x) +
          B * (gaussH x * (Real.log N + 2 * Real.log x) / x) + C * (gaussH x / x)) := by
    intro x hx
    have hx0 : 0 < x := lt_trans ha0 hx
    field_simp
  have h2 := integrableOn_gaussH_pow 2 (Real.log N) ha0 ha1
  have h1 : IntegrableOn (fun x : ℝ => gaussH x * (Real.log N + 2 * Real.log x) / x)
      (Ioi (1 / Real.sqrt N)) :=
    (integrableOn_gaussH_pow 1 (Real.log N) ha0 ha1).congr_fun
      (fun x _ => by simp only [pow_one]) measurableSet_Ioi
  have h0 : IntegrableOn (fun x : ℝ => gaussH x / x) (Ioi (1 / Real.sqrt N)) :=
    integrableOn_gaussH_div.mono_set (Ioi_subset_Ioi ha0.le)
  have h21 : IntegrableOn (fun x : ℝ =>
      A * (gaussH x * (Real.log N + 2 * Real.log x) ^ 2 / x) +
      B * (gaussH x * (Real.log N + 2 * Real.log x) / x)) (Ioi (1 / Real.sqrt N)) :=
    (h2.const_mul _).add (h1.const_mul _)
  rw [setIntegral_congr_fun measurableSet_Ioi e, integral_const_mul,
    integral_add h21 (h0.const_mul _), integral_add (h2.const_mul _) (h1.const_mul _),
    integral_const_mul, integral_const_mul, integral_const_mul,
    ← mul_sub, abs_mul, abs_of_pos (by positivity)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hE2 := integral_gaussH_pow_expand₂ 0 hℓ ha0 ha1
  have hE1 := integral_gaussH_pow_expand 0 hℓ ha0 ha1
  simp only [zero_add, pow_one, pow_zero, one_mul, Nat.cast_zero] at hE2 hE1
  have hI := abs_integral_gaussH_div_Ioc_le ha0.le ha1
  have hIa2 : (1 / Real.sqrt N) ^ 2 = 1 / N := by rw [div_pow, one_pow, Real.sq_sqrt hN0.le]
  rw [hIa2] at hI
  have hJ := abs_logMoment_cutoff_le hN
  have hI0 := integral_gaussH_div_Ioi ha0.le
  rw [hI0] at hE2 hE1
  rw [hI0]
  set J2 := ∫ x in Ioi (1 / Real.sqrt N), gaussH x * (Real.log N + 2 * Real.log x) ^ 2 / x with hJ2
  set J1 := ∫ x in Ioi (1 / Real.sqrt N), gaussH x * (Real.log N + 2 * Real.log x) / x with hJ1
  set Ia := ∫ x in Ioc (0 : ℝ) (1 / Real.sqrt N), gaussH x / x with hIa
  set Ja := ∫ x in Ioi (1 / Real.sqrt N), gaussH x * Real.log x / x with hJa
  clear_value J2 J1 Ia Ja
  set ℓ := Real.log N with hℓdef
  clear_value ℓ
  set K2 := threeTermK 0 with hK2
  set K0 := twoTermK 0 with hK0
  have hK2' : 0 ≤ K2 := threeTermK_nonneg 0
  have hK0' : 0 ≤ K0 := twoTermK_nonneg 0
  clear_value K2 K0
  set R := gaussR₀ with hR
  set J := gaussJlog with hJdef
  clear_value R J
  have hIabs : |Ia| ≤ 1 / N / 2 := hI
  have hJabs : |Ja - J| ≤ 1 / Real.sqrt N / 2 := hJ
  clear hJ2 hJ1 hIa hJa hℓdef hK2 hK0 hR hJdef e h2 h1 h0 h21 hI hJ hIa2 hI0
  have hcut2 : |ℓ ^ 2 * Ia| ≤ 2 := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    calc ℓ ^ 2 * |Ia| ≤ ℓ ^ 2 * (1 / N / 2) := mul_le_mul_of_nonneg_left hIabs (by positivity)
      _ = ℓ ^ 2 / (2 * N) := by ring
      _ ≤ 2 := by rw [div_le_iff₀ (by positivity)]; linarith
  have hcut1 : |ℓ * Ia| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg hℓ]
    calc ℓ * |Ia| ≤ ℓ * (1 / N / 2) := mul_le_mul_of_nonneg_left hIabs hℓ
      _ = ℓ / (2 * N) := by ring
      _ ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  have hcutJ : |4 * ℓ * (Ja - J)| ≤ 4 := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    calc 4 * ℓ * |Ja - J| ≤ 4 * ℓ * (1 / Real.sqrt N / 2) :=
          mul_le_mul_of_nonneg_left hJabs (by positivity)
      _ = 2 * (ℓ / Real.sqrt N) := by ring
      _ ≤ 2 * 2 := by
          gcongr
          rw [div_le_iff₀ hsN]; linarith
      _ = 4 := by norm_num
  have hIhalf : |Ia| ≤ 1 / 2 := by
    refine hIabs.trans ?_
    rw [div_le_div_iff_of_pos_right two_pos, div_le_one hN0]; exact hN
  have hA2 : |A * J2 - A * ℓ ^ 2 * R - 4 * A * ℓ * J| ≤ A * (K2 + 6) := by
    rw [show A * J2 - A * ℓ ^ 2 * R - 4 * A * ℓ * J =
      A * ((J2 - ℓ ^ 2 * (R - Ia) - 2 * 2 * ℓ * Ja) - ℓ ^ 2 * Ia + 4 * ℓ * (Ja - J)) by ring,
      abs_mul, abs_of_nonneg hA]
    refine mul_le_mul_of_nonneg_left ?_ hA
    calc |(J2 - ℓ ^ 2 * (R - Ia) - 2 * 2 * ℓ * Ja) - ℓ ^ 2 * Ia + 4 * ℓ * (Ja - J)|
        ≤ |J2 - ℓ ^ 2 * (R - Ia) - 2 * 2 * ℓ * Ja| + |ℓ ^ 2 * Ia| + |4 * ℓ * (Ja - J)| := by
          have t1 := abs_sub (J2 - ℓ ^ 2 * (R - Ia) - 2 * 2 * ℓ * Ja) (ℓ ^ 2 * Ia)
          have t2 := abs_add_le (J2 - ℓ ^ 2 * (R - Ia) - 2 * 2 * ℓ * Ja - ℓ ^ 2 * Ia)
            (4 * ℓ * (Ja - J))
          linarith
      _ ≤ K2 + 2 + 4 := add_le_add (add_le_add hE2 hcut2) hcutJ
      _ = K2 + 6 := by ring
  have hB1 : |B * J1 - B * ℓ * R| ≤ |B| * (K0 + 1) := by
    rw [show B * J1 - B * ℓ * R = B * ((J1 - ℓ * (R - Ia)) - ℓ * Ia) by ring, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    calc |(J1 - ℓ * (R - Ia)) - ℓ * Ia| ≤ |J1 - ℓ * (R - Ia)| + |ℓ * Ia| := abs_sub _ _
      _ ≤ K0 + 1 := add_le_add hE1 hcut1
  have hC0 : |C * (R - Ia) - C * R| ≤ |C| / 2 := by
    rw [show C * (R - Ia) - C * R = -(C * Ia) by ring, abs_neg, abs_mul]
    calc |C| * |Ia| ≤ |C| * (1 / 2) := mul_le_mul_of_nonneg_left hIhalf (abs_nonneg _)
      _ = |C| / 2 := by ring
  calc |A * J2 + B * J1 + C * (R - Ia) - (A * ℓ ^ 2 * R + 4 * A * ℓ * J + B * ℓ * R + C * R)|
      = |(A * J2 - A * ℓ ^ 2 * R - 4 * A * ℓ * J) + (B * J1 - B * ℓ * R) +
          (C * (R - Ia) - C * R)| := by ring_nf
    _ ≤ |A * J2 - A * ℓ ^ 2 * R - 4 * A * ℓ * J| + |B * J1 - B * ℓ * R| +
          |C * (R - Ia) - C * R| := by
        have t1 := abs_add_le (A * J2 - A * ℓ ^ 2 * R - 4 * A * ℓ * J) (B * J1 - B * ℓ * R)
        have t2 := abs_add_le ((A * J2 - A * ℓ ^ 2 * R - 4 * A * ℓ * J) + (B * J1 - B * ℓ * R))
          (C * (R - Ia) - C * R)
        linarith
    _ ≤ A * (K2 + 6) + |B| * (K0 + 1) + |C| / 2 := add_le_add (add_le_add hA2 hB1) hC0

/-- The base error piece: for `|f(t) − (A ℓ² + B ℓ + C)/√t| ≤ 8(1+ℓ)/t` on `t ≥ 1`,
`|∫_a^∞ (g f(Nx²) − g Q/(√N x))| ≤ 168/(√(2π)√N)`. -/
theorem base_err_le {f : ℝ → ℝ} (A B C : ℝ) (hrate : ∀ t : ℝ, 1 ≤ t →
      |f t - (A * (Real.log t) ^ 2 + B * Real.log t + C) / Real.sqrt t| ≤
        8 * (1 + Real.log t) / t) {N : ℝ} (hN : 1 ≤ N) :
    |∫ x in Ioi (1 / Real.sqrt N), (gaussDensity x * f (N * x ^ 2) - gaussDensity x *
      ((A * (Real.log N + 2 * Real.log x) ^ 2 + B * (Real.log N + 2 * Real.log x) + C) /
        (Real.sqrt N * x)))| ≤ 168 / (Real.sqrt (2 * Real.pi) * Real.sqrt N) := by
  have hN0 : 0 < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have hsN1 : 1 ≤ Real.sqrt N := Real.one_le_sqrt.2 hN
  have ha0 : 0 < 1 / Real.sqrt N := by positivity
  have ha1 : 1 / Real.sqrt N ≤ 1 := by rw [div_le_one hsN]; exact hsN1
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hℓ : 0 ≤ Real.log N := Real.log_nonneg hN
  have hℓs : Real.log N ≤ 2 * Real.sqrt N := log_le_two_sqrt hN0
  have hNN : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN0.le
  -- the majorant
  set Dm : ℝ → ℝ := fun x => (Ioc (1 / Real.sqrt N) 1).indicator
    (fun x => 8 / (Real.sqrt (2 * Real.pi) * N) * ((1 + Real.log N + 2 * Real.log x) / x ^ 2)) x +
    (Ioi 1).indicator (fun x => 24 * (1 + Real.log N) / (Real.sqrt (2 * Real.pi) * N) *
      Real.exp (-x / 2)) x with hDm
  have hD1 : IntegrableOn (fun x : ℝ => 8 / (Real.sqrt (2 * Real.pi) * N) *
      ((1 + Real.log N + 2 * Real.log x) / x ^ 2)) (Ioc (1 / Real.sqrt N) 1) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le ha1]
    refine (ContinuousOn.intervalIntegrable ?_).const_mul _
    refine ContinuousOn.div (continuousOn_const.add (continuousOn_const.mul
      (Real.continuousOn_log.mono fun x hx => ?_))) (by fun_prop) fun x hx => ?_
    · rw [uIcc_of_le ha1] at hx
      exact mem_compl_singleton_iff.2 (ne_of_gt (lt_of_lt_of_le ha0 hx.1))
    · rw [uIcc_of_le ha1] at hx
      have : 0 < x := lt_of_lt_of_le ha0 hx.1
      positivity
  have hD2 : IntegrableOn (fun x : ℝ => 24 * (1 + Real.log N) / (Real.sqrt (2 * Real.pi) * N) *
      Real.exp (-x / 2)) (Ioi 1) := integrableOn_exp_neg_half_Ioi_one.const_mul _
  have hD1' := (hD1.integrable_indicator measurableSet_Ioc).integrableOn
    (s := Ioi (1 / Real.sqrt N))
  have hD2' := (hD2.integrable_indicator measurableSet_Ioi).integrableOn
    (s := Ioi (1 / Real.sqrt N))
  have hDint : IntegrableOn Dm (Ioi (1 / Real.sqrt N)) := by
    rw [hDm]
    exact hD1'.add hD2'
  have hb := norm_integral_le_of_norm_le (μ := volume.restrict (Ioi (1 / Real.sqrt N)))
    (f := fun x => gaussDensity x * f (N * x ^ 2) - gaussDensity x *
      ((A * (Real.log N + 2 * Real.log x) ^ 2 + B * (Real.log N + 2 * Real.log x) + C) /
        (Real.sqrt N * x))) hDint ?_
  · rw [Real.norm_eq_abs] at hb
    refine hb.trans ?_
    rw [hDm, integral_add hD1' hD2',
      setIntegral_indicator measurableSet_Ioc, setIntegral_indicator measurableSet_Ioi,
      show Ioi (1 / Real.sqrt N) ∩ Ioc (1 / Real.sqrt N) 1 = Ioc (1 / Real.sqrt N) 1 from
        inter_eq_right.2 fun x hx => hx.1,
      show Ioi (1 / Real.sqrt N) ∩ Ioi (1 : ℝ) = Ioi 1 from
        inter_eq_right.2 fun x hx => lt_of_le_of_lt ha1 hx,
      integral_const_mul, integral_const_mul,
      integral_exp_neg_div_Ioi_one (by norm_num : (0 : ℝ) < 2)]
    -- the first piece: substitution `x = w/√N`
    have hsub : ∫ x in Ioc (1 / Real.sqrt N) 1, (1 + Real.log N + 2 * Real.log x) / x ^ 2 =
        Real.sqrt N * ∫ w in (1 : ℝ)..Real.sqrt N, (1 + 2 * Real.log w) / w ^ 2 := by
      have e : ∀ x ∈ Ioc (1 / Real.sqrt N) 1, (1 + Real.log N + 2 * Real.log x) / x ^ 2 =
          N * ((1 + 2 * Real.log (Real.sqrt N * x)) / (Real.sqrt N * x) ^ 2) := by
        intro x hx
        have hx0 : 0 < x := lt_trans ha0 hx.1
        rw [Real.log_mul hsN.ne' hx0.ne', Real.log_sqrt hN0.le, mul_pow, Real.sq_sqrt hN0.le]
        field_simp
        ring
      rw [setIntegral_congr_fun measurableSet_Ioc e, ← intervalIntegral.integral_of_le ha1,
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_comp_mul_left (fun w => (1 + 2 * Real.log w) / w ^ 2) hsN.ne',
        mul_one, show Real.sqrt N * (1 / Real.sqrt N) = 1 by field_simp, smul_eq_mul]
      field_simp
      rw [Real.sq_sqrt hN0.le]
    rw [hsub]
    have hlog := integral_one_add_two_log_div_sq_le hsN1
    have hint0 : 0 ≤ ∫ w in (1 : ℝ)..Real.sqrt N, (1 + 2 * Real.log w) / w ^ 2 :=
      intervalIntegral.integral_nonneg hsN1 fun w hw => by
        have : 0 ≤ Real.log w := Real.log_nonneg hw.1
        positivity
    have he2 : Real.exp (-1 / 2) ≤ 1 := Real.exp_le_one_iff.2 (by norm_num)
    have t1 : 8 / (Real.sqrt (2 * Real.pi) * N) *
        (Real.sqrt N * ∫ w in (1 : ℝ)..Real.sqrt N, (1 + 2 * Real.log w) / w ^ 2) ≤
        24 / (Real.sqrt (2 * Real.pi) * Real.sqrt N) := by
      calc 8 / (Real.sqrt (2 * Real.pi) * N) *
            (Real.sqrt N * ∫ w in (1 : ℝ)..Real.sqrt N, (1 + 2 * Real.log w) / w ^ 2)
          ≤ 8 / (Real.sqrt (2 * Real.pi) * N) * (Real.sqrt N * 3) := by gcongr
        _ = 24 / (Real.sqrt (2 * Real.pi) * Real.sqrt N) := by
            rw [div_mul_eq_mul_div, div_eq_div_iff (by positivity) (by positivity)]
            linear_combination (24 * Real.sqrt (2 * Real.pi)) * hNN
    have t2 : 24 * (1 + Real.log N) / (Real.sqrt (2 * Real.pi) * N) * (2 * Real.exp (-1 / 2)) ≤
        144 / (Real.sqrt (2 * Real.pi) * Real.sqrt N) := by
      have h13 : 1 + Real.log N ≤ 3 * Real.sqrt N := by linarith
      calc 24 * (1 + Real.log N) / (Real.sqrt (2 * Real.pi) * N) * (2 * Real.exp (-1 / 2))
          ≤ 24 * (3 * Real.sqrt N) / (Real.sqrt (2 * Real.pi) * N) * (2 * 1) := by gcongr
        _ = 144 / (Real.sqrt (2 * Real.pi) * Real.sqrt N) := by
            rw [div_mul_eq_mul_div, div_eq_div_iff (by positivity) (by positivity)]
            linear_combination (144 * Real.sqrt (2 * Real.pi)) * hNN
    calc _ ≤ 24 / (Real.sqrt (2 * Real.pi) * Real.sqrt N) +
          144 / (Real.sqrt (2 * Real.pi) * Real.sqrt N) := add_le_add t1 t2
      _ = 168 / (Real.sqrt (2 * Real.pi) * Real.sqrt N) := by ring
  · rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun x hx => ?_
    have hx0 : 0 < x := lt_trans ha0 hx
    have ht := one_le_mul_sq_of_le (x := x) hN hx.le
    obtain ⟨hlog, hsqrt⟩ := log_sqrt_mul_sq hN0 hx0
    have hbd := hrate (N * x ^ 2) ht
    rw [hlog, hsqrt] at hbd
    have hg0 := gaussDensity_nonneg x
    have hg1 : gaussDensity x ≤ 1 / Real.sqrt (2 * Real.pi) := gaussDensity_le x
    rw [Real.norm_eq_abs, ← mul_sub, abs_mul, abs_of_nonneg hg0, hDm]
    simp only
    by_cases hx1 : x ≤ 1
    · have hm : x ∈ Ioc (1 / Real.sqrt N) 1 := ⟨hx, hx1⟩
      have hm' : x ∉ Ioi (1 : ℝ) := fun h => absurd h (not_lt.2 hx1)
      rw [indicator_of_mem hm, indicator_of_notMem hm', add_zero]
      calc gaussDensity x * |f (N * x ^ 2) - (A * (Real.log N + 2 * Real.log x) ^ 2 +
            B * (Real.log N + 2 * Real.log x) + C) / (Real.sqrt N * x)|
          ≤ 1 / Real.sqrt (2 * Real.pi) * (8 * (1 + (Real.log N + 2 * Real.log x)) / (N * x ^ 2)) :=
            mul_le_mul hg1 hbd (abs_nonneg _) (by positivity)
        _ = 8 / (Real.sqrt (2 * Real.pi) * N) * ((1 + Real.log N + 2 * Real.log x) / x ^ 2) := by
            rw [show 1 + (Real.log N + 2 * Real.log x) = 1 + Real.log N + 2 * Real.log x by ring]
            field_simp
    · have hx1' := not_le.1 hx1
      have hm : x ∉ Ioc (1 / Real.sqrt N) 1 := fun h => absurd h.2 (not_le.2 hx1')
      have hm' : x ∈ Ioi (1 : ℝ) := hx1'
      rw [indicator_of_notMem hm, indicator_of_mem hm', zero_add]
      have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx1'.le
      have hlx : Real.log x ≤ x := by linarith [Real.log_le_sub_one_of_pos hx0]
      have hx2 : x ≤ x ^ 2 := by nlinarith
      have h3 : 1 + (Real.log N + 2 * Real.log x) ≤ (1 + Real.log N) * (3 * x ^ 2) := by nlinarith
      have hexp : Real.exp (-x ^ 2 / 2) ≤ Real.exp (-x / 2) := Real.exp_le_exp.2 (by linarith)
      unfold gaussDensity
      calc Real.exp (-x ^ 2 / 2) / Real.sqrt (2 * Real.pi) *
            |f (N * x ^ 2) - (A * (Real.log N + 2 * Real.log x) ^ 2 +
              B * (Real.log N + 2 * Real.log x) + C) / (Real.sqrt N * x)|
          ≤ Real.exp (-x / 2) / Real.sqrt (2 * Real.pi) *
            (8 * ((1 + Real.log N) * (3 * x ^ 2)) / (N * x ^ 2)) := by
            refine mul_le_mul (div_le_div_of_nonneg_right hexp hs.le) (hbd.trans ?_) (abs_nonneg _)
              (by positivity)
            gcongr
        _ = 24 * (1 + Real.log N) / (Real.sqrt (2 * Real.pi) * N) * Real.exp (-x / 2) := by
            field_simp
            ring

/-- ★★ **Three-term data at depth four** from the depth-three rate: with `A₃ = 1/(4π)`,
`B₃ = (2 log 2 − γ)/π`, `C₃ = depthThreeConst`,
`A₄ = A₃/(3s)`, `B₄ = (B₃/2 + 2 A₃ R₀)/s`, `C₄ = (C₃ + 2 B₃ R₀ + 8 A₃ J)/s`, and a bounded
residual. -/
theorem threeTermData_four : ∃ D : ℝ, 0 ≤ D ∧ ThreeTermData (gaussLaplaceL 4)
    (1 / (4 * Real.pi) / (3 * Real.sqrt (2 * Real.pi)))
    (((2 * Real.log 2 - Real.eulerMascheroniConstant) / Real.pi / 2 +
      2 * (1 / (4 * Real.pi)) * gaussR₀) / Real.sqrt (2 * Real.pi))
    ((depthThreeConst + 2 * ((2 * Real.log 2 - Real.eulerMascheroniConstant) / Real.pi) * gaussR₀ +
      8 * (1 / (4 * Real.pi)) * gaussJlog) / Real.sqrt (2 * Real.pi)) D 0 := by
  set A := 1 / (4 * Real.pi) with hAdef
  set B := (2 * Real.log 2 - Real.eulerMascheroniConstant) / Real.pi with hBdef
  set C := depthThreeConst with hCdef
  have hA : 0 ≤ A := by positivity
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hR0 : 0 ≤ gaussR₀ := by
    unfold gaussR₀
    have := Real.log_two_gt_d9
    have := Real.eulerMascheroniConstant_lt_two_thirds
    linarith
  have hK2 := threeTermK_nonneg 0
  have hK0 := twoTermK_nonneg 0
  -- the depth-three input shape
  have hrate : ∀ t : ℝ, 1 ≤ t →
      |gaussLaplaceL 3 t - (A * (Real.log t) ^ 2 + B * Real.log t + C) / Real.sqrt t| ≤
        8 * (1 + Real.log t) / t := by
    intro t ht
    have ht0 : 0 < t := by linarith
    have hst : 0 < Real.sqrt t := Real.sqrt_pos.2 ht0
    have h := gaussLaplaceL_three_rate ht
    rw [show gaussLaplaceL 3 t - (A * (Real.log t) ^ 2 + B * Real.log t + C) / Real.sqrt t =
      (Real.sqrt t * gaussLaplaceL 3 t - ((Real.log t) ^ 2 / (4 * Real.pi) +
        (2 * Real.log 2 - Real.eulerMascheroniConstant) / Real.pi * Real.log t +
        depthThreeConst)) / Real.sqrt t by
        rw [hAdef, hBdef, hCdef]; field_simp, abs_div, abs_of_pos hst,
      div_le_div_iff₀ hst ht0]
    have := Real.mul_self_sqrt ht0.le
    have h1 : 0 ≤ 1 + Real.log t := by linarith [Real.log_nonneg ht]
    calc |Real.sqrt t * gaussLaplaceL 3 t - ((Real.log t) ^ 2 / (4 * Real.pi) +
          (2 * Real.log 2 - Real.eulerMascheroniConstant) / Real.pi * Real.log t +
          depthThreeConst)| * t
        ≤ 8 * (1 + Real.log t) / Real.sqrt t * t := mul_le_mul_of_nonneg_right h ht0.le
      _ = 8 * (1 + Real.log t) * Real.sqrt t := by
          rw [div_mul_eq_mul_div, div_eq_iff hst.ne']
          linear_combination (8 * (1 + Real.log t)) * this.symm
  refine ⟨(2 + 2 * (A * (threeTermK 0 + 6) + |B| * (twoTermK 0 + 1) + |C| / 2) + 336 +
    2 * |C| * gaussR₀) / Real.sqrt (2 * Real.pi), by positivity, ?_⟩
  refine ⟨by positivity, by positivity, fun t _ => gaussLaplaceL_nonneg _ t,
    fun t ht => gaussLaplaceL_le_one _ ht, fun N hN => ?_⟩
  simp only [zero_add, pow_zero, pow_one, mul_one]
  have hN0 : 0 < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have ha0 : 0 < 1 / Real.sqrt N := by positivity
  have ha1 : 1 / Real.sqrt N ≤ 1 := by rw [div_le_one hsN]; exact Real.one_le_sqrt.2 hN
  have hℓ : 0 ≤ Real.log N := Real.log_nonneg hN
  have hs2 : 2 ≤ Real.sqrt (2 * Real.pi) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]; nlinarith [Real.pi_gt_three]
  have hint := integrable_density_mul_gaussLaplaceL 3 hN0.le
  have hZ4 : gaussLaplaceL 4 N = ∫ x, gaussDensity x * gaussLaplaceL 3 (N * x ^ 2) :=
    gaussLaplaceL_succ_scalar 3 hN0.le
  rw [hZ4]
  -- evenness and the split
  have heven : ∫ x, gaussDensity x * gaussLaplaceL 3 (N * x ^ 2) =
      2 * ∫ x in Ioi (0 : ℝ), gaussDensity x * gaussLaplaceL 3 (N * x ^ 2) := by
    rw [← integral_comp_abs (f := fun x => gaussDensity x * gaussLaplaceL 3 (N * x ^ 2))]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [gaussDensity, sq_abs]
  have hsplit : ∫ x in Ioi (0 : ℝ), gaussDensity x * gaussLaplaceL 3 (N * x ^ 2) =
      (∫ x in Ioc (0 : ℝ) (1 / Real.sqrt N), gaussDensity x * gaussLaplaceL 3 (N * x ^ 2)) +
        ∫ x in Ioi (1 / Real.sqrt N), gaussDensity x * gaussLaplaceL 3 (N * x ^ 2) := by
    rw [← Ioc_union_Ioi_eq_Ioi ha0.le,
      setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hint.integrableOn
        hint.integrableOn]
  set Q : ℝ → ℝ := fun x => A * (Real.log N + 2 * Real.log x) ^ 2 +
    B * (Real.log N + 2 * Real.log x) + C with hQ
  have hQint1 : IntegrableOn (fun x : ℝ => 1 / Real.sqrt (2 * Real.pi) * (Q x / (Real.sqrt N * x)))
      (Ioc (1 / Real.sqrt N) 1) := by
    have e : ∀ x : ℝ, 1 / Real.sqrt (2 * Real.pi) * (Q x / (Real.sqrt N * x)) =
        A / (Real.sqrt (2 * Real.pi) * Real.sqrt N) * ((Real.log N + 2 * Real.log x) ^ 2 / x) +
        B / (Real.sqrt (2 * Real.pi) * Real.sqrt N) * ((Real.log N + 2 * Real.log x) ^ 1 / x) +
        C / (Real.sqrt (2 * Real.pi) * Real.sqrt N) * ((Real.log N + 2 * Real.log x) ^ 0 / x) := by
      intro x; simp only [hQ]; ring
    simp_rw [e]
    have h2 := ((intervalIntegrable_iff_integrableOn_Ioc_of_le ha1).1
      (intervalIntegrable_pow_log_div (Real.log N) 2 ha0 ha1)).const_mul
      (A / (Real.sqrt (2 * Real.pi) * Real.sqrt N))
    have h1 := ((intervalIntegrable_iff_integrableOn_Ioc_of_le ha1).1
      (intervalIntegrable_pow_log_div (Real.log N) 1 ha0 ha1)).const_mul
      (B / (Real.sqrt (2 * Real.pi) * Real.sqrt N))
    have h0 := ((intervalIntegrable_iff_integrableOn_Ioc_of_le ha1).1
      (intervalIntegrable_pow_log_div (Real.log N) 0 ha0 ha1)).const_mul
      (C / (Real.sqrt (2 * Real.pi) * Real.sqrt N))
    have h21 : IntegrableOn (fun x : ℝ =>
        A / (Real.sqrt (2 * Real.pi) * Real.sqrt N) * ((Real.log N + 2 * Real.log x) ^ 2 / x) +
        B / (Real.sqrt (2 * Real.pi) * Real.sqrt N) * ((Real.log N + 2 * Real.log x) ^ 1 / x))
        (Ioc (1 / Real.sqrt N) 1) := h2.add h1
    exact h21.add h0
  have hQind : IntegrableOn ((Ioc (1 / Real.sqrt N) 1).indicator
      (fun x : ℝ => 1 / Real.sqrt (2 * Real.pi) * (Q x / (Real.sqrt N * x))))
      (Ioi (1 / Real.sqrt N)) :=
    (hQint1.integrable_indicator measurableSet_Ioc).integrableOn
  have hQh : IntegrableOn (fun x : ℝ => 1 / Real.sqrt (2 * Real.pi) *
      (gaussH x * Q x / (Real.sqrt N * x))) (Ioi (1 / Real.sqrt N)) := by
    have e : ∀ x : ℝ, 1 / Real.sqrt (2 * Real.pi) * (gaussH x * Q x / (Real.sqrt N * x)) =
        A / (Real.sqrt (2 * Real.pi) * Real.sqrt N) *
          (gaussH x * (Real.log N + 2 * Real.log x) ^ 2 / x) +
        B / (Real.sqrt (2 * Real.pi) * Real.sqrt N) *
          (gaussH x * (Real.log N + 2 * Real.log x) ^ 1 / x) +
        C / (Real.sqrt (2 * Real.pi) * Real.sqrt N) * (gaussH x / x) := by
      intro x; simp only [hQ]; ring
    simp_rw [e]
    have h2 := (integrableOn_gaussH_pow 2 (Real.log N) ha0 ha1).const_mul
      (A / (Real.sqrt (2 * Real.pi) * Real.sqrt N))
    have h1 := (integrableOn_gaussH_pow 1 (Real.log N) ha0 ha1).const_mul
      (B / (Real.sqrt (2 * Real.pi) * Real.sqrt N))
    have h0 := (integrableOn_gaussH_div.mono_set (Ioi_subset_Ioi ha0.le)).const_mul
      (C / (Real.sqrt (2 * Real.pi) * Real.sqrt N))
    have h21 : IntegrableOn (fun x : ℝ =>
        A / (Real.sqrt (2 * Real.pi) * Real.sqrt N) *
          (gaussH x * (Real.log N + 2 * Real.log x) ^ 2 / x) +
        B / (Real.sqrt (2 * Real.pi) * Real.sqrt N) *
          (gaussH x * (Real.log N + 2 * Real.log x) ^ 1 / x)) (Ioi (1 / Real.sqrt N)) :=
      h2.add h1
    exact h21.add h0
  have hgQ : ∀ x ∈ Ioi (1 / Real.sqrt N), gaussDensity x * (Q x / (Real.sqrt N * x)) =
      (Ioc (1 / Real.sqrt N) 1).indicator
        (fun x : ℝ => 1 / Real.sqrt (2 * Real.pi) * (Q x / (Real.sqrt N * x))) x +
      1 / Real.sqrt (2 * Real.pi) * (gaussH x * Q x / (Real.sqrt N * x)) := by
    intro x hx
    rw [gaussDensity_eq_indicator_add]
    by_cases h1 : x ≤ 1
    · have hm : x ∈ Ioc (1 / Real.sqrt N) 1 := ⟨hx, h1⟩
      have hm' : x ∈ Ioc (0 : ℝ) 1 := ⟨lt_trans ha0 hx, h1⟩
      rw [indicator_of_mem hm, indicator_of_mem hm', Pi.one_apply]
      ring
    · have h1' := not_le.1 h1
      rw [indicator_of_notMem (fun hm => absurd hm.2 (not_le.2 h1')),
        indicator_of_notMem (fun hm => absurd hm.2 (not_le.2 h1'))]
      ring
  have hgQint : IntegrableOn (fun x : ℝ => gaussDensity x * (Q x / (Real.sqrt N * x)))
      (Ioi (1 / Real.sqrt N)) :=
    (hQind.add hQh).congr_fun (fun x hx => (hgQ x hx).symm) measurableSet_Ioi
  have hmid : ∫ x in Ioi (1 / Real.sqrt N), gaussDensity x * gaussLaplaceL 3 (N * x ^ 2) =
      (∫ x in Ioc (1 / Real.sqrt N) 1, 1 / Real.sqrt (2 * Real.pi) * (Q x / (Real.sqrt N * x))) +
      (∫ x in Ioi (1 / Real.sqrt N), 1 / Real.sqrt (2 * Real.pi) *
        (gaussH x * Q x / (Real.sqrt N * x))) +
      ∫ x in Ioi (1 / Real.sqrt N), (gaussDensity x * gaussLaplaceL 3 (N * x ^ 2) -
        gaussDensity x * (Q x / (Real.sqrt N * x))) := by
    rw [integral_sub hint.integrableOn hgQint, setIntegral_congr_fun measurableSet_Ioi hgQ,
      integral_add hQind hQh, setIntegral_indicator measurableSet_Ioc,
      show Ioi (1 / Real.sqrt N) ∩ Ioc (1 / Real.sqrt N) 1 = Ioc (1 / Real.sqrt N) 1 from
        inter_eq_right.2 fun x hx => hx.1]
    ring
  -- the inner piece
  have h0 : |∫ x in Ioc (0 : ℝ) (1 / Real.sqrt N), gaussDensity x * gaussLaplaceL 3 (N * x ^ 2)| ≤
      1 / Real.sqrt (2 * Real.pi) * (1 / Real.sqrt N) := by
    have hb := norm_setIntegral_le_of_norm_le_const (μ := volume)
      (s := Ioc (0 : ℝ) (1 / Real.sqrt N))
      (f := fun x => gaussDensity x * gaussLaplaceL 3 (N * x ^ 2))
      (C := 1 / Real.sqrt (2 * Real.pi))
      measure_Ioc_lt_top (fun x _ => by
        have h0 := gaussLaplaceL_nonneg 3 (N * x ^ 2)
        have h1 := gaussLaplaceL_le_one 3 (by positivity : (0 : ℝ) ≤ N * x ^ 2)
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (gaussDensity_nonneg _) h0)]
        calc gaussDensity x * gaussLaplaceL 3 (N * x ^ 2) ≤ 1 / Real.sqrt (2 * Real.pi) * 1 :=
              mul_le_mul (gaussDensity_le x) h1 h0 (by positivity)
          _ = 1 / Real.sqrt (2 * Real.pi) := mul_one _)
    rw [Real.norm_eq_abs, measureReal_def, Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal ha0.le]
      at hb
    exact hb
  have hP1 := base_flat_main A B C hN
  have hP2 := base_h_main A B C hN hA
  have hE := base_err_le A B C hrate hN
  simp only [hQ] at hmid hP1 hP2 hE
  rw [heven, hsplit, hmid, hP1]
  set I₀ := ∫ x in Ioc (0 : ℝ) (1 / Real.sqrt N), gaussDensity x * gaussLaplaceL 3 (N * x ^ 2)
    with hI₀
  set P2 := ∫ x in Ioi (1 / Real.sqrt N), 1 / Real.sqrt (2 * Real.pi) *
    (gaussH x * (A * (Real.log N + 2 * Real.log x) ^ 2 + B * (Real.log N + 2 * Real.log x) + C) /
      (Real.sqrt N * x)) with hP2def
  set E := ∫ x in Ioi (1 / Real.sqrt N), (gaussDensity x * gaussLaplaceL 3 (N * x ^ 2) -
    gaussDensity x * ((A * (Real.log N + 2 * Real.log x) ^ 2 + B * (Real.log N + 2 * Real.log x) +
      C) / (Real.sqrt N * x))) with hEdef
  clear_value I₀ P2 E
  clear hI₀ hP2def hEdef hmid hsplit heven hgQint hgQ hQh hQind hQint1 hint hrate
  set ℓ := Real.log N with hℓdef
  clear_value ℓ
  set K2 := threeTermK 0 with hK2def
  set K0 := twoTermK 0 with hK0def
  set R := gaussR₀ with hRdef
  set J := gaussJlog with hJdef
  set s := Real.sqrt (2 * Real.pi) with hsdef
  clear_value K2 K0 R J s A B C
  clear hK2def hK0def hRdef hJdef hℓdef hsdef hAdef hBdef hCdef hQ
  have hkey : 2 * (I₀ + (1 / (s * Real.sqrt N) * (A * ℓ ^ 3 / 6 + B * ℓ ^ 2 / 4 + C * ℓ / 2) +
      P2 + E)) - (A / (3 * s) * ℓ ^ 3 + (B / 2 + 2 * A * R) / s * ℓ ^ 2 +
        (C + 2 * B * R + 8 * A * J) / s * ℓ) / Real.sqrt N =
      2 * I₀ + 2 * (P2 - 1 / (s * Real.sqrt N) * (A * ℓ ^ 2 * R + 4 * A * ℓ * J + B * ℓ * R +
        C * R)) + 2 * E + 2 * C * R / (s * Real.sqrt N) := by
    field_simp
    ring
  rw [hkey]
  have hE' : |E| ≤ 168 / (s * Real.sqrt N) := hE
  have hCR : |2 * C * R / (s * Real.sqrt N)| ≤ 2 * |C| * R / (s * Real.sqrt N) := by
    rw [abs_div, abs_mul, abs_mul, abs_of_pos two_pos, abs_of_nonneg hR0,
      abs_of_pos (mul_pos hs hsN)]
  have hbr := hP2
  calc |2 * I₀ + 2 * (P2 - 1 / (s * Real.sqrt N) * (A * ℓ ^ 2 * R + 4 * A * ℓ * J + B * ℓ * R +
        C * R)) + 2 * E + 2 * C * R / (s * Real.sqrt N)|
      ≤ 2 * |I₀| + 2 * |P2 - 1 / (s * Real.sqrt N) * (A * ℓ ^ 2 * R + 4 * A * ℓ * J + B * ℓ * R +
          C * R)| + 2 * |E| + |2 * C * R / (s * Real.sqrt N)| := by
        have t1 := abs_add_le (2 * I₀) (2 * (P2 - 1 / (s * Real.sqrt N) *
          (A * ℓ ^ 2 * R + 4 * A * ℓ * J + B * ℓ * R + C * R)))
        have t2 := abs_add_le (2 * I₀ + 2 * (P2 - 1 / (s * Real.sqrt N) *
          (A * ℓ ^ 2 * R + 4 * A * ℓ * J + B * ℓ * R + C * R))) (2 * E)
        have t3 := abs_add_le (2 * I₀ + 2 * (P2 - 1 / (s * Real.sqrt N) *
          (A * ℓ ^ 2 * R + 4 * A * ℓ * J + B * ℓ * R + C * R)) + 2 * E)
          (2 * C * R / (s * Real.sqrt N))
        have t1' : |2 * I₀| = 2 * |I₀| := by rw [abs_mul, abs_of_pos two_pos]
        have t1'' : |2 * (P2 - 1 / (s * Real.sqrt N) *
            (A * ℓ ^ 2 * R + 4 * A * ℓ * J + B * ℓ * R + C * R))| =
            2 * |P2 - 1 / (s * Real.sqrt N) *
              (A * ℓ ^ 2 * R + 4 * A * ℓ * J + B * ℓ * R + C * R)| := by
          rw [abs_mul, abs_of_pos two_pos]
        have t4 : |2 * E| = 2 * |E| := by rw [abs_mul, abs_of_pos two_pos]
        linarith
    _ ≤ 2 * (1 / s * (1 / Real.sqrt N)) + 2 * (1 / (s * Real.sqrt N) *
          (A * (K2 + 6) + |B| * (K0 + 1) + |C| / 2)) + 2 * (168 / (s * Real.sqrt N)) +
          2 * |C| * R / (s * Real.sqrt N) := by
        gcongr
    _ = (2 + 2 * (A * (K2 + 6) + |B| * (K0 + 1) + |C| / 2) + 336 + 2 * |C| * R) / s /
          Real.sqrt N := by
        field_simp
        ring

/-! ### The coefficients at every depth -/

/-- `A_{m+4} = 1/((m+3)! s^{m+3})`. -/
noncomputable def gaussCoeffA (m : ℕ) : ℝ :=
  1 / ((m + 3).factorial * Real.sqrt (2 * Real.pi) ^ (m + 3))

/-- `B_{m+4} = ((m+5) log 2 − (m+3) γ)/((m+2)! s^{m+3})`. -/
noncomputable def gaussCoeffB (m : ℕ) : ℝ :=
  ((m + 5) * Real.log 2 - (m + 3) * Real.eulerMascheroniConstant) /
    ((m + 2).factorial * Real.sqrt (2 * Real.pi) ^ (m + 3))

/-- The third coefficient `C_{m+4}` by the recursion
`C₄ = (C₃ + 2 B₃ R₀ + 8 A₃ J)/s`, `C_{L+1} = (C_L/(L−2) + 2 B_L R₀ + 4(L−1) A_L J)/s`. -/
noncomputable def thirdCoeff : ℕ → ℝ
  | 0 => (depthThreeConst +
      2 * ((2 * Real.log 2 - Real.eulerMascheroniConstant) / Real.pi) * gaussR₀ +
      8 * (1 / (4 * Real.pi)) * gaussJlog) / Real.sqrt (2 * Real.pi)
  | m + 1 => (thirdCoeff m / (m + 2) + 2 * gaussCoeffB m * gaussR₀ +
      4 * (m + 3) * gaussCoeffA m * gaussJlog) / Real.sqrt (2 * Real.pi)

/-- ★★★ **Three-term data at every depth**: for every `m` there is `D_m` with
`|Z_{m+4}(N) − (A (log N)^{m+3} + B (log N)^{m+2} + C (log N)^{m+1})/√N| ≤ D_m (1 + log N)^m/√N`,
`A = A_{m+4}`, `B = B_{m+4}`, `C = thirdCoeff m`. -/
theorem gaussLaplaceL_three_term_bound (m : ℕ) : ∃ D : ℝ, 0 ≤ D ∧
    ThreeTermData (gaussLaplaceL (m + 4)) (gaussCoeffA m) (gaussCoeffB m) (thirdCoeff m) D m := by
  induction m with
  | zero =>
    obtain ⟨D, hD, hd⟩ := threeTermData_four
    refine ⟨D, hD, ?_⟩
    have hsq : Real.sqrt (2 * Real.pi) ^ 2 = 2 * Real.pi := Real.sq_sqrt (by positivity)
    have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
    have hA : gaussCoeffA 0 = 1 / (4 * Real.pi) / (3 * Real.sqrt (2 * Real.pi)) := by
      unfold gaussCoeffA
      rw [zero_add, show Real.sqrt (2 * Real.pi) ^ 3 = Real.sqrt (2 * Real.pi) ^ 2 *
        Real.sqrt (2 * Real.pi) by ring, hsq]
      norm_num [Nat.factorial]
      have := Real.pi_pos
      field_simp
      ring
    have hB : gaussCoeffB 0 = ((2 * Real.log 2 - Real.eulerMascheroniConstant) / Real.pi / 2 +
        2 * (1 / (4 * Real.pi)) * gaussR₀) / Real.sqrt (2 * Real.pi) := by
      unfold gaussCoeffB gaussR₀
      rw [zero_add, show Real.sqrt (2 * Real.pi) ^ 3 = Real.sqrt (2 * Real.pi) ^ 2 *
        Real.sqrt (2 * Real.pi) by ring, hsq]
      norm_num [Nat.factorial]
      have := Real.pi_pos
      field_simp
      ring
    rw [hA, hB]
    exact hd
  | succ m ih =>
    obtain ⟨D, hD, hd⟩ := ih
    obtain ⟨D', hD', hstep⟩ := threeTermStep_bound hd
    refine ⟨D', hD', ?_⟩
    have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
    have hA' : gaussCoeffA (m + 1) = gaussCoeffA m / ((m + 4) * Real.sqrt (2 * Real.pi)) := by
      unfold gaussCoeffA
      rw [show m + 1 + 3 = (m + 3) + 1 by ring, Nat.factorial_succ]
      push_cast
      field_simp
      ring
    have hB' : gaussCoeffB (m + 1) = (gaussCoeffB m / (m + 3) + 2 * gaussCoeffA m * gaussR₀) /
        Real.sqrt (2 * Real.pi) := by
      unfold gaussCoeffB gaussCoeffA gaussR₀
      rw [show m + 1 + 2 = (m + 2) + 1 by ring, show m + 1 + 3 = (m + 3) + 1 by ring,
        Nat.factorial_succ, Nat.factorial_succ]
      push_cast
      field_simp
      ring
    have hC' : thirdCoeff (m + 1) = (thirdCoeff m / (m + 2) + 2 * gaussCoeffB m * gaussR₀ +
        4 * (m + 3) * gaussCoeffA m * gaussJlog) / Real.sqrt (2 * Real.pi) := rfl
    refine ⟨by rw [hA']; exact div_nonneg hd.A_nonneg (by positivity), hD',
      fun t _ => gaussLaplaceL_nonneg _ t, fun t ht => gaussLaplaceL_le_one _ ht, fun t ht => ?_⟩
    have hint := integrable_density_mul_gaussLaplaceL (m + 4) (by linarith : (0 : ℝ) ≤ t)
    have h := hstep t ht hint
    rw [← gaussLaplaceL_succ_scalar (m + 4) (by linarith)] at h
    rw [hA', hB', hC']
    exact h

/-- ★★★ **The third coefficient at every depth**:
`(√N Z_{m+4}(N) − A (log N)^{m+3} − B (log N)^{m+2})/(log N)^{m+1} → C_{m+4} = thirdCoeff m`. -/
theorem gaussLaplaceL_third_coeff (m : ℕ) :
    Tendsto (fun N : ℝ => (Real.sqrt N * gaussLaplaceL (m + 4) N -
      gaussCoeffA m * (Real.log N) ^ (m + 3) - gaussCoeffB m * (Real.log N) ^ (m + 2)) /
        (Real.log N) ^ (m + 1)) atTop (𝓝 (thirdCoeff m)) := by
  obtain ⟨D, hD, hd⟩ := gaussLaplaceL_three_term_bound m
  set A := gaussCoeffA m with hA
  set B := gaussCoeffB m with hB
  set C := thirdCoeff m with hC
  clear_value A B C
  have hbound : ∀ᶠ N : ℝ in atTop,
      |(Real.sqrt N * gaussLaplaceL (m + 4) N - A * (Real.log N) ^ (m + 3) -
        B * (Real.log N) ^ (m + 2)) / (Real.log N) ^ (m + 1) - C| ≤ D * 2 ^ m / Real.log N := by
    filter_upwards [eventually_ge_atTop (3 : ℝ)] with N hN3
    have hN : 1 ≤ N := by linarith
    have hN0 : 0 < N := by linarith
    have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
    have hℓ : 1 ≤ Real.log N := by
      rw [← Real.log_exp 1]
      exact Real.log_le_log (Real.exp_pos _) (by linarith [Real.exp_one_lt_d9])
    have hℓ0 : 0 < Real.log N := by linarith
    have h := hd.bound N hN
    have e : (Real.sqrt N * gaussLaplaceL (m + 4) N - A * (Real.log N) ^ (m + 3) -
        B * (Real.log N) ^ (m + 2)) / (Real.log N) ^ (m + 1) - C =
        (Real.sqrt N / (Real.log N) ^ (m + 1)) * (gaussLaplaceL (m + 4) N -
          (A * (Real.log N) ^ (m + 3) + B * (Real.log N) ^ (m + 2) + C * (Real.log N) ^ (m + 1)) /
            Real.sqrt N) := by
      field_simp
      ring
    rw [e, abs_mul, abs_of_pos (by positivity)]
    have hpow : (1 + Real.log N) ^ m ≤ (2 * Real.log N) ^ m :=
      pow_le_pow_left₀ (by linarith) (by linarith) m
    calc Real.sqrt N / (Real.log N) ^ (m + 1) *
          |gaussLaplaceL (m + 4) N - (A * (Real.log N) ^ (m + 3) + B * (Real.log N) ^ (m + 2) +
            C * (Real.log N) ^ (m + 1)) / Real.sqrt N|
        ≤ Real.sqrt N / (Real.log N) ^ (m + 1) * (D * (1 + Real.log N) ^ m / Real.sqrt N) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = D * (1 + Real.log N) ^ m / (Real.log N) ^ (m + 1) := by field_simp
      _ ≤ D * (2 * Real.log N) ^ m / (Real.log N) ^ (m + 1) := by gcongr
      _ = D * 2 ^ m / Real.log N := by
          rw [mul_pow, pow_succ]
          field_simp
  have hlim : Tendsto (fun N : ℝ => D * 2 ^ m / Real.log N) atTop (𝓝 0) := by
    have := (tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop).const_mul (D * 2 ^ m)
    simpa [div_eq_mul_inv] using this
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun N => norm_nonneg _) ?_ hlim
  filter_upwards [hbound] with N hN
  rw [Real.norm_eq_abs]
  exact hN

end Grammar
