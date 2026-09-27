/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.GaussianDepthFourRate

/-!
# The depth-four constant with the linear-log rate

`|√N Z₄ − A₄ℓ³ − B₄ℓ² − C₄ℓ − D₄| ≤ K (1 + ℓ)/√N` for `N ≥ 1`
(★★★ `gaussLaplaceL_four_constant_rate_linear`).  DCLII's assembly with a single change:
the `j = 0` cutoff moment is bounded by DCXXXI's `|∫₀^a h/x| ≤ a²/2`
(`abs_integral_gaussH_div_Ioc_le`) instead of the generic `(j+1)^j a/2`, so the quadratic
cutoff product `ℓ² · E₀` costs `ℓ²/(2N) ≤ ℓ/√N` (from `log N ≤ 2√N`) and every term is
`O((1 + ℓ)/√N)`.  No combined-cutoff refactor is needed
(Astra round 17, target 2).  Examples_slop §2.
Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

/-- `log N ≤ 2 √N` for `N ≥ 1`. -/
theorem log_le_two_mul_sqrt {N : ℝ} (hN : 1 ≤ N) : Real.log N ≤ 2 * Real.sqrt N := by
  have hN0 : 0 < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have h := Real.log_le_sub_one_of_pos hsN
  rw [Real.log_sqrt hN0.le] at h
  linarith

set_option maxHeartbeats 1600000 in
-- the exact remainder identity and the long `calc` exceed the default heartbeat budget
/-- ★★★ **The depth-four constant with the linear-log rate**: there is `K ≥ 0` with
`|√N Z₄ − A₄ℓ³ − B₄ℓ² − C₄ℓ − D₄| ≤ K(1 + ℓ)/√N` for all `N ≥ 1`. -/
theorem gaussLaplaceL_four_constant_rate_linear :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℝ, 1 ≤ N →
      |Real.sqrt N * gaussLaplaceL 4 N - gaussCoeffA 0 * (Real.log N) ^ 3 -
        gaussCoeffB 0 * (Real.log N) ^ 2 - thirdCoeff 0 * Real.log N - depthFourConst| ≤
        K * (1 + Real.log N) / Real.sqrt N := by
  set s := Real.sqrt (2 * Real.pi) with hs_def
  have hs : 0 < s := Real.sqrt_pos.2 (by positivity)
  set A₃ : ℝ := 1 / (4 * Real.pi) with hA₃
  set B₃ : ℝ := (2 * Real.log 2 - Real.eulerMascheroniConstant) / Real.pi with hB₃
  set C₃ : ℝ := depthThreeConst with hC₃
  have hA₃0 : 0 < A₃ := by rw [hA₃]; positivity
  refine ⟨2 / s * (1 / 2 + 4 + 24 + (A₃ + |B₃| / 2 + |C₃| / 2) + (4 * A₃ + 2 * |B₃|) +
    4 * A₃ * (9 / 2)),
    by positivity, fun N hN => ?_⟩
  have hN0 : 0 < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have hsN1 : 1 ≤ Real.sqrt N := Real.one_le_sqrt.2 hN
  have ha0 : 0 ≤ 1 / Real.sqrt N := by positivity
  have ha1 : 1 / Real.sqrt N ≤ 1 := by rw [div_le_one hsN]; exact Real.one_le_sqrt.2 hN
  have hℓ : 0 ≤ Real.log N := Real.log_nonneg hN
  have hℓX : Real.log N * (1 / Real.sqrt N) ≤ 2 := by
    rw [mul_one_div, div_le_iff₀ hsN]
    exact log_le_two_mul_sqrt hN
  set ℓ := Real.log N with hℓdef
  -- the pieces
  have hid := sqrt_mul_gaussLaplaceL_four_sub_eq hN
  have hres := residual_term_bound hN
  have he0 : |∫ x in Ioc (0 : ℝ) (1 / Real.sqrt N), gaussH x / x| ≤
      1 / 2 * (1 / Real.sqrt N * (1 / Real.sqrt N)) :=
    (abs_integral_gaussH_div_Ioc_le ha0 ha1).trans (le_of_eq (by ring))
  have he1 : |∫ x in Ioc (0 : ℝ) (1 / Real.sqrt N), gaussH x * Real.log x / x| ≤
      1 * (1 / Real.sqrt N) := by
    have := abs_integral_gaussH_log_pow_Ioc_le 1 ha0 ha1
    simp only [pow_one] at this
    convert this using 2
    try norm_num
  have he2 : |∫ x in Ioc (0 : ℝ) (1 / Real.sqrt N), gaussH x * Real.log x ^ 2 / x| ≤
      9 / 2 * (1 / Real.sqrt N) := by
    have := abs_integral_gaussH_log_pow_Ioc_le 2 ha0 ha1
    convert this using 2
    try norm_num
  set Q := ∫ v in Ioi (0 : ℝ), gaussDensity (v / Real.sqrt N) * depthFourQ v with hQ
  set E0 := ∫ x in Ioc (0 : ℝ) (1 / Real.sqrt N), gaussH x / x with hE0
  set E1 := ∫ x in Ioc (0 : ℝ) (1 / Real.sqrt N), gaussH x * Real.log x / x with hE1
  set E2 := ∫ x in Ioc (0 : ℝ) (1 / Real.sqrt N), gaussH x * Real.log x ^ 2 / x with hE2
  rw [hid]
  -- the constant cancels the full moments
  have hX : 2 * Q + 2 / s * ((ℓ ^ 2 / (4 * Real.pi) + B₃ * ℓ + C₃) * -E0 +
      (4 * ℓ / (4 * Real.pi) + 2 * B₃) * -E1 + 4 * (1 / (4 * Real.pi)) * (gaussJlog2 - E2) +
      C₃ * gaussR₀ + 2 * B₃ * gaussJlog) - depthFourConst =
      (2 * Q - 2 / s * depthFourQint) +
        2 / s * (-((A₃ * ℓ ^ 2 + B₃ * ℓ + C₃) * E0) - (4 * A₃ * ℓ + 2 * B₃) * E1 -
          4 * A₃ * E2) := by
    unfold depthFourConst
    simp only [hA₃, hB₃, hC₃]
    ring
  rw [hX]
  -- bounds on the three cutoff products
  have hc0 : |(A₃ * ℓ ^ 2 + B₃ * ℓ + C₃) * E0| ≤
      (A₃ * ℓ ^ 2 + |B₃| * ℓ + |C₃|) *
        (1 / 2 * (1 / Real.sqrt N * (1 / Real.sqrt N))) := by
    rw [abs_mul]
    refine mul_le_mul ?_ he0 (abs_nonneg _) (by positivity)
    calc |A₃ * ℓ ^ 2 + B₃ * ℓ + C₃| ≤ |A₃ * ℓ ^ 2 + B₃ * ℓ| + |C₃| := abs_add_le _ _
      _ ≤ |A₃ * ℓ ^ 2| + |B₃ * ℓ| + |C₃| := by gcongr; exact abs_add_le _ _
      _ = A₃ * ℓ ^ 2 + |B₃| * ℓ + |C₃| := by
          rw [abs_mul, abs_mul, abs_of_pos hA₃0, abs_pow, abs_of_nonneg hℓ]
  have hc1 : |(4 * A₃ * ℓ + 2 * B₃) * E1| ≤ (4 * A₃ * ℓ + 2 * |B₃|) * (1 * (1 / Real.sqrt N)) := by
    rw [abs_mul]
    refine mul_le_mul ?_ he1 (abs_nonneg _) (by positivity)
    calc |4 * A₃ * ℓ + 2 * B₃| ≤ |4 * A₃ * ℓ| + |2 * B₃| := abs_add_le _ _
      _ = 4 * A₃ * ℓ + 2 * |B₃| := by
          rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * A₃ * ℓ), abs_mul, abs_two]
  have hc2 : |4 * A₃ * E2| ≤ 4 * A₃ * (9 / 2 * (1 / Real.sqrt N)) := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 4 * A₃)]
    exact mul_le_mul_of_nonneg_left he2 (by positivity)
  -- elementary comparisons with `(1 + ℓ)/√N`
  have hN1 : 1 / (2 * N) ≤ 1 / 2 * (1 / Real.sqrt N) := by
    rw [show 1 / (2 * N) = 1 / 2 * (1 / N) by ring]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    exact one_div_le_one_div_of_le hsN (by nlinarith [Real.sq_sqrt hN0.le])
  have hB0 : 0 ≤ |B₃| := abs_nonneg _
  have hC0 : 0 ≤ |C₃| := abs_nonneg _
  have hinv : 0 < 1 / Real.sqrt N := by positivity
  set X := 1 / Real.sqrt N with hXdef
  set L := 1 + ℓ with hLdef
  have hL1 : 1 ≤ L := by rw [hLdef]; linarith
  have hres' : |2 * Q - 2 / s * depthFourQint| ≤
      2 / s * (1 / (2 * N) + 4 * L * X + 8 * (3 + ℓ) * X) := by
    refine hres.trans (le_of_eq ?_)
    rw [hXdef, hLdef]
    ring
  have fX : X ≤ L * X := by
    have := mul_le_mul_of_nonneg_right hL1 hinv.le; rwa [one_mul] at this
  have f1 : 1 / (2 * N) ≤ 1 / 2 * (L * X) := hN1.trans (by linarith)
  have f3 : (3 + ℓ) * X ≤ 3 * (L * X) := by
    rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (by rw [hLdef]; linarith) hinv.le
  have fℓ : ℓ * X ≤ L * X := mul_le_mul_of_nonneg_right (by rw [hLdef]; linarith) hinv.le
  -- the quadratic cutoff product: `ℓ² X² / 2 ≤ ℓ X ≤ L X`
  have f4 : ℓ ^ 2 * (1 / 2 * (X * X)) ≤ L * X := by
    have h1 : ℓ ^ 2 * (1 / 2 * (X * X)) = (ℓ * X) * (ℓ * X) / 2 := by ring
    rw [h1]
    have hℓX0 : 0 ≤ ℓ * X := by positivity
    nlinarith [hℓX, fℓ]
  have f5 : ℓ * (1 / 2 * (X * X)) ≤ 1 / 2 * (L * X) := by
    have h1 : ℓ * (1 / 2 * (X * X)) = 1 / 2 * ((ℓ * X) * X) := by ring
    rw [h1]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    calc (ℓ * X) * X ≤ (ℓ * X) * 1 := mul_le_mul_of_nonneg_left ha1 (by positivity)
      _ = ℓ * X := mul_one _
      _ ≤ L * X := fℓ
  have f6 : 1 / 2 * (X * X) ≤ 1 / 2 * (L * X) := by
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    calc X * X ≤ X * 1 := mul_le_mul_of_nonneg_left ha1 hinv.le
      _ = X := mul_one _
      _ ≤ L * X := fX
  have g4 := mul_le_mul_of_nonneg_left f4 hA₃0.le
  have g5 := mul_le_mul_of_nonneg_left f5 hB0
  have g6 := mul_le_mul_of_nonneg_left f6 hC0
  have g7 := mul_le_mul_of_nonneg_left fℓ hA₃0.le
  have g8 := mul_le_mul_of_nonneg_left fX hB0
  have g9 := mul_le_mul_of_nonneg_left fX hA₃0.le
  have key : 1 / (2 * N) + 4 * L * X + 8 * (3 + ℓ) * X +
      ((A₃ * ℓ ^ 2 + |B₃| * ℓ + |C₃|) * (1 / 2 * (X * X)) + (4 * A₃ * ℓ + 2 * |B₃|) * (1 * X) +
        4 * A₃ * (9 / 2 * X)) ≤
      (1 / 2 + 4 + 24 + (A₃ + |B₃| / 2 + |C₃| / 2) + (4 * A₃ + 2 * |B₃|) + 4 * A₃ * (9 / 2)) *
        (L * X) := by
    nlinarith [f1, f3, g4, g5, g6, g7, g8, g9]
  calc |(2 * Q - 2 / s * depthFourQint) + 2 / s * (-((A₃ * ℓ ^ 2 + B₃ * ℓ + C₃) * E0) -
        (4 * A₃ * ℓ + 2 * B₃) * E1 - 4 * A₃ * E2)|
      ≤ |2 * Q - 2 / s * depthFourQint| + 2 / s * (|(A₃ * ℓ ^ 2 + B₃ * ℓ + C₃) * E0| +
          |(4 * A₃ * ℓ + 2 * B₃) * E1| + |4 * A₃ * E2|) := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 / s)]
        refine add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ (by positivity : (0 : ℝ) ≤ 2 / s))
        calc |-((A₃ * ℓ ^ 2 + B₃ * ℓ + C₃) * E0) - (4 * A₃ * ℓ + 2 * B₃) * E1 - 4 * A₃ * E2|
            ≤ |-((A₃ * ℓ ^ 2 + B₃ * ℓ + C₃) * E0) - (4 * A₃ * ℓ + 2 * B₃) * E1| +
              |4 * A₃ * E2| := abs_sub _ _
          _ ≤ |-((A₃ * ℓ ^ 2 + B₃ * ℓ + C₃) * E0)| + |(4 * A₃ * ℓ + 2 * B₃) * E1| +
              |4 * A₃ * E2| := by gcongr; exact abs_sub _ _
          _ = _ := by rw [abs_neg]
    _ ≤ 2 / s * (1 / (2 * N) + 4 * L * X + 8 * (3 + ℓ) * X) +
        2 / s * ((A₃ * ℓ ^ 2 + |B₃| * ℓ + |C₃|) * (1 / 2 * (X * X)) +
          (4 * A₃ * ℓ + 2 * |B₃|) * (1 * X) + 4 * A₃ * (9 / 2 * X)) := by
        gcongr
    _ = 2 / s * (1 / (2 * N) + 4 * L * X + 8 * (3 + ℓ) * X +
        ((A₃ * ℓ ^ 2 + |B₃| * ℓ + |C₃|) * (1 / 2 * (X * X)) +
          (4 * A₃ * ℓ + 2 * |B₃|) * (1 * X) + 4 * A₃ * (9 / 2 * X))) := by ring
    _ ≤ 2 / s * ((1 / 2 + 4 + 24 + (A₃ + |B₃| / 2 + |C₃| / 2) + (4 * A₃ + 2 * |B₃|) +
        4 * A₃ * (9 / 2)) * (L * X)) :=
        mul_le_mul_of_nonneg_left key (by positivity : (0 : ℝ) ≤ 2 / s)
    _ = 2 / s * (1 / 2 + 4 + 24 + (A₃ + |B₃| / 2 + |C₃| / 2) + (4 * A₃ + 2 * |B₃|) +
        4 * A₃ * (9 / 2)) * (1 + ℓ) / Real.sqrt N := by
        rw [hLdef, hXdef]
        ring

end Grammar
