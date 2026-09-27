/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.GaussianDepthAll
import Grammar.GaussianDepthTwoExpansion

/-!
# The Gaussian-prior deep linear network at depth three: the leading asymptotic

With the scalar recursion `Z_3(N) = ∫ g(x) Z_2(N x²) dx` (`gaussLaplaceL_three`, from the
conditional reduction of `Grammar.GaussianDepthAll` and Fubini on the pair) and the depth-two
expansion of `Grammar.GaussianDepthTwoExpansion` inserted on `|x| ≥ N^{−1/2}`,

  `|Z_3(N) − (log N)²/(4π√N)| ≤ C (1 + log N)/√N`  for `N ≥ 1`  (★★★ `gaussLaplaceL_three_bound`),

hence `√N Z_3(N)/(log N)² → 1/(4π)` (★★★ `gaussLaplaceL_three_leading`): the leading coefficient
`1/((L−1)!(2π)^{(L−1)/2})` of the note's eq. (dln_gauss) at `L = 3`, proved from the integral
(Astra round-7 target 3; the lower coefficients stay derivations).  Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

/-! ### Elementary facts about the depth-two function -/

theorem gaussLaplace2_zero : gaussLaplace2 0 = 1 := by
  rw [gaussLaplace2_eq_integral le_rfl]
  have e : ∀ x : ℝ, Real.exp (-x ^ 2 / 2) / Real.sqrt (1 + 0 * x ^ 2) =
      Real.exp (-(1 / 2) * x ^ 2) := by
    intro x; simp only [zero_mul, add_zero, Real.sqrt_one, div_one]; congr 1; ring
  simp_rw [e]
  rw [integral_gaussian]
  have : Real.sqrt (Real.pi / (1 / 2)) = Real.sqrt (2 * Real.pi) := by congr 1; ring
  rw [this]
  exact inv_mul_cancel₀ (Real.sqrt_pos.2 (by positivity)).ne'

theorem gaussLaplace2_nonneg {N : ℝ} (hN : 0 ≤ N) : 0 ≤ gaussLaplace2 N := by
  rw [gaussLaplace2_eq_integral hN]
  refine mul_nonneg (by positivity) (integral_nonneg fun x => by positivity)

theorem gaussLaplace2_le_one {N : ℝ} (hN : 0 ≤ N) : gaussLaplace2 N ≤ 1 := by
  rw [← gaussLaplace2_zero]
  unfold gaussLaplace2
  refine integral_mono (integrable_gaussLaplace2 N hN) (integrable_gaussLaplace2 0 le_rfl)
    fun w => ?_
  simp only
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  exact Real.exp_le_exp.2 (by nlinarith [mul_nonneg hN (sq_nonneg (w.1 * w.2))])

/-- The depth-two function as the reduced one-dimensional integral against the density. -/
theorem gaussLaplace2_eq_density_integral {N : ℝ} (hN : 0 ≤ N) :
    gaussLaplace2 N = ∫ y : ℝ, gaussDensity y / Real.sqrt (1 + N * y ^ 2) := by
  rw [gaussLaplace2_eq_integral hN, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [gaussDensity]
  ring

/-! ### The scalar recursion -/

/-- ★★ **The scalar recursion**: `Z_3(N) = ∫ g(x) Z_2(N x²) dx` for `N ≥ 0`. -/
theorem gaussLaplaceL_three {N : ℝ} (hN : 0 ≤ N) :
    gaussLaplaceL 3 N = ∫ x : ℝ, gaussDensity x * gaussLaplace2 (N * x ^ 2) := by
  rw [gaussLaplaceL_succ 2 hN]
  -- transport `Fin 2 → ℝ` to the pair
  have hmp := volume_preserving_finTwoArrow ℝ
  set e := (MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ) with he
  set G : ℝ × ℝ → ℝ := fun p => 1 / Real.sqrt (1 + N * (p.1 * p.2) ^ 2) *
    (gaussDensity p.1 * gaussDensity p.2) with hG
  have hcomp : ∀ b : Fin 2 → ℝ, 1 / Real.sqrt (1 + N * (∏ i, b i) ^ 2) * ∏ i, gaussDensity (b i) =
      G (e b) := by
    intro b
    simp only [hG, he, MeasurableEquiv.finTwoArrow_apply, Fin.prod_univ_two]
  simp_rw [hcomp]
  rw [hmp.integral_comp e.measurableEmbedding G]
  -- Fubini on the pair
  have hg : Integrable gaussDensity := integrable_gaussDensity
  have hprod : Integrable (fun p : ℝ × ℝ => gaussDensity p.1 * gaussDensity p.2)
      (volume.prod volume) := hg.mul_prod hg
  have hint : Integrable G (volume.prod volume) := by
    refine hprod.mono' ?_ ?_
    · refine (Measurable.aestronglyMeasurable ?_)
      simp only [hG]
      have := continuous_gaussDensity
      fun_prop (disch := positivity)
    · refine Eventually.of_forall fun p => ?_
      simp only [hG]
      have h0 : 0 ≤ gaussDensity p.1 * gaussDensity p.2 :=
        mul_nonneg (gaussDensity_nonneg _) (gaussDensity_nonneg _)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have h1 : 1 / Real.sqrt (1 + N * (p.1 * p.2) ^ 2) ≤ 1 := by
        rw [div_le_one (by positivity)]
        exact Real.one_le_sqrt.2 (by nlinarith [mul_nonneg hN (sq_nonneg (p.1 * p.2))])
      exact mul_le_of_le_one_left h0 h1
  rw [Measure.volume_eq_prod, integral_prod _ hint]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [hG]
  rw [gaussLaplace2_eq_density_integral (by positivity), ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  rw [show N * (x * y) ^ 2 = N * x ^ 2 * y ^ 2 by ring]
  ring

/-- The integrand of the scalar recursion is integrable. -/
theorem integrable_density_mul_gaussLaplace2 {N : ℝ} (hN : 0 ≤ N) :
    Integrable fun x : ℝ => gaussDensity x * gaussLaplace2 (N * x ^ 2) := by
  set G : ℝ × ℝ → ℝ := fun p => 1 / Real.sqrt (1 + N * (p.1 * p.2) ^ 2) *
    (gaussDensity p.1 * gaussDensity p.2) with hG
  have hg : Integrable gaussDensity := integrable_gaussDensity
  have hprod : Integrable (fun p : ℝ × ℝ => gaussDensity p.1 * gaussDensity p.2)
      (volume.prod volume) := hg.mul_prod hg
  have hint : Integrable G (volume.prod volume) := by
    refine hprod.mono' ?_ ?_
    · refine (Measurable.aestronglyMeasurable ?_)
      simp only [hG]
      have := continuous_gaussDensity
      fun_prop (disch := positivity)
    · refine Eventually.of_forall fun p => ?_
      simp only [hG]
      have h0 : 0 ≤ gaussDensity p.1 * gaussDensity p.2 :=
        mul_nonneg (gaussDensity_nonneg _) (gaussDensity_nonneg _)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have h1 : 1 / Real.sqrt (1 + N * (p.1 * p.2) ^ 2) ≤ 1 := by
        rw [div_le_one (by positivity)]
        exact Real.one_le_sqrt.2 (by nlinarith [mul_nonneg hN (sq_nonneg (p.1 * p.2))])
      exact mul_le_of_le_one_left h0 h1
  refine hint.integral_prod_left.congr (Eventually.of_forall fun x => ?_)
  simp only [hG]
  rw [gaussLaplace2_eq_density_integral (by positivity), ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  rw [show N * (x * y) ^ 2 = N * x ^ 2 * y ^ 2 by ring]
  ring

/-! ### Bounds on the depth-two function for `t ≥ 1` -/

/-- `1 ≤ 3 log 2 − γ ≤ 3`. -/
theorem three_log_two_sub_gamma_bounds :
    1 ≤ 3 * Real.log 2 - Real.eulerMascheroniConstant ∧
      3 * Real.log 2 - Real.eulerMascheroniConstant ≤ 3 := by
  have h1 := Real.log_two_gt_d9
  have h2 := Real.eulerMascheroniConstant_lt_two_thirds
  have h3 := Real.one_half_lt_eulerMascheroniConstant
  have h4 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  constructor <;> linarith

/-- The depth-two function for `t ≥ 1`: `|Z₂(t) − (log t + c)/(√(2π)√t)| ≤ (log(2t)+3)/(2t√(2π)√t)`
and `Z₂(t) ≤ (log t + 5)/(√(2π)√t)`. -/
theorem gaussLaplace2_bounds {t : ℝ} (ht : 1 ≤ t) :
    |gaussLaplace2 t - (Real.log t + 3 * Real.log 2 - Real.eulerMascheroniConstant) /
      (Real.sqrt (2 * Real.pi) * Real.sqrt t)| ≤
      (Real.log (2 * t) + 3) / (2 * t * (Real.sqrt (2 * Real.pi) * Real.sqrt t)) ∧
    gaussLaplace2 t ≤ (Real.log t + 5) / (Real.sqrt (2 * Real.pi) * Real.sqrt t) := by
  have ht0 : 0 < t := by linarith
  have h := gaussLaplace2_two_term_bound (by linarith : 1 / 2 ≤ t)
  rw [Real.sqrt_mul (by positivity) t] at h
  have hs : 0 < Real.sqrt (2 * Real.pi) * Real.sqrt t := by positivity
  refine ⟨h, ?_⟩
  obtain ⟨hc1, hc3⟩ := three_log_two_sub_gamma_bounds
  have hlog : Real.log (2 * t) ≤ 2 * t - 1 := by
    linarith [Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 2 * t)]
  have hrem : (Real.log (2 * t) + 3) / (2 * t * (Real.sqrt (2 * Real.pi) * Real.sqrt t)) ≤
      2 / (Real.sqrt (2 * Real.pi) * Real.sqrt t) := by
    rw [div_le_div_iff₀ (by positivity) hs]
    nlinarith [hs]
  have h1 := (abs_le.1 h).2
  calc gaussLaplace2 t ≤ (Real.log t + 3 * Real.log 2 - Real.eulerMascheroniConstant) /
        (Real.sqrt (2 * Real.pi) * Real.sqrt t) +
        2 / (Real.sqrt (2 * Real.pi) * Real.sqrt t) := by linarith
    _ ≤ (Real.log t + 3) / (Real.sqrt (2 * Real.pi) * Real.sqrt t) +
        2 / (Real.sqrt (2 * Real.pi) * Real.sqrt t) := by
        gcongr
        linarith
    _ = (Real.log t + 5) / (Real.sqrt (2 * Real.pi) * Real.sqrt t) := by ring

/-- `∫₁^∞ e^{−x/k} dx = k e^{−1/k}` for `k > 0`. -/
theorem integral_exp_neg_div_Ioi_one {k : ℝ} (hk : 0 < k) :
    ∫ u in Ioi (1 : ℝ), Real.exp (-u / k) = k * Real.exp (-1 / k) := by
  have h := integral_comp_mul_left_Ioi (fun x : ℝ => Real.exp (-x)) 1 (b := 1 / k) (by positivity)
  simp only [smul_eq_mul, mul_one] at h
  have e : (fun u : ℝ => Real.exp (-u / k)) = fun u => Real.exp (-(1 / k * u)) := by
    funext u; ring_nf
  rw [e, h, integral_exp_neg_Ioi, one_div, inv_inv, show -(k⁻¹) = -1 / k by ring]

/-! ### The three pieces of the recursion integral -/

/-- The recursion integrand `F(x) = g(x) Z₂(N x²)`. -/
noncomputable def depthThreeF (N x : ℝ) : ℝ := gaussDensity x * gaussLaplace2 (N * x ^ 2)

theorem depthThreeF_nonneg {N : ℝ} (hN : 0 ≤ N) (x : ℝ) : 0 ≤ depthThreeF N x :=
  mul_nonneg (gaussDensity_nonneg _) (gaussLaplace2_nonneg (by positivity))

theorem depthThreeF_le {N : ℝ} (hN : 0 ≤ N) (x : ℝ) :
    depthThreeF N x ≤ 1 / Real.sqrt (2 * Real.pi) := by
  unfold depthThreeF gaussDensity
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have h1 : Real.exp (-x ^ 2 / 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg x])
  have h2 : gaussLaplace2 (N * x ^ 2) ≤ 1 := gaussLaplace2_le_one (by positivity)
  have h0 : 0 ≤ gaussLaplace2 (N * x ^ 2) := gaussLaplace2_nonneg (by positivity)
  calc Real.exp (-x ^ 2 / 2) / Real.sqrt (2 * Real.pi) * gaussLaplace2 (N * x ^ 2)
      ≤ 1 / Real.sqrt (2 * Real.pi) * 1 :=
        mul_le_mul (div_le_div_of_nonneg_right h1 hs.le) h2 h0 (by positivity)
    _ = 1 / Real.sqrt (2 * Real.pi) := mul_one _

theorem integrable_depthThreeF {N : ℝ} (hN : 0 ≤ N) : Integrable (depthThreeF N) :=
  integrable_density_mul_gaussLaplace2 hN

/-- The inner piece `(0, a]`: `∫₀^a F ≤ a/√(2π)`. -/
theorem depthThree_inner_le {N a : ℝ} (hN : 0 ≤ N) (ha : 0 ≤ a) :
    |∫ x in Ioc (0 : ℝ) a, depthThreeF N x| ≤ 1 / Real.sqrt (2 * Real.pi) * a := by
  have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (0 : ℝ) a)
    (f := depthThreeF N) (C := 1 / Real.sqrt (2 * Real.pi))
    (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top) (fun x _ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (depthThreeF_nonneg hN x)]; exact depthThreeF_le hN x)
  have hv : volume.real (Ioc (0 : ℝ) a) = a := by
    simp [Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal ha]
  rwa [Real.norm_eq_abs, hv] at h

/-- The pointwise bound on `(1, ∞)`: `F(x) ≤ ((log N + 5) e^{−x/2} + 8 e^{−x/4})/(2π√N)`. -/
theorem depthThreeF_tail_le {N x : ℝ} (hN : 1 ≤ N) (hx : 1 < x) :
    depthThreeF N x ≤ 1 / (2 * Real.pi * Real.sqrt N) *
      ((Real.log N + 5) * Real.exp (-x / 2) + 8 * Real.exp (-x / 4)) := by
  have hN0 : 0 < N := by linarith
  have hx0 : 0 < x := by linarith
  have ht : 1 ≤ N * x ^ 2 := by nlinarith
  have hup := (gaussLaplace2_bounds ht).2
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hsq : Real.sqrt (2 * Real.pi) * Real.sqrt (2 * Real.pi) = 2 * Real.pi :=
    Real.mul_self_sqrt (by positivity)
  have hsqrt : Real.sqrt (N * x ^ 2) = Real.sqrt N * x := by
    rw [Real.sqrt_mul hN0.le, Real.sqrt_sq hx0.le]
  have hlog : Real.log (N * x ^ 2) = Real.log N + 2 * Real.log x := by
    rw [Real.log_mul hN0.ne' (by positivity), Real.log_pow]; push_cast; ring
  rw [hsqrt, hlog] at hup
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx.le
  have hlx : Real.log x ≤ x := by linarith [Real.log_le_sub_one_of_pos hx0]
  -- `e^{−x²/2} ≤ e^{−x/2}` and `x e^{−x/2} ≤ 4 e^{−x/4}`
  have he1 : Real.exp (-x ^ 2 / 2) ≤ Real.exp (-x / 2) := Real.exp_le_exp.2 (by nlinarith)
  have he2 : x * Real.exp (-x / 2) ≤ 4 * Real.exp (-x / 4) := by
    have h := Real.add_one_le_exp (x / 4)
    have : Real.exp (-x / 2) = Real.exp (-x / 4) * Real.exp (-x / 4) := by
      rw [← Real.exp_add]; ring_nf
    have h4 : x ≤ 4 * Real.exp (x / 4) := by linarith
    have hprod : Real.exp (x / 4) * Real.exp (-x / 4) = 1 := by rw [← Real.exp_add]; ring_nf; simp
    calc x * Real.exp (-x / 2) = x * Real.exp (-x / 4) * Real.exp (-x / 4) := by rw [this]; ring
      _ ≤ 4 * Real.exp (x / 4) * Real.exp (-x / 4) * Real.exp (-x / 4) := by
          gcongr
      _ = 4 * Real.exp (-x / 4) := by rw [mul_assoc 4, hprod]; ring
  unfold depthThreeF gaussDensity
  have hnum : 0 ≤ Real.log N + 2 * Real.log x + 5 := by linarith
  have hZ0 : 0 ≤ gaussLaplace2 (N * x ^ 2) := gaussLaplace2_nonneg (by positivity)
  generalize hsdef : Real.sqrt (2 * Real.pi) = s at hup hs hsq ⊢
  rw [← hsq]
  calc Real.exp (-x ^ 2 / 2) / s * gaussLaplace2 (N * x ^ 2)
      ≤ Real.exp (-x / 2) / s *
        ((Real.log N + 2 * Real.log x + 5) / (s * (Real.sqrt N * x))) :=
        mul_le_mul (div_le_div_of_nonneg_right he1 hs.le) hup hZ0 (by positivity)
    _ = 1 / (s * s * Real.sqrt N) * (Real.exp (-x / 2) *
        ((Real.log N + 2 * Real.log x + 5) / x)) := by
        field_simp
    _ ≤ 1 / (s * s * Real.sqrt N) * (Real.exp (-x / 2) * (Real.log N + 5 + 2 * x)) := by
        gcongr
        rw [div_le_iff₀ hx0]
        nlinarith
    _ = 1 / (s * s * Real.sqrt N) *
        ((Real.log N + 5) * Real.exp (-x / 2) + 2 * (x * Real.exp (-x / 2))) := by ring
    _ ≤ 1 / (s * s * Real.sqrt N) *
        ((Real.log N + 5) * Real.exp (-x / 2) + 8 * Real.exp (-x / 4)) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- The outer piece `(1, ∞)`: `∫₁^∞ F ≤ (2(log N + 5) + 32)/(2π√N)`. -/
theorem depthThree_outer_le {N : ℝ} (hN : 1 ≤ N) :
    |∫ x in Ioi (1 : ℝ), depthThreeF N x| ≤
      1 / (2 * Real.pi * Real.sqrt N) * (2 * (Real.log N + 5) + 32) := by
  have hN0 : 0 < N := by linarith
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN
  have h2 : IntegrableOn (fun x : ℝ => Real.exp (-x / 2)) (Ioi 1) := by
    refine IntegrableOn.congr_fun (s := Ioi 1)
      (exp_neg_integrableOn_Ioi 1 (by norm_num : (0 : ℝ) < 1 / 2)) (fun w _ => ?_)
      measurableSet_Ioi
    congr 1
    ring
  have h4 : IntegrableOn (fun x : ℝ => Real.exp (-x / 4)) (Ioi 1) := by
    refine IntegrableOn.congr_fun (s := Ioi 1)
      (exp_neg_integrableOn_Ioi 1 (by norm_num : (0 : ℝ) < 1 / 4)) (fun w _ => ?_)
      measurableSet_Ioi
    congr 1
    ring
  have hmaj : IntegrableOn (fun x : ℝ => 1 / (2 * Real.pi * Real.sqrt N) *
      ((Real.log N + 5) * Real.exp (-x / 2) + 8 * Real.exp (-x / 4))) (Ioi 1) :=
    ((h2.const_mul (Real.log N + 5)).add (h4.const_mul 8)).const_mul _
  have h := norm_integral_le_of_norm_le (μ := volume.restrict (Ioi (1 : ℝ)))
    (f := depthThreeF N) hmaj ?_
  · rw [Real.norm_eq_abs] at h
    refine h.trans ?_
    rw [integral_const_mul, integral_add (h2.const_mul (Real.log N + 5)) (h4.const_mul 8),
      integral_const_mul, integral_const_mul,
      integral_exp_neg_div_Ioi_one (by norm_num : (0 : ℝ) < 2),
      integral_exp_neg_div_Ioi_one (by norm_num : (0 : ℝ) < 4)]
    have he2 : Real.exp (-1 / 2) ≤ 1 := Real.exp_le_one_iff.2 (by norm_num)
    have he4 : Real.exp (-1 / 4) ≤ 1 := Real.exp_le_one_iff.2 (by norm_num)
    have hc : 0 ≤ 1 / (2 * Real.pi * Real.sqrt N) := by positivity
    refine mul_le_mul_of_nonneg_left ?_ hc
    nlinarith [Real.exp_pos (-1 / 2), Real.exp_pos (-1 / 4)]
  · rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun x hx => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (depthThreeF_nonneg hN0.le x)]
    exact depthThreeF_tail_le hN hx

/-! ### The middle piece `(N^{−1/2}, 1]` -/

/-- The main-term integrand `M(x) = (log N + 2 log x + c)/(2π√N x)`, `c = 3 log 2 − γ`. -/
noncomputable def depthThreeM (N x : ℝ) : ℝ :=
  (Real.log N + 2 * Real.log x + (3 * Real.log 2 - Real.eulerMascheroniConstant)) /
    (2 * Real.pi * Real.sqrt N * x)

/-- `∫_{N^{−1/2}}^1 M = ((log N)²/4 + (c/2) log N)/(2π√N)`. -/
theorem integral_depthThreeM {N : ℝ} (hN : 1 ≤ N) :
    ∫ x in Ioc (1 / Real.sqrt N) 1, depthThreeM N x =
      1 / (2 * Real.pi * Real.sqrt N) * ((Real.log N) ^ 2 / 4 +
        (3 * Real.log 2 - Real.eulerMascheroniConstant) / 2 * Real.log N) := by
  have hN0 : 0 < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have ha0 : 0 < 1 / Real.sqrt N := by positivity
  have ha1 : 1 / Real.sqrt N ≤ 1 := by
    rw [div_le_one hsN]; exact Real.one_le_sqrt.2 hN
  set c := 3 * Real.log 2 - Real.eulerMascheroniConstant with hc
  set K := 1 / (2 * Real.pi * Real.sqrt N) with hK
  have hderiv : ∀ x ∈ uIcc (1 / Real.sqrt N) 1, HasDerivAt
      (fun x => K * ((Real.log N + c) * Real.log x + Real.log x * Real.log x))
      (depthThreeM N x) x := by
    intro x hx
    rw [uIcc_of_le ha1] at hx
    have hx0 : 0 < x := lt_of_lt_of_le ha0 hx.1
    have hl := Real.hasDerivAt_log hx0.ne'
    have h := (((hl.const_mul (Real.log N + c)).add (hl.mul hl)).const_mul K)
    refine h.congr_deriv ?_
    unfold depthThreeM
    rw [hK]
    field_simp
    ring
  have hint : IntervalIntegrable (depthThreeM N) volume (1 / Real.sqrt N) 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    unfold depthThreeM
    have hlogc : ContinuousOn Real.log (uIcc (1 / Real.sqrt N) 1) :=
      Real.continuousOn_log.mono fun x hx => by
        rw [uIcc_of_le ha1] at hx
        exact ne_of_gt (lt_of_lt_of_le ha0 hx.1)
    refine ContinuousOn.div (by fun_prop) (by fun_prop) fun x hx => ?_
    rw [uIcc_of_le ha1] at hx
    have : 0 < x := lt_of_lt_of_le ha0 hx.1
    positivity
  rw [← intervalIntegral.integral_of_le ha1,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have hloga : Real.log (1 / Real.sqrt N) = -(Real.log N / 2) := by
    rw [one_div, Real.log_inv, Real.log_sqrt hN0.le]
  rw [Real.log_one, hloga]
  ring

/-- The pointwise bound on the middle piece: `|F(x) − M(x)| ≤ D(x)` for `N^{−1/2} < x ≤ 1`. -/
theorem depthThreeF_sub_M_le {N x : ℝ} (hN : 1 ≤ N) (hx : x ∈ Ioc (1 / Real.sqrt N) 1) :
    |depthThreeF N x - depthThreeM N x| ≤
      (Real.log (2 * N) + 3) / (4 * Real.pi * (N * Real.sqrt N)) * x ^ (-3 : ℝ) +
        (Real.log N + 5) / (4 * Real.pi * Real.sqrt N) := by
  have hN0 : 0 < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have hx0 : 0 < x := lt_trans (by positivity) hx.1
  have hx1 : x ≤ 1 := hx.2
  have hNx : 1 ≤ N * x ^ 2 := by
    have h1 : 1 / Real.sqrt N ≤ x := hx.1.le
    have h2 : 1 / Real.sqrt N * Real.sqrt N = 1 := by field_simp
    have h3 : (1 / Real.sqrt N) ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
    have h4 : (1 / Real.sqrt N) ^ 2 * N = 1 := by
      rw [div_pow, one_pow, Real.sq_sqrt hN0.le]; field_simp
    nlinarith
  obtain ⟨hb, -⟩ := gaussLaplace2_bounds hNx
  obtain ⟨hc1, hc3⟩ := three_log_two_sub_gamma_bounds
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN
  have hlogx : Real.log x ≤ 0 := Real.log_nonpos hx0.le hx1
  have hxlogx : -(x * Real.log x) ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (inv_pos.2 hx0)
    rw [Real.log_inv] at this
    have h := mul_le_mul_of_nonneg_left this hx0.le
    rw [mul_sub, mul_inv_cancel₀ hx0.ne'] at h
    nlinarith
  have hsqrt : Real.sqrt (N * x ^ 2) = Real.sqrt N * x := by
    rw [Real.sqrt_mul hN0.le, Real.sqrt_sq hx0.le]
  have hlog : Real.log (N * x ^ 2) = Real.log N + 2 * Real.log x := by
    rw [Real.log_mul hN0.ne' (by positivity), Real.log_pow]; push_cast; ring
  have hlog2 : Real.log (2 * (N * x ^ 2)) = Real.log (2 * N) + 2 * Real.log x := by
    rw [show 2 * (N * x ^ 2) = 2 * N * x ^ 2 by ring, Real.log_mul (by positivity) (by positivity),
      Real.log_pow]; push_cast; ring
  rw [hsqrt, hlog, hlog2] at hb
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hsq : Real.sqrt (2 * Real.pi) * Real.sqrt (2 * Real.pi) = 2 * Real.pi :=
    Real.mul_self_sqrt (by positivity)
  have hg : gaussDensity x = Real.exp (-x ^ 2 / 2) / Real.sqrt (2 * Real.pi) := rfl
  have he1 : Real.exp (-x ^ 2 / 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have he2 : 1 - x ^ 2 / 2 ≤ Real.exp (-x ^ 2 / 2) := by
    linarith [Real.add_one_le_exp (-x ^ 2 / 2)]
  have hrpow : x ^ (-3 : ℝ) = 1 / x ^ 3 := by
    rw [Real.rpow_neg hx0.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      one_div]
  unfold depthThreeF depthThreeM
  set Z := gaussLaplace2 (N * x ^ 2) with hZ
  set L := (Real.log N + 2 * Real.log x + 3 * Real.log 2 - Real.eulerMascheroniConstant) /
    (Real.sqrt (2 * Real.pi) * (Real.sqrt N * x)) with hL
  set R := (Real.log (2 * N) + 2 * Real.log x + 3) /
    (2 * (N * x ^ 2) * (Real.sqrt (2 * Real.pi) * (Real.sqrt N * x))) with hR
  clear_value Z
  generalize hsdef : Real.sqrt (2 * Real.pi) = s at hb hs hsq hg hL hR ⊢
  rw [hrpow, ← hsq, hg]
  have hpi : Real.pi = s * s / 2 := by linarith
  -- the decomposition `F − M = g (Z − L) + (g − 1/s) L`
  have hM : (Real.log N + 2 * Real.log x + (3 * Real.log 2 - Real.eulerMascheroniConstant)) /
      (s * s * Real.sqrt N * x) = 1 / s * L := by
    rw [hL]; field_simp; ring
  rw [hM]
  have hdec : Real.exp (-x ^ 2 / 2) / s * Z - 1 / s * L =
      Real.exp (-x ^ 2 / 2) / s * (Z - L) + (Real.exp (-x ^ 2 / 2) / s - 1 / s) * L := by ring
  rw [hdec]
  have hZL : |Z - L| ≤ R := hb
  have hgL : |Real.exp (-x ^ 2 / 2) / s - 1 / s| ≤ x ^ 2 / (2 * s) := by
    have h1 : Real.exp (-x ^ 2 / 2) / s - 1 / s = -((1 - Real.exp (-x ^ 2 / 2)) / s) := by ring
    rw [h1, abs_neg, abs_of_nonneg (div_nonneg (by linarith) hs.le), ← div_div]
    exact div_le_div_of_nonneg_right (by linarith) hs.le
  have hden : 0 < s * (Real.sqrt N * x) := by positivity
  have hLabs : |L| ≤ (Real.log N + 2 * (-Real.log x) +
      (3 * Real.log 2 - Real.eulerMascheroniConstant)) / (s * (Real.sqrt N * x)) := by
    rw [hL, abs_div, abs_of_pos hden]
    refine div_le_div_of_nonneg_right ?_ hden.le
    rw [abs_le]; constructor <;> linarith
  -- the first term
  have hT1 : |Real.exp (-x ^ 2 / 2) / s * (Z - L)| ≤
      (Real.log (2 * N) + 3) / (4 * Real.pi * (N * Real.sqrt N)) * (1 / x ^ 3) := by
    rw [abs_mul, abs_of_pos (by positivity)]
    calc Real.exp (-x ^ 2 / 2) / s * |Z - L| ≤ 1 / s * R :=
          mul_le_mul (div_le_div_of_nonneg_right he1 hs.le) hZL (abs_nonneg _) (by positivity)
      _ = (Real.log (2 * N) + 2 * Real.log x + 3) / (4 * Real.pi * (N * Real.sqrt N)) *
          (1 / x ^ 3) := by
          rw [hR, hpi]; field_simp; ring
      _ ≤ (Real.log (2 * N) + 3) / (4 * Real.pi * (N * Real.sqrt N)) * (1 / x ^ 3) := by
          gcongr
          linarith
  -- the second term
  have hT2 : |(Real.exp (-x ^ 2 / 2) / s - 1 / s) * L| ≤
      (Real.log N + 5) / (4 * Real.pi * Real.sqrt N) := by
    rw [abs_mul]
    calc |Real.exp (-x ^ 2 / 2) / s - 1 / s| * |L|
        ≤ x ^ 2 / (2 * s) * ((Real.log N + 2 * (-Real.log x) +
            (3 * Real.log 2 - Real.eulerMascheroniConstant)) / (s * (Real.sqrt N * x))) :=
          mul_le_mul hgL hLabs (abs_nonneg _) (by positivity)
      _ = (x * Real.log N + 2 * (-(x * Real.log x)) +
          (3 * Real.log 2 - Real.eulerMascheroniConstant) * x) / (4 * Real.pi * Real.sqrt N) := by
          rw [hpi]; field_simp; ring
      _ ≤ (Real.log N + 5) / (4 * Real.pi * Real.sqrt N) := by
          refine div_le_div_of_nonneg_right ?_ (by positivity)
          nlinarith [mul_le_mul_of_nonneg_right hx1 hlogN]
  calc |Real.exp (-x ^ 2 / 2) / s * (Z - L) + (Real.exp (-x ^ 2 / 2) / s - 1 / s) * L|
      ≤ |Real.exp (-x ^ 2 / 2) / s * (Z - L)| + |(Real.exp (-x ^ 2 / 2) / s - 1 / s) * L| :=
        abs_add_le _ _
    _ ≤ _ := add_le_add hT1 hT2

/-- The middle-piece error: `|∫_{N^{−1/2}}^1 (F − M)| ≤ (log(2N)+3)/(8π√N) + (log N+5)/(4π√N)`. -/
theorem depthThree_middle_err_le {N : ℝ} (hN : 1 ≤ N) :
    |∫ x in Ioc (1 / Real.sqrt N) 1, (depthThreeF N x - depthThreeM N x)| ≤
      (Real.log (2 * N) + 3) / (8 * Real.pi * Real.sqrt N) +
        (Real.log N + 5) / (4 * Real.pi * Real.sqrt N) := by
  have hN0 : 0 < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have ha0 : 0 < 1 / Real.sqrt N := by positivity
  have ha1 : 1 / Real.sqrt N ≤ 1 := by
    rw [div_le_one hsN]; exact Real.one_le_sqrt.2 hN
  set A := (Real.log (2 * N) + 3) / (4 * Real.pi * (N * Real.sqrt N)) with hA
  set B := (Real.log N + 5) / (4 * Real.pi * Real.sqrt N) with hB
  have hA0 : 0 ≤ A := by
    rw [hA]
    have : 0 ≤ Real.log (2 * N) := Real.log_nonneg (by linarith)
    positivity
  have hB0 : 0 ≤ B := by
    rw [hB]
    have : 0 ≤ Real.log N := Real.log_nonneg hN
    positivity
  have h0 : (0 : ℝ) ∉ uIcc (1 / Real.sqrt N) 1 := fun h => by
    rw [uIcc_of_le ha1] at h; exact absurd h.1 (not_le.2 ha0)
  have hint3 : IntervalIntegrable (fun x : ℝ => x ^ (-3 : ℝ)) volume (1 / Real.sqrt N) 1 :=
    intervalIntegral.intervalIntegrable_rpow (Or.inr h0)
  have hmaj : IntegrableOn (fun x : ℝ => A * x ^ (-3 : ℝ) + B) (Ioc (1 / Real.sqrt N) 1) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le ha1]
    exact (hint3.const_mul A).add (intervalIntegrable_const)
  have h := norm_integral_le_of_norm_le (μ := volume.restrict (Ioc (1 / Real.sqrt N) 1))
    (f := fun x => depthThreeF N x - depthThreeM N x) hmaj ?_
  · rw [Real.norm_eq_abs] at h
    refine h.trans ?_
    rw [integral_add ((intervalIntegrable_iff_integrableOn_Ioc_of_le ha1).1 (hint3.const_mul A))
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le ha1).1 intervalIntegrable_const),
      integral_const_mul, setIntegral_const, ← intervalIntegral.integral_of_le ha1,
      integral_rpow (Or.inr ⟨by norm_num, h0⟩)]
    have hv : volume.real (Ioc (1 / Real.sqrt N) 1) = 1 - 1 / Real.sqrt N := by
      rw [measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
    have hpow : (1 / Real.sqrt N) ^ (-3 + 1 : ℝ) = N := by
      rw [show (-3 + 1 : ℝ) = -2 by norm_num, Real.rpow_neg (by positivity), one_div,
        Real.inv_rpow hsN.le, inv_inv, Real.rpow_two, Real.sq_sqrt hN0.le]
    rw [hv, hpow, Real.one_rpow, smul_eq_mul]
    have h1 : A * ((1 - N) / (-3 + 1)) ≤ (Real.log (2 * N) + 3) / (8 * Real.pi * Real.sqrt N) := by
      rw [hA, show (1 - N) / (-3 + 1) = (N - 1) / 2 by ring]
      have : (Real.log (2 * N) + 3) / (4 * Real.pi * (N * Real.sqrt N)) * ((N - 1) / 2) ≤
          (Real.log (2 * N) + 3) / (4 * Real.pi * (N * Real.sqrt N)) * (N / 2) :=
        mul_le_mul_of_nonneg_left (by linarith) (hA ▸ hA0)
      refine this.trans (le_of_eq ?_)
      field_simp
      ring
    have h2 : (1 - 1 / Real.sqrt N) * B ≤ B := by
      have : 1 - 1 / Real.sqrt N ≤ 1 := by linarith
      nlinarith
    linarith
  · rw [ae_restrict_iff' measurableSet_Ioc]
    refine Eventually.of_forall fun x hx => ?_
    rw [Real.norm_eq_abs]
    exact depthThreeF_sub_M_le hN hx

/-! ### Assembly -/

/-- Evenness: `∫ F = 2 ∫₀^∞ F`. -/
theorem integral_depthThreeF_eq_two_mul (N : ℝ) :
    ∫ x, depthThreeF N x = 2 * ∫ x in Ioi (0 : ℝ), depthThreeF N x := by
  rw [← integral_comp_abs (f := depthThreeF N)]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [depthThreeF, gaussDensity, sq_abs]

/-- ★★★ **The depth-three Gaussian DLN**: for `N ≥ 1`,
`|Z_3(N) − (log N)²/(4π√N)| ≤ 18 (1 + log N)/√N`. -/
theorem gaussLaplaceL_three_bound {N : ℝ} (hN : 1 ≤ N) :
    |gaussLaplaceL 3 N - (Real.log N) ^ 2 / (4 * Real.pi * Real.sqrt N)| ≤
      18 * (1 + Real.log N) / Real.sqrt N := by
  have hN0 : 0 < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have ha0 : 0 < 1 / Real.sqrt N := by positivity
  have ha1 : 1 / Real.sqrt N ≤ 1 := by
    rw [div_le_one hsN]; exact Real.one_le_sqrt.2 hN
  have hℓ : 0 ≤ Real.log N := Real.log_nonneg hN
  have hℓ2 : Real.log (2 * N) ≤ 1 + Real.log N := by
    rw [Real.log_mul two_ne_zero hN0.ne']
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hpi := Real.pi_gt_three
  have hs2 : 2 ≤ Real.sqrt (2 * Real.pi) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    nlinarith
  obtain ⟨hc1, hc3⟩ := three_log_two_sub_gamma_bounds
  -- the split
  have hF := integrable_depthThreeF hN0.le
  have hsplit : ∫ x in Ioi (0 : ℝ), depthThreeF N x =
      (∫ x in Ioc (0 : ℝ) (1 / Real.sqrt N), depthThreeF N x) +
        (∫ x in Ioc (1 / Real.sqrt N) 1, depthThreeF N x) +
        ∫ x in Ioi (1 : ℝ), depthThreeF N x := by
    rw [← Ioc_union_Ioi_eq_Ioi zero_le_one,
      setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hF.integrableOn hF.integrableOn,
      ← Ioc_union_Ioc_eq_Ioc ha0.le ha1,
      setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc hF.integrableOn
        hF.integrableOn]
  have hM : IntegrableOn (depthThreeM N) (Ioc (1 / Real.sqrt N) 1) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le ha1]
    refine ContinuousOn.intervalIntegrable ?_
    unfold depthThreeM
    have hlogc : ContinuousOn Real.log (uIcc (1 / Real.sqrt N) 1) :=
      Real.continuousOn_log.mono fun x hx => by
        rw [uIcc_of_le ha1] at hx
        exact ne_of_gt (lt_of_lt_of_le ha0 hx.1)
    refine ContinuousOn.div (by fun_prop) (by fun_prop) fun x hx => ?_
    rw [uIcc_of_le ha1] at hx
    have : 0 < x := lt_of_lt_of_le ha0 hx.1
    positivity
  have hmid : ∫ x in Ioc (1 / Real.sqrt N) 1, depthThreeF N x =
      (∫ x in Ioc (1 / Real.sqrt N) 1, depthThreeM N x) +
        ∫ x in Ioc (1 / Real.sqrt N) 1, (depthThreeF N x - depthThreeM N x) := by
    rw [integral_sub hF.integrableOn hM]; ring
  have h0 := depthThree_inner_le hN0.le ha0.le
  have h1 := depthThree_middle_err_le hN
  have h2 := depthThree_outer_le hN
  have hMval := integral_depthThreeM hN
  rw [gaussLaplaceL_three hN0.le]
  change |(∫ x, depthThreeF N x) - _| ≤ _
  rw [integral_depthThreeF_eq_two_mul, hsplit, hmid, hMval]
  -- name the pieces
  set I₀ := ∫ x in Ioc (0 : ℝ) (1 / Real.sqrt N), depthThreeF N x with hI₀
  set E₁ := ∫ x in Ioc (1 / Real.sqrt N) 1, (depthThreeF N x - depthThreeM N x) with hE₁
  set I₂ := ∫ x in Ioi (1 : ℝ), depthThreeF N x with hI₂
  clear_value I₀ E₁ I₂
  set c := 3 * Real.log 2 - Real.eulerMascheroniConstant with hc
  clear_value c
  set ℓ := Real.log N with hℓdef
  clear_value ℓ
  have hkey : 2 * (I₀ + (1 / (2 * Real.pi * Real.sqrt N) * (ℓ ^ 2 / 4 + c / 2 * ℓ) + E₁) + I₂) -
      ℓ ^ 2 / (4 * Real.pi * Real.sqrt N) =
      2 * I₀ + 2 * E₁ + 2 * I₂ + c * ℓ / (2 * Real.pi * Real.sqrt N) := by
    field_simp
    ring
  rw [hkey]
  rw [abs_le] at h0 h1 h2 ⊢
  -- the four pieces against `(1 + ℓ)/√N`
  have hT0 : 2 * (1 / Real.sqrt (2 * Real.pi) * (1 / Real.sqrt N)) ≤ 1 * (1 + ℓ) / Real.sqrt N := by
    rw [show 2 * (1 / Real.sqrt (2 * Real.pi) * (1 / Real.sqrt N)) =
      (2 / Real.sqrt (2 * Real.pi)) / Real.sqrt N by field_simp]
    refine div_le_div_of_nonneg_right ?_ hsN.le
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hT1 : 2 * ((Real.log (2 * N) + 3) / (8 * Real.pi * Real.sqrt N) +
      (ℓ + 5) / (4 * Real.pi * Real.sqrt N)) ≤ 2 * (1 + ℓ) / Real.sqrt N := by
    rw [show 2 * ((Real.log (2 * N) + 3) / (8 * Real.pi * Real.sqrt N) +
      (ℓ + 5) / (4 * Real.pi * Real.sqrt N)) =
      ((Real.log (2 * N) + 3 + 2 * (ℓ + 5)) / (4 * Real.pi)) / Real.sqrt N by field_simp; ring]
    refine div_le_div_of_nonneg_right ?_ hsN.le
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hT2 : 2 * (1 / (2 * Real.pi * Real.sqrt N) * (2 * (ℓ + 5) + 32)) ≤
      14 * (1 + ℓ) / Real.sqrt N := by
    rw [show 2 * (1 / (2 * Real.pi * Real.sqrt N) * (2 * (ℓ + 5) + 32)) =
      ((2 * (ℓ + 5) + 32) / Real.pi) / Real.sqrt N by field_simp]
    refine div_le_div_of_nonneg_right ?_ hsN.le
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hT3 : c * ℓ / (2 * Real.pi * Real.sqrt N) ≤ 1 * (1 + ℓ) / Real.sqrt N := by
    rw [show c * ℓ / (2 * Real.pi * Real.sqrt N) = (c * ℓ / (2 * Real.pi)) / Real.sqrt N by
      field_simp]
    refine div_le_div_of_nonneg_right ?_ hsN.le
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hT3' : -(1 * (1 + ℓ) / Real.sqrt N) ≤ c * ℓ / (2 * Real.pi * Real.sqrt N) := by
    have : 0 ≤ c * ℓ / (2 * Real.pi * Real.sqrt N) := by positivity
    have : 0 ≤ 1 * (1 + ℓ) / Real.sqrt N := by positivity
    linarith
  have hsum : 1 * (1 + ℓ) / Real.sqrt N + 2 * (1 + ℓ) / Real.sqrt N + 14 * (1 + ℓ) / Real.sqrt N +
      1 * (1 + ℓ) / Real.sqrt N = 18 * (1 + ℓ) / Real.sqrt N := by ring
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2]

/-- ★★★ `√N Z_3(N)/(log N)² → 1/(4π)`: the leading coefficient of the depth-three expansion. -/
theorem gaussLaplaceL_three_leading :
    Tendsto (fun N : ℝ => Real.sqrt N * gaussLaplaceL 3 N / (Real.log N) ^ 2) atTop
      (𝓝 (1 / (4 * Real.pi))) := by
  have hbound : ∀ᶠ N : ℝ in atTop,
      |Real.sqrt N * gaussLaplaceL 3 N / (Real.log N) ^ 2 - 1 / (4 * Real.pi)| ≤
        18 * (1 + Real.log N) / (Real.log N) ^ 2 := by
    filter_upwards [eventually_ge_atTop (3 : ℝ)] with N hN3
    have hN : 1 ≤ N := by linarith
    have hN0 : 0 < N := by linarith
    have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
    have hℓ : 1 ≤ Real.log N := by
      rw [← Real.log_exp 1]
      exact Real.log_le_log (Real.exp_pos _) (by linarith [Real.exp_one_lt_d9])
    have h := gaussLaplaceL_three_bound hN
    have e : Real.sqrt N * gaussLaplaceL 3 N / (Real.log N) ^ 2 - 1 / (4 * Real.pi) =
        (Real.sqrt N / (Real.log N) ^ 2) *
          (gaussLaplaceL 3 N - (Real.log N) ^ 2 / (4 * Real.pi * Real.sqrt N)) := by
      field_simp
    rw [e, abs_mul, abs_of_pos (by positivity)]
    calc Real.sqrt N / (Real.log N) ^ 2 *
          |gaussLaplaceL 3 N - (Real.log N) ^ 2 / (4 * Real.pi * Real.sqrt N)|
        ≤ Real.sqrt N / (Real.log N) ^ 2 * (18 * (1 + Real.log N) / Real.sqrt N) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = 18 * (1 + Real.log N) / (Real.log N) ^ 2 := by field_simp
  have hlim : Tendsto (fun N : ℝ => 18 * (1 + Real.log N) / (Real.log N) ^ 2) atTop (𝓝 0) := by
    have hl := Real.tendsto_log_atTop
    have ha : Tendsto (fun N : ℝ => (Real.log N)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hl
    have hb : Tendsto (fun N : ℝ => ((Real.log N) ^ 2)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hl)
    have h1 : Tendsto (fun N : ℝ => 18 * ((Real.log N)⁻¹ + ((Real.log N) ^ 2)⁻¹)) atTop (𝓝 0) := by
      simpa using (ha.add hb).const_mul 18
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop (3 : ℝ)] with N hN3
    have hℓ : 0 < Real.log N := Real.log_pos (by linarith)
    field_simp
    ring
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun N => norm_nonneg _) ?_ hlim
  filter_upwards [hbound] with N hN
  rw [Real.norm_eq_abs]
  exact hN

end Grammar
