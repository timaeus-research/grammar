/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.GaussianDepthThreeResidual

/-!
# The depth-three Gaussian DLN: the constant term with a rate

DCXXXI identifies the residual `√N Z_3(N) − [A₃ (log N)² + B₃ log N] → C₃ = depthThreeConst` by
dominated convergence.  Here the convergence is quantified (★★★ `gaussLaplaceL_three_rate`):

  `|√N Z_3(N) − (A₃ (log N)² + B₃ log N + C₃)| ≤ 8 (1 + log N)/√N`  for `N ≥ 1`,

`A₃ = 1/(4π)`, `B₃ = (2 log 2 − γ)/π`.  The four pieces of the DCXXXI decomposition are bounded
explicitly: the inner piece by `|g(v/√N) − g(0)| ≤ v²/(2s N)` on `(0,1]`; the remainder piece by the
same on `(1, √N]` against `|q| ≤ 4/(s v²)` and by `1/s` on `(√N, ∞)` against the tail of `v^{−2}`;
the cutoff term `(log N + c) I_a` by `(log N + 3)/(2N)`; and `J_a − J` by `1/(2√N)`.  This is the
base of the three-term propagation at every depth (`GaussianDepthAllThreeTerm`).
Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

/-- `|g(y) − 1/√(2π)| ≤ y²/(2√(2π))`. -/
theorem abs_gaussDensity_sub_le (y : ℝ) :
    |gaussDensity y - 1 / Real.sqrt (2 * Real.pi)| ≤ y ^ 2 / (2 * Real.sqrt (2 * Real.pi)) := by
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  unfold gaussDensity
  have h1 : Real.exp (-y ^ 2 / 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg y])
  have h2 : 1 - y ^ 2 / 2 ≤ Real.exp (-y ^ 2 / 2) := by
    have := Real.add_one_le_exp (-y ^ 2 / 2); linarith
  rw [show Real.exp (-y ^ 2 / 2) / Real.sqrt (2 * Real.pi) - 1 / Real.sqrt (2 * Real.pi) =
    -((1 - Real.exp (-y ^ 2 / 2)) / Real.sqrt (2 * Real.pi)) by ring, abs_neg,
    abs_of_nonneg (div_nonneg (by linarith) hs.le)]
  rw [div_le_div_iff₀ hs (by positivity)]
  nlinarith

theorem gaussDensity_le (y : ℝ) : gaussDensity y ≤ 1 / Real.sqrt (2 * Real.pi) := by
  unfold gaussDensity
  exact div_le_div_of_nonneg_right (Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg y]))
    (Real.sqrt_nonneg _)

/-! ### The inner piece -/

/-- `|√N I₀ − (1/s) ∫₀¹ q| ≤ 1/(2 s N)`. -/
theorem inner_rate {N : ℝ} (hN : 1 ≤ N) :
    |Real.sqrt N * (∫ x in Ioc (0 : ℝ) (1 / Real.sqrt N), depthThreeF N x) -
      1 / Real.sqrt (2 * Real.pi) * ∫ v in Ioc (0 : ℝ) 1, depthThreeQ v| ≤
      1 / (2 * Real.sqrt (2 * Real.pi) * N) := by
  have hN0 : 0 < N := by linarith
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hmeas : Measurable fun v : ℝ => gaussDensity (v / Real.sqrt N) * gaussLaplace2 (v ^ 2) :=
    (continuous_gaussDensity.comp (continuous_id.div_const _)).measurable.mul
      (measurable_gaussLaplace2.comp (measurable_id.pow_const 2))
  have hint : IntegrableOn (fun v : ℝ => gaussDensity (v / Real.sqrt N) * gaussLaplace2 (v ^ 2))
      (Ioc 0 1) := by
    refine Measure.integrableOn_of_bounded (M := 1 / Real.sqrt (2 * Real.pi)) measure_Ioc_lt_top.ne
      hmeas.aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Eventually.of_forall fun v _ => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (gaussDensity_nonneg _)
      (gaussLaplace2_nonneg (sq_nonneg _)))]
    calc gaussDensity (v / Real.sqrt N) * gaussLaplace2 (v ^ 2)
        ≤ 1 / Real.sqrt (2 * Real.pi) * 1 := mul_le_mul (gaussDensity_le _)
          (gaussLaplace2_le_one (sq_nonneg _)) (gaussLaplace2_nonneg (sq_nonneg _)) (by positivity)
      _ = 1 / Real.sqrt (2 * Real.pi) := mul_one _
  rw [sqrt_mul_inner_eq hN0, ← integral_const_mul,
    ← integral_sub hint (integrableOn_depthThreeQ_inner.const_mul _)]
  have hb := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (0 : ℝ) 1)
    (f := fun v => gaussDensity (v / Real.sqrt N) * gaussLaplace2 (v ^ 2) -
      1 / Real.sqrt (2 * Real.pi) * depthThreeQ v)
    (C := 1 / (2 * Real.sqrt (2 * Real.pi) * N)) measure_Ioc_lt_top (fun v hv => by
      rw [depthThreeQ_inner hv, show gaussDensity (v / Real.sqrt N) * gaussLaplace2 (v ^ 2) -
        1 / Real.sqrt (2 * Real.pi) * gaussLaplace2 (v ^ 2) =
        (gaussDensity (v / Real.sqrt N) - 1 / Real.sqrt (2 * Real.pi)) * gaussLaplace2 (v ^ 2)
        by ring, Real.norm_eq_abs, abs_mul, abs_of_nonneg (gaussLaplace2_nonneg (sq_nonneg _))]
      have h1 := abs_gaussDensity_sub_le (v / Real.sqrt N)
      have hv2 : (v / Real.sqrt N) ^ 2 ≤ 1 / N := by
        rw [div_pow, Real.sq_sqrt hN0.le]
        exact div_le_div_of_nonneg_right (by nlinarith [hv.1, hv.2]) hN0.le
      calc |gaussDensity (v / Real.sqrt N) - 1 / Real.sqrt (2 * Real.pi)| * gaussLaplace2 (v ^ 2)
          ≤ (v / Real.sqrt N) ^ 2 / (2 * Real.sqrt (2 * Real.pi)) * 1 :=
            mul_le_mul h1 (gaussLaplace2_le_one (sq_nonneg _)) (gaussLaplace2_nonneg (sq_nonneg _))
              (by positivity)
        _ ≤ 1 / N / (2 * Real.sqrt (2 * Real.pi)) * 1 := by gcongr
        _ = 1 / (2 * Real.sqrt (2 * Real.pi) * N) := by field_simp)
  rw [Real.norm_eq_abs, measureReal_def, Real.volume_Ioc, sub_zero,
    ENNReal.toReal_ofReal zero_le_one,
    mul_one] at hb
  exact hb

/-! ### The remainder piece -/

theorem integral_Ioi_inv_sq {c : ℝ} (hc : 0 < c) :
    ∫ v in Ioi c, 1 / v ^ 2 = 1 / c := by
  have h := integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hc
  have e : ∀ v ∈ Ioi c, v ^ (-2 : ℝ) = 1 / v ^ 2 := by
    intro v hv
    have hv0 : 0 < v := lt_trans hc hv
    rw [Real.rpow_neg hv0.le, Real.rpow_two, one_div]
  rw [setIntegral_congr_fun measurableSet_Ioi e] at h
  rw [h, show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
  field_simp

/-- `|√N E − (1/s) ∫₁^∞ q| ≤ 6/(s² √N)`. -/
theorem rem_rate {N : ℝ} (hN : 1 ≤ N) :
    |Real.sqrt N * (∫ x in Ioi (1 / Real.sqrt N), (depthThreeF N x - gaussDensity x *
      ((Real.log N + 2 * Real.log x + 3 * Real.log 2 - Real.eulerMascheroniConstant) /
        (Real.sqrt (2 * Real.pi) * (Real.sqrt N * x))))) -
      1 / Real.sqrt (2 * Real.pi) * ∫ v in Ioi (1 : ℝ), depthThreeQ v| ≤
      6 / (Real.sqrt (2 * Real.pi) ^ 2 * Real.sqrt N) := by
  have hN0 : 0 < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have hsN1 : 1 ≤ Real.sqrt N := Real.one_le_sqrt.2 hN
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hqi := integrableOn_depthThreeQ_outer
  have hgq : IntegrableOn (fun v => gaussDensity (v / Real.sqrt N) * depthThreeQ v) (Ioi 1) :=
    hqi.abs.mono' ((continuous_gaussDensity.comp (continuous_id.div_const _)).measurable.mul
      measurable_depthThreeQ).aestronglyMeasurable (Eventually.of_forall fun v => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gaussDensity_nonneg _)]
        exact mul_le_of_le_one_left (abs_nonneg _) ((gaussDensity_le _).trans (by
          rw [div_le_one hs]; rw [Real.le_sqrt (by norm_num) (by positivity)]
          nlinarith [Real.pi_gt_three])))
  rw [sqrt_mul_rem_eq hN0, ← integral_const_mul, ← integral_sub hgq (hqi.const_mul _)]
  have e : ∀ v : ℝ, gaussDensity (v / Real.sqrt N) * depthThreeQ v -
      1 / Real.sqrt (2 * Real.pi) * depthThreeQ v =
      (gaussDensity (v / Real.sqrt N) - 1 / Real.sqrt (2 * Real.pi)) * depthThreeQ v :=
    fun v => by ring
  simp_rw [e]
  have hint : IntegrableOn (fun v => (gaussDensity (v / Real.sqrt N) - 1 / Real.sqrt (2 * Real.pi))
      * depthThreeQ v) (Ioi 1) := by
    have := hgq.sub (hqi.const_mul (1 / Real.sqrt (2 * Real.pi)))
    exact this.congr_fun (fun v _ => (e v)) measurableSet_Ioi
  -- split at `√N`
  have hsplit : ∫ v in Ioi (1 : ℝ), (gaussDensity (v / Real.sqrt N) - 1 / Real.sqrt (2 * Real.pi))
      * depthThreeQ v =
      (∫ v in Ioc (1 : ℝ) (Real.sqrt N), (gaussDensity (v / Real.sqrt N) -
        1 / Real.sqrt (2 * Real.pi)) * depthThreeQ v) +
      ∫ v in Ioi (Real.sqrt N), (gaussDensity (v / Real.sqrt N) - 1 / Real.sqrt (2 * Real.pi)) *
        depthThreeQ v := by
    rw [← Ioc_union_Ioi_eq_Ioi hsN1, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hint.mono_set Ioc_subset_Ioi_self) (hint.mono_set (Ioi_subset_Ioi hsN1))]
  rw [hsplit]
  -- the near piece: `|g − 1/s| ≤ v²/(2sN)`, `|q| ≤ 4/(sv²)`
  have h1 : |∫ v in Ioc (1 : ℝ) (Real.sqrt N), (gaussDensity (v / Real.sqrt N) -
      1 / Real.sqrt (2 * Real.pi)) * depthThreeQ v| ≤
      2 / (Real.sqrt (2 * Real.pi) ^ 2 * Real.sqrt N)
      := by
    have hb := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (1 : ℝ) (Real.sqrt N))
      (f := fun v => (gaussDensity (v / Real.sqrt N) - 1 / Real.sqrt (2 * Real.pi)) *
        depthThreeQ v) (C := 2 / (Real.sqrt (2 * Real.pi) ^ 2 * N)) measure_Ioc_lt_top
      (fun v hv => by
        have hv1 : 1 < v := hv.1
        have hv0 : 0 < v := by linarith
        rw [Real.norm_eq_abs, abs_mul]
        have ha := abs_gaussDensity_sub_le (v / Real.sqrt N)
        have hq := depthThreeQ_outer_le hv1
        rw [div_pow, Real.sq_sqrt hN0.le] at ha
        calc |gaussDensity (v / Real.sqrt N) - 1 / Real.sqrt (2 * Real.pi)| * |depthThreeQ v|
            ≤ v ^ 2 / N / (2 * Real.sqrt (2 * Real.pi)) * (4 / (Real.sqrt (2 * Real.pi) * v ^ 2)) :=
              mul_le_mul ha hq (abs_nonneg _) (by positivity)
          _ = 2 / (Real.sqrt (2 * Real.pi) ^ 2 * N) := by field_simp; ring)
    rw [Real.norm_eq_abs, measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
      at hb
    refine hb.trans ?_
    have hNN : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN0.le
    calc 2 / (Real.sqrt (2 * Real.pi) ^ 2 * N) * (Real.sqrt N - 1)
        ≤ 2 / (Real.sqrt (2 * Real.pi) ^ 2 * N) * Real.sqrt N :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 2 / (Real.sqrt (2 * Real.pi) ^ 2 * Real.sqrt N) := by
          rw [div_mul_eq_mul_div, div_eq_div_iff (by positivity) (by positivity)]
          linear_combination (2 * Real.sqrt (2 * Real.pi) ^ 2) * hNN
  -- the far piece: `|g − 1/s| ≤ 1/s`, `|q| ≤ 4/(sv²)`, `∫_{√N}^∞ v^{−2} = 1/√N`
  have h2 : |∫ v in Ioi (Real.sqrt N), (gaussDensity (v / Real.sqrt N) -
      1 / Real.sqrt (2 * Real.pi)) * depthThreeQ v| ≤
      4 / (Real.sqrt (2 * Real.pi) ^ 2 * Real.sqrt N) := by
    have hmaj : IntegrableOn (fun v : ℝ => 4 / Real.sqrt (2 * Real.pi) ^ 2 * (1 / v ^ 2))
        (Ioi (Real.sqrt N)) := by
      have h0 : IntegrableOn (fun v : ℝ => 4 / Real.sqrt (2 * Real.pi) ^ 2 * v ^ (-2 : ℝ))
          (Ioi (Real.sqrt N)) :=
        (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hsN).const_mul _
      refine h0.congr_fun (fun v hv => ?_) measurableSet_Ioi
      have hv0 : 0 < v := lt_trans hsN hv
      simp only
      rw [Real.rpow_neg hv0.le, Real.rpow_two, one_div]
    have hb := norm_integral_le_of_norm_le (μ := volume.restrict (Ioi (Real.sqrt N)))
      (f := fun v => (gaussDensity (v / Real.sqrt N) - 1 / Real.sqrt (2 * Real.pi)) *
        depthThreeQ v) hmaj ?_
    · rw [Real.norm_eq_abs] at hb
      refine hb.trans (le_of_eq ?_)
      rw [integral_const_mul, integral_Ioi_inv_sq hsN]
      field_simp
    · rw [ae_restrict_iff' measurableSet_Ioi]
      refine Eventually.of_forall fun v hv => ?_
      have hv1 : 1 < v := lt_of_le_of_lt hsN1 hv
      rw [Real.norm_eq_abs, abs_mul]
      have hg0 := gaussDensity_nonneg (v / Real.sqrt N)
      have hg1 := gaussDensity_le (v / Real.sqrt N)
      have ha : |gaussDensity (v / Real.sqrt N) - 1 / Real.sqrt (2 * Real.pi)| ≤
          1 / Real.sqrt (2 * Real.pi) := by
        rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
      calc |gaussDensity (v / Real.sqrt N) - 1 / Real.sqrt (2 * Real.pi)| * |depthThreeQ v|
          ≤ 1 / Real.sqrt (2 * Real.pi) * (4 / (Real.sqrt (2 * Real.pi) * v ^ 2)) :=
            mul_le_mul ha (depthThreeQ_outer_le hv1) (abs_nonneg _) (by positivity)
        _ = 4 / Real.sqrt (2 * Real.pi) ^ 2 * (1 / v ^ 2) := by field_simp
  calc |(∫ v in Ioc (1 : ℝ) (Real.sqrt N), (gaussDensity (v / Real.sqrt N) -
        1 / Real.sqrt (2 * Real.pi)) * depthThreeQ v) +
        ∫ v in Ioi (Real.sqrt N), (gaussDensity (v / Real.sqrt N) - 1 / Real.sqrt (2 * Real.pi)) *
          depthThreeQ v|
      ≤ 2 / (Real.sqrt (2 * Real.pi) ^ 2 * Real.sqrt N) +
        4 / (Real.sqrt (2 * Real.pi) ^ 2 * Real.sqrt N) := (abs_add_le _ _).trans (add_le_add h1 h2)
    _ = 6 / (Real.sqrt (2 * Real.pi) ^ 2 * Real.sqrt N) := by ring

/-! ### The rate -/

/-- ★★★ **The depth-three constant with a rate**:
`|√N Z_3(N) − (A₃ (log N)² + B₃ log N + C₃)| ≤ 8(1 + log N)/√N` for `N ≥ 1`. -/
theorem gaussLaplaceL_three_rate {N : ℝ} (hN : 1 ≤ N) :
    |Real.sqrt N * gaussLaplaceL 3 N - ((Real.log N) ^ 2 / (4 * Real.pi) +
      (2 * Real.log 2 - Real.eulerMascheroniConstant) / Real.pi * Real.log N + depthThreeConst)| ≤
      8 * (1 + Real.log N) / Real.sqrt N := by
  have hN0 : 0 < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have hsN1 : 1 ≤ Real.sqrt N := Real.one_le_sqrt.2 hN
  have hsNN : Real.sqrt N ≤ N := by nlinarith [Real.sq_sqrt hN0.le]
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hs2 : 2 ≤ Real.sqrt (2 * Real.pi) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]; nlinarith [Real.pi_gt_three]
  have hpi := Real.pi_gt_three
  have hℓ : 0 ≤ Real.log N := Real.log_nonneg hN
  obtain ⟨hc1, hc3⟩ := three_log_two_sub_gamma_bounds
  have ha0 : 0 ≤ 1 / Real.sqrt N := by positivity
  have ha1 : 1 / Real.sqrt N ≤ 1 := by rw [div_le_one hsN]; exact hsN1
  -- the decomposition and the constant
  have hdec := sqrt_mul_gaussLaplaceL_three_eq hN
  have hQ : depthThreeQint = (∫ v in Ioc (0 : ℝ) 1, depthThreeQ v) +
      ∫ v in Ioi (1 : ℝ), depthThreeQ v := by
    unfold depthThreeQint
    rw [← Ioc_union_Ioi_eq_Ioi zero_le_one,
      setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
        integrableOn_depthThreeQ_inner integrableOn_depthThreeQ_outer]
  have hI := inner_rate hN
  have hE := rem_rate hN
  have hIa := abs_integral_gaussH_div_Ioc_le ha0 ha1
  rw [div_pow, one_pow, Real.sq_sqrt hN0.le] at hIa
  -- `J_a − J`
  have hJa : |(∫ x in Ioi (1 / Real.sqrt N), gaussH x * Real.log x / x) - gaussJlog| ≤
      1 / Real.sqrt N / 2 := by
    have hsplit : gaussJlog = (∫ x in Ioc (0 : ℝ) (1 / Real.sqrt N), gaussH x * Real.log x / x) +
        ∫ x in Ioi (1 / Real.sqrt N), gaussH x * Real.log x / x := by
      unfold gaussJlog
      rw [← Ioc_union_Ioi_eq_Ioi ha0,
        setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
          (integrableOn_gaussH_log_Ioc le_rfl |>.mono_set (Ioc_subset_Ioc_right ha1))
          (integrableOn_gaussH_log ha0 ha1)]
    rw [hsplit, show ∀ A B : ℝ, B - (A + B) = -A from fun A B => by ring, abs_neg]
    have hb := norm_setIntegral_le_of_norm_le_const (μ := volume)
      (s := Ioc (0 : ℝ) (1 / Real.sqrt N)) (f := fun x => gaussH x * Real.log x / x) (C := 1 / 2)
      measure_Ioc_lt_top (fun x hx => norm_gaussH_log_inner ⟨hx.1, hx.2.trans ha1⟩)
    rw [Real.norm_eq_abs, measureReal_def, Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal ha0]
      at hb
    linarith
  -- assemble: the residual is the sum of four small pieces
  set ℓ := Real.log N with hℓdef
  set c := 3 * Real.log 2 - Real.eulerMascheroniConstant with hc
  set d := Real.log 2 - Real.eulerMascheroniConstant with hd
  set I₀ := ∫ x in Ioc (0 : ℝ) (1 / Real.sqrt N), depthThreeF N x with hI₀
  set E := ∫ x in Ioi (1 / Real.sqrt N), (depthThreeF N x - gaussDensity x *
    ((Real.log N + 2 * Real.log x + 3 * Real.log 2 - Real.eulerMascheroniConstant) /
      (Real.sqrt (2 * Real.pi) * (Real.sqrt N * x)))) with hEdef
  set Ia := ∫ x in Ioc (0 : ℝ) (1 / Real.sqrt N), gaussH x / x with hIa'
  set Ja := ∫ x in Ioi (1 / Real.sqrt N), gaussH x * Real.log x / x with hJa'
  set Q₁ := ∫ v in Ioc (0 : ℝ) 1, depthThreeQ v with hQ₁
  set Q₂ := ∫ v in Ioi (1 : ℝ), depthThreeQ v with hQ₂
  set J := gaussJlog with hJ
  set s := Real.sqrt (2 * Real.pi) with hsdef
  have hconst : depthThreeConst = (c * (d / 2) + 2 * J) / Real.pi + 2 / s * (Q₁ + Q₂) := by
    unfold depthThreeConst
    rw [hQ, ← hc, ← hd, ← hJ, ← hsdef]
  clear_value I₀ E Ia Ja Q₁ Q₂ J s ℓ c d
  rw [hconst]
  have hkey : Real.sqrt N * gaussLaplaceL 3 N - (ℓ ^ 2 / (4 * Real.pi) +
      (2 * Real.log 2 - Real.eulerMascheroniConstant) / Real.pi * ℓ +
      ((c * (d / 2) + 2 * J) / Real.pi + 2 / s * (Q₁ + Q₂))) =
      2 * (Real.sqrt N * I₀ - 1 / s * Q₁) + 2 * (Real.sqrt N * E - 1 / s * Q₂) -
        1 / Real.pi * ((ℓ + c) * Ia) + 2 / Real.pi * (Ja - J) := by
    linear_combination hdec
  rw [hkey]
  clear hI₀ hEdef hIa' hJa' hQ₁ hQ₂ hJ hsdef hℓdef hc hd hQ hdec hconst hkey
  -- the four bounds against `8(1+ℓ)/√N`
  have hb1 : |2 * (Real.sqrt N * I₀ - 1 / s * Q₁)| ≤ 1 / Real.sqrt N := by
    rw [abs_mul, abs_of_pos two_pos]
    calc 2 * |Real.sqrt N * I₀ - 1 / s * Q₁| ≤ 2 * (1 / (2 * s * N)) :=
          mul_le_mul_of_nonneg_left hI two_pos.le
      _ = 1 / (s * N) := by field_simp
      _ ≤ 1 / Real.sqrt N := by
          rw [div_le_div_iff₀ (by positivity) hsN]
          nlinarith
  have hb2 : |2 * (Real.sqrt N * E - 1 / s * Q₂)| ≤ 3 / Real.sqrt N := by
    rw [abs_mul, abs_of_pos two_pos]
    calc 2 * |Real.sqrt N * E - 1 / s * Q₂| ≤ 2 * (6 / (s ^ 2 * Real.sqrt N)) :=
          mul_le_mul_of_nonneg_left hE two_pos.le
      _ = 12 / s ^ 2 / Real.sqrt N := by field_simp; norm_num
      _ ≤ 3 / Real.sqrt N := by
          refine div_le_div_of_nonneg_right ?_ hsN.le
          rw [div_le_iff₀ (by positivity)]
          nlinarith
  have hb3 : |1 / Real.pi * ((ℓ + c) * Ia)| ≤ (ℓ + 3) / Real.sqrt N := by
    rw [abs_mul, abs_of_pos (by positivity), abs_mul, abs_of_nonneg (by linarith)]
    have hIabs : |Ia| ≤ 1 / N / 2 := hIa
    calc 1 / Real.pi * ((ℓ + c) * |Ia|) ≤ 1 / Real.pi * ((ℓ + 3) * (1 / N / 2)) := by gcongr
      _ = (ℓ + 3) / (2 * Real.pi * N) := by field_simp
      _ ≤ (ℓ + 3) / Real.sqrt N := by
          refine div_le_div_of_nonneg_left (by linarith) hsN ?_
          nlinarith
  have hb4 : |2 / Real.pi * (Ja - J)| ≤ 1 / Real.sqrt N := by
    rw [abs_mul, abs_of_pos (by positivity)]
    calc 2 / Real.pi * |Ja - J| ≤ 2 / Real.pi * (1 / Real.sqrt N / 2) :=
          mul_le_mul_of_nonneg_left hJa (by positivity)
      _ = 1 / Real.pi / Real.sqrt N := by field_simp
      _ ≤ 1 / Real.sqrt N := by
          refine div_le_div_of_nonneg_right ?_ hsN.le
          rw [div_le_one (by positivity)]; linarith
  calc |2 * (Real.sqrt N * I₀ - 1 / s * Q₁) + 2 * (Real.sqrt N * E - 1 / s * Q₂) -
        1 / Real.pi * ((ℓ + c) * Ia) + 2 / Real.pi * (Ja - J)|
      ≤ |2 * (Real.sqrt N * I₀ - 1 / s * Q₁)| + |2 * (Real.sqrt N * E - 1 / s * Q₂)| +
        |1 / Real.pi * ((ℓ + c) * Ia)| + |2 / Real.pi * (Ja - J)| := by
        have t1 := abs_add_le (2 * (Real.sqrt N * I₀ - 1 / s * Q₁))
          (2 * (Real.sqrt N * E - 1 / s * Q₂))
        have t2 := abs_sub (2 * (Real.sqrt N * I₀ - 1 / s * Q₁) +
          2 * (Real.sqrt N * E - 1 / s * Q₂)) (1 / Real.pi * ((ℓ + c) * Ia))
        have t3 := abs_add_le (2 * (Real.sqrt N * I₀ - 1 / s * Q₁) +
          2 * (Real.sqrt N * E - 1 / s * Q₂) - 1 / Real.pi * ((ℓ + c) * Ia))
          (2 / Real.pi * (Ja - J))
        linarith
    _ ≤ 1 / Real.sqrt N + 3 / Real.sqrt N + (ℓ + 3) / Real.sqrt N + 1 / Real.sqrt N := by
        linarith
    _ = (ℓ + 8) / Real.sqrt N := by ring
    _ ≤ 8 * (1 + ℓ) / Real.sqrt N := by
        refine div_le_div_of_nonneg_right ?_ hsN.le
        linarith

end Grammar
