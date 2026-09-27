/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.GaussianDepthFourRate

/-!
# The residual and cutoff bounds, generically

The two quantitative lemmas of DCLII, stated for an arbitrary residual and an arbitrary log-moment
so that every depth's rate is an instance (Astra round 18: "prove the two quantitative lemmas
first and use depth five as their acceptance test"):

* `residual_term_bound_of_le` : for measurable `q` with `|q| ≤ 1` on `(0,1]` and
  `|q(v)| ≤ K(1 + 2 log v)/v²` on `(1,∞)`,
  `|2∫₀^∞ γ(v/√N) q − (2/s)∫₀^∞ q| ≤ (2/s)[1/(2N) + K(1+ℓ)/(2√N) + K(3+ℓ)/√N]` for `N ≥ 1`
  (the split `(0,1] ∪ (1,√N] ∪ (√N,∞)`; the logarithmic exponent is preserved);
* `abs_integral_gaussH_log_pow_Ioc_le_sqrt` : the cutoff moment
  `|∫₀^a h log^j x/x| ≤ (2j)^j/3 · a√a` for `0 < a ≤ 1` — one power of `√a` better than DCLI's
  `(j+1)^j a/2`, from `|h(x)| ≤ x²/2` and
  `|log x|^j ≤ (2j)^j/√x` on `(0,1]` (`abs_log_pow_le_div_sqrt`), so that the cutoff products
  `c_j(ℓ)ε_j` of a degree-`d` polynomial cost `(1+ℓ)^d N^{−3/4}`, which is `O((1+ℓ)/√N)` as soon
  as `(1+ℓ)^{d−1} ≤ C N^{1/4}` (`one_add_log_le_nine_mul_rpow`: `1 + log N ≤ 9N^{1/8}`).
Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

/-! ### The residual term, generically -/

theorem integrableOn_of_le_one_add_two_log {q : ℝ → ℝ} (hq : Measurable q) {K : ℝ}
    (hin : ∀ v ∈ Ioc (0 : ℝ) 1, |q v| ≤ 1)
    (hout : ∀ v : ℝ, 1 < v → |q v| ≤ K * (1 + 2 * Real.log v) / v ^ 2) :
    IntegrableOn q (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  refine IntegrableOn.union ?_ ?_
  · refine Measure.integrableOn_of_bounded (M := 1) measure_Ioc_lt_top.ne
      hq.aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    exact Eventually.of_forall fun v hv => by rw [Real.norm_eq_abs]; exact hin v hv
  · have h : IntegrableOn (fun v : ℝ => K * v ^ (-2 : ℝ) + 2 * K * (v ^ (-2 : ℝ) * Real.log v))
        (Ioi 1) := by
      have h1 := (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) one_pos).const_mul K
      have h2 := (integrableOn_Ioi_one_rpow_mul_log (z := 0) (by norm_num)).const_mul (2 * K)
      refine IntegrableOn.congr_fun (h1.add h2) (fun v _ => ?_) measurableSet_Ioi
      simp only [Pi.add_apply, zero_sub]
    refine h.mono' hq.aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun v hv => ?_
    have hv1 : (1 : ℝ) < v := hv
    have hv0 : 0 < v := by linarith
    rw [Real.norm_eq_abs]
    refine (hout v hv1).trans (le_of_eq ?_)
    rw [Real.rpow_neg hv0.le, Real.rpow_two]
    field_simp

theorem integrableOn_gaussDensity_div_mul_of_integrableOn {q : ℝ → ℝ} (hq : Measurable q)
    (hqi : IntegrableOn q (Ioi 0)) {N : ℝ} :
    IntegrableOn (fun v : ℝ => gaussDensity (v / Real.sqrt N) * q v) (Ioi 0) := by
  refine (hqi.abs.const_mul (1 / Real.sqrt (2 * Real.pi))).mono'
    ((continuous_gaussDensity.comp (continuous_id.div_const _)).measurable.mul
      hq).aestronglyMeasurable (Eventually.of_forall fun v => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gaussDensity_nonneg _)]
  exact mul_le_mul_of_nonneg_right (gaussDensity_le_inv_sqrt _) (abs_nonneg _)

/-- ★★ **The residual term, quantitatively and generically**: for measurable `q` with `|q| ≤ 1`
on `(0,1]` and `|q(v)| ≤ K(1 + 2 log v)/v²` on `(1,∞)`,
`|2∫ γ(v/√N) q − (2/s)∫ q| ≤ (2/s)[1/(2N) + K(1+ℓ)/(2√N) + K(3+ℓ)/√N]` for `N ≥ 1`
(DCLII's `residual_term_bound` is the instance `K = 8`). -/
theorem residual_term_bound_of_le {q : ℝ → ℝ} (hq : Measurable q) {K : ℝ} (hK : 0 ≤ K)
    (hin : ∀ v ∈ Ioc (0 : ℝ) 1, |q v| ≤ 1)
    (hout : ∀ v : ℝ, 1 < v → |q v| ≤ K * (1 + 2 * Real.log v) / v ^ 2)
    {N : ℝ} (hN : 1 ≤ N) :
    |2 * (∫ v in Ioi (0 : ℝ), gaussDensity (v / Real.sqrt N) * q v) -
      2 / Real.sqrt (2 * Real.pi) * ∫ v in Ioi (0 : ℝ), q v| ≤
      2 / Real.sqrt (2 * Real.pi) *
        (1 / (2 * N) + K * (1 + Real.log N) / (2 * Real.sqrt N) +
          K * (3 + Real.log N) / Real.sqrt N) := by
  have hN0 : 0 < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have hsN1 : 1 ≤ Real.sqrt N := Real.one_le_sqrt.2 hN
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hℓ : 0 ≤ Real.log N := Real.log_nonneg hN
  have hlogR : Real.log (Real.sqrt N) = Real.log N / 2 := Real.log_sqrt hN0.le
  have hqi : IntegrableOn q (Ioi 0) := integrableOn_of_le_one_add_two_log hq hin hout
  set s := Real.sqrt (2 * Real.pi) with hs_def
  have hdiff : 2 * (∫ v in Ioi (0 : ℝ), gaussDensity (v / Real.sqrt N) * q v) -
      2 / s * ∫ v in Ioi (0 : ℝ), q v =
      2 * ∫ v in Ioi (0 : ℝ), (gaussDensity (v / Real.sqrt N) - 1 / s) * q v := by
    rw [show 2 / s * ∫ v in Ioi (0 : ℝ), q v = 2 * ∫ v in Ioi (0 : ℝ), 1 / s * q v
      by rw [integral_const_mul]; ring, ← mul_sub,
      ← integral_sub (integrableOn_gaussDensity_div_mul_of_integrableOn hq hqi (N := N))
        (hqi.const_mul _)]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
    ring
  rw [hdiff, abs_mul, abs_two]
  rw [show 2 / s * (1 / (2 * N) + K * (1 + Real.log N) / (2 * Real.sqrt N) +
      K * (3 + Real.log N) / Real.sqrt N) =
      2 * ((1 / s) * (1 / (2 * N) + K * (1 + Real.log N) / (2 * Real.sqrt N) +
        K * (3 + Real.log N) / Real.sqrt N)) by ring]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  set g : ℝ → ℝ := fun v => (Ioc (0 : ℝ) 1).indicator (fun _ => 1 / (2 * N)) v +
    (Ioc (1 : ℝ) (Real.sqrt N)).indicator (fun v => K * (1 + 2 * Real.log v) / (2 * N)) v +
    (Ioi (Real.sqrt N)).indicator (fun v => K * ((1 + 2 * Real.log v) / v ^ 2)) v with hg
  have hpt : ∀ v ∈ Ioi (0 : ℝ), |(gaussDensity (v / Real.sqrt N) - 1 / s) * q v| ≤
      1 / s * g v := by
    intro v hv
    have hv0 : (0 : ℝ) < v := hv
    have hγ : |gaussDensity (v / Real.sqrt N) - 1 / s| ≤ (v / Real.sqrt N) ^ 2 / (2 * s) :=
      abs_gaussDensity_sub_le _
    have hγ' : |gaussDensity (v / Real.sqrt N) - 1 / s| ≤ 1 / s := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith [gaussDensity_le (v / Real.sqrt N)])]
      linarith [gaussDensity_nonneg (v / Real.sqrt N)]
    rw [div_pow, Real.sq_sqrt hN0.le] at hγ
    rw [abs_mul]
    simp only [hg]
    rcases le_or_gt v 1 with h1 | h1
    · have hq1 : |q v| ≤ 1 := hin v ⟨hv0, h1⟩
      rw [indicator_of_mem (show v ∈ Ioc (0 : ℝ) 1 from ⟨hv0, h1⟩),
        indicator_of_notMem (fun hm : v ∈ Ioc (1 : ℝ) (Real.sqrt N) => absurd h1 (not_le.2 hm.1)),
        indicator_of_notMem (fun hm : v ∈ Ioi (Real.sqrt N) => by
          have : Real.sqrt N < v := hm; linarith), add_zero, add_zero]
      have hv2 : v ^ 2 / N / (2 * s) ≤ 1 / (2 * N) / s := by
        have hvv : v ^ 2 ≤ 1 := by nlinarith
        calc v ^ 2 / N / (2 * s) ≤ 1 / N / (2 * s) := by gcongr
          _ = 1 / (2 * N) / s := by ring
      calc |gaussDensity (v / Real.sqrt N) - 1 / s| * |q v|
          ≤ (v ^ 2 / N / (2 * s)) * 1 := mul_le_mul hγ hq1 (abs_nonneg _) (by positivity)
        _ ≤ 1 / (2 * N) / s := by rw [mul_one]; exact hv2
        _ = 1 / s * (1 / (2 * N)) := by ring
    · rcases le_or_gt v (Real.sqrt N) with h2 | h2
      · have hq1 := hout v h1
        rw [indicator_of_notMem (fun hm : v ∈ Ioc (0 : ℝ) 1 => absurd hm.2 (not_le.2 h1)),
          indicator_of_mem (show v ∈ Ioc (1 : ℝ) (Real.sqrt N) from ⟨h1, h2⟩),
          indicator_of_notMem (fun hm : v ∈ Ioi (Real.sqrt N) => absurd h2 (not_le.2 hm)),
          zero_add, add_zero]
        have hl : 0 ≤ 1 + 2 * Real.log v := by linarith [Real.log_nonneg h1.le]
        calc |gaussDensity (v / Real.sqrt N) - 1 / s| * |q v|
            ≤ (v ^ 2 / N / (2 * s)) * (K * (1 + 2 * Real.log v) / v ^ 2) :=
              mul_le_mul hγ hq1 (abs_nonneg _) (by positivity)
          _ = 1 / s * (K * (1 + 2 * Real.log v) / (2 * N)) := by
              field_simp
      · have hq1 := hout v h1
        rw [indicator_of_notMem (fun hm : v ∈ Ioc (0 : ℝ) 1 => absurd hm.2 (not_le.2 h1)),
          indicator_of_notMem (fun hm : v ∈ Ioc (1 : ℝ) (Real.sqrt N) => absurd hm.2 (not_le.2 h2)),
          indicator_of_mem (show v ∈ Ioi (Real.sqrt N) from h2), zero_add, zero_add]
        calc |gaussDensity (v / Real.sqrt N) - 1 / s| * |q v|
            ≤ 1 / s * (K * (1 + 2 * Real.log v) / v ^ 2) :=
              mul_le_mul hγ' hq1 (abs_nonneg _) (by positivity)
          _ = 1 / s * (K * ((1 + 2 * Real.log v) / v ^ 2)) := by rw [mul_div_assoc]
  have hi1 : IntegrableOn (fun v : ℝ => (Ioc (0 : ℝ) 1).indicator (fun _ => 1 / (2 * N)) v)
      (Ioi 0) :=
    ((integrableOn_const (C := 1 / (2 * N)) (s := Ioc (0 : ℝ) 1)
      (hs := measure_Ioc_lt_top.ne)).integrable_indicator measurableSet_Ioc).integrableOn
  have hi2 : IntegrableOn (fun v : ℝ => (Ioc (1 : ℝ) (Real.sqrt N)).indicator
      (fun v => K * (1 + 2 * Real.log v) / (2 * N)) v) (Ioi 0) := by
    have hlog : ContinuousOn (fun v : ℝ => Real.log v) (Icc 1 (Real.sqrt N)) :=
      Real.continuousOn_log.mono fun v hv =>
        mem_compl_singleton_iff.2 (ne_of_gt (lt_of_lt_of_le one_pos hv.1))
    have hc : ContinuousOn (fun v : ℝ => K * (1 + 2 * Real.log v) / (2 * N))
        (Icc 1 (Real.sqrt N)) :=
      (continuousOn_const.mul (continuousOn_const.add (continuousOn_const.mul hlog))).div_const _
    exact ((hc.integrableOn_Icc).mono_set Ioc_subset_Icc_self
      |>.integrable_indicator measurableSet_Ioc).integrableOn
  have hi3 : IntegrableOn (fun v : ℝ => (Ioi (Real.sqrt N)).indicator
      (fun v => K * ((1 + 2 * Real.log v) / v ^ 2)) v) (Ioi 0) := by
    have h0 := integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hsN
    have h1 := (integrableOn_Ioi_one_rpow_mul_log (z := 0) (by norm_num)).mono_set
      (Ioi_subset_Ioi hsN1)
    refine (IntegrableOn.congr_fun ((h0.const_mul K).add (h1.const_mul (2 * K)))
      (fun v hv => ?_) measurableSet_Ioi |>.integrable_indicator measurableSet_Ioi).integrableOn
    have hv0 : (0 : ℝ) < v := lt_of_lt_of_le hsN (le_of_lt hv)
    simp only [Pi.add_apply, zero_sub]
    rw [Real.rpow_neg hv0.le, Real.rpow_two]
    field_simp
  have hg_int : IntegrableOn g (Ioi 0) := by
    simp only [hg]
    exact (hi1.add hi2).add hi3
  have hg_le : ∫ v in Ioi (0 : ℝ), g v ≤ 1 / (2 * N) + K * (1 + Real.log N) / (2 * Real.sqrt N) +
      K * (3 + Real.log N) / Real.sqrt N := by
    have h12 : IntegrableOn (fun v : ℝ => (Ioc (0 : ℝ) 1).indicator (fun _ => 1 / (2 * N)) v +
        (Ioc (1 : ℝ) (Real.sqrt N)).indicator (fun v => K * (1 + 2 * Real.log v) / (2 * N)) v)
        (Ioi 0) := hi1.add hi2
    simp only [hg]
    rw [integral_add h12 hi3, integral_add hi1 hi2, setIntegral_indicator measurableSet_Ioc,
      setIntegral_indicator measurableSet_Ioc, setIntegral_indicator measurableSet_Ioi,
      show Ioi (0 : ℝ) ∩ Ioc 0 1 = Ioc 0 1 from inter_eq_right.2 fun v hv => hv.1,
      show Ioi (0 : ℝ) ∩ Ioc 1 (Real.sqrt N) = Ioc 1 (Real.sqrt N) from
        inter_eq_right.2 fun v (hv : v ∈ Ioc (1 : ℝ) (Real.sqrt N)) =>
          (show (0 : ℝ) < v from lt_trans one_pos hv.1),
      show Ioi (0 : ℝ) ∩ Ioi (Real.sqrt N) = Ioi (Real.sqrt N) from
        inter_eq_right.2 fun v (hv : Real.sqrt N < v) => (show (0 : ℝ) < v from lt_trans hsN hv),
      integral_const_mul, integral_Ioi_one_add_two_log_div_sq hsN1, hlogR]
    have hc : ∫ _v in Ioc (0 : ℝ) 1, (1 / (2 * N) : ℝ) = 1 / (2 * N) := by
      rw [setIntegral_const, measureReal_def, Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal
        zero_le_one, one_smul]
    have hm : ∫ v in Ioc (1 : ℝ) (Real.sqrt N), K * (1 + 2 * Real.log v) / (2 * N) ≤
        K * (1 + Real.log N) / (2 * Real.sqrt N) := by
      have hb := norm_setIntegral_le_of_norm_le_const (μ := volume)
        (s := Ioc (1 : ℝ) (Real.sqrt N)) (f := fun v => K * (1 + 2 * Real.log v) / (2 * N))
        (C := K * (1 + Real.log N) / (2 * N)) measure_Ioc_lt_top (fun v hv => by
          have hv1 : (1 : ℝ) < v := hv.1
          have hl : Real.log v ≤ Real.log N / 2 := by
            rw [← hlogR]; exact Real.log_le_log (by linarith) hv.2
          rw [Real.norm_eq_abs, abs_of_nonneg (by
            have := Real.log_nonneg hv1.le; positivity)]
          apply div_le_div_of_nonneg_right _ (by positivity)
          have := Real.log_nonneg hv1.le
          nlinarith)
      rw [Real.norm_eq_abs] at hb
      refine (le_abs_self _).trans (hb.trans ?_)
      rw [measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
      have hdiv : Real.sqrt N / N = 1 / Real.sqrt N := by
        field_simp
        exact Real.sq_sqrt hN0.le
      calc K * (1 + Real.log N) / (2 * N) * (Real.sqrt N - 1)
          ≤ K * (1 + Real.log N) / (2 * N) * Real.sqrt N := by gcongr; linarith
        _ = K * (1 + Real.log N) / 2 * (Real.sqrt N / N) := by ring
        _ = K * (1 + Real.log N) / (2 * Real.sqrt N) := by rw [hdiv]; ring
    rw [hc]
    have h3 : K * ((3 + 2 * (Real.log N / 2)) / Real.sqrt N) =
        K * (3 + Real.log N) / Real.sqrt N := by
      ring
    rw [h3]
    linarith
  calc |∫ v in Ioi (0 : ℝ), (gaussDensity (v / Real.sqrt N) - 1 / s) * q v|
      ≤ ∫ v in Ioi (0 : ℝ), 1 / s * g v := by
        refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
          (Eventually.of_forall fun v => abs_nonneg _) (hg_int.const_mul _) ?_)
        rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioi]
        exact Eventually.of_forall hpt
    _ = 1 / s * ∫ v in Ioi (0 : ℝ), g v := integral_const_mul _ _
    _ ≤ 1 / s * (1 / (2 * N) + K * (1 + Real.log N) / (2 * Real.sqrt N) +
        K * (3 + Real.log N) / Real.sqrt N) := mul_le_mul_of_nonneg_left hg_le (by positivity)

/-! ### The cutoff moments, with the extra `√a` -/

/-- `|log x|^j ≤ (2j)^j/√x` on `(0,1]`. -/
theorem abs_log_pow_le_div_sqrt {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) (j : ℕ) :
    |Real.log x| ^ j ≤ (2 * j) ^ j / Real.sqrt x := by
  have hx0 : 0 < x := hx.1
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hsx1 : Real.sqrt x ≤ 1 := by
    rw [Real.sqrt_le_one]; exact hx.2
  rcases Nat.eq_zero_or_pos j with hj | hj
  · subst hj
    simp only [pow_zero, Nat.cast_zero, mul_zero]
    rw [le_div_iff₀ hsx, one_mul]; exact hsx1
  · have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
    set ε : ℝ := 1 / (2 * j) with hε
    have hε0 : 0 < ε := by positivity
    have hlog : -Real.log x ≤ 2 * j * x ^ (-ε) := by
      have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx0 (-ε))
      rw [Real.log_rpow hx0] at h
      have h1 : 0 < x ^ (-ε) := Real.rpow_pos_of_pos hx0 _
      have h2 : -ε * Real.log x ≤ x ^ (-ε) := by linarith
      have h3 : -Real.log x ≤ x ^ (-ε) / ε := by
        rw [le_div_iff₀ hε0]; linarith
      calc -Real.log x ≤ x ^ (-ε) / ε := h3
        _ = 2 * j * x ^ (-ε) := by rw [hε]; field_simp
    have hlog0 : 0 ≤ -Real.log x := by linarith [Real.log_nonpos hx0.le hx.2]
    rw [abs_of_nonpos (Real.log_nonpos hx0.le hx.2)]
    calc (-Real.log x) ^ j ≤ (2 * j * x ^ (-ε)) ^ j := pow_le_pow_left₀ hlog0 hlog j
      _ = (2 * j) ^ j * (x ^ (-ε)) ^ j := mul_pow _ _ _
      _ = (2 * j) ^ j / Real.sqrt x := by
          rw [← Real.rpow_natCast (x ^ (-ε)) j, ← Real.rpow_mul hx0.le, Real.sqrt_eq_rpow,
            div_eq_mul_inv, ← Real.rpow_neg hx0.le]
          congr 2
          rw [hε]; field_simp

/-- ★★ The cutoff moment with the extra `√a`: `|∫₀^a h log^j x/x| ≤ (2j)^j/3 · a√a` for
`0 < a ≤ 1`. -/
theorem abs_integral_gaussH_log_pow_Ioc_le_sqrt (j : ℕ) {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) :
    |∫ x in Ioc (0 : ℝ) a, gaussH x * Real.log x ^ j / x| ≤
      (2 * j) ^ j / 3 * (a * Real.sqrt a) := by
  have hmaj : IntegrableOn (fun x : ℝ => (2 * j) ^ j / 2 * x ^ (1 / 2 : ℝ)) (Ioc 0 a) := by
    have := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := a) (r := (1 / 2 : ℝ))
      (by norm_num)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ha0.le] at this
    exact this.const_mul _
  have hpt : ∀ x ∈ Ioc (0 : ℝ) a, ‖gaussH x * Real.log x ^ j / x‖ ≤
      (2 * j) ^ j / 2 * x ^ (1 / 2 : ℝ) := by
    intro x hx
    have hx0 : 0 < x := hx.1
    have hx' : x ∈ Ioc (0 : ℝ) 1 := ⟨hx0, hx.2.trans ha1⟩
    have hsx : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
    obtain ⟨h1, h2⟩ := gaussH_inner hx'
    have hh : |gaussH x| ≤ x ^ 2 / 2 := by
      rw [abs_of_nonpos h2]; linarith
    have hl := abs_log_pow_le_div_sqrt hx' j
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_pow, abs_of_pos hx0, div_le_iff₀ hx0,
      ← Real.sqrt_eq_rpow]
    calc |gaussH x| * |Real.log x| ^ j ≤ x ^ 2 / 2 * ((2 * j) ^ j / Real.sqrt x) :=
          mul_le_mul hh hl (by positivity) (by positivity)
      _ = (2 * j) ^ j / 2 * Real.sqrt x * x := by
          have hxx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
          field_simp
          nlinarith [hxx]
  have h := norm_integral_le_of_norm_le (μ := volume.restrict (Ioc (0 : ℝ) a)) hmaj
    ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall hpt))
  rw [Real.norm_eq_abs] at h
  refine h.trans (le_of_eq ?_)
  rw [integral_const_mul, ← intervalIntegral.integral_of_le ha0.le,
    integral_rpow (Or.inl (by norm_num)), Real.zero_rpow (by norm_num), sub_zero]
  have e : a ^ ((1 / 2 : ℝ) + 1) = a * Real.sqrt a := by
    rw [Real.rpow_add ha0, Real.rpow_one, Real.sqrt_eq_rpow]; ring
  rw [e]
  ring

end Grammar
