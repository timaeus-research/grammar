/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.GaussianDepthFourConst
import Grammar.GaussianThirdCoeffClosed
import Grammar.MellinLogPolynomialTransfer

/-!
# The depth-four constant with a rate

`|√N Z₄ − A₄ℓ³ − B₄ℓ² − C₄ℓ − D₄| ≤ K (1 + ℓ)²/√N` for `N ≥ 1`
(★★★ `gaussLaplaceL_four_constant_rate`): DCLI's exact remainder identity with the
dominated-convergence step made quantitative by splitting at `R = √N` —
`|γ(v/√N) − γ(0)| ≤ v²/(2sN)` on `v ≤ R` (so the residual `|q₃| ≤ 8(1 + 2 log v)/v²` costs
`O((1 + ℓ)/√N)` on `(1, R]` and `O(1/N)` on `(0,1]`) and `≤ 1/s` beyond (`∫_R^∞ (1 + 2 log v)/v² =
(3 + 2 log R)/R`) — and the cutoff `h`-moments bounded by `(j+1)^j/(2√N)`.  Also the two polish
items of Astra round 16: the third-coefficient limit restated with the closed form
(`gaussLaplaceL_third_coeff_closed`) and the bridge `depthFourTail = mellinLogTail ![C₃, 2B₃, 4A₃]`
(`depthFourTail_eq_mellinLogTail`).  Examples_slop §2; Astra round-16 target 1.
Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

/-! ### Polish -/

/-- The third-coefficient limit with the closed form in the target. -/
theorem gaussLaplaceL_third_coeff_closed (m : ℕ) :
    Tendsto (fun N : ℝ => (Real.sqrt N * gaussLaplaceL (m + 4) N -
      gaussCoeffA m * (Real.log N) ^ (m + 3) - gaussCoeffB m * (Real.log N) ^ (m + 2)) /
        (Real.log N) ^ (m + 1)) atTop (𝓝 (thirdCoeffClosed m)) := by
  rw [← thirdCoeff_eq_closed]
  exact gaussLaplaceL_third_coeff m

/-- `depthFourTail = mellinLogTail ![C₃, 2B₃, 4A₃]`: the depth-four tail is the log-polynomial tail
of DCXLIX with coefficients `p₀ = C₃`, `p₁ = 2B₃`, `p₂ = 4A₃` (the jet is evaluated at
`2 log v`). -/
theorem depthFourTail_eq_mellinLogTail (v : ℝ) :
    depthFourTail v = mellinLogTail ![depthThreeConst,
      2 * ((2 * Real.log 2 - Real.eulerMascheroniConstant) / Real.pi),
      4 * (1 / (4 * Real.pi))] v := by
  unfold depthFourTail mellinLogTail depthThreeJet
  by_cases h : 1 < v
  · rw [indicator_of_mem (show v ∈ Ioi (1 : ℝ) from h), if_pos h]
    simp [Fin.sum_univ_succ]
    ring
  · rw [indicator_of_notMem (fun hm : v ∈ Ioi (1 : ℝ) => h hm), if_neg h]

/-! ### The tail integral `∫_R^∞ (1 + 2 log v)/v²` -/

/-- `∫_R^∞ (1 + 2 log v)/v² dv = (3 + 2 log R)/R` for `R ≥ 1`. -/
theorem integral_Ioi_one_add_two_log_div_sq {R : ℝ} (hR : 1 ≤ R) :
    ∫ v in Ioi R, (1 + 2 * Real.log v) / v ^ 2 = (3 + 2 * Real.log R) / R := by
  have hR0 : 0 < R := by linarith
  set F : ℝ → ℝ := fun v => -((3 + 2 * Real.log v) / v) with hF
  have hderiv : ∀ v : ℝ, 0 < v → HasDerivAt F ((1 + 2 * Real.log v) / v ^ 2) v := by
    intro v hv
    have h1 : HasDerivAt (fun v : ℝ => 3 + 2 * Real.log v) (2 * v⁻¹) v :=
      ((Real.hasDerivAt_log hv.ne').const_mul 2).const_add 3
    have h2 : HasDerivAt (fun v : ℝ => v) 1 v := hasDerivAt_id' (x := v)
    refine ((h1.div h2 hv.ne').neg).congr_deriv ?_
    field_simp
    try ring
  have hint : IntegrableOn (fun v : ℝ => (1 + 2 * Real.log v) / v ^ 2) (Ioi R) := by
    have h0 := integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hR0
    have h1 := (integrableOn_Ioi_one_rpow_mul_log (z := 0) (by norm_num)).mono_set
      (Ioi_subset_Ioi hR)
    refine IntegrableOn.congr_fun (h0.add (h1.const_mul 2)) (fun v hv => ?_) measurableSet_Ioi
    have hv0 : (0 : ℝ) < v := lt_of_lt_of_le hR0 (le_of_lt hv)
    simp only [Pi.add_apply, zero_sub]
    rw [Real.rpow_neg hv0.le, Real.rpow_two]
    field_simp
  have hlim : Tendsto F atTop (𝓝 0) := by
    have h1 : Tendsto (fun v : ℝ => 3 / v) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
    have h2 := tendsto_log_div_atTop.const_mul 2
    simp only [mul_zero] at h2
    have := (h1.add h2).neg
    simp only [neg_zero, add_zero] at this
    refine this.congr fun v => ?_
    simp only [hF]
    try ring
  rw [integral_Ioi_of_hasDerivAt_of_tendsto (f := F) (hderiv R hR0).continuousAt.continuousWithinAt
    (fun v (hv : R < v) => hderiv v (by linarith)) hint hlim]
  simp only [hF]
  ring

/-! ### The residual term, quantitatively -/

/-- `|2∫ γ(v/√N) q₃ − (2/s) Q₃| ≤ (2/s)[1/(2N) + 4(1 + ℓ)/√N + 8(3 + ℓ)/√N]` for `N ≥ 1`. -/
theorem residual_term_bound {N : ℝ} (hN : 1 ≤ N) :
    |2 * (∫ v in Ioi (0 : ℝ), gaussDensity (v / Real.sqrt N) * depthFourQ v) -
      2 / Real.sqrt (2 * Real.pi) * depthFourQint| ≤
      2 / Real.sqrt (2 * Real.pi) *
        (1 / (2 * N) + 4 * (1 + Real.log N) / Real.sqrt N +
          8 * (3 + Real.log N) / Real.sqrt N) := by
  have hN0 : 0 < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have hsN1 : 1 ≤ Real.sqrt N := Real.one_le_sqrt.2 hN
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hℓ : 0 ≤ Real.log N := Real.log_nonneg hN
  have hlogR : Real.log (Real.sqrt N) = Real.log N / 2 := Real.log_sqrt hN0.le
  set s := Real.sqrt (2 * Real.pi) with hs_def
  -- the difference as one integral
  have hdiff : 2 * (∫ v in Ioi (0 : ℝ), gaussDensity (v / Real.sqrt N) * depthFourQ v) -
      2 / s * depthFourQint =
      2 * ∫ v in Ioi (0 : ℝ), (gaussDensity (v / Real.sqrt N) - 1 / s) * depthFourQ v := by
    unfold depthFourQint
    rw [show 2 / s * ∫ v in Ioi (0 : ℝ), depthFourQ v = 2 * ∫ v in Ioi (0 : ℝ), 1 / s * depthFourQ v
      by rw [integral_const_mul]; ring, ← mul_sub,
      ← integral_sub (integrableOn_gaussDensity_div_mul_depthFourQ (N := N))
        (integrableOn_depthFourQ.const_mul _)]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
    ring
  rw [hdiff, abs_mul, abs_two]
  rw [show 2 / s * (1 / (2 * N) + 4 * (1 + Real.log N) / Real.sqrt N +
      8 * (3 + Real.log N) / Real.sqrt N) =
      2 * ((1 / s) * (1 / (2 * N) + 4 * (1 + Real.log N) / Real.sqrt N +
        8 * (3 + Real.log N) / Real.sqrt N)) by ring]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  -- pointwise bound
  set g : ℝ → ℝ := fun v => (Ioc (0 : ℝ) 1).indicator (fun _ => 1 / (2 * N)) v +
    (Ioc (1 : ℝ) (Real.sqrt N)).indicator (fun v => 4 * (1 + 2 * Real.log v) / N) v +
    (Ioi (Real.sqrt N)).indicator (fun v => 8 * ((1 + 2 * Real.log v) / v ^ 2)) v with hg
  have hpt : ∀ v ∈ Ioi (0 : ℝ), |(gaussDensity (v / Real.sqrt N) - 1 / s) * depthFourQ v| ≤
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
    · -- `(0,1]`: `|q₃| ≤ 1`, `|γ − 1/s| ≤ v²/(2sN) ≤ 1/(2sN)`
      have hq : |depthFourQ v| ≤ 1 := by
        rw [depthFourQ_inner ⟨hv0, h1⟩, abs_of_nonneg (gaussLaplaceL_nonneg 3 _)]
        exact gaussLaplaceL_le_one 3 (sq_nonneg _)
      rw [indicator_of_mem (show v ∈ Ioc (0 : ℝ) 1 from ⟨hv0, h1⟩),
        indicator_of_notMem (fun hm : v ∈ Ioc (1 : ℝ) (Real.sqrt N) => absurd h1 (not_le.2 hm.1)),
        indicator_of_notMem (fun hm : v ∈ Ioi (Real.sqrt N) => by
          have : Real.sqrt N < v := hm; linarith), add_zero, add_zero]
      have hv2 : v ^ 2 / N / (2 * s) ≤ 1 / (2 * N) / s := by
        have hvv : v ^ 2 ≤ 1 := by nlinarith
        calc v ^ 2 / N / (2 * s) ≤ 1 / N / (2 * s) := by gcongr
          _ = 1 / (2 * N) / s := by ring
      calc |gaussDensity (v / Real.sqrt N) - 1 / s| * |depthFourQ v|
          ≤ (v ^ 2 / N / (2 * s)) * 1 := mul_le_mul hγ hq (abs_nonneg _) (by positivity)
        _ ≤ 1 / (2 * N) / s := by rw [mul_one]; exact hv2
        _ = 1 / s * (1 / (2 * N)) := by ring
    · rcases le_or_gt v (Real.sqrt N) with h2 | h2
      · -- `(1, √N]`: `|q₃| ≤ 8(1+2log v)/v²`, `|γ − 1/s| ≤ v²/(2sN)`
        have hq := depthFourQ_outer_le h1
        rw [indicator_of_notMem (fun hm : v ∈ Ioc (0 : ℝ) 1 => absurd hm.2 (not_le.2 h1)),
          indicator_of_mem (show v ∈ Ioc (1 : ℝ) (Real.sqrt N) from ⟨h1, h2⟩),
          indicator_of_notMem (fun hm : v ∈ Ioi (Real.sqrt N) => absurd h2 (not_le.2 hm)),
          zero_add, add_zero]
        have hl : 0 ≤ 1 + 2 * Real.log v := by linarith [Real.log_nonneg h1.le]
        calc |gaussDensity (v / Real.sqrt N) - 1 / s| * |depthFourQ v|
            ≤ (v ^ 2 / N / (2 * s)) * (8 * (1 + 2 * Real.log v) / v ^ 2) :=
              mul_le_mul hγ hq (abs_nonneg _) (by positivity)
          _ = 1 / s * (4 * (1 + 2 * Real.log v) / N) := by
              field_simp
              ring
      · -- `(√N, ∞)`: `|γ − 1/s| ≤ 1/s`
        have hq := depthFourQ_outer_le h1
        rw [indicator_of_notMem (fun hm : v ∈ Ioc (0 : ℝ) 1 => absurd hm.2 (not_le.2 h1)),
          indicator_of_notMem (fun hm : v ∈ Ioc (1 : ℝ) (Real.sqrt N) => absurd hm.2 (not_le.2 h2)),
          indicator_of_mem (show v ∈ Ioi (Real.sqrt N) from h2), zero_add, zero_add]
        rw [← mul_div_assoc]
        exact mul_le_mul hγ' hq (abs_nonneg _) (by positivity)
  -- the bound integrates
  have hg_int : IntegrableOn g (Ioi 0) := by
    simp only [hg]
    refine (IntegrableOn.add ?_ ?_).add ?_
    · exact ((integrableOn_const (C := 1 / (2 * N)) (s := Ioc (0 : ℝ) 1)
        (hs := measure_Ioc_lt_top.ne)).integrable_indicator measurableSet_Ioc).integrableOn
    · have hlog : ContinuousOn (fun v : ℝ => Real.log v) (Icc 1 (Real.sqrt N)) :=
        Real.continuousOn_log.mono fun v hv =>
          mem_compl_singleton_iff.2 (ne_of_gt (lt_of_lt_of_le one_pos hv.1))
      have hc : ContinuousOn (fun v : ℝ => 4 * (1 + 2 * Real.log v) / N) (Icc 1 (Real.sqrt N)) :=
        (continuousOn_const.mul (continuousOn_const.add (continuousOn_const.mul hlog))).div_const _
      exact ((hc.integrableOn_Icc).mono_set Ioc_subset_Icc_self
        |>.integrable_indicator measurableSet_Ioc).integrableOn
    · have h0 := integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hsN
      have h1 := (integrableOn_Ioi_one_rpow_mul_log (z := 0) (by norm_num)).mono_set
        (Ioi_subset_Ioi hsN1)
      refine (IntegrableOn.congr_fun ((h0.const_mul 8).add (h1.const_mul 16)) (fun v hv => ?_)
        measurableSet_Ioi |>.integrable_indicator measurableSet_Ioi).integrableOn
      have hv0 : (0 : ℝ) < v := lt_of_lt_of_le hsN (le_of_lt hv)
      simp only [Pi.add_apply, zero_sub]
      rw [Real.rpow_neg hv0.le, Real.rpow_two]
      field_simp
      ring
  have hg_le : ∫ v in Ioi (0 : ℝ), g v ≤ 1 / (2 * N) + 4 * (1 + Real.log N) / Real.sqrt N +
      8 * (3 + Real.log N) / Real.sqrt N := by
    have hi1 : IntegrableOn (fun v : ℝ => (Ioc (0 : ℝ) 1).indicator (fun _ => 1 / (2 * N)) v)
        (Ioi 0) :=
      ((integrableOn_const (C := 1 / (2 * N)) (s := Ioc (0 : ℝ) 1)
        (hs := measure_Ioc_lt_top.ne)).integrable_indicator measurableSet_Ioc).integrableOn
    have hi2 : IntegrableOn (fun v : ℝ => (Ioc (1 : ℝ) (Real.sqrt N)).indicator
        (fun v => 4 * (1 + 2 * Real.log v) / N) v) (Ioi 0) := by
      have hlog : ContinuousOn (fun v : ℝ => Real.log v) (Icc 1 (Real.sqrt N)) :=
        Real.continuousOn_log.mono fun v hv =>
          mem_compl_singleton_iff.2 (ne_of_gt (lt_of_lt_of_le one_pos hv.1))
      have hc : ContinuousOn (fun v : ℝ => 4 * (1 + 2 * Real.log v) / N) (Icc 1 (Real.sqrt N)) :=
        (continuousOn_const.mul (continuousOn_const.add (continuousOn_const.mul hlog))).div_const _
      exact ((hc.integrableOn_Icc).mono_set Ioc_subset_Icc_self
        |>.integrable_indicator measurableSet_Ioc).integrableOn
    have hi3 : IntegrableOn (fun v : ℝ => (Ioi (Real.sqrt N)).indicator
        (fun v => 8 * ((1 + 2 * Real.log v) / v ^ 2)) v) (Ioi 0) := by
      have h0 := integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hsN
      have h1 := (integrableOn_Ioi_one_rpow_mul_log (z := 0) (by norm_num)).mono_set
        (Ioi_subset_Ioi hsN1)
      refine (IntegrableOn.congr_fun ((h0.const_mul 8).add (h1.const_mul 16)) (fun v hv => ?_)
        measurableSet_Ioi |>.integrable_indicator measurableSet_Ioi).integrableOn
      have hv0 : (0 : ℝ) < v := lt_of_lt_of_le hsN (le_of_lt hv)
      simp only [Pi.add_apply, zero_sub]
      rw [Real.rpow_neg hv0.le, Real.rpow_two]
      field_simp
      ring
    have h12 : IntegrableOn (fun v : ℝ => (Ioc (0 : ℝ) 1).indicator (fun _ => 1 / (2 * N)) v +
        (Ioc (1 : ℝ) (Real.sqrt N)).indicator (fun v => 4 * (1 + 2 * Real.log v) / N) v)
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
    -- the constant piece
    have hc : ∫ _v in Ioc (0 : ℝ) 1, (1 / (2 * N) : ℝ) = 1 / (2 * N) := by
      rw [setIntegral_const, measureReal_def, Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal
        zero_le_one, one_smul]
    -- the middle piece: `1 + 2 log v ≤ 1 + ℓ` on `(1, √N]`
    have hm : ∫ v in Ioc (1 : ℝ) (Real.sqrt N), 4 * (1 + 2 * Real.log v) / N ≤
        4 * (1 + Real.log N) / Real.sqrt N := by
      have hb := norm_setIntegral_le_of_norm_le_const (μ := volume)
        (s := Ioc (1 : ℝ) (Real.sqrt N)) (f := fun v => 4 * (1 + 2 * Real.log v) / N)
        (C := 4 * (1 + Real.log N) / N) measure_Ioc_lt_top (fun v hv => by
          have hv1 : (1 : ℝ) < v := hv.1
          have hl : Real.log v ≤ Real.log N / 2 := by
            rw [← hlogR]; exact Real.log_le_log (by linarith) hv.2
          rw [Real.norm_eq_abs, abs_of_nonneg (by
            have := Real.log_nonneg hv1.le; positivity)]
          apply div_le_div_of_nonneg_right _ hN0.le
          linarith)
      rw [Real.norm_eq_abs] at hb
      refine (le_abs_self _).trans (hb.trans ?_)
      rw [measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
      have hNN : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN0.le
      have hdiv : Real.sqrt N / N = 1 / Real.sqrt N := by
        field_simp
        exact Real.sq_sqrt hN0.le
      calc 4 * (1 + Real.log N) / N * (Real.sqrt N - 1)
          ≤ 4 * (1 + Real.log N) / N * Real.sqrt N := by gcongr; linarith
        _ = 4 * (1 + Real.log N) * (Real.sqrt N / N) := by ring
        _ = 4 * (1 + Real.log N) / Real.sqrt N := by rw [hdiv]; ring
    rw [hc]
    have h3 : 8 * ((3 + 2 * (Real.log N / 2)) / Real.sqrt N) =
        8 * (3 + Real.log N) / Real.sqrt N := by
      ring
    rw [h3]
    linarith
  calc |∫ v in Ioi (0 : ℝ), (gaussDensity (v / Real.sqrt N) - 1 / s) * depthFourQ v|
      ≤ ∫ v in Ioi (0 : ℝ), 1 / s * g v := by
        refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
          (Eventually.of_forall fun v => abs_nonneg _) (hg_int.const_mul _) ?_)
        rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioi]
        exact Eventually.of_forall hpt
    _ = 1 / s * ∫ v in Ioi (0 : ℝ), g v := integral_const_mul _ _
    _ ≤ 1 / s * (1 / (2 * N) + 4 * (1 + Real.log N) / Real.sqrt N +
        8 * (3 + Real.log N) / Real.sqrt N) := mul_le_mul_of_nonneg_left hg_le (by positivity)

/-! ### The rate -/

set_option maxHeartbeats 1600000 in
-- the exact remainder identity and the long `calc` exceed the default heartbeat budget
/-- ★★★ **The depth-four constant with a rate**: there is `K ≥ 0` with
`|√N Z₄ − A₄ℓ³ − B₄ℓ² − C₄ℓ − D₄| ≤ K(1 + ℓ)²/√N` for all `N ≥ 1`. -/
theorem gaussLaplaceL_four_constant_rate :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℝ, 1 ≤ N →
      |Real.sqrt N * gaussLaplaceL 4 N - gaussCoeffA 0 * (Real.log N) ^ 3 -
        gaussCoeffB 0 * (Real.log N) ^ 2 - thirdCoeff 0 * Real.log N - depthFourConst| ≤
        K * (1 + Real.log N) ^ 2 / Real.sqrt N := by
  set s := Real.sqrt (2 * Real.pi) with hs_def
  have hs : 0 < s := Real.sqrt_pos.2 (by positivity)
  set A₃ : ℝ := 1 / (4 * Real.pi) with hA₃
  set B₃ : ℝ := (2 * Real.log 2 - Real.eulerMascheroniConstant) / Real.pi with hB₃
  set C₃ : ℝ := depthThreeConst with hC₃
  have hA₃0 : 0 < A₃ := by rw [hA₃]; positivity
  refine ⟨2 / s * (1 / 2 + 4 + 24 + (A₃ + |B₃| + |C₃|) / 2 + (4 * A₃ + 2 * |B₃|) +
    4 * A₃ * (9 / 2)),
    by positivity, fun N hN => ?_⟩
  have hN0 : 0 < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have hsN1 : 1 ≤ Real.sqrt N := Real.one_le_sqrt.2 hN
  have ha0 : 0 ≤ 1 / Real.sqrt N := by positivity
  have ha1 : 1 / Real.sqrt N ≤ 1 := by rw [div_le_one hsN]; exact Real.one_le_sqrt.2 hN
  have hℓ : 0 ≤ Real.log N := Real.log_nonneg hN
  set ℓ := Real.log N with hℓdef
  -- the pieces
  have hid := sqrt_mul_gaussLaplaceL_four_sub_eq hN
  have hres := residual_term_bound hN
  have he0 : |∫ x in Ioc (0 : ℝ) (1 / Real.sqrt N), gaussH x / x| ≤ 1 / 2 * (1 / Real.sqrt N) := by
    have := abs_integral_gaussH_log_pow_Ioc_le 0 ha0 ha1
    simp only [pow_zero, mul_one] at this
    convert this using 2
    try norm_num
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
      (A₃ * ℓ ^ 2 + |B₃| * ℓ + |C₃|) * (1 / 2 * (1 / Real.sqrt N)) := by
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
  -- elementary comparisons with `(1 + ℓ)²/√N`
  have hℓ1 : 1 ≤ (1 + ℓ) ^ 2 := by nlinarith
  have hℓ2 : 1 + ℓ ≤ (1 + ℓ) ^ 2 := by nlinarith
  have hℓ3 : ℓ ^ 2 ≤ (1 + ℓ) ^ 2 := by nlinarith
  have hℓ4 : 3 + ℓ ≤ 3 * (1 + ℓ) ^ 2 := by nlinarith
  have hℓ5 : ℓ ≤ (1 + ℓ) ^ 2 := by nlinarith
  have hN1 : 1 / (2 * N) ≤ 1 / 2 * (1 / Real.sqrt N) := by
    rw [show 1 / (2 * N) = 1 / 2 * (1 / N) by ring]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    exact one_div_le_one_div_of_le hsN (by nlinarith [Real.sq_sqrt hN0.le])
  have hB0 : 0 ≤ |B₃| := abs_nonneg _
  have hC0 : 0 ≤ |C₃| := abs_nonneg _
  have hinv : 0 < 1 / Real.sqrt N := by positivity
  set X := 1 / Real.sqrt N with hXdef
  set L := (1 + ℓ) ^ 2 with hLdef
  have hres' : |2 * Q - 2 / s * depthFourQint| ≤
      2 / s * (1 / (2 * N) + 4 * (1 + ℓ) * X + 8 * (3 + ℓ) * X) := by
    refine hres.trans (le_of_eq ?_)
    rw [hXdef]
    ring
  have f1 : 1 / (2 * N) ≤ 1 / 2 * (L * X) := by
    refine hN1.trans ?_
    have := mul_le_mul_of_nonneg_right hℓ1 hinv.le
    rw [one_mul] at this
    linarith
  have f2 : (1 + ℓ) * X ≤ L * X := mul_le_mul_of_nonneg_right hℓ2 hinv.le
  have f3 : (3 + ℓ) * X ≤ 3 * (L * X) := by
    rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hℓ4 hinv.le
  have f4 : ℓ ^ 2 * X ≤ L * X := mul_le_mul_of_nonneg_right hℓ3 hinv.le
  have f5 : ℓ * X ≤ L * X := mul_le_mul_of_nonneg_right hℓ5 hinv.le
  have f6 : X ≤ L * X := by
    have := mul_le_mul_of_nonneg_right hℓ1 hinv.le; rwa [one_mul] at this
  have g4 := mul_le_mul_of_nonneg_left f4 hA₃0.le
  have g5 := mul_le_mul_of_nonneg_left f5 hB0
  have g6 := mul_le_mul_of_nonneg_left f6 hC0
  have g7 := mul_le_mul_of_nonneg_left f5 hA₃0.le
  have g8 := mul_le_mul_of_nonneg_left f6 hB0
  have g9 := mul_le_mul_of_nonneg_left f6 hA₃0.le
  have key : 1 / (2 * N) + 4 * (1 + ℓ) * X + 8 * (3 + ℓ) * X +
      ((A₃ * ℓ ^ 2 + |B₃| * ℓ + |C₃|) * (1 / 2 * X) + (4 * A₃ * ℓ + 2 * |B₃|) * (1 * X) +
        4 * A₃ * (9 / 2 * X)) ≤
      (1 / 2 + 4 + 24 + (A₃ + |B₃| + |C₃|) / 2 + (4 * A₃ + 2 * |B₃|) + 4 * A₃ * (9 / 2)) *
        (L * X) := by
    nlinarith [f1, f2, f3, g4, g5, g6, g7, g8, g9]
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
    _ ≤ 2 / s * (1 / (2 * N) + 4 * (1 + ℓ) * X + 8 * (3 + ℓ) * X) +
        2 / s * ((A₃ * ℓ ^ 2 + |B₃| * ℓ + |C₃|) * (1 / 2 * X) +
          (4 * A₃ * ℓ + 2 * |B₃|) * (1 * X) + 4 * A₃ * (9 / 2 * X)) := by
        gcongr
    _ = 2 / s * (1 / (2 * N) + 4 * (1 + ℓ) * X + 8 * (3 + ℓ) * X +
        ((A₃ * ℓ ^ 2 + |B₃| * ℓ + |C₃|) * (1 / 2 * X) +
          (4 * A₃ * ℓ + 2 * |B₃|) * (1 * X) + 4 * A₃ * (9 / 2 * X))) := by ring
    _ ≤ 2 / s * ((1 / 2 + 4 + 24 + (A₃ + |B₃| + |C₃|) / 2 + (4 * A₃ + 2 * |B₃|) +
        4 * A₃ * (9 / 2)) * (L * X)) :=
        mul_le_mul_of_nonneg_left key (by positivity : (0 : ℝ) ≤ 2 / s)
    _ = 2 / s * (1 / 2 + 4 + 24 + (A₃ + |B₃| + |C₃|) / 2 + (4 * A₃ + 2 * |B₃|) +
        4 * A₃ * (9 / 2)) * (1 + ℓ) ^ 2 / Real.sqrt N := by
        rw [hLdef, hXdef]
        ring

end Grammar
