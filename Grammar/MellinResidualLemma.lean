/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.DepthThreeMellinBridge

/-!
# The abstract Mellin residual lemma and the log-power Mellin transforms

DCXLII's mechanism as a library lemma (★★★ `tendsto_mellin_residual`): if `v^{a−1} q` is
integrable on `(0,1]` for some `a < 1` and `q` is integrable on `(1,∞)`, then

  `∫₀^∞ v^{z−1} q(v) dv → ∫₀^∞ q(v) dv`  as `z → 1⁻`

(dominated convergence: eventually `a < z < 1`, `v^{z−1} ≤ v^{a−1}` on `(0,1]`, `≤ 1` beyond).
So for `Z(v) = q(v) + 1_{(1,∞)}(v) P(log v)/v` the finite part of the Mellin transform at its pole
is the residual integral, the polar part being `Σ_k p_k k!/(1−z)^{k+1}` by the log-power transforms

  `∫₁^∞ v^{z−2} (log v)^k dv = k!/(1−z)^{k+1}`  for `z < 1`
  (★★ `integral_Ioi_one_rpow_mul_log_pow`),

evaluated by the substitution `v = e^x` (`integral_comp_exp_Ioi`) and the Gamma integral — no
integration by parts.  Examples_slop §2 (the Mellin transfer between `Z(N)` expansions and zeta
poles); Astra round-14 target 2.  Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

/-! ### The log-power Mellin transforms on `(1,∞)` -/

/-- ★★ `∫₁^∞ v^{z−2} (log v)^k dv = k!/(1−z)^{k+1}` for `z < 1`. -/
theorem integral_Ioi_one_rpow_mul_log_pow {z : ℝ} (hz : z < 1) (k : ℕ) :
    ∫ v in Ioi (1 : ℝ), v ^ (z - 2) * Real.log v ^ k = (k.factorial : ℝ) / (1 - z) ^ (k + 1) := by
  have h := integral_comp_exp_Ioi (fun v : ℝ => v ^ (z - 2) * Real.log v ^ k) 0
  rw [Real.exp_zero] at h
  rw [← h]
  have e : ∀ x ∈ Ioi (0 : ℝ), Real.exp x • (Real.exp x ^ (z - 2) * Real.log (Real.exp x) ^ k) =
      x ^ (k : ℝ) * Real.exp (-(1 - z) * x ^ (1 : ℝ)) := by
    intro x _
    rw [smul_eq_mul, Real.log_exp, Real.rpow_def_of_pos (Real.exp_pos x), Real.log_exp,
      Real.rpow_natCast, Real.rpow_one, ← mul_assoc, ← Real.exp_add,
      show x + x * (z - 2) = -(1 - z) * x by ring]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi e, integral_rpow_mul_exp_neg_mul_rpow one_pos
    (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]) (by linarith)]
  rw [show -((k : ℝ) + 1) / 1 = -((k : ℝ) + 1) by ring,
    show ((k : ℝ) + 1) / 1 = (k : ℝ) + 1 by ring,
    Real.Gamma_nat_eq_factorial, Real.rpow_neg (by linarith),
    show ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  have : (0 : ℝ) < (1 - z) ^ (k + 1) := by positivity
  field_simp

/-- `v^{z−2} (log v)^k` is integrable on `(1,∞)` for `z < 1`
(`(log v)^k ≤ (v^ε/ε)^k`, `ε = (1−z)/(2(k+1))`). -/
theorem integrableOn_Ioi_one_rpow_mul_log_pow {z : ℝ} (hz : z < 1) (k : ℕ) :
    IntegrableOn (fun v : ℝ => v ^ (z - 2) * Real.log v ^ k) (Ioi 1) := by
  set ε : ℝ := (1 - z) / (2 * (k + 1)) with hε
  have hε0 : 0 < ε := by rw [hε]; positivity
  have hexp : z - 2 + k * ε < -1 := by
    rw [hε]
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hz' : 0 < 1 - z := by linarith
    have : (k : ℝ) * ((1 - z) / (2 * (k + 1))) ≤ (1 - z) / 2 := by
      calc (k : ℝ) * ((1 - z) / (2 * (k + 1))) = (1 - z) / 2 * ((k : ℝ) / (k + 1)) := by
            field_simp
        _ ≤ (1 - z) / 2 * 1 := by
            gcongr
            exact div_le_one_of_le₀ (by linarith) (by positivity)
        _ = (1 - z) / 2 := mul_one _
    linarith
  have hI : IntegrableOn (fun v : ℝ => (1 / ε ^ k) * v ^ (z - 2 + k * ε)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt hexp one_pos).const_mul _
  refine hI.mono' ((measurable_id.pow_const _).mul
    (Real.measurable_log.pow_const k)).aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Eventually.of_forall fun v hv => ?_
  have hv1 : (1 : ℝ) < v := hv
  have hv0 : 0 < v := by linarith
  have hl : 0 ≤ Real.log v := Real.log_nonneg hv1.le
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.rpow_add hv0, mul_comm (k : ℝ) ε,
    Real.rpow_mul hv0.le, Real.rpow_natCast]
  have hlog : Real.log v ≤ v ^ ε / ε := Real.log_le_rpow_div hv0.le hε0
  have hpow : Real.log v ^ k ≤ (v ^ ε / ε) ^ k := pow_le_pow_left₀ hl hlog k
  calc v ^ (z - 2) * Real.log v ^ k ≤ v ^ (z - 2) * (v ^ ε / ε) ^ k := by gcongr
    _ = 1 / ε ^ k * (v ^ (z - 2) * (v ^ ε) ^ k) := by rw [div_pow]; ring

/-! ### The residual lemma -/

/-- ★★★ **The Mellin residual lemma**: if `v^{a−1} q` is integrable on `(0,1]` for some
`a < 1` and `q` is integrable on `(1,∞)`, then `∫₀^∞ v^{z−1} q → ∫₀^∞ q` as `z → 1⁻`. -/
theorem tendsto_mellin_residual {q : ℝ → ℝ} {a : ℝ} (ha1 : a < 1)
    (hq : Measurable q) (hsmall : IntegrableOn (fun v => v ^ (a - 1) * q v) (Ioc 0 1))
    (hlarge : IntegrableOn q (Ioi 1)) :
    Tendsto (fun z : ℝ => ∫ v in Ioi (0 : ℝ), v ^ (z - 1) * q v) (𝓝[<] (1 : ℝ))
      (𝓝 (∫ v in Ioi (0 : ℝ), q v)) := by
  have hmem : Ioo a 1 ∈ 𝓝[<] (1 : ℝ) := Ioo_mem_nhdsLT ha1
  -- the dominating function
  have hbound : IntegrableOn (fun v : ℝ =>
      (Ioc (0 : ℝ) 1).indicator (fun v => v ^ (a - 1) * |q v|) v +
        (Ioi (1 : ℝ)).indicator (fun v => |q v|) v) (Ioi 0) := by
    have h1 : IntegrableOn (fun v : ℝ => v ^ (a - 1) * |q v|) (Ioc 0 1) := by
      refine IntegrableOn.congr_fun hsmall.abs (fun v hv => ?_) measurableSet_Ioc
      rw [abs_mul, abs_of_nonneg (by have : (0 : ℝ) < v := hv.1; positivity)]
    exact ((h1.integrable_indicator measurableSet_Ioc).integrableOn).add
      ((IntegrableOn.integrable_indicator hlarge.abs measurableSet_Ioi).integrableOn)
  refine tendsto_integral_filter_of_dominated_convergence
    (fun v => (Ioc (0 : ℝ) 1).indicator (fun v => v ^ (a - 1) * |q v|) v +
      (Ioi (1 : ℝ)).indicator (fun v => |q v|) v)
    (Eventually.of_forall fun z => ((measurable_id.pow_const _).mul hq).aestronglyMeasurable)
    ?_ hbound ?_
  · filter_upwards [hmem] with z hz
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun v hv => ?_
    have hv0 : (0 : ℝ) < v := hv
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ v ^ (z - 1))]
    rcases le_or_gt v 1 with h1 | h1
    · have hm : v ∈ Ioc (0 : ℝ) 1 := ⟨hv0, h1⟩
      rw [indicator_of_mem hm, indicator_of_notMem (fun hm' : v ∈ Ioi (1 : ℝ) =>
        absurd h1 (not_le.2 hm')), add_zero]
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_ge hv0 h1 (by linarith [hz.1])) (abs_nonneg _)
    · rw [indicator_of_notMem (fun hm : v ∈ Ioc (0 : ℝ) 1 => absurd hm.2 (not_le.2 h1)),
        indicator_of_mem (show v ∈ Ioi (1 : ℝ) from h1), zero_add]
      calc v ^ (z - 1) * |q v| ≤ 1 * |q v| :=
            mul_le_mul_of_nonneg_right
              (Real.rpow_le_one_of_one_le_of_nonpos h1.le (by linarith [hz.2])) (abs_nonneg _)
        _ = |q v| := one_mul _
  · rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun v hv => ?_
    have hv0 : (0 : ℝ) < v := hv
    have hc : Tendsto (fun z : ℝ => v ^ (z - 1)) (𝓝 1) (𝓝 (v ^ ((1 : ℝ) - 1))) :=
      ((Real.continuousAt_const_rpow hv0.ne').comp
        (continuousAt_id.sub continuousAt_const)).tendsto
    have := (hc.mono_left (nhdsWithin_le_nhds (s := Iio (1 : ℝ)))).mul_const (q v)
    rwa [sub_self, Real.rpow_zero, one_mul] at this

/-- The residual lemma with a Lebesgue-integrable `q` on `(0,∞)` and `v^{a−1}` bounded on `(0,1]`
by an explicit hypothesis is a special case; the version above only asks for the weighted
integrability near `0`.  Consequence for DCXLII: `depthThreeQ` satisfies the hypotheses with
`a = ½` (`q = Z₂(v²) ≤ 1` on `(0,1]`). -/
theorem tendsto_mellin_residual_depthThreeQ :
    Tendsto (fun z : ℝ => ∫ v in Ioi (0 : ℝ), v ^ (z - 1) * depthThreeQ v) (𝓝[<] (1 : ℝ))
      (𝓝 depthThreeQint) := by
  refine tendsto_mellin_residual (a := 1 / 2) (by norm_num) measurable_depthThreeQ
    ?_ integrableOn_depthThreeQ_outer
  have h1 : IntegrableOn (fun v : ℝ => v ^ ((1 / 2 : ℝ) - 1)) (Ioc 0 1) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    exact intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  refine h1.mono' ((measurable_id.pow_const _).mul measurable_depthThreeQ).aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioc]
  refine Eventually.of_forall fun v hv => ?_
  have hv0 : 0 < v := hv.1
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ v ^ ((1 / 2 : ℝ) - 1)),
    depthThreeQ_inner hv, abs_of_nonneg (gaussLaplace2_nonneg (sq_nonneg _))]
  calc v ^ ((1 / 2 : ℝ) - 1) * gaussLaplace2 (v ^ 2) ≤ v ^ ((1 / 2 : ℝ) - 1) * 1 :=
        mul_le_mul_of_nonneg_left (gaussLaplace2_le_one (sq_nonneg _)) (by positivity)
    _ = v ^ ((1 / 2 : ℝ) - 1) := mul_one _

end Grammar
