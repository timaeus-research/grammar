/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.GaussianDepthThreeResidual

/-!
# The Mellin residual bridge for the depth-three constant `Q`

`Q = depthThreeQint = ∫₀^∞ q`, `q(v) = Z₂(v²) − 1_{(1,∞)}(v)(2 log v + c)/(s v)`, `c = 3 log 2 − γ`,
`s = √(2π)` (DCXXXI).  The Mellin transform `M(z) = ∫₀^∞ v^{z−1} Z₂(v²) dv` (`depthThreeMellin`) has
a double pole at `z = 1` whose polar part is the Mellin transform of the subtracted term:

  `∫₁^∞ v^{z−1}(2 log v + c)/(s v) dv = 2/(s(1−z)²) + c/(s(1−z))`
  (`depthThree_mellin_pole_integral`)

for `z < 1`, so for `0 < z < 1`

  `M(z) − [2/(s(1−z)²) + c/(s(1−z))] = ∫₀^∞ v^{z−1} q(v) dv`   (★★ `depthThree_mellin_sub_poles`)

and by dominated convergence (`v^{z−1} ≤ v^{−1/2}` on `(0,1]`, `≤ 1` beyond, for `½ ≤ z < 1`)

  `M(z) − poles → Q` as `z → 1⁻`   (★★★ `tendsto_depthThree_mellin_sub_poles`).

With the closed form `M(z) = 2^{−1−z/2}Γ(z/2)Γ((1−z)/2)²/π` and the regularised Gamma jet (next
units) this identifies `Q = (c² + 5π²/6)/(4s)` (examples_slop §2; Astra round-13 target 2).
Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

/-- `c = 3 log 2 − γ`. -/
noncomputable def depthThreeC : ℝ := 3 * Real.log 2 - Real.eulerMascheroniConstant

/-- The Mellin transform `M(z) = ∫₀^∞ v^{z−1} Z₂(v²) dv`. -/
noncomputable def depthThreeMellin (z : ℝ) : ℝ :=
  ∫ v in Ioi (0 : ℝ), v ^ (z - 1) * gaussLaplace2 (v ^ 2)

/-- The polar part `2/(s(1−z)²) + c/(s(1−z))`. -/
noncomputable def depthThreePoles (z : ℝ) : ℝ :=
  2 / (Real.sqrt (2 * Real.pi) * (1 - z) ^ 2) + depthThreeC / (Real.sqrt (2 * Real.pi) * (1 - z))

/-! ### The two elementary Mellin integrals on `(1,∞)` -/

/-- `∫₁^∞ v^{z−2} dv = 1/(1−z)` for `z < 1`. -/
theorem integral_Ioi_one_rpow {z : ℝ} (hz : z < 1) :
    ∫ v in Ioi (1 : ℝ), v ^ (z - 2) = 1 / (1 - z) := by
  rw [integral_Ioi_rpow_of_lt (by linarith) one_pos, Real.one_rpow]
  have : z - 2 + 1 ≠ 0 := by linarith
  have h1z : 1 - z ≠ 0 := by linarith
  field_simp
  ring

theorem integrableOn_Ioi_one_rpow {z : ℝ} (hz : z < 1) :
    IntegrableOn (fun v : ℝ => v ^ (z - 2)) (Ioi 1) :=
  integrableOn_Ioi_rpow_of_lt (by linarith) one_pos

/-- `v^{z−2} log v` is integrable on `(1,∞)` for `z < 1` (`log v ≤ v^ε/ε`, `ε = (1−z)/2`). -/
theorem integrableOn_Ioi_one_rpow_mul_log {z : ℝ} (hz : z < 1) :
    IntegrableOn (fun v : ℝ => v ^ (z - 2) * Real.log v) (Ioi 1) := by
  have hε : 0 < (1 - z) / 2 := by linarith
  have hI : IntegrableOn (fun v : ℝ => 1 / ((1 - z) / 2) * v ^ (z - 2 + (1 - z) / 2)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos).const_mul _
  refine hI.mono' ((measurable_id.pow_const _).mul Real.measurable_log).aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Eventually.of_forall fun v hv => ?_
  have hv1 : (1 : ℝ) < v := hv
  have hv0 : 0 < v := by linarith
  have hl : 0 ≤ Real.log v := Real.log_nonneg hv1.le
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.rpow_add hv0]
  have hlog : Real.log v ≤ v ^ ((1 - z) / 2) / ((1 - z) / 2) := Real.log_le_rpow_div hv0.le hε
  calc v ^ (z - 2) * Real.log v ≤ v ^ (z - 2) * (v ^ ((1 - z) / 2) / ((1 - z) / 2)) := by gcongr
    _ = 1 / ((1 - z) / 2) * (v ^ (z - 2) * v ^ ((1 - z) / 2)) := by ring

/-- `∫₁^∞ v^{z−2} log v dv = 1/(1−z)²` for `z < 1`. -/
theorem integral_Ioi_one_rpow_mul_log {z : ℝ} (hz : z < 1) :
    ∫ v in Ioi (1 : ℝ), v ^ (z - 2) * Real.log v = 1 / (1 - z) ^ 2 := by
  have hz1 : z - 1 ≠ 0 := by linarith
  -- the antiderivative `F(v) = v^{z−1}((z−1) log v − 1)/(z−1)²`
  set F : ℝ → ℝ := fun v => v ^ (z - 1) * ((z - 1) * Real.log v - 1) / (z - 1) ^ 2 with hF
  have hderiv : ∀ v : ℝ, 0 < v → HasDerivAt F (v ^ (z - 2) * Real.log v) v := by
    intro v hv
    have h1 : HasDerivAt (fun v : ℝ => v ^ (z - 1)) ((z - 1) * v ^ (z - 1 - 1)) v :=
      Real.hasDerivAt_rpow_const (Or.inl hv.ne')
    have h2 : HasDerivAt (fun v : ℝ => (z - 1) * Real.log v - 1) ((z - 1) * v⁻¹) v :=
      ((Real.hasDerivAt_log hv.ne').const_mul (z - 1)).sub_const 1
    refine ((h1.mul h2).div_const ((z - 1) ^ 2)).congr_deriv ?_
    have hv2 : v ^ (z - 2) = v ^ (z - 1) / v := by
      rw [← Real.rpow_sub_one hv.ne']; congr 1; ring
    rw [show z - 1 - 1 = z - 2 by ring, hv2]
    field_simp
    ring
  have hlim : Tendsto F atTop (𝓝 0) := by
    have hpos : 0 < 1 - z := by linarith
    have h1 : Tendsto (fun v : ℝ => v ^ (z - 1)) atTop (𝓝 0) := by
      have := tendsto_rpow_neg_atTop hpos
      refine this.congr fun v => ?_
      rw [neg_sub]
    have h2 : Tendsto (fun v : ℝ => v ^ (z - 1) * Real.log v) atTop (𝓝 0) := by
      have := (isLittleO_log_rpow_atTop hpos).tendsto_div_nhds_zero
      refine this.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with v hv
      rw [div_eq_mul_inv, ← Real.rpow_neg hv.le, neg_sub, mul_comm]
    have := ((h2.const_mul (z - 1)).sub h1).div_const ((z - 1) ^ 2)
    simp only [mul_zero, sub_zero, zero_div] at this
    refine this.congr fun v => ?_
    simp only [hF]
    ring
  have hF1 : F 1 = -(1 / (1 - z) ^ 2) := by
    simp only [hF, Real.one_rpow, Real.log_one, mul_zero, zero_sub, one_mul]
    rw [show (1 - z) ^ 2 = (z - 1) ^ 2 by ring]
    field_simp
  rw [integral_Ioi_of_hasDerivAt_of_tendsto (f := F)
    (hderiv 1 one_pos).continuousAt.continuousWithinAt
    (fun v (hv : (1 : ℝ) < v) => hderiv v (by linarith))
    (integrableOn_Ioi_one_rpow_mul_log hz) hlim,
    hF1]
  ring

/-! ### The pole integral -/

/-- `∫₁^∞ v^{z−1}(2 log v + c)/(s v) dv = 2/(s(1−z)²) + c/(s(1−z))` for `z < 1`. -/
theorem depthThree_mellin_pole_integral {z : ℝ} (hz : z < 1) :
    ∫ v in Ioi (1 : ℝ), v ^ (z - 1) *
      ((2 * Real.log v + depthThreeC) / (Real.sqrt (2 * Real.pi) * v)) = depthThreePoles z := by
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have e : ∀ v ∈ Ioi (1 : ℝ), v ^ (z - 1) *
      ((2 * Real.log v + depthThreeC) / (Real.sqrt (2 * Real.pi) * v)) =
      2 / Real.sqrt (2 * Real.pi) * (v ^ (z - 2) * Real.log v) +
        depthThreeC / Real.sqrt (2 * Real.pi) * v ^ (z - 2) := by
    intro v hv
    have hv0 : (0 : ℝ) < v := lt_trans one_pos hv
    rw [show z - 1 = (z - 2) + 1 by ring, Real.rpow_add_one hv0.ne']
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi e,
    integral_add ((integrableOn_Ioi_one_rpow_mul_log hz).const_mul _)
      ((integrableOn_Ioi_one_rpow hz).const_mul _),
    integral_const_mul, integral_const_mul, integral_Ioi_one_rpow_mul_log hz,
    integral_Ioi_one_rpow hz]
  unfold depthThreePoles
  field_simp

/-! ### `M(z) − poles = ∫ v^{z−1} q` -/

theorem integrableOn_rpow_mul_gaussLaplace2_inner {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun v : ℝ => v ^ (z - 1) * gaussLaplace2 (v ^ 2)) (Ioc 0 1) := by
  have hI : IntegrableOn (fun v : ℝ => v ^ (z - 1)) (Ioc 0 1) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    exact intervalIntegral.intervalIntegrable_rpow' (by linarith)
  refine hI.mono' ((measurable_id.pow_const _).mul
    (measurable_gaussLaplace2.comp (measurable_id.pow_const 2))).aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioc]
  refine Eventually.of_forall fun v hv => ?_
  have hv0 : 0 < v := hv.1
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity)
    (gaussLaplace2_nonneg (sq_nonneg _)))]
  calc v ^ (z - 1) * gaussLaplace2 (v ^ 2) ≤ v ^ (z - 1) * 1 :=
        mul_le_mul_of_nonneg_left (gaussLaplace2_le_one (sq_nonneg _)) (by positivity)
    _ = v ^ (z - 1) := mul_one _

/-- On `(1,∞)`: `Z₂(v²) = q(v) + (2 log v + c)/(s v)`. -/
theorem gaussLaplace2_sq_eq_depthThreeQ_add {v : ℝ} (hv : 1 < v) :
    gaussLaplace2 (v ^ 2) = depthThreeQ v +
      (2 * Real.log v + depthThreeC) / (Real.sqrt (2 * Real.pi) * v) := by
  unfold depthThreeQ depthThreeC
  rw [indicator_of_mem (show v ∈ Ioi (1 : ℝ) from hv)]
  ring

theorem integrableOn_rpow_mul_pole {z : ℝ} (hz : z < 1) :
    IntegrableOn (fun v : ℝ => v ^ (z - 1) *
      ((2 * Real.log v + depthThreeC) / (Real.sqrt (2 * Real.pi) * v))) (Ioi 1) := by
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  refine IntegrableOn.congr_fun (((integrableOn_Ioi_one_rpow_mul_log hz).const_mul
    (2 / Real.sqrt (2 * Real.pi))).add ((integrableOn_Ioi_one_rpow hz).const_mul
    (depthThreeC / Real.sqrt (2 * Real.pi)))) (fun v hv => ?_) measurableSet_Ioi
  have hv0 : (0 : ℝ) < v := lt_trans one_pos hv
  simp only [Pi.add_apply]
  rw [show z - 1 = (z - 2) + 1 by ring, Real.rpow_add_one hv0.ne']
  field_simp

theorem integrableOn_rpow_mul_depthThreeQ {z : ℝ} (hz : z ≤ 1) :
    IntegrableOn (fun v : ℝ => v ^ (z - 1) * depthThreeQ v) (Ioi 1) := by
  refine integrableOn_depthThreeQ_outer.abs.mono'
    ((measurable_id.pow_const _).mul measurable_depthThreeQ).aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Eventually.of_forall fun v hv => ?_
  have hv1 : (1 : ℝ) < v := hv
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ v ^ (z - 1))]
  calc v ^ (z - 1) * |depthThreeQ v| ≤ 1 * |depthThreeQ v| :=
        mul_le_mul_of_nonneg_right
          (Real.rpow_le_one_of_one_le_of_nonpos hv1.le (by linarith)) (abs_nonneg _)
    _ = |depthThreeQ v| := one_mul _

theorem integrableOn_rpow_mul_gaussLaplace2_outer {z : ℝ} (hz : z < 1) :
    IntegrableOn (fun v : ℝ => v ^ (z - 1) * gaussLaplace2 (v ^ 2)) (Ioi 1) := by
  refine IntegrableOn.congr_fun ((integrableOn_rpow_mul_depthThreeQ hz.le).add
    (integrableOn_rpow_mul_pole hz)) (fun v hv => ?_) measurableSet_Ioi
  simp only [Pi.add_apply]
  rw [gaussLaplace2_sq_eq_depthThreeQ_add hv]
  ring

theorem integrableOn_rpow_mul_gaussLaplace2 {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    IntegrableOn (fun v : ℝ => v ^ (z - 1) * gaussLaplace2 (v ^ 2)) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  exact (integrableOn_rpow_mul_gaussLaplace2_inner hz0).union
    (integrableOn_rpow_mul_gaussLaplace2_outer hz1)

/-- ★★ **The Mellin transform minus its poles is the Mellin transform of `q`**: for `0 < z < 1`,
`M(z) − [2/(s(1−z)²) + c/(s(1−z))] = ∫₀^∞ v^{z−1} q(v) dv`. -/
theorem depthThree_mellin_sub_poles {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    depthThreeMellin z - depthThreePoles z =
      ∫ v in Ioi (0 : ℝ), v ^ (z - 1) * depthThreeQ v := by
  have hpole : IntegrableOn (fun v : ℝ => v ^ (z - 1) * (Ioi (1 : ℝ)).indicator (fun v =>
      (2 * Real.log v + (3 * Real.log 2 - Real.eulerMascheroniConstant)) /
        (Real.sqrt (2 * Real.pi) * v)) v) (Ioi 0) := by
    have h := (integrableOn_rpow_mul_pole hz1).integrable_indicator measurableSet_Ioi
    refine h.integrableOn.congr_fun (fun v _ => ?_) measurableSet_Ioi
    unfold depthThreeC at h ⊢
    by_cases hv : v ∈ Ioi (1 : ℝ)
    · rw [indicator_of_mem hv, indicator_of_mem hv]
    · rw [indicator_of_notMem hv, indicator_of_notMem hv, mul_zero]
  have hint : ∫ v in Ioi (0 : ℝ), v ^ (z - 1) * (Ioi (1 : ℝ)).indicator (fun v =>
      (2 * Real.log v + (3 * Real.log 2 - Real.eulerMascheroniConstant)) /
        (Real.sqrt (2 * Real.pi) * v)) v = depthThreePoles z := by
    rw [← depthThree_mellin_pole_integral hz1]
    have e : (fun v : ℝ => v ^ (z - 1) * (Ioi (1 : ℝ)).indicator (fun v =>
        (2 * Real.log v + (3 * Real.log 2 - Real.eulerMascheroniConstant)) /
          (Real.sqrt (2 * Real.pi) * v)) v) = (Ioi (1 : ℝ)).indicator (fun v =>
        v ^ (z - 1) * ((2 * Real.log v + depthThreeC) / (Real.sqrt (2 * Real.pi) * v))) := by
      funext v
      unfold depthThreeC
      by_cases hv : v ∈ Ioi (1 : ℝ)
      · rw [indicator_of_mem hv, indicator_of_mem hv]
      · rw [indicator_of_notMem hv, indicator_of_notMem hv, mul_zero]
    rw [e, setIntegral_indicator measurableSet_Ioi,
      show Ioi (0 : ℝ) ∩ Ioi 1 = Ioi 1 from
        inter_eq_right.2 fun v (hv : (1 : ℝ) < v) => (show (0 : ℝ) < v from lt_trans one_pos hv)]
  unfold depthThreeMellin
  rw [← hint, ← integral_sub (integrableOn_rpow_mul_gaussLaplace2 hz0 hz1) hpole]
  refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
  unfold depthThreeQ
  ring

/-! ### The limit `z → 1⁻` -/

/-- The dominating function `1_{(0,1]}(v) v^{−1/2} + |q(v)|`. -/
theorem integrable_mellin_bound :
    IntegrableOn (fun v : ℝ => (Ioc (0 : ℝ) 1).indicator (fun v => v ^ (-(1 / 2 : ℝ))) v +
      |depthThreeQ v|) (Ioi 0) := by
  have h1 : IntegrableOn (fun v : ℝ => v ^ (-(1 / 2 : ℝ))) (Ioc 0 1) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    exact intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  exact ((h1.integrable_indicator measurableSet_Ioc).integrableOn).add
    integrableOn_depthThreeQ.abs

/-- ★★★ **The residual bridge**: `M(z) − [2/(s(1−z)²) + c/(s(1−z))] → Q` as `z → 1⁻`. -/
theorem tendsto_depthThree_mellin_sub_poles :
    Tendsto (fun z => depthThreeMellin z - depthThreePoles z) (𝓝[<] (1 : ℝ))
      (𝓝 depthThreeQint) := by
  have hmem : Ioo (1 / 2 : ℝ) 1 ∈ 𝓝[<] (1 : ℝ) := Ioo_mem_nhdsLT (by norm_num)
  have hlim : Tendsto (fun z => ∫ v in Ioi (0 : ℝ), v ^ (z - 1) * depthThreeQ v)
      (𝓝[<] (1 : ℝ)) (𝓝 depthThreeQint) := by
    unfold depthThreeQint
    refine tendsto_integral_filter_of_dominated_convergence
      (fun v => (Ioc (0 : ℝ) 1).indicator (fun v => v ^ (-(1 / 2 : ℝ))) v + |depthThreeQ v|)
      (Eventually.of_forall fun z =>
        ((measurable_id.pow_const _).mul measurable_depthThreeQ).aestronglyMeasurable)
      ?_ integrable_mellin_bound ?_
    · filter_upwards [hmem] with z hz
      rw [ae_restrict_iff' measurableSet_Ioi]
      refine Eventually.of_forall fun v hv => ?_
      have hv0 : (0 : ℝ) < v := hv
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ v ^ (z - 1))]
      rcases le_or_gt v 1 with h1 | h1
      · have hm : v ∈ Ioc (0 : ℝ) 1 := ⟨hv0, h1⟩
        rw [indicator_of_mem hm]
        have hq : |depthThreeQ v| ≤ 1 := by
          rw [depthThreeQ_inner hm, abs_of_nonneg (gaussLaplace2_nonneg (sq_nonneg _))]
          exact gaussLaplace2_le_one (sq_nonneg _)
        have hr : v ^ (z - 1) ≤ v ^ (-(1 / 2 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_ge hv0 h1 (by linarith [hz.1])
        calc v ^ (z - 1) * |depthThreeQ v| ≤ v ^ (-(1 / 2 : ℝ)) * 1 :=
              mul_le_mul hr hq (abs_nonneg _) (by positivity)
          _ ≤ v ^ (-(1 / 2 : ℝ)) + |depthThreeQ v| := by linarith [abs_nonneg (depthThreeQ v)]
      · rw [indicator_of_notMem (fun hm : v ∈ Ioc (0 : ℝ) 1 => absurd hm.2 (not_le.2 h1)),
          zero_add]
        calc v ^ (z - 1) * |depthThreeQ v| ≤ 1 * |depthThreeQ v| :=
              mul_le_mul_of_nonneg_right
                (Real.rpow_le_one_of_one_le_of_nonpos h1.le (by linarith [hz.2])) (abs_nonneg _)
          _ = |depthThreeQ v| := one_mul _
    · rw [ae_restrict_iff' measurableSet_Ioi]
      refine Eventually.of_forall fun v hv => ?_
      have hv0 : (0 : ℝ) < v := hv
      have hc : Tendsto (fun z : ℝ => v ^ (z - 1)) (𝓝 1) (𝓝 (v ^ ((1 : ℝ) - 1))) :=
        ((Real.continuousAt_const_rpow hv0.ne').comp
          (continuousAt_id.sub continuousAt_const)).tendsto
      have := (hc.mono_left (nhdsWithin_le_nhds (s := Iio (1 : ℝ)))).mul_const (depthThreeQ v)
      rwa [sub_self, Real.rpow_zero, one_mul] at this
  refine hlim.congr' ?_
  filter_upwards [hmem] with z hz
  exact (depthThree_mellin_sub_poles (by linarith [hz.1]) hz.2).symm

end Grammar
