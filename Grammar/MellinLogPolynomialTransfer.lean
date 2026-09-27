/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.MellinResidualLemma

/-!
# The Mellin transfer for a log-polynomial tail

For `Z(v) = q(v) + 1_{(1,∞)}(v) P(log v)/v` with `P(y) = Σ_{k ≤ d} p_k y^k` and a residual `q` as in
DCXLVII (`v^{a−1} q` integrable on `(0,1]` for some `a < 1`, `q` integrable on `(1,∞)`),

  `∫₀^∞ v^{z−1} Z(v) dv − Σ_k p_k k!/(1−z)^{k+1} → ∫₀^∞ q(v) dv`  as `z → 1⁻`

(★★★ `tendsto_mellin_sub_logPolynomial`): the polar part of the Mellin transform at `z = 1` is read
off the logarithmic expansion of `Z` and the finite part is the residual integral.  This is the
transfer from an expansion of `Z` in `(log v)^k/v` to the poles of its Mellin transform, in the
direction from the expansion to the poles (examples_slop §2; Astra round-15 target 1).
Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

/-- The log-polynomial tail `1_{(1,∞)}(v) (Σ_k p_k (log v)^k)/v`. -/
noncomputable def mellinLogTail {d : ℕ} (p : Fin (d + 1) → ℝ) (v : ℝ) : ℝ :=
  if 1 < v then (∑ k : Fin (d + 1), p k * Real.log v ^ (k : ℕ)) / v else 0

theorem measurable_mellinLogTail {d : ℕ} (p : Fin (d + 1) → ℝ) :
    Measurable (mellinLogTail p) := by
  unfold mellinLogTail
  refine Measurable.ite measurableSet_Ioi ?_ measurable_const
  exact (Finset.measurable_sum _ fun k _ =>
    (Real.measurable_log.pow_const _).const_mul _).div measurable_id

/-- The weighted residual `v^{z−1} q` is integrable on `(0,∞)` for `a ≤ z ≤ 1`. -/
theorem integrableOn_rpow_mul_residual {q : ℝ → ℝ} {a z : ℝ} (hq : Measurable q)
    (hsmall : IntegrableOn (fun v => v ^ (a - 1) * q v) (Ioc 0 1))
    (hlarge : IntegrableOn q (Ioi 1)) (hz0 : a ≤ z) (hz1 : z ≤ 1) :
    IntegrableOn (fun v => v ^ (z - 1) * q v) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  refine IntegrableOn.union ?_ ?_
  · refine hsmall.abs.mono' ((measurable_id.pow_const _).mul hq).aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Eventually.of_forall fun v hv => ?_
    have hv0 : 0 < v := hv.1
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ v ^ (z - 1)),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ v ^ (a - 1))]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_ge hv0 hv.2 (by linarith)) (abs_nonneg _)
  · refine hlarge.abs.mono' ((measurable_id.pow_const _).mul hq).aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun v hv => ?_
    have hv1 : (1 : ℝ) < v := hv
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ v ^ (z - 1))]
    calc v ^ (z - 1) * |q v| ≤ 1 * |q v| :=
          mul_le_mul_of_nonneg_right
            (Real.rpow_le_one_of_one_le_of_nonpos hv1.le (by linarith)) (abs_nonneg _)
      _ = |q v| := one_mul _

/-- The weighted tail `v^{z−1} · tail` on `(0,∞)` equals the indicator of `(1,∞)` of
`Σ_k p_k v^{z−2}(log v)^k`. -/
theorem rpow_mul_mellinLogTail_eq {d : ℕ} (p : Fin (d + 1) → ℝ) {z v : ℝ} (hv : 0 < v) :
    v ^ (z - 1) * mellinLogTail p v =
      (Ioi (1 : ℝ)).indicator (fun v => ∑ k : Fin (d + 1),
        p k * (v ^ (z - 2) * Real.log v ^ (k : ℕ))) v := by
  unfold mellinLogTail
  by_cases h : 1 < v
  · rw [if_pos h, indicator_of_mem (show v ∈ Ioi (1 : ℝ) from h), Finset.sum_div, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show z - 1 = (z - 2) + 1 by ring, Real.rpow_add_one hv.ne']
    field_simp
  · rw [if_neg h, indicator_of_notMem (fun hm : v ∈ Ioi (1 : ℝ) => h hm), mul_zero]

/-- `∫₀^∞ v^{z−1} · tail = Σ_k p_k k!/(1−z)^{k+1}` for `z < 1`. -/
theorem integral_rpow_mul_mellinLogTail {d : ℕ} (p : Fin (d + 1) → ℝ) {z : ℝ} (hz : z < 1) :
    ∫ v in Ioi (0 : ℝ), v ^ (z - 1) * mellinLogTail p v =
      ∑ k : Fin (d + 1), p k * ((k : ℕ).factorial : ℝ) / (1 - z) ^ ((k : ℕ) + 1) := by
  rw [setIntegral_congr_fun measurableSet_Ioi fun v (hv : (0 : ℝ) < v) =>
    rpow_mul_mellinLogTail_eq p hv, setIntegral_indicator measurableSet_Ioi,
    show Ioi (0 : ℝ) ∩ Ioi 1 = Ioi 1 from
      inter_eq_right.2 fun v (hv : (1 : ℝ) < v) => (show (0 : ℝ) < v from lt_trans one_pos hv),
    integral_finsetSum (Finset.univ : Finset (Fin (d + 1)))
      (f := fun k v => p k * (v ^ (z - 2) * Real.log v ^ (k : ℕ)))
      (fun k _ => (integrableOn_Ioi_one_rpow_mul_log_pow hz k).const_mul _)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_const_mul, integral_Ioi_one_rpow_mul_log_pow hz]
  ring

theorem integrableOn_rpow_mul_mellinLogTail {d : ℕ} (p : Fin (d + 1) → ℝ) {z : ℝ} (hz : z < 1) :
    IntegrableOn (fun v => v ^ (z - 1) * mellinLogTail p v) (Ioi 0) := by
  have h : IntegrableOn (fun v : ℝ => ∑ k : Fin (d + 1),
      p k * (v ^ (z - 2) * Real.log v ^ (k : ℕ))) (Ioi 1) :=
    integrable_finsetSum (Finset.univ : Finset (Fin (d + 1)))
      (f := fun k v => p k * (v ^ (z - 2) * Real.log v ^ (k : ℕ)))
      (fun k _ => (integrableOn_Ioi_one_rpow_mul_log_pow hz k).const_mul _)
  refine ((h.integrable_indicator measurableSet_Ioi).integrableOn).congr_fun
    (fun v (hv : (0 : ℝ) < v) => (rpow_mul_mellinLogTail_eq p hv).symm) measurableSet_Ioi

/-- ★★★ **The Mellin transfer for a log-polynomial tail**: for `Z = q + tail`,
`∫₀^∞ v^{z−1} Z − Σ_k p_k k!/(1−z)^{k+1} → ∫₀^∞ q` as `z → 1⁻`. -/
theorem tendsto_mellin_sub_logPolynomial {d : ℕ} (p : Fin (d + 1) → ℝ) {q : ℝ → ℝ} {a : ℝ}
    (ha : a < 1) (hq : Measurable q)
    (hsmall : IntegrableOn (fun v => v ^ (a - 1) * q v) (Ioc 0 1))
    (hlarge : IntegrableOn q (Ioi 1)) :
    Tendsto (fun z : ℝ => (∫ v in Ioi (0 : ℝ), v ^ (z - 1) * (q v + mellinLogTail p v)) -
      ∑ k : Fin (d + 1), p k * ((k : ℕ).factorial : ℝ) / (1 - z) ^ ((k : ℕ) + 1))
      (𝓝[<] (1 : ℝ)) (𝓝 (∫ v in Ioi (0 : ℝ), q v)) := by
  refine (tendsto_mellin_residual ha hq hsmall hlarge).congr' ?_
  filter_upwards [Ioo_mem_nhdsLT ha] with z hz
  have e : (fun v : ℝ => v ^ (z - 1) * (q v + mellinLogTail p v)) =
      fun v => v ^ (z - 1) * q v + v ^ (z - 1) * mellinLogTail p v := by
    funext v; ring
  rw [e, integral_add (integrableOn_rpow_mul_residual hq hsmall hlarge hz.1.le hz.2.le)
    (integrableOn_rpow_mul_mellinLogTail p hz.2), integral_rpow_mul_mellinLogTail p hz.2]
  ring

end Grammar
