/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.Fluctuation

/-!
# The product of two uniform variables has density `−log u` (§20, two-dimensional log example)

For `φ` continuous on `[0,1]`,
★ `integral_integral_mul_eq_neg_log : ∫_0^1 ∫_0^1 φ(xy) dy dx = ∫_0^1 φ(u)(−log u) du`.
Proof: the inner integral is `Φ(x)/x` with `Φ(x) = ∫_0^x φ` (`inner_mul_integral`), and
`∫_0^1 Φ(x)/x dx = −∫_0^1 φ log` by the fundamental theorem of calculus with limits at the
singular endpoint for `F(x) = Φ(x) log x` (`F' = φ log + Φ/x`, `F → 0` at both ends since
`|Φ(x)| ≤ M x`). This is the change of variables `u = xy` behind the logarithm of the
two-dimensional normal-crossing example `K = x²y²`. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology intervalIntegral

namespace Grammar

namespace SmoothEngine

variable {φ : ℝ → ℝ}

/-- The inner integral: `∫_0^1 φ(xy) dy = x⁻¹ ∫_0^x φ`. -/
theorem inner_mul_integral {x : ℝ} (hx : 0 < x) :
    ∫ y in (0 : ℝ)..1, φ (x * y) = x⁻¹ * ∫ u in (0 : ℝ)..x, φ u := by
  rw [intervalIntegral.integral_comp_mul_left (fun u => φ u) hx.ne', mul_zero, mul_one,
    smul_eq_mul]

/-- The primitive is bounded by `M x`. -/
theorem abs_primitive_le {M : ℝ} (hM : ∀ u ∈ Icc (0 : ℝ) 1, |φ u| ≤ M) {x : ℝ} (hx0 : 0 ≤ x)
    (hx1 : x ≤ 1) : |∫ u in (0 : ℝ)..x, φ u| ≤ M * x := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := x) (C := M)
    (f := φ) fun u hu => by
      rw [uIoc_of_le hx0] at hu
      exact (Real.norm_eq_abs _).trans_le (hM u ⟨hu.1.le, hu.2.trans hx1⟩)
  rwa [Real.norm_eq_abs, sub_zero, abs_of_nonneg hx0] at h

/-- ★ **The product of two uniforms has density `−log u`**: for `φ` continuous on `[0,1]`,
`∫_0^1 ∫_0^1 φ(xy) dy dx = ∫_0^1 φ(u)(−log u) du`. -/
theorem integral_integral_mul_eq_neg_log (hφ : ContinuousOn φ (Icc 0 1)) :
    ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, φ (x * y) = ∫ u in (0 : ℝ)..1, φ u * (-Real.log u) := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hφ
  have hM' : ∀ u ∈ Icc (0 : ℝ) 1, |φ u| ≤ M := fun u hu =>
    (Real.norm_eq_abs _).symm.trans_le (hM u hu)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM' 0 ⟨le_rfl, zero_le_one⟩)
  set Φ : ℝ → ℝ := fun x => ∫ u in (0 : ℝ)..x, φ u with hΦ
  have hφint : IntervalIntegrable φ volume 0 1 :=
    (hφ.mono (by rw [uIcc_of_le zero_le_one])).intervalIntegrable
  -- Step 1: the inner integrals
  have h1 : ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, φ (x * y) = ∫ x in (0 : ℝ)..1, x⁻¹ * Φ x := by
    rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one]
    refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
    exact inner_mul_integral hx.1
  -- Step 2: the fundamental theorem of calculus for `F(x) = Φ(x) log x` on `(0,1)`
  have hΦcont : ContinuousOn Φ (Icc 0 1) := by
    have := intervalIntegral.continuousOn_primitive_interval (a := (0 : ℝ)) (b := 1) (μ := volume)
      (f := φ) (by rw [uIcc_of_le zero_le_one]; exact hφ.integrableOn_compact isCompact_Icc)
    rwa [uIcc_of_le zero_le_one] at this
  have hΦd : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt Φ (φ x) x := by
    intro x hx
    have hopen : IsOpen (Ioo (0 : ℝ) 1) := isOpen_Ioo
    have hφo : ContinuousOn φ (Ioo 0 1) := hφ.mono Ioo_subset_Icc_self
    exact intervalIntegral.integral_hasDerivAt_right
      ((hφ.mono (by
        rw [uIcc_of_le hx.1.le]
        exact Icc_subset_Icc le_rfl hx.2.le)).intervalIntegrable)
      (hφo.stronglyMeasurableAtFilter hopen x hx) (hφo.continuousAt (hopen.mem_nhds hx))
  have hFd : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun x => Φ x * Real.log x)
      (φ x * Real.log x + Φ x * x⁻¹) x := fun x hx =>
    (hΦd x hx).mul (Real.hasDerivAt_log hx.1.ne')
  -- integrability of the derivative on `[0,1]`
  have hint1 : IntervalIntegrable (fun x => φ x * Real.log x) volume 0 1 :=
    intervalIntegrable_log'.continuousOn_mul (by rw [uIcc_of_le zero_le_one]; exact hφ)
  have hint2 : IntervalIntegrable (fun x => Φ x * x⁻¹) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    refine Integrable.mono' (integrable_const M) ?_ ?_
    · refine (ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc)
      exact (hΦcont.mono Ioc_subset_Icc_self).mul
        (continuousOn_inv₀.mono fun x hx => ne_of_gt hx.1)
    · rw [ae_restrict_iff' measurableSet_Ioc]
      filter_upwards with x hx
      rw [Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos hx.1]
      calc |Φ x| * x⁻¹ ≤ M * x * x⁻¹ :=
            mul_le_mul_of_nonneg_right (abs_primitive_le hM' hx.1.le hx.2) (inv_nonneg.2 hx.1.le)
        _ = M := by rw [mul_assoc, mul_inv_cancel₀ hx.1.ne', mul_one]
  -- limits at the endpoints
  have hlim0 : Tendsto (fun x => Φ x * Real.log x) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hbig : Tendsto (fun x : ℝ => |Real.log x * x|) (𝓝[>] 0) (𝓝 0) := by
      have := (tendsto_log_mul_rpow_nhdsGT_zero (r := 1) one_pos).norm
      simpa using this
    have hbig' : Tendsto (fun x : ℝ => M * |Real.log x * x|) (𝓝[>] 0) (𝓝 0) := by
      simpa using hbig.const_mul M
    refine squeeze_zero_norm' ?_ hbig'
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with x hx
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hx.1]
    calc |Φ x| * |Real.log x| ≤ M * x * |Real.log x| :=
          mul_le_mul_of_nonneg_right (abs_primitive_le hM' hx.1.le hx.2.le) (abs_nonneg _)
      _ = M * (|Real.log x| * x) := by ring
  have hlim1 : Tendsto (fun x => Φ x * Real.log x) (𝓝[<] (1 : ℝ)) (𝓝 0) := by
    have hc : ContinuousWithinAt (fun x => Φ x * Real.log x) (Icc 0 1) 1 :=
      (hΦcont 1 ⟨zero_le_one, le_rfl⟩).mul
        ((Real.continuousAt_log one_ne_zero).continuousWithinAt)
    have h := hc.tendsto.mono_left (nhdsWithin_mono _ (Ioo_subset_Icc_self (a := (0 : ℝ))))
    rw [nhdsWithin_Ioo_eq_nhdsLT zero_lt_one] at h
    simpa using h
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto zero_lt_one hFd
    (hint1.add hint2) hlim0 hlim1
  rw [sub_zero, intervalIntegral.integral_add hint1 hint2] at hFTC
  -- assemble
  rw [h1]
  have h2 : ∫ x in (0 : ℝ)..1, x⁻¹ * Φ x = ∫ x in (0 : ℝ)..1, Φ x * x⁻¹ := by
    congr 1
    funext x
    ring
  rw [h2, show ∫ x in (0 : ℝ)..1, Φ x * x⁻¹ = -∫ x in (0 : ℝ)..1, φ x * Real.log x by linarith,
    ← intervalIntegral.integral_neg]
  congr 1
  funext u
  ring

end SmoothEngine

end Grammar
