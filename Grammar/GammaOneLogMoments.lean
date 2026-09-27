/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.GaussJlogExact
import Grammar.PowerLogFaceCertificate
import Grammar.PolynomialJetTools

/-!
# The log moments of `e^{−u}` at `Γ(1)` and the renormalised integrals for every power

`G_r = ∫₀^∞ e^{−u} log^r u du` (`gammaOneLogMoment`; formally `Γ^{(r)}(1)`, not identified here),
integrable for every `r` (`integrableOn_exp_neg_mul_log_pow`: the DCXLVIII certificate
`(1 + |log u|)^r` near `0`, `log u ≤ u` beyond `1` against `u^r e^{−u}`), and the renormalised
integrals of DCXI/DCXXXVIII for every power (Astra round 21, the `J_k` bridge, stage 1):
★★ `integral_renormalised_exp_log_pow (r) : ∫₀^∞ (e^{−u} − 1_{(0,1]}(u)) log^r u/u du =
G_{r+1}/(r+1)`,
by the split integration by parts with `F₋ = (e^{−u} − 1) log^{r+1}u/(r+1)` on `(0,1)` and
`F₊ = e^{−u} log^{r+1}u/(r+1)` on `(1,∞)` (all endpoint terms vanish: `log 1 = 0`,
`u log^{r+1} u → 0` at `0⁺`, `e^{−u} log^{r+1} u → 0` at `∞`).  Comparing with DCXI and DCXXXVIII:
`G₀ = 1`, `G₁ = −γ`, `G₂ = γ² + π²/6` (`gammaOneLogMoment_zero/one/two`), with no new
differentiation under the integral.  Examples_slop §2.
Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

/-- `G_r = ∫₀^∞ e^{−u} log^r u du`. -/
noncomputable def gammaOneLogMoment (r : ℕ) : ℝ :=
  ∫ u in Ioi (0 : ℝ), Real.exp (-u) * Real.log u ^ r

/-! ### Integrability -/

/-- `|log u|^r ≤ (1 + |log u|)^r`. -/
theorem abs_log_pow_le_one_add_abs (u : ℝ) (r : ℕ) : |Real.log u| ^ r ≤ (1 + |Real.log u|) ^ r :=
  pow_le_pow_left₀ (abs_nonneg _) (by linarith [abs_nonneg (Real.log u)]) r

theorem integrableOn_one_add_abs_log_pow_Ioc (r : ℕ) :
    IntegrableOn (fun u : ℝ => (1 + |Real.log u|) ^ r) (Ioc 0 1) := by
  have h := integrableOn_rpow_mul_logWeight (a := 0) (by norm_num) r
  simp only [Real.rpow_zero, one_mul] at h
  rwa [integrableOn_Ioc_iff_integrableOn_Ioo]

theorem measurable_exp_neg_mul_log_pow (r : ℕ) :
    Measurable fun u : ℝ => Real.exp (-u) * Real.log u ^ r :=
  (Real.measurable_exp.comp measurable_neg).mul (Real.measurable_log.pow_const r)

/-- On `[1, ∞)`, `0 ≤ log u ≤ u`. -/
theorem log_le_self_of_one_le {u : ℝ} (hu : 1 ≤ u) : Real.log u ≤ u := by
  linarith [Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < u)]

theorem integrableOn_exp_neg_mul_log_pow_Ioi_one (r : ℕ) :
    IntegrableOn (fun u : ℝ => Real.exp (-u) * Real.log u ^ r) (Ioi 1) := by
  have h := (integrableOn_rpow_mul_exp_neg_rpow (s := r) (p := 1)
    (by have := Nat.cast_nonneg (α := ℝ) r; linarith) one_pos).mono_set
    (Ioi_subset_Ioi zero_le_one)
  refine h.mono' (measurable_exp_neg_mul_log_pow r).aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Eventually.of_forall fun u hu => ?_
  have hu1 : (1 : ℝ) < u := hu
  have hl0 : 0 ≤ Real.log u := Real.log_nonneg hu1.le
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_pow, abs_of_nonneg hl0,
    Real.rpow_one, Real.rpow_natCast, mul_comm]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hl0 (log_le_self_of_one_le hu1.le) r)
    (Real.exp_pos _).le

theorem integrableOn_exp_neg_mul_log_pow_Ioc (r : ℕ) :
    IntegrableOn (fun u : ℝ => Real.exp (-u) * Real.log u ^ r) (Ioc 0 1) := by
  refine (integrableOn_one_add_abs_log_pow_Ioc r).mono'
    (measurable_exp_neg_mul_log_pow r).aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioc]
  refine Eventually.of_forall fun u hu => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_pow]
  calc Real.exp (-u) * |Real.log u| ^ r ≤ 1 * |Real.log u| ^ r :=
        mul_le_mul_of_nonneg_right (Real.exp_le_one_iff.2 (by linarith [hu.1])) (by positivity)
    _ ≤ (1 + |Real.log u|) ^ r := by rw [one_mul]; exact abs_log_pow_le_one_add_abs u r

/-- ★★ `e^{−u} log^r u` is integrable on `(0, ∞)` for every `r`. -/
theorem integrableOn_exp_neg_mul_log_pow (r : ℕ) :
    IntegrableOn (fun u : ℝ => Real.exp (-u) * Real.log u ^ r) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  exact (integrableOn_exp_neg_mul_log_pow_Ioc r).union (integrableOn_exp_neg_mul_log_pow_Ioi_one r)

/-- `|e^{−u} − 1| ≤ u` for `u ≥ 0`. -/
theorem abs_exp_neg_sub_one_le {u : ℝ} (hu : 0 ≤ u) : |Real.exp (-u) - 1| ≤ u := by
  have h1 : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have h2 : -u + 1 ≤ Real.exp (-u) := Real.add_one_le_exp (-u)
  rw [abs_of_nonpos (by linarith)]
  linarith

theorem measurable_renormalised_log_pow (r : ℕ) :
    Measurable fun u : ℝ => (Real.exp (-u) - (Ioc 0 1).indicator 1 u) * Real.log u ^ r / u :=
  (((Real.measurable_exp.comp measurable_neg).sub
    (measurable_const.indicator measurableSet_Ioc)).mul (Real.measurable_log.pow_const r)).div
    measurable_id

theorem integrableOn_renormalised_log_pow_Ioc (r : ℕ) :
    IntegrableOn (fun u : ℝ => (Real.exp (-u) - (Ioc 0 1).indicator 1 u) * Real.log u ^ r / u)
      (Ioc 0 1) := by
  refine (integrableOn_one_add_abs_log_pow_Ioc r).mono'
    (measurable_renormalised_log_pow r).aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioc]
  refine Eventually.of_forall fun u hu => ?_
  have hu0 : 0 < u := hu.1
  rw [indicator_of_mem hu, Pi.one_apply, Real.norm_eq_abs, abs_div, abs_mul, abs_pow,
    abs_of_pos hu0, div_le_iff₀ hu0]
  calc |Real.exp (-u) - 1| * |Real.log u| ^ r ≤ u * (1 + |Real.log u|) ^ r :=
        mul_le_mul (abs_exp_neg_sub_one_le hu0.le) (abs_log_pow_le_one_add_abs u r) (by positivity)
          hu0.le
    _ = (1 + |Real.log u|) ^ r * u := mul_comm _ _

theorem integrableOn_renormalised_log_pow_Ioi_one (r : ℕ) :
    IntegrableOn (fun u : ℝ => (Real.exp (-u) - (Ioc 0 1).indicator 1 u) * Real.log u ^ r / u)
      (Ioi 1) := by
  refine (integrableOn_exp_neg_mul_log_pow_Ioi_one r).mono'
    (measurable_renormalised_log_pow r).aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Eventually.of_forall fun u hu => ?_
  have hu1 : (1 : ℝ) < u := hu
  have hu0 : 0 < u := by linarith
  rw [indicator_of_notMem (fun h : u ∈ Ioc (0 : ℝ) 1 => absurd h.2 (not_le.2 hu1)), sub_zero,
    Real.norm_eq_abs, abs_div, abs_of_pos hu0, div_le_iff₀ hu0, abs_mul,
    abs_of_pos (Real.exp_pos _), abs_pow, abs_of_nonneg (Real.log_nonneg hu1.le)]
  exact le_mul_of_one_le_right
    (mul_nonneg (Real.exp_pos _).le (pow_nonneg (Real.log_nonneg hu1.le) r)) hu1.le

theorem integrableOn_renormalised_log_pow (r : ℕ) :
    IntegrableOn (fun u : ℝ => (Real.exp (-u) - (Ioc 0 1).indicator 1 u) * Real.log u ^ r / u)
      (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  exact (integrableOn_renormalised_log_pow_Ioc r).union
    (integrableOn_renormalised_log_pow_Ioi_one r)

/-! ### The two primitives and their endpoint limits -/

/-- `u log^m u → 0` at `0⁺`. -/
theorem tendsto_mul_log_pow_nhdsGT_zero (m : ℕ) :
    Tendsto (fun u : ℝ => u * Real.log u ^ m) (𝓝[>] 0) (𝓝 0) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp only [pow_zero, mul_one]
    exact tendsto_id.mono_left nhdsWithin_le_nhds
  · have hm' : (0 : ℝ) < 1 / m := by positivity
    have h := (tendsto_log_mul_rpow_nhdsGT_zero hm').pow m
    simp only [zero_pow hm.ne'] at h
    refine h.congr' (eventually_nhdsWithin_of_forall fun u hu => ?_)
    have hu0 : (0 : ℝ) < u := hu
    rw [mul_pow, ← Real.rpow_natCast (u ^ (1 / (m : ℝ))) m, ← Real.rpow_mul hu0.le,
      show 1 / (m : ℝ) * m = 1 by field_simp, Real.rpow_one, mul_comm]

/-- `e^{−u} log^m u → 0` at `∞`. -/
theorem tendsto_exp_neg_mul_log_pow_atTop (m : ℕ) :
    Tendsto (fun u : ℝ => Real.exp (-u) * Real.log u ^ m) atTop (𝓝 0) := by
  have h := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero m
  refine squeeze_zero_norm' ?_ h
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with u hu
  have hl0 : 0 ≤ Real.log u := Real.log_nonneg hu
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_pow, abs_of_nonneg hl0, mul_comm]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hl0 (log_le_self_of_one_le hu) m)
    (Real.exp_pos _).le

/-- The inner primitive `F₋ = (e^{−u} − 1) log^{r+1}u/(r+1)`. -/
theorem hasDerivAt_inner_primitive (r : ℕ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun u : ℝ => (Real.exp (-u) - 1) * Real.log u ^ (r + 1) / (r + 1))
      ((Real.exp (-u) - 1) * Real.log u ^ r / u - Real.exp (-u) * Real.log u ^ (r + 1) / (r + 1))
      u := by
  have he : HasDerivAt (fun u : ℝ => Real.exp (-u) - 1) (-Real.exp (-u)) u := by
    refine (((Real.hasDerivAt_exp (-u)).comp u (hasDerivAt_neg u)).sub_const 1).congr_deriv ?_
    ring
  have hl := (Real.hasDerivAt_log hu.ne').pow (r + 1)
  refine ((he.mul hl).div_const ((r : ℝ) + 1)).congr_deriv ?_
  have hr : ((r : ℝ) + 1) ≠ 0 := by positivity
  simp only [Pi.pow_apply, Nat.add_sub_cancel]
  push_cast
  field_simp
  ring

/-- The outer primitive `F₊ = e^{−u} log^{r+1}u/(r+1)`. -/
theorem hasDerivAt_outer_primitive (r : ℕ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun u : ℝ => Real.exp (-u) * Real.log u ^ (r + 1) / (r + 1))
      (Real.exp (-u) * Real.log u ^ r / u - Real.exp (-u) * Real.log u ^ (r + 1) / (r + 1)) u := by
  have he : HasDerivAt (fun u : ℝ => Real.exp (-u)) (-Real.exp (-u)) u := by
    refine ((Real.hasDerivAt_exp (-u)).comp u (hasDerivAt_neg u)).congr_deriv ?_
    ring
  have hl := (Real.hasDerivAt_log hu.ne').pow (r + 1)
  refine ((he.mul hl).div_const ((r : ℝ) + 1)).congr_deriv ?_
  have hr : ((r : ℝ) + 1) ≠ 0 := by positivity
  simp only [Pi.pow_apply, Nat.add_sub_cancel]
  push_cast
  field_simp
  ring

theorem tendsto_inner_primitive_zero (r : ℕ) :
    Tendsto (fun u : ℝ => (Real.exp (-u) - 1) * Real.log u ^ (r + 1) / (r + 1)) (𝓝[>] 0)
      (𝓝 0) := by
  have h0 := (tendsto_mul_log_pow_nhdsGT_zero (r + 1)).abs
  rw [abs_zero] at h0
  have h := h0.div_const ((r : ℝ) + 1)
  rw [zero_div] at h
  refine squeeze_zero_norm' (eventually_nhdsWithin_of_forall fun u hu => ?_) h
  have hu0 : (0 : ℝ) < u := hu
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < r + 1), abs_mul, abs_mul,
    abs_of_pos hu0]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (abs_exp_neg_sub_one_le hu0.le) (abs_nonneg _)) (by positivity)

/-! ### The integration by parts -/

/-- The inner piece: `∫₀¹ (e^{−u} − 1) log^r u/u = ∫₀¹ e^{−u} log^{r+1} u/(r+1)`. -/
theorem integral_renormalised_log_pow_Ioc (r : ℕ) :
    ∫ u in Ioc (0 : ℝ) 1, (Real.exp (-u) - (Ioc 0 1).indicator 1 u) * Real.log u ^ r / u =
      (∫ u in Ioc (0 : ℝ) 1, Real.exp (-u) * Real.log u ^ (r + 1)) / (r + 1) := by
  have hi1 := integrableOn_renormalised_log_pow_Ioc r
  have hi2 := integrableOn_exp_neg_mul_log_pow_Ioc (r + 1)
  have hf : IntegrableOn (fun u : ℝ => (Real.exp (-u) - 1) * Real.log u ^ r / u) (Ioc 0 1) :=
    hi1.congr_fun (fun u hu => by beta_reduce; rw [indicator_of_mem hu, Pi.one_apply])
      measurableSet_Ioc
  have hint : IntervalIntegrable (fun u : ℝ => (Real.exp (-u) - 1) * Real.log u ^ r / u -
      Real.exp (-u) * Real.log u ^ (r + 1) / (r + 1)) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    exact hf.sub (hi2.div_const _)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto zero_lt_one
    (fun u hu => hasDerivAt_inner_primitive r hu.1) hint (tendsto_inner_primitive_zero r)
    ((hasDerivAt_inner_primitive r one_pos).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  simp only [Real.log_one, zero_pow (Nat.succ_ne_zero r), mul_zero, zero_div, sub_zero] at hFTC
  rw [intervalIntegral.integral_of_le zero_le_one] at hFTC
  have e : ∫ u in Ioc (0 : ℝ) 1, (Real.exp (-u) - (Ioc 0 1).indicator 1 u) * Real.log u ^ r / u =
      ∫ u in Ioc (0 : ℝ) 1, (Real.exp (-u) - 1) * Real.log u ^ r / u :=
    setIntegral_congr_fun measurableSet_Ioc fun u hu => by rw [indicator_of_mem hu, Pi.one_apply]
  rw [e]
  have hsub := integral_sub (μ := volume.restrict (Ioc (0 : ℝ) 1))
    (f := fun u : ℝ => (Real.exp (-u) - 1) * Real.log u ^ r / u)
    (g := fun u : ℝ => Real.exp (-u) * Real.log u ^ (r + 1) / (r + 1)) hf (hi2.div_const _)
  rw [hFTC] at hsub
  rw [integral_div] at hsub
  linarith

/-- The outer piece: `∫₁^∞ e^{−u} log^r u/u = ∫₁^∞ e^{−u} log^{r+1} u/(r+1)`. -/
theorem integral_renormalised_log_pow_Ioi_one (r : ℕ) :
    ∫ u in Ioi (1 : ℝ), (Real.exp (-u) - (Ioc 0 1).indicator 1 u) * Real.log u ^ r / u =
      (∫ u in Ioi (1 : ℝ), Real.exp (-u) * Real.log u ^ (r + 1)) / (r + 1) := by
  have hi1 := integrableOn_renormalised_log_pow_Ioi_one r
  have hi2 := integrableOn_exp_neg_mul_log_pow_Ioi_one (r + 1)
  have hi1' : IntegrableOn (fun u : ℝ => Real.exp (-u) * Real.log u ^ r / u) (Ioi 1) :=
    hi1.congr_fun (fun u hu => by
      beta_reduce
      rw [indicator_of_notMem (fun h : u ∈ Ioc (0 : ℝ) 1 => absurd h.2 (not_le.2 hu)), sub_zero])
      measurableSet_Ioi
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto
    (hasDerivAt_outer_primitive r one_pos).continuousAt.continuousWithinAt
    (fun u (hu : 1 < u) => hasDerivAt_outer_primitive r (by linarith))
    (hi1'.sub (hi2.div_const _)) (by
      have := (tendsto_exp_neg_mul_log_pow_atTop (r + 1)).div_const ((r : ℝ) + 1)
      rwa [zero_div] at this)
  simp only [Real.log_one, zero_pow (Nat.succ_ne_zero r), mul_zero, zero_div, sub_zero] at hFTC
  have e : ∫ u in Ioi (1 : ℝ), (Real.exp (-u) - (Ioc 0 1).indicator 1 u) * Real.log u ^ r / u =
      ∫ u in Ioi (1 : ℝ), Real.exp (-u) * Real.log u ^ r / u :=
    setIntegral_congr_fun measurableSet_Ioi fun u hu => by
      rw [indicator_of_notMem (fun h : u ∈ Ioc (0 : ℝ) 1 => absurd h.2 (not_le.2 hu)), sub_zero]
  rw [e]
  rw [integral_sub hi1' (hi2.div_const _), integral_div] at hFTC
  linarith

/-- ★★ **The renormalised integral for every power**:
`∫₀^∞ (e^{−u} − 1_{(0,1]}(u)) log^r u/u du = G_{r+1}/(r+1)`. -/
theorem integral_renormalised_exp_log_pow (r : ℕ) :
    ∫ u in Ioi (0 : ℝ), (Real.exp (-u) - (Ioc 0 1).indicator 1 u) * Real.log u ^ r / u =
      gammaOneLogMoment (r + 1) / (r + 1) := by
  unfold gammaOneLogMoment
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one,
    setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (integrableOn_renormalised_log_pow_Ioc r) (integrableOn_renormalised_log_pow_Ioi_one r),
    setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (integrableOn_exp_neg_mul_log_pow_Ioc (r + 1))
      (integrableOn_exp_neg_mul_log_pow_Ioi_one (r + 1)),
    integral_renormalised_log_pow_Ioc, integral_renormalised_log_pow_Ioi_one, add_div]

/-! ### The first three moments from DCXI and DCXXXVIII -/

theorem gammaOneLogMoment_zero : gammaOneLogMoment 0 = 1 := by
  unfold gammaOneLogMoment
  simp only [pow_zero, mul_one]
  exact integral_exp_neg_Ioi_zero

/-- `G₁ = Γ'(1) = −γ`, from DCXI's renormalised integral. -/
theorem gammaOneLogMoment_one : gammaOneLogMoment 1 = -Real.eulerMascheroniConstant := by
  have h := integral_renormalised_exp_log_pow 0
  simp only [pow_zero, mul_one, Nat.cast_zero, zero_add, div_one] at h
  rw [← h]
  exact integral_renormalised_exp_inv

/-- `G₂ = Γ''(1) = γ² + π²/6`, from DCXXXVIII's renormalised integral. -/
theorem gammaOneLogMoment_two :
    gammaOneLogMoment 2 = Real.eulerMascheroniConstant ^ 2 + Real.pi ^ 2 / 6 := by
  have h := integral_renormalised_exp_log_pow 1
  simp only [pow_one, Nat.cast_one] at h
  rw [integral_renormalised_exp_log] at h
  linarith

end Grammar
